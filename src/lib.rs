use num_traits::identities::One;
use range_alloc::RangeAllocator;
use std::borrow::Borrow;
use std::borrow::BorrowMut;
use std::clone::Clone;
use std::cmp::PartialOrd;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Deref;
use std::ops::Range;
use std::ops::Sub;
use std::sync::Arc;
use std::sync::Mutex;

pub trait RangeInternerKey: Eq + Hash + Send + Sync {}
pub trait RangeInternerVal<V>: Clone + Copy + Add<Output=V> + AddAssign + Sub<Output=V> + Eq + PartialOrd + Debug + One 
{}

impl <T> RangeInternerKey for T
where
T: Eq + Hash + Send + Sync {}

impl <T> RangeInternerVal<T> for T
where
T: Clone + Copy + Add<Output=T> + AddAssign + Sub<Output=T> + Eq + PartialOrd + Debug + One
{}

pub struct RangeInternerInner<K, V> {
    name: String,
    interner: HashMap<Arc<K>, Option<V>>,
    allocator: RangeAllocator<V>,
}

impl<K, V> Debug for RangeInternerInner<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.write_fmt(format_args!("RangeInterner '{}'", self.name))
    }
}

#[derive(Debug)]
pub struct RangeInterner<K, V> {
    inner: Arc<Mutex<RangeInternerInner<K, V>>>,
}

impl<K, V> Clone for RangeInterner<K, V> {
    fn clone(&self) -> Self {
        RangeInterner {
            inner: self.inner.clone(),
        }
    }
}

impl<K, V> PartialEq for RangeInterner<K,V> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    } 
}
impl<K, V> Eq for RangeInterner<K,V> {}

impl<K, V> RangeInterner<K, V>
{
    pub fn inner(&self) -> &Arc<Mutex<RangeInternerInner<K, V>>> {
        &self.inner
    }
    pub fn name(&self) -> String {
        self.inner.lock().unwrap().name.clone()
    }
}

impl<K, V> RangeInterner<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    pub fn new(name: &str, range: Range<V>) -> Self {
        RangeInterner {
            inner: Arc::new(Mutex::new(RangeInternerInner {
                name: name.to_string(),
                interner: HashMap::new(),
                allocator: RangeAllocator::new(range),
            })),
        }
    }

    /// See how many objects have been interned.
    pub fn num_objects_interned(&self) -> usize {
        self.inner.lock().unwrap().interner.len()
    }

    pub fn intern(&self, k: K) -> RangeIntern<K, V> {
        let mut interner_guard = self.inner.lock().unwrap();
        let interner: &mut RangeInternerInner<K, V> = interner_guard.borrow_mut();
        let (k, v) = match interner.interner.entry(Arc::new(k)) {
            Entry::Occupied(e) => (e.key().clone(), *e.get()),
            Entry::Vacant(e) => {
                let k = e.key().clone();
                let v = if let Ok(r) = interner.allocator.allocate_range(V::one()) {
                    e.insert(Some(r.start))
                } else {
                    e.insert(None)
                };
                (k, *v)
            }
        };
        RangeIntern {
            k,
            v,
            interner: self.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    k: Arc<K>,
    v: Option<V>,
    interner: RangeInterner<K, V>,
}

impl<K, V> RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    /// Return the number of references for this value.
    pub fn refcount(&self) -> usize {
        // One reference is held by the hashmap; we return the number of
        // references held by actual clients.
        Arc::strong_count(&self.k) - 1
    }

    pub fn key(&self) -> &K {
        &*self.k
    }

    pub fn val(&self) -> Option<V> {
        self.v
    }

    pub fn interner(&self) -> &RangeInterner<K,V> {
        &self.interner
    }
}

impl<K, V> Drop for RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    fn drop(&mut self) {
        let mut interner = self.interner.inner.lock().unwrap();
        if Arc::strong_count(&self.k) == 2 {
            let _ = interner.interner.remove(&self.k);
            if let Some(v) = self.v {
                interner.allocator.free_range(Range {
                    start: v,
                    end: v + V::one(),
                });
            }
        }
    }
}

impl<K, V> AsRef<K> for RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    fn as_ref(&self) -> &K {
        self.k.as_ref()
    }
}

impl<K, V> Borrow<K> for RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    fn borrow(&self) -> &K {
        self.as_ref()
    }
}
impl<K, V> Deref for RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    type Target = K;
    fn deref(&self) -> &K {
        self.as_ref()
    }
}

/// The hash implementation returns the hash of the pointer
/// value, not the hash of the value pointed to.  This should
/// be irrelevant, since there is a unique pointer for every
/// value, but it *is* observable, since you could compare the
/// hash of the pointer with hash of the data itself.
impl<K, V> Hash for RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::into_raw(self.k.clone()).hash(state);
    }
}

/// Efficiently compares two interned values by comparing their pointers.
impl<K, V> PartialEq for RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
    fn eq(&self, other: &RangeIntern<K, V>) -> bool {
        Arc::ptr_eq(&self.k, &other.k)
    }
}

impl<K, V> Eq for RangeIntern<K, V>
where
    K: RangeInternerKey,
    V: RangeInternerVal<V>,
{
}

impl<K, V> PartialOrd for RangeIntern<K, V>
where
    K: RangeInternerKey + PartialOrd,
    V: RangeInternerVal<V>,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_ref().partial_cmp(other)
    }
    fn lt(&self, other: &Self) -> bool {
        self.as_ref().lt(other)
    }
    fn le(&self, other: &Self) -> bool {
        self.as_ref().le(other)
    }
    fn gt(&self, other: &Self) -> bool {
        self.as_ref().gt(other)
    }
    fn ge(&self, other: &Self) -> bool {
        self.as_ref().ge(other)
    }
}

impl<K, V> Ord for RangeIntern<K, V>
where
    K: RangeInternerKey + Ord,
    V: RangeInternerVal<V>,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ref().cmp(other)
    }
}

#[cfg(test)]
mod tests {
    use crate::RangeInterner;
    use std::ops::Range;
    use std::thread;

    // Test basic functionality.
    #[test]
    fn basic() {
        let str_interner = RangeInterner::new("str_interner", Range { start: 10, end: 20 });
        assert_eq!(str_interner.intern("foo"), str_interner.intern("foo"));
        assert_ne!(str_interner.intern("foo"), str_interner.intern("bar"));
        // The above refs should be deallocated by now.
        assert_eq!(str_interner.num_objects_interned(), 0);

        let string_interner = RangeInterner::new("string_interner", Range { start: 10, end: 15 });
        let _interned1 = string_interner.intern("foo".to_string());
        {
            let interned2 = string_interner.intern("foo".to_string());
            let interned3 = string_interner.intern("bar".to_string());

            assert_eq!(interned2.refcount(), 2);
            assert_eq!(interned2.val(), Some(10));
            assert_eq!(interned3.refcount(), 1);
            assert_eq!(interned3.val(), Some(11));
            // We now have two unique interned strings: "foo" and "bar".
            assert_eq!(string_interner.num_objects_interned(), 2);
        }

        // "bar" is now gone. Value 11 gets freed.
        assert_eq!(string_interner.num_objects_interned(), 1);
        let interned4 = string_interner.intern("buzz".to_string());
        assert_eq!(interned4.val(), Some(11));

        // Exhaust address space.
        let interned12 = string_interner.intern("12".to_string());
        assert_eq!(interned12.val(), Some(12));
        let interned13 = string_interner.intern("13".to_string());
        assert_eq!(interned13.val(), Some(13));
        let interned14 = string_interner.intern("14".to_string());
        assert_eq!(interned14.val(), Some(14));
        let interned15 = string_interner.intern("15".to_string());
        assert_eq!(interned15.val(), None);
    }

    // Ordering should be based on values, not pointers.
    // Also tests `Display` implementation.
    #[test]
    fn sorting() {
        let interner = RangeInterner::new(
            "u32_interner",
            Range {
                start: 1_000_000,
                end: 2_000_000,
            },
        );
        let mut interned_vals = vec![
            interner.intern(4),
            interner.intern(2),
            interner.intern(5),
            interner.intern(0),
            interner.intern(1),
            interner.intern(3),
        ];
        let vals: Vec<String> = interned_vals
            .iter()
            .map(|v| format!("{}", v.val().unwrap()))
            .collect();
        assert_eq!(
            &vals.join(","),
            "1000000,1000001,1000002,1000003,1000004,1000005"
        );
        interned_vals.sort();
        let sorted: Vec<String> = interned_vals.iter().map(|v| format!("{}", **v)).collect();
        assert_eq!(&sorted.join(","), "0,1,2,3,4,5");
    }

    #[derive(Eq, PartialEq, Hash)]
    pub struct TestStruct2(String, u64);

    #[test]
    fn sequential() {
        let interner = RangeInterner::new(
            "struct2_interner",
            Range {
                start: 1_000_000,
                end: 2_000_000,
            },
        );
        for _i in 0..10_000 {
            let mut interned = Vec::with_capacity(100);
            for j in 0..100 {
                interned.push(interner.intern(TestStruct2("foo".to_string(), j)));
            }
        }

        assert_eq!(interner.num_objects_interned(), 0);
    }

    #[derive(Eq, PartialEq, Hash, Clone)]
    pub struct TestStruct(String, u64);

    // Quickly create and destroy a small number of interned objects from
    // multiple threads.
    #[test]
    fn multithreading1() {
        let interner = RangeInterner::new(
            "struct_interner",
            Range {
                start: 1_000_000,
                end: 2_000_000,
            },
        );
        let mut thandles = vec![];
        for _i in 0..10 {
            let interner = interner.clone();
            thandles.push(thread::spawn(move || {
                for _i in 0..100_000 {
                    let _interned1 = interner.intern(TestStruct("foo".to_string(), 5));
                    let _interned2 = interner.intern(TestStruct("bar".to_string(), 10));
                }
            }));
        }
        for h in thandles.into_iter() {
            h.join().unwrap()
        }

        assert_eq!(interner.num_objects_interned(), 0);
    }
}
