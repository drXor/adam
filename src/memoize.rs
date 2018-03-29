//! Infrastructure for memoization

use std::collections::HashMap;
use std::sync::Mutex;
use std::hash::Hash;

pub struct Memo<K: Eq + Hash + Clone, V: Clone> {
    pub inner: Mutex<HashMap<K, V>>,
}

impl<K: Eq + Hash + Clone, V: Clone> Memo<K, V> {

    #[inline]
    pub fn get(&self, k: &K) -> Option<V> {
        self.inner.lock().unwrap().get(k).map(V::clone)
    }

    #[inline]
    pub fn insert(&self, k: &K, v: &V) {
        let mut map = self.inner.lock().unwrap();
        if !map.contains_key(k) {
            map.insert(k.clone(), v.clone());
        }
    }
}

macro_rules! memo {
    ($name:ident: $K:ty, $V:ty) => {
        lazy_static! {
            pub static ref $name: $crate::memoize::Memo<$K, $V> = {
                $crate::memoize::Memo { inner: ::std::sync::Mutex::new(::std::collections::HashMap::new()) }
            };
        }
    }
}

macro_rules! memo_check {
    ($name:ident, $k:expr) => {
        if let Some(x) = $name.get($k) {
            return x;
        }
    }
}

macro_rules! memo_return {
    ($name:ident, $k:expr, $v:expr) => {
        $name.insert(&$k, &$v);
        return $v
    }
}