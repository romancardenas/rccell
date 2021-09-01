//! A convenient wrapper for `Rc<RefCell<T>>>` and `Weak<RefCell<T>>>`.
//!
//! The `RcCell` library defines two structs:
//! - `RcCell<T>`: a wrapper for `Rc<RefCell<T>>`.
//! - `WeakCell<T>`: a wrapper for `Weak<RefCell<T>>`.
//!
//! ```rust
//! use rccell::{RcCell, WeakCell};
//!
//! let a = RcCell::new(1);     // a is a RcCell that wraps an Rc<RefCell<i32>>
//! let b = a.clone();          // You can create multiple RcCells pointing to the same data.
//!
//! let mut c = a.borrow_mut();  // You can use borrow and borrow_mut methods as if  RcCells were RefCells
//! *c = 2;
//! // let mut d = b.borrow_mut()   You cannot create two RefMuts for the same RcCell.
//! drop(c);
//!
//! assert!(a.try_borrow().is_ok());  // You can use try_borrow and try_borrow_mut to avoid panicking
//! // let d = a.unwrap()  You can use unwrap to get the inner value (if there is only one RcCell)
//! assert!(a.try_unwrap().is_err());  // You can use try_unwrap to avoid panicking
//!
//! let d: WeakCell<i32> = b.downgrade();  // Use downgrade to create a WeakCell pointing to the same data
//! assert!(d.upgrade().is_some());  // Use the upgrade method to get a RcCell pointing to the same data as the WeakCell.
//! ```
//!
//! `RcCell<T>` structs implement the `Hash` trait by using the value of their inner `Rc` pointer value.

use std::cell::{BorrowError, BorrowMutError, Ref, RefCell, RefMut};
use std::cmp::PartialEq;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::pin::Pin;
use std::rc::{Rc, Weak};

/// Wrapper for `Rc<RefCell<T>>`.
#[derive(Debug, Default, Eq)]
pub struct RcCell<T>(Rc<RefCell<T>>);

/// Version of `RefCell` that holds a non-owning reference to the managed allocation.
#[derive(Debug, Default)]
pub struct WeakCell<T>(Weak<RefCell<T>>);

impl<T> RcCell<T> {
    /// Constructs a new `RcCell<T>`.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// ```
    pub fn new(value: T) -> Self {
        Self(Rc::new(RefCell::new(value)))
    }

    /// Similar to [Rc::try_unwrap].
    /// Returns the inner value if the `RefCell` has only one strong reference.
    /// Otherwise, it returns an `Err` with the same `RefCell` that was passed in.
    /// Note that this function success even if there are multiple weak references.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// assert_eq!(RcCell::try_unwrap(x), Ok(1));
    ///
    /// let x = RcCell::new(2);
    /// let _y = RcCell::clone(&x);
    /// assert!(RcCell::try_unwrap(x).is_err());
    /// ```
    pub fn try_unwrap(self) -> Result<T, Self> {
        Rc::try_unwrap(self.0)
            .map(RefCell::into_inner)
            .map_err(Self)
    }

    /// Returns the inner value if the `RefCell` has only one strong reference. Otherwise, it panics.
    /// Note that this function success even if there are multiple weak references.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// assert_eq!(RcCell::unwrap(x), 1);
    ///
    /// let x = RcCell::new(2);
    /// let _y = RcCell::clone(&x);
    /// // assert_eq!(RcCell::unwrap(x), 2);  // This will panic, as there are two RcCells
    /// ```
    pub fn unwrap(self) -> T {
        self.try_unwrap().ok().unwrap()
    }

    /// Similar to [Rc::downgrade].
    /// Creates a new [WeakCell] pointer to this allocation.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// let weak_five = x.downgrade();
    /// ```
    pub fn downgrade(&self) -> WeakCell<T> {
        WeakCell(Rc::downgrade(&self.0))
    }

    /// Similar to [Rc::weak_count].
    /// Gets the number of [WeakCell] pointers to this allocation.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// let weak_five = x.downgrade();
    ///
    /// assert_eq!(RcCell::weak_count(&x), 1);
    /// ```
    pub fn weak_count(this: &Self) -> usize {
        Rc::weak_count(&this.0)
    }

    /// Similar to [Rc::strong_count].
    /// Gets the number of strong ([RcCell]) pointers to this allocation.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// let _y = x.clone();
    ///
    /// assert_eq!(RcCell::strong_count(&x), 2);
    /// ```
    pub fn strong_count(this: &Self) -> usize {
        Rc::strong_count(&this.0)
    }

    /// Similar to [Rc::ptr_eq].
    /// Returns `true` if two `RcCell`s point to the same allocation.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// let xx = x.clone();
    /// let y = RcCell::new(1);
    ///
    /// assert!(RcCell::ptr_eq(&x, &xx));
    /// assert!(!RcCell::ptr_eq(&x, &y));
    /// ```
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        Rc::ptr_eq(&this.0, &other.0)
    }

    /// Similar to [RefCell::try_borrow].
    /// Returns a [Ref] to the inner value if there is no [RefMut] pointing to the same allocation.
    /// Otherwise, it returns a `BorrowError`.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    ///
    /// let x_ref = x.try_borrow();
    /// assert!(x_ref.is_ok());
    /// ```
    pub fn try_borrow(&self) -> Result<Ref<T>, BorrowError> {
        self.0.try_borrow()
    }

    /// Similar to [RefCell::try_borrow_mut].
    /// Returns a [RefMut] to the inner value if there is no [RefMut] nor [Ref] pointing to the same allocation.
    /// Otherwise, it returns a `BorrowMutError`.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    ///
    /// let mut x_ref = x.try_borrow_mut();
    /// assert!(x_ref.is_ok());
    /// ```
    pub fn try_borrow_mut(&self) -> Result<RefMut<T>, BorrowMutError> {
        self.0.try_borrow_mut()
    }

    /// Similar to [RefCell::borrow].
    /// Returns a [Ref] to the inner value if there is no [RefMut] pointing to the same allocation.
    /// Otherwise, it panics.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// let x_ref = x.borrow();
    /// ```
    pub fn borrow(&self) -> Ref<T> {
        self.0.borrow()
    }

    /// Similar to [RefCell::borrow_mut].
    /// Returns a [RefMut] to the inner value if there is no [RefMut] nor [Ref] pointing to the same allocation.
    /// Otherwise, it panics.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let x = RcCell::new(1);
    /// let x_ref = x.borrow_mut();
    /// ```
    pub fn borrow_mut(&self) -> RefMut<T> {
        self.0.borrow_mut()
    }
}

impl<T: std::marker::Unpin> RcCell<T> {
    /// Constructs a new `Pin<RcCell<T>>`. It is only implemented if T implements [Unpin].
    pub fn pin(value: T) -> Pin<Self> {
        Pin::new(Self::new(value))
    }
}

impl<T> WeakCell<T> {
    /// Constructs a new `WeakCell<T>`, without allocating any memory.
    /// Calling [WeakCell::upgrade] on the return value always gives [None].
    /// # Examples
    /// ```rust
    /// use rccell::WeakCell;
    ///
    /// let empty: WeakCell<i32> = WeakCell::new();
    /// assert!(empty.upgrade().is_none());
    /// ```
    pub fn new() -> Self {
        Self(Weak::new())
    }

    /// Similar to [Weak::upgrade].
    /// Attempts to upgrade the `WeakCell` pointer to an `RcCell`.
    /// Returns `None` if the inner value has been dropped.
    /// # Examples
    /// ```rust
    /// use rccell::RcCell;
    ///
    /// let five = RcCell::new(5);
    ///
    /// let weak_five = five.downgrade();
    /// let strong_five = weak_five.upgrade();
    /// assert!(strong_five.is_some());
    ///
    /// drop(strong_five);
    /// drop(five);
    /// assert!(weak_five.upgrade().is_none());
    /// ```
    pub fn upgrade(&self) -> Option<RcCell<T>> {
        self.0.upgrade().map(RcCell)
    }

    /// Gets the number of strong (`RcCell`) pointers pointing to this allocation.
    /// If `self` was created using [WeakCell::new], this will return 0.
    pub fn strong_count(&self) -> usize {
        self.0.strong_count()
    }

    /// Gets the number of `WeakCell` pointers pointing to this allocation.
    /// If no strong pointers remain, this will return 0.
    pub fn weak_count(&self) -> usize {
        self.0.weak_count()
    }

    /// Returns `true` if the two `Weak`s point to the same allocation, or if both don't point to any allocation.
    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(&other.0)
    }
}

impl<T> Clone for RcCell<T> {
    fn clone(&self) -> Self {
        RcCell(self.0.clone())
    }
}

/// `RefCell<T>` does not implement `Deref`, and borrowing its inner value can cause a lot of panic errors.
/// Therefore, `Deref::deref` will return a reference to the inner `RefCell<T>`.
impl<T> Deref for RcCell<T> {
    type Target = RefCell<T>;
    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

/// `RefCell<T>` does not implement `PartialEq`, and borrowing its inner value can cause a lot of panic errors.
/// Therefore, `Hash` will only use the value of the `Rc` pointer inside `RefCell<T>`.
impl<T> Hash for RcCell<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.as_ptr().hash(state);
    }
}

/// `RefCell<T>` does not implement `PartialEq`, and borrowing its inner value can cause a lot of panic errors.
/// Therefore, `PartialEq` will check that two `RefCell<T>` point to the exact same allocation.
impl<T> PartialEq for RcCell<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ptr() == other.0.as_ptr()
    }
}

impl<T> Clone for WeakCell<T> {
    fn clone(&self) -> Self {
        WeakCell(self.0.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::RcCell;
    use std::collections::HashMap;

    #[derive(Debug, PartialEq, Eq)]
    struct DummyStruct {
        name: String,
    }
    impl DummyStruct {
        fn new(name: &str) -> Self {
            Self {
                name: name.to_string(),
            }
        }
    }

    #[test]
    fn test_try_unwrap() {
        let a = RcCell::new(DummyStruct::new("dummy"));
        let b = a.clone();
        let c = b.clone();
        let d = c.downgrade();
        let e = d.clone();
        assert!(RcCell::ptr_eq(&a, &c));
        assert_eq!(RcCell::weak_count(&a), 2);
        assert_eq!(RcCell::strong_count(&a), 3);

        assert!(RcCell::try_unwrap(a).is_err());
        assert!(d.upgrade().is_some());
        assert!(RcCell::try_unwrap(b).is_err());
        assert!(e.upgrade().is_some());
        let res = RcCell::try_unwrap(c);
        assert!(res.is_ok());
        assert_eq!(res.ok().unwrap().name, "dummy");
        assert!(d.upgrade().is_none());
        assert!(e.upgrade().is_none());
    }

    #[test]
    #[should_panic(expected = "called `Option::unwrap()` on a `None` value")]
    fn test_unwrap_panic() {
        let a = RcCell::new(DummyStruct::new("dummy"));
        let _b = a.clone();
        let _res = RcCell::unwrap(a);
    }

    #[test]
    fn test_unwrap_ok() {
        let a = RcCell::new(DummyStruct::new("dummy"));
        let _b = a.downgrade();
        assert_eq!(RcCell::unwrap(a).name, "dummy")
    }

    #[test]
    fn test_try_borrows() {
        let a = RcCell::new(DummyStruct::new("dummy"));
        let b = a.downgrade();
        assert_eq!(RcCell::weak_count(&a), 1);
        assert_eq!(RcCell::strong_count(&a), 1);
        assert!(a.try_borrow().is_ok());
        assert!(b.upgrade().is_some());
        assert!(b.upgrade().unwrap().try_borrow().is_ok());

        let c = b.upgrade().unwrap();
        assert!(a.try_borrow().is_ok());
        assert!(b.upgrade().is_some());
        assert!(b.upgrade().unwrap().try_borrow().is_ok());
        assert!(c.try_borrow().is_ok());

        let d = a.try_borrow_mut();
        assert!(d.is_ok());
        assert!(c.try_borrow().is_err());
        assert!(c.try_borrow_mut().is_err());
        drop(d);
        let d = a.try_borrow();
        assert!(d.is_ok());
        assert!(c.try_borrow().is_ok());
        assert!(c.try_borrow_mut().is_err());
    }

    #[test]
    #[should_panic(expected = "already borrowed: BorrowMutError")]
    fn test_borrow_mut_panic() {
        let a = RcCell::new(DummyStruct::new("dummy"));
        let _b = a.try_borrow();
        a.borrow_mut();
    }

    #[test]
    #[should_panic(expected = "already borrowed: BorrowMutError")]
    fn test_mut_borrow_panic() {
        let a = RcCell::new(DummyStruct::new("dummy"));
        let _b = a.try_borrow_mut();
        a.borrow_mut();
    }

    #[test]
    #[should_panic(expected = "already mutably borrowed: BorrowError")]
    fn test_mut_borrow_mut_panic() {
        let a = RcCell::new(DummyStruct::new("dummy"));
        let _b = a.try_borrow_mut();
        a.borrow();
    }

    #[test]
    fn test_borrow() {
        let a = RcCell::new(DummyStruct::new("dummy"));
        let b = a.clone();
        let c = RcCell::new(DummyStruct::new("dummy"));
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(*a.borrow(), *c.borrow());
        assert!(RcCell::ptr_eq(&a, &b));
        assert!(!RcCell::ptr_eq(&a, &c));

        a.borrow_mut().name = String::from("DUMMY");
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(*a.borrow(), *c.borrow());
    }

    #[test]
    fn test_hashmap() {
        let a = RcCell::new(DummyStruct::new("a"));
        let b = RcCell::new(DummyStruct::new("a"));
        let c = RcCell::new(DummyStruct::new("a"));
        assert!(!RcCell::ptr_eq(&a, &b));

        let mut map = HashMap::new();
        assert!(map.is_empty());
        assert!(map.insert(a.clone(), 1).is_none());
        assert!(map.insert(b.clone(), 2).is_none());
        assert!(map.insert(a.clone(), 3).is_some());
        assert!(map.get(&a).is_some());
        assert_eq!(map.get(&a).unwrap(), &3);
        assert!(map.get(&b).is_some());
        assert_eq!(map.get(&b).unwrap(), &2);
        assert!(map.get(&c).is_none());
    }
}
