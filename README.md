# RcCell
A convenient wrapper for `Rc<RefCell<T>>>` and `Weak<RefCell<T>>>`.

The `RcCell` library adds two new structs:
- `RcCell<T>`: a wrapper for `Rc<RefCell<T>>`.
- `WeakCell<T>`: a wrapper for `Weak<RefCell<T>>`.

This library extends the [`rc-cell`](https://crates.io/crates/rc-cell) library.

## Example

```rust
use rccell::{RcCell, WeakCell};

let a = RcCell::new(1);     // a is a RcCell that wraps an Rc<RefCell<i32>>
let b = a.clone();          // You can create multiple RcCells pointing to the same data.

let mut c = a.borrow_mut();  // You can use borrow and borrow_mut methods as if  RcCells were RefCells
*c = 2;
// let mut d = b.borrow_mut()   You cannot create two RefMuts for the same RcCell.
drop(c);

assert!(a.try_borrow().is_ok());  // You can use try_borrow and try_borrow_mut to avoid panicking
// let d = a.unwrap()  You can use unwrap to get the inner value (if there is only one RcCell)
assert!(a.try_unwrap().is_err());  // You can use try_unwrap to avoid panicking

let d: WeakCell<i32> = b.downgrade();  // Use downgrade to create a WeakCell pointing to the same data
assert!(d.upgrade().is_some());  // Use the upgrade method to get a RcCell pointing to the same data as the WeakCell.
 ```
