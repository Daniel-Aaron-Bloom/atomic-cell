use std::mem;

use atomic_cell::{atomic::*, AtomicCell};
use Ordering::SeqCst;

#[test]
fn supported() {
    struct UsizeWrap(usize);
    struct U8Wrap(bool);
    struct I16Wrap(i16);
    #[repr(align(8))]
    struct U64Align8(u64);

    assert!(AtomicCell::<usize, AtomicUsize>::SUPPORTED);
    assert!(AtomicCell::<isize, AtomicIsize>::SUPPORTED);
    assert!(AtomicCell::<UsizeWrap, AtomicUsize>::SUPPORTED);

    assert!(AtomicCell::<(), AtomicUnit>::SUPPORTED);

    assert!(AtomicCell::<u8, AtomicU8>::SUPPORTED);
    assert!(AtomicCell::<i8, AtomicI8>::SUPPORTED);
    assert!(AtomicCell::<bool, AtomicBool>::SUPPORTED);
    assert!(AtomicCell::<U8Wrap, AtomicU8>::SUPPORTED);

    assert!(AtomicCell::<u16, AtomicU16>::SUPPORTED);
    assert!(AtomicCell::<i16, AtomicI16>::SUPPORTED);
    assert!(AtomicCell::<I16Wrap, AtomicI16>::SUPPORTED);

    assert!(AtomicCell::<u32, AtomicU32>::SUPPORTED);
    assert!(AtomicCell::<i32, AtomicI32>::SUPPORTED);
    assert!(AtomicCell::<u64, AtomicU64>::SUPPORTED);

    assert_eq!(mem::size_of::<U64Align8>(), 8);
    assert_eq!(mem::align_of::<U64Align8>(), 8);
    assert!(AtomicCell::<U64Align8, AtomicU64>::SUPPORTED);

    // AtomicU128 is unstable
    assert!(!AtomicCell::<u128, AtomicU64>::SUPPORTED);
}

#[test]
fn drops_unit() {
    static CNT: AtomicUsize = AtomicUsize::new(0);
    CNT.store(0, SeqCst);

    #[derive(Debug, PartialEq, Eq)]
    struct Foo();

    impl Foo {
        fn new() -> Foo {
            CNT.fetch_add(1, SeqCst);
            Foo()
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            CNT.fetch_sub(1, SeqCst);
        }
    }

    impl Default for Foo {
        fn default() -> Foo {
            Foo::new()
        }
    }

    let a = AtomicCell::<_, AtomicUnit>::new(Foo::new());

    assert_eq!(a.swap(Foo::new()), Foo::new());
    assert_eq!(CNT.load(SeqCst), 1);

    a.store(Foo::new());
    assert_eq!(CNT.load(SeqCst), 1);

    assert_eq!(a.swap(Foo::default()), Foo::new());
    assert_eq!(CNT.load(SeqCst), 1);

    drop(a);
    assert_eq!(CNT.load(SeqCst), 0);
}

#[test]
fn drops_u8() {
    static CNT: AtomicUsize = AtomicUsize::new(0);
    CNT.store(0, SeqCst);

    #[derive(Debug, PartialEq, Eq)]
    struct Foo(u8);

    impl Foo {
        fn new(val: u8) -> Foo {
            CNT.fetch_add(1, SeqCst);
            Foo(val)
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            CNT.fetch_sub(1, SeqCst);
        }
    }

    impl Default for Foo {
        fn default() -> Foo {
            Foo::new(0)
        }
    }

    let a = AtomicCell::<_, AtomicU8>::new(Foo::new(5));

    assert_eq!(a.swap(Foo::new(6)), Foo::new(5));
    assert_eq!(a.swap(Foo::new(1)), Foo::new(6));
    assert_eq!(CNT.load(SeqCst), 1);

    a.store(Foo::new(2));
    assert_eq!(CNT.load(SeqCst), 1);

    assert_eq!(a.swap(Foo::default()), Foo::new(2));
    assert_eq!(CNT.load(SeqCst), 1);

    assert_eq!(a.swap(Foo::default()), Foo::new(0));
    assert_eq!(CNT.load(SeqCst), 1);

    drop(a);
    assert_eq!(CNT.load(SeqCst), 0);
}

#[test]
fn drops_usize() {
    static CNT: AtomicUsize = AtomicUsize::new(0);
    CNT.store(0, SeqCst);

    #[derive(Debug, PartialEq, Eq)]
    struct Foo(usize);

    impl Foo {
        fn new(val: usize) -> Foo {
            CNT.fetch_add(1, SeqCst);
            Foo(val)
        }
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            CNT.fetch_sub(1, SeqCst);
        }
    }

    impl Default for Foo {
        fn default() -> Foo {
            Foo::new(0)
        }
    }

    let a = AtomicCell::<_, AtomicUsize>::new(Foo::new(5));

    assert_eq!(a.swap(Foo::new(6)), Foo::new(5));
    assert_eq!(a.swap(Foo::new(1)), Foo::new(6));
    assert_eq!(CNT.load(SeqCst), 1);

    a.store(Foo::new(2));
    assert_eq!(CNT.load(SeqCst), 1);

    assert_eq!(a.swap(Foo::default()), Foo::new(2));
    assert_eq!(CNT.load(SeqCst), 1);

    assert_eq!(a.swap(Foo::default()), Foo::new(0));
    assert_eq!(CNT.load(SeqCst), 1);

    drop(a);
    assert_eq!(CNT.load(SeqCst), 0);
}

#[test]
fn modular_u8() {
    #[derive(Clone, Copy, Eq, Debug, Default)]
    struct Foo(u8);

    impl PartialEq for Foo {
        fn eq(&self, other: &Foo) -> bool {
            self.0 % 5 == other.0 % 5
        }
    }

    let a = AtomicCell::<_, AtomicU8>::new(Foo(1));

    assert_eq!(a.load(), Foo(1));
    assert_eq!(a.swap(Foo(2)), Foo(11));
    assert_eq!(a.load(), Foo(52));

    a.store(Foo(0));
    assert_eq!(a.compare_exchange::<true>(Foo(0), Foo(5)), Ok(Foo(100)));
    assert_eq!(a.load().0, 5);
    assert_eq!(a.compare_exchange::<true>(Foo(10), Foo(15)), Ok(Foo(100)));
    assert_eq!(a.load().0, 15);
}

#[test]
fn modular_usize() {
    #[derive(Clone, Copy, Eq, Debug, Default)]
    struct Foo(usize);

    impl PartialEq for Foo {
        fn eq(&self, other: &Foo) -> bool {
            self.0 % 5 == other.0 % 5
        }
    }

    let a = AtomicCell::<_, AtomicUsize>::new(Foo(1));

    assert_eq!(a.load(), Foo(1));
    assert_eq!(a.swap(Foo(2)), Foo(11));
    assert_eq!(a.load(), Foo(52));

    a.store(Foo(0));
    assert_eq!(a.compare_exchange::<true>(Foo(0), Foo(5)), Ok(Foo(100)));
    assert_eq!(a.load().0, 5);
    assert_eq!(a.compare_exchange::<true>(Foo(10), Foo(15)), Ok(Foo(100)));
    assert_eq!(a.load().0, 15);
}
