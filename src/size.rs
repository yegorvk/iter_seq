use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ops::Mul;
use sealed::sealed;
use typenum::Unsigned;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum SizeKind {
    Finite(usize),
    Infinite,
}

impl PartialOrd for SizeKind {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl Ord for SizeKind {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (SizeKind::Finite(n), SizeKind::Finite(m)) => n.cmp(m),
            (SizeKind::Finite(_), SizeKind::Infinite) => Ordering::Less,
            (SizeKind::Infinite, SizeKind::Finite(_)) => Ordering::Greater,
            (SizeKind::Infinite, SizeKind::Infinite) => Ordering::Equal,
        }
    }
}

#[sealed]
pub trait Size {
    const SIZE: Option<SizeKind>;

    fn size(&self) -> SizeKind;
}

pub trait ToSize {
    type Size: Size;
}

#[derive(Debug, Copy, Clone)]
pub struct ConstSize<N: Unsigned>(PhantomData<N>);

#[sealed]
impl<N: Unsigned> Size for ConstSize<N> {
    const SIZE: Option<SizeKind> = Some(SizeKind::Finite(N::USIZE));

    fn size(&self) -> SizeKind {
        SizeKind::Finite(N::to_usize())
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct DynamicSize {
    size: usize,
}

#[sealed]
impl Size for DynamicSize {
    const SIZE: Option<SizeKind> = None;

    fn size(&self) -> SizeKind {
        SizeKind::Finite(self.size)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct InfiniteSize;

#[sealed]
impl Size for InfiniteSize {
    const SIZE: Option<SizeKind> = Some(SizeKind::Infinite);

    fn size(&self) -> SizeKind {
        SizeKind::Infinite
    }
}

#[sealed]
pub trait IsFinite {}

#[sealed]
impl<N: Unsigned> IsFinite for ConstSize<N> {}

#[sealed]
pub trait IsInfinite {}

#[sealed]
impl IsInfinite for InfiniteSize {}

#[sealed]
pub trait IsDynamic {}

#[sealed]
impl IsDynamic for DynamicSize {}

#[sealed]
pub trait IsLessThan<Rhs: Size> {}

#[sealed]
pub trait IsLessOrEqual<Rhs: Size> {}

#[sealed]
pub trait IsGreaterThan<Rhs: Size> {}

#[sealed]
pub trait IsGreaterOrEqual<Rhs: Size> {}

#[sealed]
pub trait IsEqual<Rhs: Size> {}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsEqual<ConstSize<M>> for ConstSize<N> 
where 
    N: typenum::IsEqual<M> 
{}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsLessThan<ConstSize<M>> for ConstSize<N> 
where 
    N: typenum::IsLess<M> 
{}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsLessOrEqual<ConstSize<M>> for ConstSize<N> 
where 
    N: typenum::IsLessOrEqual<M> 
{}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsGreaterThan<ConstSize<M>> for ConstSize<N> 
where 
    N: typenum::IsGreater<M> 
{}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsGreaterOrEqual<ConstSize<M>> for ConstSize<N> 
where
    N: typenum::IsGreaterOrEqual<M>
{}

#[sealed]
impl<N: Unsigned> IsLessThan<InfiniteSize> for ConstSize<N> {}

#[sealed]
impl<N: Unsigned> IsLessOrEqual<InfiniteSize> for ConstSize<N> {}

#[sealed]
impl<N: Unsigned> IsGreaterThan<ConstSize<N>> for InfiniteSize {}

#[sealed]
impl<N: Unsigned> IsGreaterOrEqual<ConstSize<N>> for InfiniteSize {}

#[doc(hidden)]
pub struct FlattenSize<Outer, Inner>(PhantomData<(Outer, Inner)>);

impl<N, M> ToSize for FlattenSize<ConstSize<N>, ConstSize<M>>
where
    N: Unsigned + Mul<M>,
    M: Unsigned,
    typenum::Prod<N, M>: Unsigned,
{
    type Size = ConstSize<typenum::Prod<N, M>>;
}

impl<N: Unsigned> ToSize for FlattenSize<ConstSize<N>, DynamicSize> {
    type Size = DynamicSize;
}

impl<N: Unsigned> ToSize for FlattenSize<DynamicSize, ConstSize<N>> {
    type Size = DynamicSize;
}

impl<N: Unsigned> ToSize for FlattenSize<ConstSize<N>, InfiniteSize> {
    // TODO: write proper dispatch logic.
    type Size = DynamicSize;
}

impl<N: Unsigned> ToSize for FlattenSize<InfiniteSize, ConstSize<N>> {
    // TODO: write proper dispatch logic.
    type Size = DynamicSize;
}

impl ToSize for FlattenSize<DynamicSize, InfiniteSize> {
    type Size = DynamicSize;
}

impl ToSize for FlattenSize<InfiniteSize, DynamicSize> {
    type Size = DynamicSize;
}

pub(crate) const fn flatten_size(outer: SizeKind, inner: SizeKind) -> SizeKind {
    match (outer, inner) {
        (SizeKind::Finite(n), SizeKind::Finite(m)) => SizeKind::Finite(n * m),
        (_, SizeKind::Finite(0)) => SizeKind::Finite(0),
        (SizeKind::Finite(0), _) => SizeKind::Finite(0),
        (SizeKind::Infinite, _) => SizeKind::Infinite,
        (_, SizeKind::Infinite) => SizeKind::Infinite,
    }
}
