use core::marker::PhantomData;
use core::ops::Mul;
use sealed::sealed;
use typenum::Unsigned;

pub enum SizeKind {
    Finite(usize),
    Infinite,
}

pub const fn flatten_size(outer: SizeKind, inner: SizeKind) -> SizeKind {
    match (outer, inner) {
        (SizeKind::Finite(n), SizeKind::Finite(m)) => SizeKind::Finite(n * m),
        (_, SizeKind::Finite(0)) => SizeKind::Finite(0),
        (SizeKind::Finite(0), _) => SizeKind::Finite(0),
        (SizeKind::Infinite, _) => SizeKind::Infinite,
        (_, SizeKind::Infinite) => SizeKind::Infinite,
    }
}

#[sealed]
pub trait Size {
    const STATIC_SIZE: Option<SizeKind>;

    fn size(&self) -> SizeKind;
}

#[sealed]
pub trait ToSize {
    type Size: Size;
}

pub struct StaticSize<N: Unsigned>(PhantomData<N>);

#[sealed]
impl<N: Unsigned> Size for StaticSize<N> {
    const STATIC_SIZE: Option<SizeKind> = Some(SizeKind::Finite(N::USIZE));

    fn size(&self) -> SizeKind {
        SizeKind::Finite(N::to_usize())
    }
}

pub struct DynamicSize(pub usize);

#[sealed]
impl Size for DynamicSize {
    const STATIC_SIZE: Option<SizeKind> = None;

    fn size(&self) -> SizeKind {
        SizeKind::Finite(self.0)
    }
}

pub struct InfiniteSize;

#[sealed]
impl Size for InfiniteSize {
    const STATIC_SIZE: Option<SizeKind> = Some(SizeKind::Infinite);

    fn size(&self) -> SizeKind {
        SizeKind::Infinite
    }
}

#[sealed]
pub trait IsFinite {}

#[sealed]
impl<N: Unsigned> IsFinite for StaticSize<N> {}

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
impl<N: Unsigned, M: Unsigned> IsEqual<StaticSize<M>> for StaticSize<N> 
where 
    N: typenum::IsEqual<M> 
{}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsLessThan<StaticSize<M>> for StaticSize<N> 
where 
    N: typenum::IsLess<M> 
{}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsLessOrEqual<StaticSize<M>> for StaticSize<N> 
where 
    N: typenum::IsLessOrEqual<M> 
{}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsGreaterThan<StaticSize<M>> for StaticSize<N> 
where 
    N: typenum::IsGreater<M> 
{}

#[rustfmt::skip]
#[sealed]
impl<N: Unsigned, M: Unsigned> IsGreaterOrEqual<StaticSize<M>> for StaticSize<N> 
where
    N: typenum::IsGreaterOrEqual<M>
{}

#[sealed]
impl<N: Unsigned> IsLessThan<InfiniteSize> for StaticSize<N> {}

#[sealed]
impl<N: Unsigned> IsLessOrEqual<InfiniteSize> for StaticSize<N> {}

#[sealed]
impl<N: Unsigned> IsGreaterThan<StaticSize<N>> for InfiniteSize {}

#[sealed]
impl<N: Unsigned> IsGreaterOrEqual<StaticSize<N>> for InfiniteSize {}

pub struct FlattenSize<Outer, Inner>(PhantomData<(Outer, Inner)>);

#[sealed]
impl<N, M> ToSize for FlattenSize<StaticSize<N>, StaticSize<M>>
where
    N: Unsigned + Mul<M>,
    M: Unsigned,
    typenum::Prod<N, M>: Unsigned,
{
    type Size = StaticSize<typenum::Prod<N, M>>;
}

#[sealed]
impl<N: Unsigned> ToSize for FlattenSize<StaticSize<N>, DynamicSize> {
    type Size = DynamicSize;
}

#[sealed]
impl<N: Unsigned> ToSize for FlattenSize<DynamicSize, StaticSize<N>> {
    type Size = DynamicSize;
}

#[sealed]
impl<N: Unsigned> ToSize for FlattenSize<StaticSize<N>, InfiniteSize> {
    // TODO: write proper dispatch logic.
    type Size = DynamicSize;
}

#[sealed]
impl<N: Unsigned> ToSize for FlattenSize<InfiniteSize, StaticSize<N>> {
    // TODO: write proper dispatch logic.
    type Size = DynamicSize;
}

#[sealed]
impl ToSize for FlattenSize<DynamicSize, InfiniteSize> {
    type Size = DynamicSize;
}

#[sealed]
impl ToSize for FlattenSize<InfiniteSize, DynamicSize> {
    type Size = DynamicSize;
}
