use coq::kernel::esubst::{
    IdxError,
    IdxResult,
};
use coq::lib::hashcons::{HashconsedType, Hlist, Hstring, Table};
use coq::lib::hashset::combine;
use core::convert::TryFrom;
use ocaml::de::{
    Array,
    ORef,
};
use ocaml::values::{
    ConstraintType,
    Cstrs,
    Expr,
    HList,
    Instance,
    Int,
    Level,
    RawLevel,
    Univ,
    UnivConstraint,
};
use std::cmp::{Ord, Ordering};
use std::collections::{HashSet, HashMap};
use std::option::{NoneError};
use std::sync::{Arc};

/// Comparison on this type is pointer equality
struct CanonicalArc {
    univ: Level,
    lt: Vec<Level>,
    le: Vec<Level>,
    rank: Int,
    predicative: bool,
}

#[derive(Clone,Copy,Debug,Eq,PartialEq)]
enum FastOrder {
    Eq,
    Lt,
    Le,
    NLe,
}

/// A Level.t is either an alias for another one, or a canonical one,
/// for which we know the universes that are above
enum UnivEntry {
  Canonical(CanonicalArc),
  Equiv(Level),
}

pub struct Universes(UMap<UnivEntry>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnivError {
    Anomaly(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SubstError {
    NotFound,
    Idx(IdxError),
}

/// Support for universe polymorphism

/// Polymorphic maps from universe levels to 'a
pub type LMap<T> = HashMap<Level, T>;

pub type UMap<T> = LMap<T>;

type Hexpr = ();

pub type Helem<T, U> = Table<ORef<(T, Int, HList<T>)>, U>;

pub type Huniv = Helem<Expr, ()>;

pub type UnivResult<T> = Result<T, UnivError>;

pub type SubstResult<T> = Result<T, SubstError>;

pub trait Hashconsed<U> {
    fn hash(&self) -> IdxResult<i64>;
    fn eq(&self, &Self) -> bool;
    fn hcons<'a>(self, &'a U) -> Self
        where Self: ToOwned;
}

impl ::std::convert::From<IdxError> for SubstError {
    fn from(e: IdxError) -> Self {
        SubstError::Idx(e)
    }
}

impl<T, U> HashconsedType<U> for ORef<(T, Int, HList<T>)>
    where
        T: Hashconsed<U>,
        T: Clone,
{
    fn hash(&self) -> i64 {
        let (_, h, _) = **self;
        h
    }

    fn eq(&self, o2: &Self) -> bool {
        let (ref x1, _, ref l1) = **self;
        let (ref x2, _, ref l2) = **o2;
        x1.eq(x2) && l1.hequal(l2)
    }

    fn hashcons(self, u: &U) -> Self
    {
        // FIXME: Should these terms be new each time, or should we try to get more sharing?
        let (ref x, h, ref l) = *self;
        let x = x.to_owned().hcons(u);
        ORef(Arc::new((x, h, l.to_owned())))
    }
}

/// Note: the OCaml is needlessly generic over T.  At the end of the day, we only use HList with
/// Univ.
impl<T> HList<T>
{
    fn hash(&self) -> i64 {
        match *self {
            HList::Nil => 0,
            HList::Cons(ref o) => {
                let (_, h, _) = **o;
                h
            }
        }
    }

    pub fn hequal(&self, l2: &Self) -> bool {
        // Works assuming all HLists are already hconsed.
        match (self, l2) {
            (&HList::Nil, &HList::Nil) => true,
            (&HList::Cons(ref o1), &HList::Cons(ref o2)) => &**o1 as *const _ == &**o2 as *const _,
            (_, _) => false,
        }
    }

    /// No recursive call: the interface guarantees that all HLists from this
    /// program are already hashconsed. If we get some external HList, we can
    /// still reconstruct it by traversing it entirely.
    fn hcons<'a, U>(self, u: &'a Helem<T, U>) -> Self
        where
            T: Hashconsed<U>,
            T: Clone,
    {
        match self {
            HList::Nil => HList::Nil,
            HList::Cons(o) => HList::Cons(u.hcons(o)),
        }
    }

    fn nil() -> Self {
        HList::Nil
    }

    fn cons<'a, U>(x: T, l: Self, u: &'a Helem<T, U>) -> IdxResult<Self>
        where
            T: Hashconsed<U>,
            T: Clone,
    {
        let h = x.hash()?;
        let hl = l.hash();
        let h = combine::combine(h, hl);
        Ok(HList::Cons(ORef(Arc::new((x, h, l)))).hcons(u))
    }

    fn tip<'a, U>(e: T, u: &'a Helem<T, U>) -> IdxResult<Self>
        where
            T: Hashconsed<U>,
            T: Clone,
    {
        Self::cons(e, Self::nil(), u)
    }

    pub fn map<'a, U, F, E>(&self, mut f: F, u: &'a Helem<T, U>) -> Result<Self, E>
        where
            E: From<IdxError>,
            F: FnMut(&T) -> Result<T, E>,
            T: Hashconsed<U>,
            T: Clone,
    {
        match *self {
            HList::Nil => Ok(HList::nil()),
            HList::Cons(ref o) => {
                let (ref x, _, ref l) = **o;
                Ok(Self::cons(f(x)?, l.map(f, u)?, u)?)
            }
        }
    }

    /// Apriori hashconsing ensures that the map is equal to its argument
    pub fn smart_map<'a, U, F, E>(&self, f: F, u: &'a Helem<T, U>) -> Result<Self, E>
        where
            E: From<IdxError>,
            F: FnMut(&T) -> Result<T, E>,
            T: Hashconsed<U>,
            T: Clone,
    {
        self.map(f, u)
    }

    fn for_all2<F>(&self, l2: &Self, f: F) -> bool
        where
            F: Fn(&T, &T) -> bool,
    {
        let mut l1 = self.iter();
        let mut l2 = l2.iter();
        loop {
            match (l1.next(), l2.next()) {
                (None, None) => return true,
                (Some(x1), Some(x2)) => { if !f(x1, x2) { return false } },
                (_, _) => return false,
            }
        }
    }
}


impl RawLevel {
    fn equal(&self, y: &Self) -> bool {
        match (self, y) {
            (&RawLevel::Prop, &RawLevel::Prop) => true,
            (&RawLevel::Set, &RawLevel::Set) => true,
            (&RawLevel::Level(n, ref d), &RawLevel::Level(n_, ref d_)) =>
                n == n_ && d.equal(d_),
            (&RawLevel::Var(n), &RawLevel::Var(n_)) => n == n_,
            (_, _) => false,
        }
    }

    fn compare(&self, v: &Self) -> Ordering {
        match (self, v) {
            (&RawLevel::Prop, &RawLevel::Prop) => Ordering::Equal,
            (&RawLevel::Prop, _) => Ordering::Less,
            (_, &RawLevel::Prop) => Ordering::Greater,
            (&RawLevel::Set, &RawLevel::Set) => Ordering::Equal,
            (&RawLevel::Set, _) => Ordering::Less,
            (_, &RawLevel::Set) => Ordering::Greater,
            (&RawLevel::Level(i1, ref dp1), &RawLevel::Level(i2, ref dp2)) => {
                match i1.cmp(&i2) {
                    Ordering::Less => Ordering::Less,
                    Ordering::Greater => Ordering::Greater,
                    Ordering::Equal => dp1.compare(dp2),
                }
            },
            (&RawLevel::Level(_, _), _) => Ordering::Less,
            (_, &RawLevel::Level(_, _)) => Ordering::Greater,
            (&RawLevel::Var(n), &RawLevel::Var(m)) => n.cmp(&m),
        }
    }

    fn hequal(&self, y: &Self) -> bool {
        match (self, y) {
            (&RawLevel::Prop, &RawLevel::Prop) => true,
            (&RawLevel::Set, &RawLevel::Set) => true,
            (&RawLevel::Level(n, ref d), &RawLevel::Level(n_, ref d_)) =>
                n == n_ && HashconsedType::<Hlist<_, _, _, fn(&Hstring, _) -> _>>::eq(d, d_),
            (&RawLevel::Var(n), &RawLevel::Var(n_)) => n == n_,
            _ => false,
        }
    }

    /* fn hash(&self) -> i64 {
        match *self {
            RawLevel::Prop => combine::combinesmall(1, 0),
            RawLevel::Set => combine::combinesmall(1, 1),
            RawLevel::Var(n) => combine::combinesmall(2, n),
            RawLevel::Level(n, ref d) =>
                combine::combinesmall(3, combine::combine(n, d.hash()))
        }
    } */
}

/// Hashcons on levels + their hash
impl Level {
    fn hequal(&self, y: &Self) -> bool {
        self.hash == y.hash && self.data.hequal(&y.data)
    }

    fn hash(&self) -> i64 {
        self.hash
    }

    fn data(&self) -> &RawLevel {
        &self.data
    }

    pub fn equal(&self, y: &Self) -> bool {
        self.hash == y.hash &&
        self.data.equal(&y.data)
    }
}

/// For use in UMap.
/// TODO: Consider replacing this with a LevelKey wrapper, once it's been ascertained that this
/// won't cause problems.
impl PartialEq for Level {
    fn eq(&self, v: &Self) -> bool {
        // Comparison equals 0 for RawLevels and Levels is the same as equality.
        self.equal(v)
    }
}

/// For use in UMap.
/// TODO: Consider replacing this with a LevelKey wrapper, once it's been ascertained that this
/// won't cause problems.
impl Eq for Level {}

/// For use in UMap.
/// TODO: Consider replacing this with a LevelKey wrapper, once it's been ascertained that this
/// won't cause problems.
impl ::std::hash::Hash for Level {
    fn hash<H>(&self, state: &mut H)
        where
            H: ::std::hash::Hasher,
    {
        // Just write the hash directly to the state... note that if this isn't a dummy hasher,
        // this will try to scramble the hash, which is possibly not a good thing for collisions.
        state.write_i64(self.hash());
    }
}

impl Expr {
    fn hequal(&self, l2: &Self) -> bool {
        match (self, l2) {
            (&Expr(ref b, n), &Expr(ref b_, n_)) =>
                b.hequal(b_) && n == n_,
        }
    }

    fn hash(&self) -> IdxResult<i64> {
        let Expr(ref x, n) = *self;
        n.checked_add(x.hash()).ok_or(IdxError::from(NoneError))
    }
}

impl Hashconsed<()> for Expr {
    /// NOTE: Right now we assume Dps are all already hash consed, so we don't need HDp to
    /// implement this.
    fn hcons(self, _: &Hexpr) -> Self {
        self
    }

    fn hash(&self) -> IdxResult<i64> {
        Expr::hash(self)
    }

    /// Interestingly, this just uses normal equality, which suggests that we really *aren't*
    /// relying on the hash consing in any fundamental way...
    fn eq(&self, y: &Self) -> bool {
        self.equal(y)
    }
}

impl CanonicalArc {
    /// [compare_neq] : is [arcv] in the transitive upward closure of [arcu] ?

    /// In [strict] mode, we fully distinguish between LE and LT, while in
    /// non-strict mode, we simply answer LE for both situations.
    ///
    /// If [arcv] is encountered in a LT part, we could directly answer
    /// without visiting unneeded parts of this transitive closure.
    /// In [strict] mode, if [arcv] is encountered in a LE part, we could only
    /// change the default answer (1st arg [c]) from NLE to LE, since a strict
    /// constraint may appear later. During the recursive traversal,
    /// [lt_done] and [le_done] are universes we have already visited,
    /// they do not contain [arcv]. The 4rd arg is [(lt_todo,le_todo)],
    /// two lists of universes not yet considered, known to be above [arcu],
    /// strictly or not.
    ///
    /// We use depth-first search, but the presence of [arcv] in [new_lt]
    /// is checked as soon as possible : this seems to be slightly faster
    /// on a test.
    ///
    /// The universe should actually be in the universe map, or else it will return an error.
    fn fast_compare_neq(&self, arcv: &Self, strict: bool, g: &Universes) -> UnivResult<FastOrder> {
        // [c] characterizes whether arcv has already been related
        // to arcu among the lt_done,le_done universe
        let mut c = FastOrder::NLe;
        let mut lt_done = Vec::new();
        let mut le_done = Vec::new();
        let mut lt_todo : Vec<&CanonicalArc> = Vec::new();
        let mut le_todo = vec![self];
        loop {
            if let Some(arc) = lt_todo.pop() {
                if !lt_done.iter().any( |&arc_| arc as *const _ == arc_ as *const _) {
                    for u in arc.le.iter() {
                        let arc = u.repr(g)?;
                        if arc as *const _ == arcv as *const _ {
                            return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                        } else {
                            lt_todo.push(arc);
                        }
                    }
                    for u in arc.lt.iter() {
                        let arc = u.repr(g)?;
                        if arc as *const _ == arcv as *const _ {
                            return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                        } else {
                            lt_todo.push(arc);
                        }
                    }
                    lt_done.push(arc);
                }
            } else if let Some(arc) = le_todo.pop() {
                // lt_todo = []
                if arc as *const _ == arcv as *const _ {
                    // No need to continue inspecting universes above arc;
                    // if arcv is strictly above arc, then we would have a cycle.
                    // But we cannot answer LE yet, a stronger constraint may
                    // come later from [le_todo].
                    if strict {
                        c = FastOrder::Le;
                    } else {
                        return Ok(FastOrder::Le);
                    }
                } else {
                    if !(lt_done.iter().any( |&arc_| arc as *const _ == arc_ as *const _) ||
                         le_done.iter().any( |&arc_| arc as *const _ == arc_ as *const _)) {
                        for u in arc.lt.iter() {
                            let arc = u.repr(g)?;
                            if arc as *const _ == arcv as *const _ {
                                return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                            } else {
                                lt_todo.push(arc);
                            }
                        }
                        // Cannot use .extend here because we need to fail fast on failure.  There
                        // is probably a better way to deal with this.
                        for u in arc.le.iter() {
                            le_todo.push(u.repr(g)?);
                        }
                        le_done.push(arc);
                    }
                }
            } else {
                // lt_todo = [], le_todo = []
                return Ok(c)
            }
        }
    }

    // /// The universe should actually be in the universe map, or else it will return an error.
    // fn fast_compare(&self, arcv: &Self, g: &Universes) -> UnivResult<FastOrder> {
    //     if self as *const _ == arcv as *const _ { Ok(FastOrder::Eq) }
    //     else { self.fast_compare_neq(arcv, true, g) }
    // }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn is_leq(&self, arcv: &Self, g: &Universes) -> UnivResult<bool> {
        Ok(self as *const _ == arcv as *const _ ||
           match self.fast_compare_neq(arcv, false, g)? {
               FastOrder::NLe => false,
               FastOrder::Eq | FastOrder::Le | FastOrder::Lt => true,
           })
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn is_lt(&self, arcv: &Self, g: &Universes) -> UnivResult<bool> {
        if self as *const _ == arcv as *const _ {
            Ok(false)
        } else {
            self.fast_compare_neq(arcv, true, g).map( |c| match c {
                FastOrder::Lt => true,
                FastOrder::Eq | FastOrder::Le | FastOrder::NLe => false,
            })
        }
    }

    fn is_prop(&self) -> bool {
        self.univ.is_prop()
    }

    fn is_set(&self) -> bool {
        self.univ.is_set()
    }
}

impl Level {
    /// Worked out elsewhere; if this is wrong, we can figure out another way to get this value.
    const PROP : Self = Level { hash: 7, data: RawLevel::Prop };
    const SET : Self = Level { hash: 8, data: RawLevel::Set };

    fn is_prop(&self) -> bool {
        match self.data {
            RawLevel::Prop => true,
            _ => false,
        }
    }

    fn is_set(&self) -> bool {
        match self.data {
            RawLevel::Set => true,
            _ => false,
        }
    }

    fn compare(&self, v: &Self) -> Ordering {
        if self.hequal(v) { Ordering::Equal }
        else {
            match self.hash().cmp(&v.hash()) {
                Ordering::Equal => self.data().compare(v.data()),
                // FIXME: Is hash ordering really reliable?
                o => o,
            }
        }
    }

    /// Every Level.t has a unique canonical arc representative

    /// repr : universes -> Level.t -> canonical_arc
    /// canonical representative : we follow the Equiv links
    /// The universe should actually be in the universe map, or else it will return an error.
    /// Also note: if the map universe map contains Equiv cycles, this will loop forever!
    fn repr<'a>(&'a self, g: &'a Universes) -> UnivResult<&CanonicalArc> {
        let mut u = self;
        loop {
            match g.0.get(u) {
                Some(&UnivEntry::Equiv(ref v)) => { u = v },
                Some(&UnivEntry::Canonical(ref arc)) => return Ok(arc),
                None =>
                    return Err(UnivError::Anomaly(format!("Univ.repr: Universe {:?} undefined",
                                                          u))),
            }
        }
    }

    /// Invariants : compare(u,v) = EQ <=> compare(v,u) = EQ
    ///              compare(u,v) = LT or LE => compare(v,u) = NLE
    ///              compare(u,v) = NLE => compare(v,u) = NLE or LE or LT
    ///
    /// Adding u>=v is consistent iff compare(v,u) # LT
    ///  and then it is redundant iff compare(u,v) # NLE
    /// Adding u>v is consistent iff compare(v,u) = NLE
    ///  and then it is redundant iff compare(u,v) = LT

    /// Universe checks [check_eq] and [check_leq], used in coqchk

    /// First, checks on universe levels

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_equal(&self, v: &Level, g: &Universes) -> UnivResult<bool> {
        let arcu = self.repr(g)?;
        let arcv = v.repr(g)?;
        Ok(arcu as *const _ == arcv as *const _)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_eq(&self, v: &Level, g: &Universes) -> UnivResult<bool> {
        Ok(self.check_equal(v, g)?)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_smaller(&self, v: &Self, strict: bool, g: &Universes) -> UnivResult<bool> {
        let arcu = self.repr(g)?;
        let arcv = v.repr(g)?;
        if strict {
            arcu.is_lt(arcv, g)
        } else {
            Ok(arcu.is_prop()
               || (arcu.is_set() && arcv.predicative)
               || (arcu.is_leq(arcv, g)?))
        }
    }

    /// Substitute instance inst for ctx in csts
    fn subst_instance(&self, s: &Instance) -> SubstResult<Level> {
        Ok(match self.data {
            RawLevel::Var(n) => {
                // TODO: Check whether this get is handled at typechecking time?
                let n = usize::try_from(n).map_err(IdxError::from)?;
                // TODO: Check whether this is checked at typechecking time?
                s.get(n).ok_or(SubstError::NotFound)?
            },
            _ => self,
        }.clone())
    }
}

impl Expr {
    /// Worked out elsewhere; if this is wrong, we can figure out another way to get this value.
    const PROP : Self = Expr(Level::PROP, 0);

    const SET : Self = Expr(Level::SET, 0);

    const TYPE1 : Self = Expr(Level::SET, 1);

    fn make(l: Level) -> Self {
        Expr(l, 0)
    }

    fn is_prop(&self) -> bool {
        if let Expr(ref l, 0) = *self { l.is_prop() }
        else { false }
    }

    fn equal(&self, y: &Self) -> bool {
        let Expr(ref u, n) = *self;
        let Expr(ref v, n_) = *y;
        n == n_ && u.equal(v)
    }

    fn successor(&self) -> IdxResult<Self> {
        let Expr(ref u, n) = *self;
        if u.is_prop() { Ok(Self::TYPE1) }
        // NOTE: Assuming Dps are all maximally hconsed already when loaded from the file, we just
        // need to clone() here to retain maximal sharing.
        else { Ok(Expr(u.clone(), n.checked_add(1).ok_or(IdxError::from(NoneError))?)) }
    }

    fn addn(&self, k: Int) -> IdxResult<Self> {
        let Expr(ref u, n) = *self;
        if k == 0 { Ok(self.clone()) }
        else if u.is_prop() {
            Ok(Expr(Level::SET, n.checked_add(k).ok_or(IdxError::from(NoneError))?))
        } else {
            Ok(Expr(u.clone(), n.checked_add(k).ok_or(IdxError::from(NoneError))?))
        }
    }

    fn super_(&self, y: &Self) -> Result<bool, Ordering> {
        let Expr(ref u, n) = *self;
        let Expr(ref v, n_) = *self;
        match u.compare(v) {
            Ordering::Equal => if n < n_ { Ok(true) } else { Ok(false) },
            _ if self.is_prop() => Ok(true),
            _ if y.is_prop() => Ok(false),
            o => Err(o)
        }
    }

    fn map<F, E>(&self, f: F, u: &Hexpr) -> Result<Self, E>
        where
            F: Fn(&Level) -> Result<Level, E>,
    {
        let Expr(ref v, n) = *self;
        let v_ = f(v)?;
        Ok(if v_.is_prop() && n != 0 {
            Expr(Level::SET, n).hcons(u)
        } else {
            Expr(v_, n).hcons(u)
        })
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_equal(&self, y: &Self, g: &Universes) -> UnivResult<bool> {
        Ok(self.hequal(y) || {
            let Expr(ref u, n) = *self;
            let Expr(ref v, m) = *y;
            n == m && u.check_equal(v, g)?
        })
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_smaller(&self, &Expr(ref v, m): &Self, g: &Universes) -> UnivResult<bool> {
        let Expr(ref u, n) = *self;
        if n <= m {
            u.check_smaller(v, false, g)
        } else if n - m == 1 {
            // n - m is valid, because n > m, so 0 < n - m ≤ n ≤ i64::MAX.
            u.check_smaller(v, true, g)
        } else {
            Ok(false)
        }
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn exists_bigger(&self, l: &Univ, g: &Universes) -> UnivResult<bool> {
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        for ul_ in l.iter() {
            if self.check_smaller(ul_, g)? { return Ok(true) }
        }
        return Ok(false)
    }
}

impl Univ {
    pub fn equal(&self, y: &Self) -> bool {
        self.hequal(y) ||
        self.hash() == y.hash() &&
        self.for_all2(y, Expr::equal)
    }

    pub fn make(l: Level, u: &Huniv) -> IdxResult<Self> {
        Self::tip(Expr::make(l), u)
    }

    /// The lower predicative level of the hierarchy that contains (impredicative)
    /// Prop and singleton inductive types
    pub fn type0m(u: &Huniv) -> Self {
        // We know the hash for the lower levels of the hierarchy won't overflow,
        // so it's okay to unwrap it.
        Self::tip(Expr::PROP, u).unwrap()
    }

    /// The level of sets
    pub fn type0(u: &Huniv) -> Self {
        // We know the hash for the lower levels of the hierarchy won't overflow,
        // so it's okay to unwrap it.
        Self::tip(Expr::SET, u).unwrap()
    }

    /// When typing [Prop] and [Set], there is no constraint on the level,
    /// hence the definition of [type1_univ], the type of [Prop]
    pub fn type1(u: &Huniv) -> Self {
        // We know the hash for the lower levels of the hierarchy won't overflow,
        // so it's okay to unwrap it.
        Self::tip(Expr::SET.successor().unwrap(), u).unwrap()
    }

    pub fn is_type0m(&self) -> bool {
        // I believe type0m is:
        //    Cons (({ hash = 7; data = Prop }, 0), 459193, Nil)
        // Details worked out elsewhere; if they're wrong, we can fgure out something else.
        match *self {
            HList::Nil => false,
            HList::Cons(ref o) => {
                let (ref x, h, ref l) = **o;
                h == 459193 &&
                x.equal(&Expr::PROP) &&
                if let HList::Nil = *l { true } else { false }
            }
        }
    }

    pub fn is_type0(&self) -> bool {
        // I believe type0 is:
        //    Cons (({ hash = 8; data = Set }, 0), 524792, Nil)
        // Details worked out elsewhere; if they're wrong, we can fgure out something else.
        match *self {
            HList::Nil => false,
            HList::Cons(ref o) => {
                let (ref x, h, ref l) = **o;
                h == 524792 &&
                x.equal(&Expr::SET) &&
                if let HList::Nil = *l { true } else { false }
            }
        }
    }

    /// Returns the formal universe that lies just above the universe variable u.
    /// Used to type the sort u.
    pub fn super_(&self, u: &Huniv) -> IdxResult<Self> {
        self.map( |x| x.successor(), u)
    }

    pub fn addn(&self, n: Int, u: &Huniv) -> IdxResult<Self> {
        self.map( |x| x.addn(n), u)
    }

    pub fn merge_univs(&self, mut l2: &Self, u: &Huniv) -> IdxResult<Self> {
        let mut l1 = self;
        loop {
            match (l1, l2) {
                (&HList::Nil, _) => return Ok(l2.clone()),
                (_, &HList::Nil) => return Ok(l1.clone()),
                (&HList::Cons(ref o1), &HList::Cons(ref o2)) => {
                    let (ref h1, _, ref t1) = **o1;
                    let (ref h2, _, ref t2) = **o2;
                    match h1.super_(h2) {
                        Ok(true) => { /* h1 < h2 */ l1 = t1 },
                        Ok(false) => { l2 = t2 },
                        Err(c) => return match c {
                            Ordering::Less => /* h1 < h2 is name order */
                                Self::cons(h1.clone(), t1.merge_univs(l2, u)?, u),
                            _ => Self::cons(h2.clone(), l1.merge_univs(t2, u)?, u),
                        },
                    }
                },
            }
        }
    }

    fn sort(&self, tbl: &Huniv) -> IdxResult<Self> {
        fn aux(a: &Expr, mut l: Univ, tbl: &Huniv) -> IdxResult<Univ> {
            while let HList::Cons(o) = l {
                match a.super_(&(*o).0) {
                    Ok(false) => { l = (*o).2.clone(); },
                    Ok(true) => return Ok(HList::Cons(o)),
                    Err(Ordering::Less) => return Univ::cons(a.clone(), HList::Cons(o), tbl),
                    Err(_) =>
                        return Univ::cons((&(*o).0).clone(), aux(a, (&(*o).2).clone(), tbl)?, tbl),
                }
            }
            Univ::cons(a.clone(), l, tbl)
        }
        self.iter().fold(Ok(HList::nil()), |acc, a| aux(a, acc?, tbl))
    }

    /// Returns the formal universe that is greater than the universes u and v.
    /// Used to type the products.
    ///
    /// NOTE: mutates in place compared to the OCaml implementation.  Could easily
    /// be fixed not to.
    pub fn sup(&mut self, y: &Self, tbl: &Huniv) -> IdxResult<()> {
        *self = self.merge_univs(y, tbl)?;
        Ok(())
    }

    /// Then, checks on universes
    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_eq_univs(&self, l2: &Self, g: &Universes) -> UnivResult<bool> {
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        let exists = |x1: &Expr, l: &Univ| {
            for x2 in l.iter() {
                if x1.check_equal(x2, g)? { return Ok(true) }
            }
            Ok(false)
        };
        for x1 in self.iter() {
            if !exists(x1, l2)? { return Ok(false) }
        }
        for x2 in l2.iter() {
            if !exists(x2, self)? { return Ok(false) }
        }
        return Ok(true)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_eq(&self, v: &Self, g: &Universes) -> UnivResult<bool> {
        Ok(self.hequal(v) ||
           self.check_eq_univs(v, g)?)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn real_check_leq(&self, v: &Self, g: &Universes) -> UnivResult<bool> {
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        for ul in self.iter() {
            if !ul.exists_bigger(v, g)? { return Ok(false) }
        }
        return Ok(true)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_leq(&self, v: &Self, g: &Universes) -> UnivResult<bool> {
        Ok(self.hequal(v) ||
           self.is_type0m() ||
           self.check_eq_univs(v, g)? ||
           self.real_check_leq(v, g)?)
    }

    pub fn subst_instance(&self, s: &Instance, tbl: &Huniv) -> SubstResult<Univ> {
        let u_ = self.smart_map( |x| x.map( |u| u.subst_instance(s), &()), tbl)?;
        if self.hequal(&u_) { Ok(u_) }
        else { Ok(u_.sort(tbl)?) }
    }

    fn subst_expr_opt<'a, F>(&Expr(ref l, n): &'a Expr, tbl: &Huniv, fn_: &F) -> SubstResult<Self>
        where
            F: Fn(&'a Level) -> Option<&Self>,
    {
        Ok(fn_(l).ok_or(SubstError::NotFound)?.addn(n, tbl)?)
    }

    pub fn subst_univs<'a, F>(&'a self, tbl: &Huniv, fn_: F) -> IdxResult<Self>
        where
            F: Fn(&'a Level) -> Option<&Self>,
    {
        let mut subst = vec![];
        let mut nosubst = vec![];
        for u in self.iter() {
            match Self::subst_expr_opt(u, tbl, &fn_) {
                Ok(a) => subst.push(a),
                Err(SubstError::NotFound) => nosubst.push(u),
                Err(SubstError::Idx(e)) => return Err(e),
            }
        }
        if subst.is_empty() { Ok(self.clone()) }
        else {
            // FIXME: Lots of unnecessary reference counting going on here given that the HLists
            // are only intermediate structures.
            // TODO: Figure out whether the iterator reversal here is really necessary.
            let substs = subst.iter()
                              .rev()
                              .fold(Ok(HList::nil()),
                                    |acc, u| Self::merge_univs(&acc?, u, tbl));
            // TODO: Figure out whether the iterator reversal here is really necessary.
            nosubst.into_iter()
                   .rev()
                   .fold(substs,
                         |acc, u| Self::merge_univs(&acc?, &Self::tip(u.clone(), tbl)?, tbl))
        }
    }
}

impl Instance {
    pub fn empty() -> Self {
        Array(Arc::from(vec![]))
    }

    pub fn equal(&self, u: &Self) -> bool {
        &***self as *const _ == &***u as *const _ ||
        (self.is_empty() && u.is_empty()) ||
        (/* Necessary as universe instances might come from different modules and
            unmarshalling doesn't preserve sharing */
         self.len() == u.len() && self.iter().zip(u.iter()).all( |(x, y)| x.equal(y)))
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_eq(&self, t2: &Instance, g: &Universes) -> UnivResult<bool> {
        if &***self as *const _ == &***t2 as *const _ { return Ok(true) }
        if self.len() != t2.len() { return Ok(false) }
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        for (u, v) in self.iter().zip(t2.iter()) {
            if !u.check_eq(v, g)? {
                return Ok(false)
            }
        }
        return Ok(true)
    }

    /// Substitution functions

    pub fn subst_instance(&self, s: &Instance) -> SubstResult<Instance> {
        self.smart_map( |l| l.subst_instance(s), Level::hequal)
    }
}

/* impl Context {
    pub fn make(ctx: Instance, cst: Cstrs) -> Self {
        Context(ctx, cst)
    }
} */

impl Universes {
    fn check_constraint(&self, &UnivConstraint(ref l, d, ref r): &UnivConstraint
                       ) -> UnivResult<bool> {
        match d {
            ConstraintType::Eq => l.check_equal(r, self),
            ConstraintType::Le => l.check_smaller(r, false, self),
            ConstraintType::Lt => l.check_smaller(r, true, self),
        }
    }

    pub fn check_constraints<'a, I>(&self, c: I) -> UnivResult<bool>
        where
            I: Iterator<Item=&'a UnivConstraint>,
    {
        for c in c {
            if !self.check_constraint(c)? { return Ok(false) }
        }
        Ok(true)
    }
}

impl UnivConstraint {
    fn subst_instance(&self, s: &Instance) -> SubstResult<Self> {
        let UnivConstraint(ref u, d, ref v) = *self;
        let u_ = u.subst_instance(s)?;
        let v_ = v.subst_instance(s)?;
        // Ok(if u.hequal(u_) && v.hequal(v_) { Cow::Borrowed(self) }
        //    else { Cow::Owned(UnivConstraint(u_, d, v_)) })
        Ok(UnivConstraint(u_, d, v_))
    }
}

/// For use in Constraint.
/// TODO: Consider replacing this with a UnivConstraintKey wrapper, once it's been ascertained that
/// this won't cause problems.
impl PartialEq for UnivConstraint {
    fn eq(&self, &UnivConstraint(ref u_, c_, ref v_): &Self) -> bool {
        // Inlined version of UConstraintOrd.compare where we only care whether comparison is 0.
        let UnivConstraint(ref u, c, ref v) = *self;
        // constraint_type_ord == 0 is the same as structural equality for ConstraintType.
        c == c_ &&
        // Level.compare == 0 is the same as Level.equal.
        u.equal(u_) && v.equal(v_)
    }
}

/// For use in Constraint.
/// TODO: Consider replacing this with a UnivConstraintKey wrapper, once it's been ascertained that
/// this won't cause problems.
impl Eq for UnivConstraint {}

impl Cstrs {
    pub fn subst_instance(&self, s: &Instance) -> SubstResult<HashSet<UnivConstraint>> {
        self.iter().map( |c| c.subst_instance(s) ).collect()
    }
}
