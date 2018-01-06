use coq::kernel::esubst::{
    IdxError,
    IdxResult,
};
use coq::lib::hashcons::{HashconsedType, Hlist, Hstring, KeyHasher, Table};
use coq::lib::hashset::combine;
use core::convert::TryFrom;
use fnv::{FnvHashSet, FnvHashMap};
use ocaml::de::{
    Array,
    ORef,
};
use ocaml::values::{
    ConstraintType,
    Context,
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
use std::collections::hash_map::{self};
use std::hash::{BuildHasherDefault};
use std::mem::{self};
use std::option::{NoneError};
use std::sync::{Arc};

/// Comparison on this type is pointer equality
/// TODO: If we do want to use Vecs here, consider using a RingBuf, so we have one contiguous
/// allocation instead of two, pushing onto the front for le and the back for lt, and using an
/// index to see where the split happens; this should use less space, and may be faster overall.
/// TODO: Consider using a variant of Level (LevelRef<'g>?) that uses a &'g Dp and is otherwise
/// a value, so we don't have as many Level indirections.
struct CanonicalArc<'g> {
    univ: &'g Level,
    /// NOTE: reversed from the order in the OCaml implementation!
    /// TODO: consider using a HashSet here.
    lt: Vec<&'g Level>,
    /// NOTE: reversed from the order in the OCaml implementation!
    /// TODO: consider using a HashSet here.
    le: Vec<&'g Level>,
    /// NOTE: consider using a u32 here because because we have an extra bool; if the structure is
    /// word-aligned and we use a usize, the bool ends up in its own word, which is undesirable.
    /// Another alternative would be to bit-pack the predicative bit into the rank, but that may be
    /// premature optimization.
    rank: usize,
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
enum UnivEntry<'g> {
  Canonical(CanonicalArc<'g>),
  Equiv(&'g Level),
}


/// INVARIANT:
///   max rank (canonical_values self) + len (canonical_values self) ≤ len self
/// INVARIANT:
///   Set and Prop:
///     (1) always have entries in the table;
///     (2) have canonical instances whose level is also Set / Prop, respectively;
///     (3) Set < Prop;
///     (4) ∀ x s.t. x is not small, Prop ≤ x;
pub struct Universes<'g>(UMap<'g, UnivEntry<'g>>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnivError {
    Anomaly(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SubstError {
    NotFound,
    Idx(IdxError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnivConstraintError {
    /// Universe inconsistency: error raised when trying to enforce a relation
    /// that would create a cycle in the graph of universes.
    ///
    /// NOTE: Unlike OCaml, use Level instead of Universe, since as actually used we never
    /// instantiate it with universes of more than one level.
    UniverseInconsistency(ConstraintType, Level, Level),
    Anomaly(String),
}

/// Support for universe polymorphism

/// Polymorphic maps from universe levels to 'a
pub type LMap<'g, T> = HashMap<&'g Level, T, BuildHasherDefault<KeyHasher>>;
pub type LSet<'g> = HashSet<&'g Level, BuildHasherDefault<KeyHasher>>;

pub type UMap<'g, T> = LMap<'g, T>;

type Hexpr = ();

pub type Helem<T, U> = Table<ORef<(T, Int, HList<T>)>, U>;

pub type Huniv = Helem<Expr, ()>;

pub type UnivResult<T> = Result<T, UnivError>;

pub type UnivConstraintResult<T> = Result<T, Box<UnivConstraintError>>;

pub type SubstResult<T> = Result<T, SubstError>;

pub trait Hashconsed<U> {
    fn hash(&self) -> IdxResult<i64>;
    fn eq(&self, &Self) -> bool;
    fn hcons<'a>(self, &'a U) -> Self
        where Self: ToOwned;
}

impl ::std::convert::From<UnivError> for Box<UnivConstraintError> {
    fn from(e: UnivError) -> Self {
        match e {
            UnivError::Anomaly(s) => Box::new(UnivConstraintError::Anomaly(s)),
        }
    }
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

/// For use in HashSet<CanonicalArc>.
/// TODO: Consider replacing this with a CanonicalArc wrapper, once it's been ascertained that this
/// won't cause problems.
impl<'g> ::std::hash::Hash for CanonicalArc<'g> {
    fn hash<H>(&self, state: &mut H)
        where
            H: ::std::hash::Hasher,
    {
        // Hash pointer
        (self as *const CanonicalArc).hash(state)
    }
}

/// For use in HashSet<CanonicalArc>.
/// TODO: Consider replacing this with a CanonicalArc wrapper, once it's been ascertained that this
/// won't cause problems.
impl<'g> PartialEq for CanonicalArc<'g> {
    fn eq(&self, y: &Self) -> bool {
        // Comparison is pointer equality
        self as *const _ == y as *const _
    }
}

/// For use in HashSet<CanonicalArc>.
/// TODO: Consider replacing this with a CanonicalArc wrapper, once it's been ascertained that this
/// won't cause problems.
impl<'g> Eq for CanonicalArc<'g> {}

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

impl<'g> CanonicalArc<'g> {
    fn terminal(u: &'g Level) -> Self {
        CanonicalArc { univ: u, lt: Vec::new(), le: Vec::new(), rank: 0, predicative: false, }
    }

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
    fn fast_compare_neq(&self, arcv: &Self, strict: bool,
                        g: &Universes<'g>) -> UnivResult<FastOrder> {
        // [c] characterizes whether arcv has already been related
        // to arcu among the lt_done,le_done universe
        let mut c = FastOrder::NLe;
        // TODO: Consider allowing reuse of storage between invocations of fast_compare_neq.
        // NOTE: Using HashSet instead of Vec, contrary to the OCaml implementation.
        // Unless there are very few entries, this should be faster.
        let mut lt_done = FnvHashSet::default();
        let mut le_done = FnvHashSet::default();
        let mut lt_todo : Vec<&CanonicalArc> = Vec::new();
        let mut le_todo = vec![self];
        loop {
            if let Some(arc) = lt_todo.pop() {
                if lt_done.insert(arc) { // arc was not in lt_done
                    // Because the le vector in arc is reversed from what it is in OCaml, we
                    // re-reverse it here.  TODO: Determine whether this is necessary (it seems
                    // likely that it isn't).
                    for u in arc.le.iter().rev() {
                        let arc = u.repr(g)?;
                        if arc as *const _ == arcv as *const _ {
                            return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                        } else {
                            lt_todo.push(arc);
                        }
                    }
                    // Because the lt vector in arc is reversed from what it is in OCaml, we
                    // re-reverse it here.  TODO: Determine whether this is necessary (it seems
                    // likely that it isn't).
                    for u in arc.lt.iter().rev() {
                        let arc = u.repr(g)?;
                        if arc as *const _ == arcv as *const _ {
                            return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                        } else {
                            lt_todo.push(arc);
                        }
                    }
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
                    if !lt_done.contains(arc) && le_done.insert(arc) { // arc was not in le_done
                        for u in arc.lt.iter().rev() {
                            let arc = u.repr(g)?;
                            if arc as *const _ == arcv as *const _ {
                                return Ok(if strict { FastOrder::Lt } else { FastOrder::Le })
                            } else {
                                lt_todo.push(arc);
                            }
                        }
                        // Cannot use .extend here because we need to fail fast on failure.  There
                        // is probably a better way to deal with this.
                        // Because the le vector in arc is reversed from what it is in OCaml, we
                        // re-reverse it here.  TODO: Determine whether this is necessary (it seems
                        // likely that it isn't).
                        for u in arc.le.iter().rev() {
                            le_todo.push(u.repr(g)?);
                        }
                    }
                }
            } else {
                // lt_todo = [], le_todo = []
                return Ok(c)
            }
        }
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn fast_compare(&self, arcv: &Self, g: &Universes<'g>) -> UnivResult<FastOrder> {
        if self as *const _ == arcv as *const _ { Ok(FastOrder::Eq) }
        else { self.fast_compare_neq(arcv, true, g) }
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn is_leq(&self, arcv: &Self, g: &Universes<'g>) -> UnivResult<bool> {
        Ok(self as *const _ == arcv as *const _ ||
           match self.fast_compare_neq(arcv, false, g)? {
               FastOrder::NLe => false,
               FastOrder::Eq | FastOrder::Le | FastOrder::Lt => true,
           })
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn is_lt(&self, arcv: &Self, g: &Universes<'g>) -> UnivResult<bool> {
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

    fn is_small(&self) -> bool {
        match self.data {
            RawLevel::Level(_, _) => false,
            _ => true,
        }
    }

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
    ///
    /// repr : universes -> Level.t -> canonical_arc
    ///
    /// canonical representative : we follow the Equiv links
    ///
    /// The universe should actually be in the universe map, or else it will return an error.
    ///
    /// Also note: if the map universe map contains Equiv cycles, this will loop forever!
    fn repr<'a, 'g>(&'a self, g: &'a Universes<'g>) -> UnivResult<&'a CanonicalArc<'g>> {
        let mut u = self;
        loop {
            match g.0.get(u) {
                Some(&UnivEntry::Equiv(v)) => { u = v },
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
    fn check_equal<'g>(&self, v: &Level, g: &Universes<'g>) -> UnivResult<bool> {
        let arcu = self.repr(g)?;
        let arcv = v.repr(g)?;
        Ok(arcu as *const _ == arcv as *const _)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_eq<'g>(&self, v: &Level, g: &Universes<'g>) -> UnivResult<bool> {
        Ok(self.check_equal(v, g)?)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_smaller<'g>(&self, v: &Self, strict: bool, g: &Universes<'g>) -> UnivResult<bool> {
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
    fn check_equal<'g>(&self, y: &Self, g: &Universes<'g>) -> UnivResult<bool> {
        Ok(self.hequal(y) || {
            let Expr(ref u, n) = *self;
            let Expr(ref v, m) = *y;
            n == m && u.check_equal(v, g)?
        })
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn check_smaller<'g>(&self, &Expr(ref v, m): &Self, g: &Universes<'g>) -> UnivResult<bool> {
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
    fn exists_bigger<'g>(&self, l: &Univ, g: &Universes<'g>) -> UnivResult<bool> {
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
        self.iter().try_fold(HList::nil(), |acc, a| aux(a, acc, tbl))
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
    fn check_eq_univs<'g>(&self, l2: &Self, g: &Universes<'g>) -> UnivResult<bool> {
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
    pub fn check_eq<'g>(&self, v: &Self, g: &Universes<'g>) -> UnivResult<bool> {
        Ok(self.hequal(v) ||
           self.check_eq_univs(v, g)?)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    fn real_check_leq<'g>(&self, v: &Self, g: &Universes<'g>) -> UnivResult<bool> {
        // NOTE: We don't just use any / all because we want to propagate errors; there may be a
        // way to do both somehow.
        for ul in self.iter() {
            if !ul.exists_bigger(v, g)? { return Ok(false) }
        }
        return Ok(true)
    }

    /// The universe should actually be in the universe map, or else it will return an error.
    pub fn check_leq<'g>(&self, v: &Self, g: &Universes) -> UnivResult<bool> {
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
                              .try_fold(HList::nil(), |acc, u| Self::merge_univs(&acc, u, tbl))?;
            // TODO: Figure out whether the iterator reversal here is really necessary.
            nosubst.into_iter()
                   .rev()
                   .try_fold(substs,
                            |acc, u| Self::merge_univs(&acc, &Self::tip(u.clone(), tbl)?, tbl))
        }
    }
}

impl ConstraintType {
    fn error_inconsistency(self, u: Level, v: Level) -> Box<UnivConstraintError> {
        Box::new(UnivConstraintError::UniverseInconsistency(self, u, v))
    }
}

/* impl Context {
    pub fn make(ctx: Instance, cst: Cstrs) -> Self {
        Context(ctx, cst)
    }
} */

impl<'g> Universes<'g> {
    /// Panics if either u does not exist in the map, or the arc to which it directly points is not
    /// canonical!
    ///
    /// Additionally, v should be a valid entry in the map.
    ///
    /// (it could return an error, but panicking seems correct everywhere this is used).
    fn enter_equiv_arc(&mut self, u: &Level, v: &'g Level) -> CanonicalArc<'g> {
        // NOTE: We don't care about any value that was already in the map.
        let can = self.0.get_mut(u).expect("enter_equiv_arc: level was not in the map");
        if let UnivEntry::Canonical(ca) = mem::replace(can, UnivEntry::Equiv(v)) {
            ca
        } else {
            panic!("enter_equiv_arc: level was not canonical")
        }
    }

    /// Panics if either ca_univ does not exist in the map, or the arc to which it directly
    /// points is not canonical!
    ///
    /// (it could return an error, but panicking seems correct everywhere this is used).
    fn enter_arc<'a>(&'a mut self, ca_univ: &Level) -> &'a mut CanonicalArc<'g> {
        let can = self.0.get_mut(ca_univ).expect("enter_arc: level was not in the map");
        if let UnivEntry::Canonical(ref mut ca) = *can {
            ca
        } else {
            panic!("enter_arc: level was not canonical")
        }
    }

    /// Panics if self is not properly initialized (which should never happen) or if somehow Set
    /// has become non-canonical (which should also never happen).
    fn get_set_arc(&mut self) -> &mut CanonicalArc<'g> {
        let can = self.0.get_mut(&Level::SET).expect("get_set_arc: level was not in the map");
        if let UnivEntry::Canonical(ref mut ca) = *can {
            ca
        } else {
            panic!("get_set_arc: Level.set was not canonical")
        }
    }

    /// NOTE: In the unlikely event that this method panics, invariants are *not* guaranteed to be
    /// maintained.  Do not mark structures containing Universes PanicSafe!
    ///
    /// Returns `Ok(())` if add_universe succeeded, and `Err(())` if the entry already exists.
    pub fn add_universe(&mut self, vlev: &'g Level, strict: bool) -> Result<(), ()> {
        {
            let arcv = if let hash_map::Entry::Vacant(arcv) = self.0.entry(vlev) {
                arcv
            } else { return Err(()) };
            let v = CanonicalArc::terminal(vlev);
            arcv.insert(UnivEntry::Canonical(v));
        }
        let arc = self.get_set_arc();
        Ok(if strict { arc.lt.push(vlev) } else { arc.le.push(vlev) })
    }

    /// reprleq : canonical_arc -> canonical_arc list
    /// All canonical arcv such that arcu<=arcv with arcv#arcu
    ///
    /// NOTE: must have arcu actually in the map before calling this.
    ///
    /// NOTE: the returned iterator is in the opposite order from the OCaml implementation!
    ///
    /// NOTE: There is an algorithmic difference here; in the OCaml, a list is used but the
    ///       duplicate canonical arcs are removed.  Here, we simply return an iterator, with
    ///       duplicates; hopefully the way this is used (in between) should already
    ///       filter out duplicates anyway before they have a chance to impact the result, and this
    ///       allows us to not perform any intermediate allocations here or keep searching over the
    ///       inner list (which may be fast, but still probably not as fast as the hash table
    ///       lookup except for small numbers of list entries).  TODO: benchmark, and consider
    ///       using some sort of hybrid if most lists are small.
    fn reprleq<'a>(&'a self,
                   arcu: &'a CanonicalArc<'g>) -> impl Iterator<Item=&'a CanonicalArc<'g>> + 'a {
        // We reverse the order in which we iterate, since CanonicalArc has reversed le from the
        // OCaml implementation.
        arcu.le.iter().rev().filter_map(move |v| {
            const ERR : &'static str =
                "reprleq: le and lt references from entries in the map should be in the map.";
            let arcv = v.repr(self).expect(ERR);
            if arcu as *const _ == arcv as *const _ { None } else { Some(arcv) }
        })
    }

    /// between : Level.t -> canonical_arc -> canonical_arc list
    /// between u v = { w | u<=w<=v, w canonical }
    /// between is the most costly operation
    /// (Observe that we must have compare u v = LE before calling this)
    ///
    /// NOTE: In the Rust version, there are some algorithmic differences:
    ///
    /// - We use an explicit stack rather than tail recursion (we may change this if it hurts
    ///   performance too much).
    ///
    /// - Rather than vectors for remembering good and bad arcs, we use hash tables; as far as I
    ///   can tell, we don't actually rely on the order in the lists anywhere, so unless these are
    ///   in practice very small it seems likely that hashing should be a performance win here.  We
    ///   also use FnvHashMap over Rust's default hash map, as it is much faster for small keys and
    ///   we are not terribly worried about denial of service attacks due to hash table collisions
    ///   (given that [1] the Coq implementation uses linked lists already, [2] we're hashing
    ///   pointers, which are at the very least tricky to make sure always hash to the same thing,
    ///   and [3] if you want to make the checker run slowly there are much easier ways to do it
    ///   than by attacking the universe hash function!).
    ///
    /// - We coalesce the good and bad hash tables into a single hashmap, goodbad.  This allows us
    ///   to replace two lookups with one; because hash lookup time is (effectively) O(1)
    ///   regardless of table size, except for cache effects that are just as bad with two tables,
    ///   this should hopefully improve performance.  The only other cost is that we have to
    ///   iterate through the bad elements once at the end; if this turns out to be a problem, we
    ///   can always go back to two hash sets, but it seems likely that it isn't if we're willing
    ///   to iterate through the entire bad list so often in the OCaml implementation (and in
    ///   general we would always hit the bad list at least as many times as there are keys looking
    ///   up an element in the hash table, so filtering at the end is probably strictly better).
    ///
    /// - We compute the maximum good key during the between search, instead of doing it
    ///   afterwards (and also compute the next-best maximum).  This allows us to iterate
    ///   through the hash set just once afterwards, instead of twice.
    fn between<'a>(&'a self, arcu: &'a CanonicalArc<'g>, arcv: &'a CanonicalArc<'g>,
                  ) -> (usize, usize, &CanonicalArc<'g>, FnvHashMap<&'a CanonicalArc<'g>, bool>) {
        // good are all w | u <= w <= v
        // bad are all w | u <= w ~<= v

        // find good and bad nodes in {w | u <= w}
        // explore b u = (b or "u is good")
        /* fn explore<'a>(g: &Universes,
                       b: &mut bool, arcu: &'a CanonicalArc, stk: &mut Vec<(bool, &'a CanonicalArc, )>,
                       good_bad: &mut FnvHashMap<&'a CanonicalArc, bool>,
                       best_arc: &'a CanonicalArc) {
        } */
        // TODO: consider trying to work out a reasonable default capacity to make reallocation
        // less likely.
        // TODO: figure out if there's some sort of safe interface we could use that would allow
        // reusing the backing storage of this hash table between functions (after we drain it);
        // because it stores references with a particular lifetime, this seems tricky in general.
        let mut good_bad = FnvHashMap::default();
        // We don't put arcv into good_bad yet, even though it's known to be good; instead, we set
        // it as the arc with maximal rank currently known to be good.
        let mut stk = Vec::new();
        let mut b_leq = false;
        // The maximal rank currently known to be good
        let mut max_rank = arcv.rank;
        // The next-best maximal rank currently known to be good
        let mut old_max_rank = 0;
        // The arc with maximal rank currently known to be good
        let mut best_arc = arcv;
        {
            // TODO: Check whether adding this branch hurts performance more than just adding it to
            // the hash table and removing the max key at the end.
            if best_arc as *const _ == arcu as *const _ {
                b_leq = true // b or true
            } else if let Some(&b_leq_) = good_bad.get(arcu) {
                b_leq = b_leq || b_leq_ // b or b_leq
            } else {
                let leq = self.reprleq(arcu);
                // is some universe >= u good?
                stk.push((b_leq, arcu, leq));
                b_leq = false
            }
        }
        // explore(self, &mut b_leq, arcu, &mut stk, &mut good_bad, best_arc);
        loop {
            if let Some(arcu) = stk.last_mut().and_then( |&mut (_, _, ref mut leq)| leq.next()) {
                // Process one entry of the top-level fold.
                // TODO: Check whether adding this branch hurts performance more than just adding
                // it to the hash table and removing the max key at the end.
                if best_arc as *const _ == arcu as *const _ {
                    b_leq = true // b or true
                } else if let Some(&b_leq_) = good_bad.get(arcu) {
                    b_leq = b_leq || b_leq_ // b or b_leq
                } else {
                    let leq = self.reprleq(arcu);
                    // is some universe >= u good?
                    stk.push((b_leq, arcu, leq));
                    b_leq = false
                }
                // explore(self, &mut b_leq, arcu, &mut stk, &mut good_bad, best_arc);
            } else if let Some((b, arcu, _)) = stk.pop() {
                // We finished the top-level fold; b_leq = (false or "u is good") = "u is good"
                // NOTE: good_bad should be disjoint partitions, so we shouldn't need to check
                // whether good already contains a value for this key when we perform inserts,
                // since if we repeat an insert it should always have the same value.
                // (FIXME: Verify this).
                // NOTE: We special case arcu.univ.is_small() to make sure that we maintain the
                // invariant that small universes always point to a canonical instance with their
                // own level.
                if b_leq && (arcu.univ.is_small() || arcu.rank >= max_rank) {
                    max_rank = arcu.rank;
                    old_max_rank = max_rank;
                    // Insert the old best_arc into good_bad.
                    good_bad.insert(best_arc, true);
                    best_arc = arcu; // b or true
                } else {
                    good_bad.insert(arcu, b_leq);
                    b_leq = b_leq || b; // b or b_leq
                }
            } else {
                // We are done processing
                // Observe: since we know u ≤ v before, good_bad now contains at least two
                // elements, u and v (they must be distinct, or else we would have had u = v).
                // Let's generalize to "all elements other than best_arc" (rest) and best_arc.
                // If best_arc.rank > max rank rest, then best_arc.rank > 0; otherwise, there
                // are at least two elements with the same top rank (be it 0 or any other
                // rank) and we need to increment it to create an unambiguous max rank.
                // Therefore, we lose no interesting information by starting with
                // old_max_rank = 0.
                return (max_rank, old_max_rank, best_arc, good_bad)
            }
        }
    }

    /// merge : Level.t -> Level.t -> unit
    /// we assume compare(u,v) = LE
    /// merge u v forces u ~ v with repr u as canonical repr
    ///
    /// FIXME: Verify that the order of iteration here doesn't really matter.
    ///
    /// NOTE: Arc invariants are *not* preserved through panics.  This function is not intended to
    /// throw exceptions, but if they are thrown, and later caught, PanicSafe should not be
    /// enabled for structures containing Universes!
    fn merge(&mut self, u: &Level, v: &Level) {
        const ERR: &'static str =
            "merge: le and lt references from entries in the map should be in the map.";
        let (v, u_univ, u_incr_rank) = {
            // NOTE: Would be nice to have these available from the getgo, but the lifetimes don't
            // work very well.
            let arcu = u.repr(self).expect(ERR);
            let arcv = v.repr(self).expect(ERR);
            // NOTE: Should probably assert that arc1 and arc2 are different here.
            let (max_rank, old_max_rank, arcu, rest) = self.between(arcu, arcv);
            let u_rank = max_rank == old_max_rank; // true if redirected node also has max rank
            (rest.into_iter().filter_map(|(arcv, b)| if b { Some(arcv.univ) } else { None } )
                 .collect::<Vec<_>>(), arcu.univ, u_rank)
        };
        // TODO: use expected size to influence size of hash sets somehow.
        let mut w = LSet::default();
        // TODO: Figure out why w' is a list but w is a set (under OCaml semantics; in OCaml unionq
        // is used on w but @ on w').
        let mut w_ = Vec::new();
        // NOTE: We do this slightly out of order compared to the OCaml--in it, the rank is
        // incremented first--but it doesn't affect enter_equiv_arc's behavior, and this way is
        // exception safe re: the rank increment (though it may not preserve other invariants!).
        for v_univ in v {
            // Safe because all levels are distinct, and all v entries start as canonical entries
            // int the map.
            let CanonicalArc { lt, le, .. } = self.enter_equiv_arc(v_univ, u_univ);
            w.extend(lt);
            // NOTE: w_ is backwards from how it is in OCaml!
            w_.extend(le);
        }
        if u_incr_rank {
            // NOTE: the addition is safe because rank is of type usize, and we have an
            // invariant: max rank (between u v) ≤
            //            max rank (canonical_values self) + len (canonical_values self)
            //            ≤ len self
            //            <= usize::MAX.
            //
            // The first and last inequalities are trivial.  It is not much harder to see that if
            // the invariant is true initially, adding a new canonical value preserves it
            // (we never change a non-canonical value to a canonical one, except during a revert,
            // and adding a canonical entry definitionally increases len self by 1, so the number
            // of canonical entries and len self go up by in lockstep).
            //
            // To see why the second is true, first observe that we never take entries out of
            // self without reverting all changes (so elements are only added or merged;
            // changes are effectively monotonic).  As a result, we just need to know that
            // every increase in rank is associated with an equal or greater decrease in the
            // number of canonical elements (any reversion actions also preserve the
            // inequality, of course, since they just revert to previously valid state).
            //
            // This holds because we never call merge unless arcu and
            // arcv have distinct canonical elements (compare u v = LE), and after a merge
            // max rank (canonical_values self) has increased by at most 1, while the number of
            // canonical elements has decreased by at least 1 thanks to enter_equiv_arc; the
            // number of entries in self remains the same throughout the merge, so if the
            // invariant was true before merge it remains true after merge.
            //
            // (There is one other places that modifies ranks, and it also preserves this
            // invariant).
            //
            // Finally, note that even if there is a panic here calling enter_arc, or was one
            // during any of the enter_equiv_arc calls, the invariant is still maintained, because
            // if enter_equiv_arc succeeds it decreases the number of canonical arcs by 1, and if
            // it fails it does not change self (it may result in other inconsistencies in the map,
            // though!)
            self.enter_arc(u_univ).rank += 1;
        }

        let u_is_set = u_univ.is_set(); // Does not change throughout the loop
        for v in w {
            // FIXME: It would be really nice to have arcu around without having to keep rereading
            // it... but it seems tricky to make that work (without cloning arcu, at least).
            let (set_predicative, v_univ) = {
                let arcu = u_univ.repr(self).expect(ERR);
                let arcv = v.repr(self).expect(ERR);
                if arcu.is_lt(arcv, self).expect(ERR) { continue }
                else { (!arcv.predicative && u_is_set, arcv.univ) }
            };
            if set_predicative {
                // We only need to bother setting the arcv if (1) arcu was a set, and (2) arcv wasn't
                // already predicative.
                self.enter_arc(v_univ).predicative = true
            }
            // Note that le is reversed from the OCaml implementation!
            self.enter_arc(u_univ).lt.push(v_univ);
        }
        for v in w_ {
            // FIXME: It would be really nice to have arcu around without having to keep rereading
            // it... but it seems tricky to make that work (without cloning arcu, at least).
            let (set_predicative, v_univ) = {
                let arcu = u_univ.repr(self).expect(ERR);
                let arcv = v.repr(self).expect(ERR);
                if arcu.is_leq(arcv, self).expect(ERR) { continue }
                else { (!arcv.predicative && u_is_set, arcv.univ) }
            };
            if set_predicative {
                // We only need to bother setting the arcv if (1) arcu was a set, and (2) arcv wasn't
                // already predicative.
                self.enter_arc(v_univ).predicative = true
            }
            // Note that le is reversed from the OCaml implementation!
            self.enter_arc(u_univ).le.push(v_univ);
        }
    }

    /// merge_disc : Level.t -> Level.t -> unit
    /// we assume  compare(u,v) = compare(v,u) = NLE
    /// merge_disc u v  forces u ~ v with repr u as canonical repr
    ///
    /// NOTE: PRECONDITION: Neither u nor v is small.
    ///
    /// FIXME: Verify that the order of iteration here doesn't really matter.
    ///
    /// NOTE: Arc invariants are *not* preserved through panics.  This function is not intended to
    /// throw exceptions, but if they are thrown, and later caught, PanicSafe should not be
    /// enabled for structures containing Universes!
    fn merge_disc(&mut self, u: &Level, v: &Level) {
        const ERR: &'static str =
            "merge_disc: le and lt references from entries in the map should be in the map.";
        let (u_univ, v_univ, u_incr_rank) = {
            // NOTE: Would be nice to have these available from the getgo, but the lifetimes don't
            // work very well.
            let arc1 = u.repr(self).expect(ERR);
            let arc2 = v.repr(self).expect(ERR);
            // NOTE: Should probably assert that arc1 and arc2 are different here.
            // NOTE: We don't need to check for is_small here like we do for regular merge, because
            //       our precondition is that neither u nor v is small.
            match arc1.rank.cmp(&arc2.rank) {
                Ordering::Less => (arc2.univ, arc1.univ, false),
                Ordering::Equal => (arc1.univ, arc2.univ, true),
                Ordering::Greater => (arc1.univ, arc2.univ, false),
            }
        };
        // NOTE: We do this slightly out of order compared to the OCaml--in it, the rank is
        // incremented first--but it doesn't affect enter_equiv_arc's behavior, and this way is
        // exception safe re: the rank increment (though it may not preserve other invariants!).
        let CanonicalArc { lt, le, .. } = self.enter_equiv_arc(v_univ, u_univ);
        if u_incr_rank {
            // NOTE: This is safe because of the invariant mentioned in merge, and it works the
            // exact same way--we have a precondition that compare u v = NLE, so we
            // know they were not the same beforehand; hence, we always decrement the number of
            // canonical arcs by 1, then increment the rank of one of the remaining two by
            // at most 1 (if we enter this branch).  The same exception safety concerns also apply.
            self.enter_arc(u_univ).rank += 1;
        }
        for v in lt {
            // FIXME: It would be really nice to have arcu around without having to keep rereading
            // it... but it seems tricky to make that work (without cloning arcu, at least).
            let v_univ = {
                let arcu = u_univ.repr(self).expect(ERR);
                let arcv = v.repr(self).expect(ERR);
                if arcu.is_lt(arcv, self).expect(ERR) { continue } else { arcv.univ }
            };
            // We don't need to set predicativity for v, because u is definitely not Set.
            // Note that le is reversed from the OCaml implementation!
            self.enter_arc(u_univ).lt.push(v_univ);
        }
        for v in le {
            // FIXME: It would be really nice to have arcu around without having to keep rereading
            // it... but it seems tricky to make that work (without cloning arcu, at least).
            let v_univ = {
                let arcu = u_univ.repr(self).expect(ERR);
                let arcv = v.repr(self).expect(ERR);
                if arcu.is_leq(arcv, self).expect(ERR) { continue } else { arcv.univ }
            };
            // We don't need to set predicativity for v, because u is definitely not Set.
            // Note that le is reversed from the OCaml implementation!
            self.enter_arc(u_univ).le.push(v_univ);
        }
    }

    /// enforce_univ_eq : Level.t -> Level.t -> unit
    /// enforce_univ_eq u v will force u=v if possible, will fail otherwise
    fn enforce_eq(&mut self, u: &Level, v: &Level) -> UnivConstraintResult<()> {
        let (do_neq, u_univ, v_univ) = {
            let g = &*self;
            let arcu = u.repr(g)?;
            let arcv = v.repr(g)?;
            const ERR : &'static str =
                "enforce_eq: le and lt references from entries in the map should be in the map.";
            match arcu.fast_compare(arcv, g).expect(ERR) {
                FastOrder::Eq => return Ok(()),
                FastOrder::Lt =>
                    return Err(ConstraintType::Eq.error_inconsistency(u.clone(), v.clone())),
                FastOrder::Le => (false, arcu.univ, arcv.univ),
                FastOrder::NLe => match arcv.fast_compare_neq(arcu, false, g).expect(ERR) {
                    FastOrder::Lt =>
                        return Err(ConstraintType::Eq.error_inconsistency(u.clone(), v.clone())),
                    FastOrder::Le => (false, arcv.univ, arcu.univ),
                    FastOrder::NLe => (true, arcu.univ, arcv.univ),
                    FastOrder::Eq =>
                        return Err(Box::new(UnivConstraintError::Anomaly("Univ.compare".into()))),
                },
            }
        };
        // Since u_univ and v_univ are both values in the table, and both canonical, their univs
        // are the same as their keys in the table, so we know the lookups below won't panic.
        // We must be careful to set things in the correct order (arcv is updated before arcu).
        if do_neq {
            // merge_disc
            // NOTE: We know compare u v is not Eq, Le, or Lt, and compare v u is not Eq, Le, or
            // Lt, so we can conclude that neither u nor v are small (since add_universes ensures
            // that Set ≤ every added level except Prop, and Prop < Set so Prop < every added
            // level except Prop and Set).  This satisies the precondition for merge_disc and
            // ensures that Set and Prop remain their own canonical entries.
            self.merge_disc(u_univ, v_univ);
        } else {
            // merge
            self.merge(u_univ, v_univ);
        }
        Ok(())
    }

    /// enforce_univ_leq : Level.t -> Level.t -> unit
    /// enforce_univ_leq u v will force u<=v if possible, will fail otherwise
    fn enforce_leq(&mut self, u: &Level, v: &Level) -> UnivConstraintResult<()> {
        let (do_leq, u_univ, v_univ) = {
            let g = &*self;
            let arcu = u.repr(g)?;
            let arcv = v.repr(g)?;
            const ERR : &'static str =
                "enforce_leq: le and lt references from entries in the map should be in the map.";
            if arcu.is_leq(arcv, g).expect(ERR) { return Ok(()) }
            match arcv.fast_compare(arcu, g).expect(ERR) {
                FastOrder::Lt =>
                    return Err(ConstraintType::Le.error_inconsistency(u.clone(), v.clone())),
                FastOrder::Le => (None, arcu.univ, arcv.univ),
                FastOrder::NLe => (Some(!arcv.predicative && arcu.is_set()), arcu.univ, arcv.univ),
                FastOrder::Eq =>
                    return Err(Box::new(UnivConstraintError::Anomaly("Univ.compare".into()))),
            }
        };
        // Since u_univ and v_univ are both values in the table, and both canonical, their univs
        // are the same as their keys in the table, so we know the lookups below won't panic.
        // We must be careful to set things in the correct order (arcv is updated before arcu).
        Ok(if let Some(set_predicative) = do_leq {
            // setleq
            if set_predicative {
                // We only need to bother setting the arcv if (1) arcu was a set, and (2) arcv
                // wasn't already predicative.
                self.enter_arc(v_univ).predicative = true
            }
            // Note that le is reversed from the OCaml implementation!
            self.enter_arc(u_univ).le.push(v_univ);
        } else {
            // merge
            self.merge(v_univ, u_univ);
        })
    }

    /// enforce_univ_lt u v will force u<v if possible, will fail otherwise
    fn enforce_lt(&mut self, u: &Level, v: &Level) -> UnivConstraintResult<()> {
        let (set_predicative, u_univ, v_univ) = {
            let g = &*self;
            let arcu = u.repr(g)?;
            let arcv = v.repr(g)?;
            const ERR : &'static str =
                "enforce_lt: le and lt references from entries in the map should be in the map.";
            match arcu.fast_compare(arcv, g).expect(ERR) {
                FastOrder::Lt => return Ok(()),
                FastOrder::Le => (!arcv.predicative && arcu.is_set(), arcu.univ, arcv.univ),
                FastOrder::Eq =>
                    return Err(ConstraintType::Lt.error_inconsistency(u.clone(), v.clone())),
                FastOrder::NLe => match arcv.fast_compare_neq(arcu, false, g).expect(ERR) {
                    FastOrder::NLe => (!arcv.predicative && arcu.is_set(), arcu.univ, arcv.univ),
                    FastOrder::Eq =>
                        return Err(Box::new(UnivConstraintError::Anomaly("Univ.compare".into()))),
                    FastOrder::Le | FastOrder::Lt =>
                        return Err(ConstraintType::Lt.error_inconsistency(u.clone(), v.clone())),
                },
            }
        };
        // Since u_univ and v_univ are both values in the table, and both canonical, their univs
        // are the same as their keys in the table, so we know the lookups below won't panic.
        // We must be careful to set things in the correct order (arcv is updated before arcu).
        if set_predicative {
            // We only need to bother setting the arcv if (1) arcu was a set, and (2) arcv wasn't
            // already predicative.
            self.enter_arc(v_univ).predicative = true
        }
        // Note that lt is reversed from the OCaml implementation!
        self.enter_arc(u_univ).lt.push(v_univ);
        Ok(())
    }

    /// Constraints and sets of constraints
    fn enforce_constraint(&mut self,
                          &UnivConstraint(ref u, d, ref v): &UnivConstraint
                         ) -> UnivConstraintResult<()> {
        match d {
            ConstraintType::Lt => self.enforce_lt(u, v),
            ConstraintType::Le => self.enforce_leq(u, v),
            ConstraintType::Eq => self.enforce_eq(u, v),
        }
    }

    /// NOTE: Any partial modifications are not currently rolled back on error.
    pub fn merge_constraints<'a, I>(&mut self, c: I) -> UnivConstraintResult<()>
        where I: Iterator<Item=&'a UnivConstraint>,
    {
        for c in c {
            self.enforce_constraint(c)?;
        }
        Ok(())
    }

    /// Constraint functions

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

    pub fn merge_context(&mut self, strict: bool, c: &'g Context) -> UnivConstraintResult<()> {
        for v in c.0.iter() {
            // Be lenient, module typing reintroduces universes and
            // constraints due to includes
            // NOTE: Purposefully ignoring error as a result of the above.
            // TODO: Figure out whether there's any way to avoid this...
            let _ = self.add_universe(v, strict);
        }
        self.merge_constraints(c.1.iter())
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
    pub fn check_eq<'g>(&self, t2: &Instance, g: &Universes<'g>) -> UnivResult<bool> {
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

impl Cstrs {
    pub fn subst_instance(&self, s: &Instance) -> SubstResult<HashSet<UnivConstraint>> {
        self.iter().map( |c| c.subst_instance(s) ).collect()
    }
}
