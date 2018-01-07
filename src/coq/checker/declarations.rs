use coq::lib::rtree::{
    RTreeResult,
};
use ocaml::de::{
    ORef,
};
use ocaml::values::{
    Constr,
    Mp,
    MpResolver,
    RecArg,
    RTree,
    Substituted,
    UId,
    Wfp,
};
use std::collections::{HashMap};

struct UMap<'b>(HashMap<Mp, &'b MpResolver>, HashMap<&'b UId, &'b MpResolver>);

impl<'b> UMap<'b> {
    pub fn mps<'c>(&mut self, _c: &'c mut ORef<Constr>) -> Constr {
        unimplemented!("mp substitution not yet implemented")
    }
}

impl<T> Substituted<ORef<T>> {
    fn force<'b, F>(&mut self, _fsubst: F)
        where F: for<'c> FnOnce(&mut UMap<'b>, &'c mut ORef<T>) -> T,
              T: Clone,
    {
        let Substituted { ref mut subst, value: ref mut _value } = *self;
        if subst.len() != 0 {
            unimplemented!("Module substitutions are yet implemented")
        }
    }
}

impl Substituted<ORef<Constr>> {
    pub fn force_constr(&mut self) {
        self.force(UMap::mps)
    }
}

impl RecArg {
    /// Mutual inductives

    pub fn mk_norec() -> Wfp {
        RTree::mk_node(RecArg::NoRec, Vec::new())
    }

    pub fn mk_paths(self, recargs: Vec<Vec<Wfp>>) -> Wfp {
        RTree::mk_node(self,
                       recargs.into_iter().map(|l| RTree::mk_node(RecArg::NoRec, l)).collect())
    }

    pub fn eq(&self, r2: &Self) -> bool {
        match (self, r2) {
            (&RecArg::NoRec, &RecArg::NoRec) => true,
            (&RecArg::MRec(ref i1), &RecArg::MRec(ref i2)) => (**i1).eq(&**i2),
            (&RecArg::Imbr(ref i1), &RecArg::Imbr(ref i2)) => (**i1).eq(&**i2),
            (_, _) => false,
        }
    }
}

impl Wfp {
    pub fn eq_wf_paths(&self, t_: &Self) -> RTreeResult<bool> {
        self.equal(t_, RecArg::eq)
    }
}
