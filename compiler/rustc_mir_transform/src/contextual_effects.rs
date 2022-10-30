use crate::MirPass;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

pub struct ContextualEffects;

impl<'tcx> MirPass<'tcx> for ContextualEffects {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        debug!("contextual_effects({:?})", body.source.instance);
        self.generate_contextual_effects(body)
    }
}

impl ContextualEffects {
    fn generate_contextual_effects(&self, body: &mut Body<'_>) {
        let mut effects = Effects::new();
        let preorder: Vec<_> = traversal::preorder(body).map(|(bb, _)| bb).collect();
        for bb in preorder {
            debug!("bb id {:?}", bb);
            effects.current.insert(bb, body[bb].clone());
            effects.generate_prior_effects(bb, body);
            let future = effects.generate_future_effects(&body[bb]);
            effects.future.insert(bb, future);
        }
        debug!("prior: {:?}", effects.prior);
    }
}

struct Effects<'tcx> {
    prior: FxHashMap<BasicBlock, Vec<BasicBlockData<'tcx>>>,
    current: FxHashMap<BasicBlock, BasicBlockData<'tcx>>,
    future: FxHashMap<BasicBlock, Vec<BasicBlockData<'tcx>>>,
}

impl<'tcx> Effects<'tcx> {
    fn new() -> Self {
        Effects {
            prior: FxHashMap::default(),
            future: FxHashMap::default(),
            current: FxHashMap::default(),
        }
    }

    fn generate_prior_effects(&mut self, bb: BasicBlock, body: &Body<'tcx>) {
        for target in body[bb].terminator().successors() {
            let mut prior = match self.prior.get(&bb) {
                Some(prior) => prior.clone(),
                None => vec![],
            };
            match self.current.get(&bb) {
                Some(current) => prior.push(current.clone()),
                None => {}
            }
            match self.prior.get_mut(&target) {
                Some(prior_vec) => prior_vec.extend(prior),
                None => {
                    self.prior.insert(target, prior);
                }
            }
        }
    }

    fn generate_future_effects(&mut self, bb: &BasicBlockData<'tcx>) -> Vec<BasicBlockData<'tcx>> {
        for _target in bb.terminator().successors() {
            // debug!("target: {:?}", target);
        }
        return vec![];
    }
}
