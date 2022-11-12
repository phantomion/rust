use crate::MirPass;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

pub struct ContextualEffects;

impl<'tcx> MirPass<'tcx> for ContextualEffects {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        debug!("function {:?}", body.source.instance);
        self.generate_contextual_effects(body)
    }
}

static mut EFFECT_COUNTER: i64 = 0;

impl ContextualEffects {
    fn generate_contextual_effects(&self, body: &mut Body<'_>) {
        let mut effects = BlockConstraints::new();
        let preorder: Vec<_> = traversal::preorder(body).map(|(bb, _)| bb).collect();
        for bb in preorder {
            unsafe {
                effects.current.insert(bb, EFFECT_COUNTER);
            }
            effects.generate_prior_blocks(bb, body);
            let mut future = FxHashSet::default();
            effects.generate_future_blocks(bb, body, &mut future);
            effects.future.insert(bb, future);
            unsafe {
                EFFECT_COUNTER += 1;
            }
        }
        /* debug!("prior: {:?}", effects.prior);
        debug!("future: {:?}", effects.future);
        debug!("current: {:?}", effects.current); */
        for (bb, effect) in effects.current.clone() {
            debug!("ε_{} {{", effect);
            effects.visit_basic_block_data(bb, &body[bb]);
        }
        for (bb, set) in effects.prior.clone() {
            for block in set {
                let set_block_effect = effects.current.get(&block).unwrap();
                let curr_block_effect = effects.current.get(&bb).unwrap();
                debug!("α_{} -> α_{}", curr_block_effect, set_block_effect);
            }
        }
        for (bb, set) in effects.future.clone() {
            for block in set {
                let set_block_effect = effects.current.get(&block).unwrap();
                let curr_block_effect = effects.current.get(&bb).unwrap();
                debug!("ω_{} <- ω_{}", curr_block_effect, set_block_effect);
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for BlockConstraints {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, _location: Location) {
        debug!("{:?}", statement);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        debug!("}}");
        match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let block = self.current.get(&location.block).unwrap();
                debug!("ε_{} -> ε_{:?}", block, func);
            }
            TerminatorKind::SwitchInt { .. } => {}
            TerminatorKind::Drop { .. } => {}
            TerminatorKind::Goto { .. }
            | TerminatorKind::Resume
            | TerminatorKind::Abort
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::DropAndReplace { .. }
            | TerminatorKind::Assert { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::GeneratorDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::InlineAsm { .. } => {}
        }
    }
}

struct BlockConstraints {
    prior: FxHashMap<BasicBlock, FxHashSet<BasicBlock>>,
    current: FxHashMap<BasicBlock, i64>,
    future: FxHashMap<BasicBlock, FxHashSet<BasicBlock>>,
}

impl<'tcx> BlockConstraints {
    fn new() -> Self {
        BlockConstraints {
            prior: FxHashMap::default(),
            future: FxHashMap::default(),
            current: FxHashMap::default(),
        }
    }

    fn generate_prior_blocks(&mut self, bb: BasicBlock, body: &Body<'tcx>) {
        for target in body[bb].terminator().successors() {
            let mut prior = match self.prior.get(&bb) {
                Some(prior) => prior.clone(),
                None => FxHashSet::default(),
            };
            prior.insert(bb);
            match self.prior.get_mut(&target) {
                Some(prior_vec) => prior_vec.extend(prior),
                None => {
                    self.prior.insert(target, prior);
                }
            };
        }
    }

    fn generate_future_blocks(
        &mut self,
        bb: BasicBlock,
        body: &Body<'tcx>,
        future: &mut FxHashSet<BasicBlock>,
    ) {
        for target in body[bb].terminator().successors() {
            if future.contains(&target) {
                continue;
            }
            future.insert(target);
            self.generate_future_blocks(target, body, future);
        }
    }
}
