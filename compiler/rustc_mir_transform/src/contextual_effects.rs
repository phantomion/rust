use crate::MirPass;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

pub struct ContextualEffects;

impl<'tcx> MirPass<'tcx> for ContextualEffects {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        info!("function {:?}", body.source.instance);
        self.generate_contextual_effects(body)
    }
}

static mut EFFECT_COUNTER: u64 = 0;

impl ContextualEffects {
    fn generate_contextual_effects(&self, body: &mut Body<'_>) {
        let mut constraints = BlockConstraints::new();
        let preorder: Vec<_> = traversal::preorder(body).map(|(bb, _)| bb).collect();
        for bb in preorder {
            // debug!("block {:?}", bb);
            unsafe {
                // debug!("effect {}", EFFECT_COUNTER);
                constraints.current.insert(bb, EFFECT_COUNTER);
            }
            constraints.generate_prior_blocks(bb, body);
            let mut future = FxHashSet::default();
            constraints.generate_future_blocks(bb, body, &mut future);
            constraints.future.insert(bb, future);
            unsafe {
                EFFECT_COUNTER += 1;
            }
        }
        // debug!("prior: {:?}", constraints.prior);
        // debug!("future: {:?}", constraints.future);
        // debug!("current: {:?}", constraints.current);
        for (bb, effect) in constraints.current.clone() {
            info!("ε_{} {{", effect);
            constraints.visit_basic_block_data(bb, &body[bb]);

            if let Some(set) = constraints.prior.get(&bb) {
                for block in set.into_iter() {
                    let set_block_effect = constraints.current.get(&block).unwrap();
                    info!("α_{} <- α_{}", set_block_effect, effect);
                }
            }

            if let Some(set) = constraints.future.get(&bb) {
                for block in set.into_iter() {
                    let set_block_effect = constraints.current.get(&block).unwrap();
                    info!("ω_{} <- ω_{}", set_block_effect, effect);
                }
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for BlockConstraints {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, _location: Location) {
        info!("{:?}", statement);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        info!("}}");
        match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let block = self.current.get(&location.block).unwrap();
                info!("ε_{} <- ε_{:?}", block, func);
                info!("α_{} <- α_{:?}", block, func);
                info!("ω_{} -> ω_{:?}", block, func);
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
    current: FxHashMap<BasicBlock, u64>,
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
