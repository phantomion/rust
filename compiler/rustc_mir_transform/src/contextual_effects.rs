use crate::MirPass;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use std::fs::OpenOptions;
use std::io::BufWriter;
use std::io::Write;

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
        let file = unsafe {
            if EFFECT_COUNTER == 0 {
                OpenOptions::new().write(true).create(true).truncate(true).open("effects.txt")
            } else {
                OpenOptions::new().write(true).create(true).append(true).open("effects.txt")
            }
        };
        let file = match file {
            Ok(file) => BufWriter::new(file),
            Err(e) => {
                error!("unable to open effects file: {}", e);
                return;
            }
        };
        let mut constraints = BlockConstraints::new(file);
        let preorder: Vec<_> = traversal::preorder(body).map(|(bb, _)| bb).collect();
        for bb in preorder {
            // debug!("block {:?}", bb);
            unsafe {
                // debug!("effect {}", EFFECT_COUNTER);
                constraints.current.insert(bb, EFFECT_COUNTER);
            }
            constraints.generate_prior_blocks(bb, body);
            /* let mut future = FxHashSet::default();
            constraints.generate_future_blocks(bb, body, &mut future);
            constraints.future.insert(bb, future); */
            unsafe {
                EFFECT_COUNTER += 1;
            }
        }
        let postorder: Vec<_> = traversal::postorder(body).map(|(bb, _)| bb).collect();
        for bb in postorder {
            constraints.generate_future_blocks(bb, body);
        }
        // debug!("prior: {:?}", constraints.prior);
        // debug!("future: {:?}", constraints.future);
        // debug!("current: {:?}", constraints.current);
        for (bb, effect) in constraints.current.clone() {
            info!("ε_{} {{", effect);
            constraints.file.write_all(format!("ε_{} {{", effect).as_bytes()).unwrap();
            constraints.visit_basic_block_data(bb, &body[bb]);

            if let Some(set) = constraints.prior.get(&bb) {
                for block in set.into_iter() {
                    let set_block_effect = constraints.current.get(&block).unwrap();
                    info!("α_{} <- α_{}", set_block_effect, effect);
                    constraints
                        .file
                        .write_all(format!("α_{} <- α_{}", set_block_effect, effect).as_bytes())
                        .unwrap();
                }
            }

            if let Some(set) = constraints.future.get(&bb) {
                for block in set.into_iter() {
                    let set_block_effect = constraints.current.get(&block).unwrap();
                    info!("ω_{} <- ω_{}", set_block_effect, effect);
                    constraints
                        .file
                        .write_all(format!("ω_{} <- ω_{}", set_block_effect, effect).as_bytes())
                        .unwrap();
                }
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for BlockConstraints {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, _location: Location) {
        info!("{:?}", statement);
        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                self.visit_assign(&place, &rvalue, _location)
            }
            StatementKind::FakeRead(_) => {}
            StatementKind::SetDiscriminant { .. } => {}
            StatementKind::Deinit(_) => {}
            StatementKind::StorageLive(_) => {}
            StatementKind::StorageDead(_) => {}
            StatementKind::Retag(_, _) => {}
            StatementKind::AscribeUserType(_, _) => {}
            StatementKind::Coverage(_) => {}
            StatementKind::CopyNonOverlapping(_) => {}
            StatementKind::Nop => {}
        }
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, _rvalue: &Rvalue<'tcx>, _location: Location) {
        self.file.write_all(format!("{:?} = ", place).as_bytes()).unwrap();
        self.visit_rvalue(rvalue, location)
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Use(op) => self.visit_operand(op, location),
            Rvalue::Repeat(_, _) => todo!(),
            Rvalue::Ref(_, _, _) => todo!(),
            Rvalue::ThreadLocalRef(_) => todo!(),
            Rvalue::AddressOf(_, _) => todo!(),
            Rvalue::Len(_) => todo!(),
            Rvalue::Cast(_, _, _) => todo!(),
            Rvalue::BinaryOp(_, _) => todo!(),
            Rvalue::CheckedBinaryOp(_, _) => todo!(),
            Rvalue::NullaryOp(_, _) => todo!(),
            Rvalue::UnaryOp(_, _) => todo!(),
            Rvalue::Discriminant(_) => todo!(),
            Rvalue::Aggregate(_, _) => todo!(),
            Rvalue::ShallowInitBox(_, _) => todo!(),
            Rvalue::CopyForDeref(_) => todo!(),
        }
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {}
            Operand::Constant(constant) => {
                self.visit_constant(constant, location);
            }
        }
    }

    fn visit_constant(&mut self, constant: &Constant<'tcx>, location: Location) {
        self.super_constant(constant, location);
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
    file: std::io::BufWriter<std::fs::File>,
}

impl<'tcx> BlockConstraints {
    fn new(file: std::io::BufWriter<std::fs::File>) -> Self {
        BlockConstraints {
            prior: FxHashMap::default(),
            future: FxHashMap::default(),
            current: FxHashMap::default(),
            file,
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

    fn generate_future_blocks(&mut self, bb: BasicBlock, body: &Body<'tcx>) {
        for target in body[bb].terminator().successors() {
            let mut future = match self.future.get(&target) {
                Some(future) => future.clone(),
                None => FxHashSet::default(),
            };
            future.insert(target);
            match self.future.get_mut(&bb) {
                Some(future_vec) => future_vec.extend(future),
                None => {
                    self.future.insert(bb, future);
                }
            };
        }
    }

    /* fn generate_future_blocks(
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
    } */
}
