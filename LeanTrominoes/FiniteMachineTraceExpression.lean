/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFMachineFormula

/-! # Initialization, bounded TM2 steps, and acceptance at specified times -/
namespace LeanTrominoes.PeriodicCNF.TransitionExpr

def atCurrent : TransitionExpr → TransitionExpr
  | .constant b => .constant b
  | .wire w => .wire ⟨.current,w.atom⟩
  | .not e => .not e.atCurrent
  | .and e f => .and e.atCurrent f.atCurrent
  | .or e f => .or e.atCurrent f.atCurrent

theorem atCurrent_eval (e : TransitionExpr) (current next : Nat → Bool) :
    e.atCurrent.eval current next=e.eval current current := by
  induction e with
  | constant b => rfl
  | wire w => cases w with | mk s atom => cases s <;> rfl
  | not e ih => simp [atCurrent,eval,ih]
  | and e f ih1 ih2 => simp [atCurrent,eval,ih1,ih2]
  | or e f ih1 ih2 => simp [atCurrent,eval,ih1,ih2]

theorem atCurrent_atomsBelow {e : TransitionExpr} {bound : Nat} (h : e.AtomsBelow bound) :
    e.atCurrent.AtomsBelow bound := by
  induction e <;> simp_all [atCurrent,AtomsBelow]

theorem atCurrent_gateCount (e : TransitionExpr) : e.atCurrent.gateCount=e.gateCount := by
  induction e <;> simp_all [atCurrent,gateCount]

def atNext : TransitionExpr → TransitionExpr
  | .constant b => .constant b
  | .wire w => .wire ⟨.next,w.atom⟩
  | .not e => .not e.atNext
  | .and e f => .and e.atNext f.atNext
  | .or e f => .or e.atNext f.atNext

theorem atNext_eval (e : TransitionExpr) (current next : Nat → Bool) :
    e.atNext.eval current next=e.eval next next := by
  induction e with
  | constant b => rfl
  | wire w => cases w with | mk s atom => cases s <;> rfl
  | not e ih => simp [atNext,eval,ih]
  | and e f ih1 ih2 => simp [atNext,eval,ih1,ih2]
  | or e f ih1 ih2 => simp [atNext,eval,ih1,ih2]

theorem atNext_atomsBelow {e : TransitionExpr} {bound : Nat} (h : e.AtomsBelow bound) :
    e.atNext.AtomsBelow bound := by
  induction e <;> simp_all [atNext,AtomsBelow]

theorem atNext_gateCount (e : TransitionExpr) : e.atNext.gateCount=e.gateCount := by
  induction e <;> simp_all [atNext,gateCount]

end LeanTrominoes.PeriodicCNF.TransitionExpr

noncomputable section
namespace LeanTrominoes.FiniteMachineTrace
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- The last time has a final-state test instead of an outgoing machine step.
At time zero both the initial-state test and the appropriate last/step test
are imposed, so zero-step computations are represented correctly. -/
def expression (initial final : tm.Cfg) (steps time : Nat) : TransitionExpr :=
  .and (wellFormedFields (tm := tm) (space := space) (clockBits := 0))
    (.and
      (if time=0 then (currentConfigIs (space := space) (clockBits := 0) initial).atCurrent else .constant true)
      (if time=steps then (currentConfigIs (space := space) (clockBits := 0) final).atCurrent
       else machineStepExpression (tm := tm) (space := space) (clockBits := 0)))

theorem expression_atomsBelow (initial final : tm.Cfg) (steps time : Nat) :
    (expression tm space initial final steps time).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := 0)) := by
  refine ⟨wellFormedFields_atomsBelow,?_,?_⟩
  · split_ifs
    · exact TransitionExpr.atCurrent_atomsBelow (currentConfigIs_atomsBelow initial)
    · trivial
  · split_ifs
    · exact TransitionExpr.atCurrent_atomsBelow (currentConfigIs_atomsBelow final)
    · exact machineStepExpression_atomsBelow

/-- Endpoint tests on arbitrary well-formed Boolean slices identify their
actual decoded machine configuration, not merely a canonical witness. -/
theorem currentConfig_decode (target : tm.Cfg) (values : Nat → Bool)
    (fit : ∀ stack, (target.stk stack).length≤space)
    (wf : (wellFormedFields (tm := tm) (space := space) (clockBits := 0)).eval values values=true) :
    (currentConfigIs (space := space) (clockBits := 0) target).eval values values=true ↔
      (decode (tm := tm) (space := space) (clockBits := 0) values).toCfg=target := by
  let state := (decode (tm := tm) (space := space) (clockBits := 0) values).toResetClockState
  have agree := encode_toResetClockState_decode_below wf
  have bound := currentConfigIs_atomsBelow (clockBits := 0) (space := space) target
  have eq1 := TransitionExpr.eval_congr_current bound (next := values) agree
  have eq2 := TransitionExpr.eval_congr_next bound
    (current := encode (space := space) (clockBits := 0) state) agree
  rw [← eq1,← eq2]
  exact currentConfigIs_encode_iff state state target
    (fun stack => BoundedMachineSlice.toCfg_stack_length_le _ stack) fit

end LeanTrominoes.FiniteMachineTrace
