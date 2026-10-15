/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteCertificateWords
import LeanTrominoes.Complexity.FiniteSymbolicMachineCNF

/-! # Linear-size Boolean constraints for an unknown binary certificate -/
noncomputable section
namespace LeanTrominoes.FiniteCertificate
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]
variable (stack : tm.K) (initial : List (tm.Γ stack)) (bit : Bool → tm.Γ stack) (capacity : Nat)

def cellExpression (index : Fin space) : TransitionExpr :=
  if index.val < initial.length then currentStackCellIs (clockBits := 0) stack index initial[index.val]?
  else if index.val < initial.length+capacity then
    .or (currentStackCellIs (clockBits := 0) stack index none)
      (.or (currentStackCellIs (clockBits := 0) stack index (some (bit false)))
        (currentStackCellIs (clockBits := 0) stack index (some (bit true))))
  else currentStackCellIs (clockBits := 0) stack index none

def stackExpression : TransitionExpr :=
  TransitionExpr.all ((List.finRange space).map (cellExpression tm space stack initial bit capacity))

theorem cellExpression_encode (index : Fin space) (cfg : tm.Cfg) :
    (cellExpression tm space stack initial bit capacity index).eval
      (FiniteMachineTrace.configValues tm space cfg) (FiniteMachineTrace.configValues tm space cfg)=true ↔
      CellAllowed initial bit capacity index.val (cfg.stk stack)[index.val]? := by
  simp only [cellExpression,CellAllowed]
  split_ifs
  all_goals simp [currentStackCellIs,TransitionExpr.current,TransitionExpr.eval,
    TransitionWire.value,FiniteMachineTrace.configValues,Bool.exists_bool]

theorem stackExpression_encode (cfg : tm.Cfg)
    (fits : (cfg.stk stack).length ≤ space) (room : initial.length+capacity ≤ space) :
    (stackExpression tm space stack initial bit capacity).eval
      (FiniteMachineTrace.configValues tm space cfg) (FiniteMachineTrace.configValues tm space cfg)=true ↔
      ∃ certificate : List Bool, certificate.length ≤ capacity ∧ cfg.stk stack=initial++certificate.map bit := by
  rw [stackExpression,TransitionExpr.all_eval,List.all_eq_true]
  simp only [List.forall_mem_map,List.mem_finRange,forall_const,
    cellExpression_encode]
  exact bounded_cellAllowed_iff initial bit capacity space (cfg.stk stack) fits room

theorem cellExpression_atomsBelow (index : Fin space) :
    (cellExpression tm space stack initial bit capacity index).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := 0)) := by
  unfold cellExpression
  split_ifs
  · exact currentStackCellIs_atomsBelow _ _ _
  · exact ⟨currentStackCellIs_atomsBelow _ _ _,currentStackCellIs_atomsBelow _ _ _,
      currentStackCellIs_atomsBelow _ _ _⟩
  · exact currentStackCellIs_atomsBelow _ _ _

theorem stackExpression_atomsBelow :
    (stackExpression tm space stack initial bit capacity).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := 0)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression member
  obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
  exact cellExpression_atomsBelow tm space stack initial bit capacity index

theorem cellExpression_gateCount_le (index : Fin space) :
    (cellExpression tm space stack initial bit capacity index).gateCount ≤ 5 := by
  unfold cellExpression
  split_ifs <;> simp [currentStackCellIs,TransitionExpr.current,TransitionExpr.gateCount]

theorem stackExpression_gateCount_le :
    (stackExpression tm space stack initial bit capacity).gateCount ≤ 6*space+1 := by
  have bound (indices : List (Fin space)) :
      (TransitionExpr.all (indices.map (cellExpression tm space stack initial bit capacity))).gateCount ≤
        6*indices.length+1 := by
    induction indices with
    | nil => simp [TransitionExpr.all,TransitionExpr.gateCount]
    | cons index rest ih =>
      have h := cellExpression_gateCount_le tm space stack initial bit capacity index
      simp only [List.map_cons,TransitionExpr.all,TransitionExpr.gateCount,List.length_cons]
      omega
  simpa [stackExpression] using bound (List.finRange space)

end LeanTrominoes.FiniteCertificate
