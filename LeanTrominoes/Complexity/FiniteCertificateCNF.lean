/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteCertificateInitialization

/-! # Finite 3CNF for existence of an accepted bounded certificate -/
noncomputable section
namespace LeanTrominoes.FiniteCertificate
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom FiniteMachineTrace
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def formula (initial : List (tm.Γ tm.k₀)) (bit : Bool → tm.Γ tm.k₀)
    (capacity : Nat) (final : tm.Cfg) (steps : Nat) : FiniteCNF.Formula (Nat × Nat) :=
  symbolicFormula tm space (initialExpression tm space initial bit capacity) final steps

theorem formula_correct (initial : List (tm.Γ tm.k₀)) (bit : Bool → tm.Γ tm.k₀)
    (capacity : Nat) (final : tm.Cfg) (steps : Nat)
    (enough : initial.length+capacity+steps*TM2OutputLength.machinePushBound tm ≤ space)
    (finalFits : ∀ stack, (final.stk stack).length ≤ space) :
    FiniteCNF.Satisfiable (formula tm space initial bit capacity final steps) ↔
      ∃ certificate : List Bool, certificate.length ≤ capacity ∧
        Nonempty (StateTransition.EvalsToInTime tm.step
          (initList tm (initial++certificate.map bit)) (some final) steps) := by
  have room : initial.length+capacity ≤ space := by omega
  have spaceBound (cfg : tm.Cfg) (fits : ∀ stack, (cfg.stk stack).length ≤ space)
      (accepted : (initialExpression tm space initial bit capacity).eval
        (configValues tm space cfg) (configValues tm space cfg)=true) :
      TM2.stackSpace cfg+steps*TM2OutputLength.machinePushBound tm ≤ space := by
    obtain ⟨certificate,bound,rfl⟩ := (initialExpression_encode tm space initial bit capacity cfg fits room).mp accepted
    rw [TM2OutputLength.stackSpace_initList]
    simp only [List.length_append,List.length_map]
    omega
  rw [formula,symbolicFormula_iff_evals tm space _ final steps
    (initialExpression_atomsBelow tm space initial bit capacity) spaceBound finalFits]
  constructor
  · rintro ⟨cfg,fits,accepted,run⟩
    obtain ⟨certificate,bound,rfl⟩ := (initialExpression_encode tm space initial bit capacity cfg fits room).mp accepted
    exact ⟨certificate,bound,run⟩
  · rintro ⟨certificate,bound,run⟩
    have fits (stack : tm.K) : ((initList tm (initial++certificate.map bit)).stk stack).length ≤ space := by
      by_cases same : stack=tm.k₀
      · subst stack
        simp [initList]
        omega
      · simp [initList,same]
    refine ⟨initList tm (initial++certificate.map bit),fits,?_,run⟩
    exact (initialExpression_encode tm space initial bit capacity _ fits room).mpr ⟨certificate,bound,rfl⟩

theorem formula_width (initial : List (tm.Γ tm.k₀)) (bit : Bool → tm.Γ tm.k₀)
    (capacity : Nat) (final : tm.Cfg) (steps : Nat) :
    FiniteCNF.WidthAtMost 3 (formula tm space initial bit capacity final steps) :=
  symbolicFormula_width tm space _ final steps

theorem formula_length_le (initial : List (tm.Γ tm.k₀)) (bit : Bool → tm.Γ tm.k₀)
    (capacity : Nat) (final : tm.Cfg) (steps : Nat) :
    (formula tm space initial bit capacity final steps).length ≤
      (steps+1)*(3*(paddedTraceSlope tm*space+paddedTraceIntercept tm+
        (Fintype.card tm.K*(2*space+2)+6*space+7))+1) := by
  have h := symbolicFormula_length_le tm space (initialExpression tm space initial bit capacity) final steps
  have count := initialExpression_gateCount_le tm space initial bit capacity
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.mul_le_mul_left 3 (Nat.add_le_add_left count _)) 1))

end LeanTrominoes.FiniteCertificate
