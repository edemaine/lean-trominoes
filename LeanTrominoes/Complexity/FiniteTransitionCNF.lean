/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteCNF
import LeanTrominoes.SAT.CNF.PeriodicCNFTransitionExprFormula

/-! # Unrolling forward-local constraints into an ordinary finite CNF

No periodic boundary condition is added: the last slice remains distinct from
the initial slice. This is the finite-time interface for the machine compiler.
-/
namespace LeanTrominoes.FiniteCNF

def timeLiteral {V : Type*} (time : Nat) (literal : PeriodicLiteral V) : Literal (Nat × V) :=
  ((if literal.offset=(0,0) then time else time+1,literal.atom),literal.value)

theorem timeLiteral_holds {V : Type*} (time : Nat) (literal : PeriodicLiteral V)
    (forward : literal.IsForwardLocal) (assignment : Nat × V → Bool) :
    assignment (timeLiteral time literal).1=(timeLiteral time literal).2 ↔
      literal.HoldsBetween (fun v => assignment (time,v)) (fun v => assignment (time+1,v)) := by
  rcases forward with current|next <;> simp_all [timeLiteral,PeriodicLiteral.HoldsBetween]

def atTime {V : Type*} (formula : PeriodicCNF V) (time : Nat) : Formula (Nat × V) :=
  formula.clauses.map fun clause => clause.map (timeLiteral time)

theorem satisfies_atTime {V : Type*} (formula : PeriodicCNF V)
    (forward : formula.IsForwardLocal) (time : Nat) (assignment : Nat × V → Bool) :
    Satisfies (atTime formula time) assignment ↔
      formula.Transition (fun v => assignment (time,v)) (fun v => assignment (time+1,v)) := by
  constructor
  · intro h clause hc
    obtain ⟨l,hl,truth⟩ := h _ (List.mem_map.mpr ⟨clause,hc,rfl⟩)
    obtain ⟨literal,member,rfl⟩ := List.mem_map.mp hl
    exact ⟨literal,member,(timeLiteral_holds time literal (forward clause hc literal member) assignment).mp truth⟩
  · intro h clause hc
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp hc
    obtain ⟨literal,hl,truth⟩ := h original member
    exact ⟨timeLiteral time literal,List.mem_map.mpr ⟨literal,hl,rfl⟩,
      (timeLiteral_holds time literal (forward original member literal hl) assignment).mpr truth⟩

/-- Explicitly repeat the finite transition constraints at times `0,...,steps-1`. -/
def unroll {V : Type*} (formula : PeriodicCNF V) (steps : Nat) : Formula (Nat × V) :=
  (List.range steps).flatMap (atTime formula)

theorem satisfies_unroll {V : Type*} (formula : PeriodicCNF V)
    (forward : formula.IsForwardLocal) (steps : Nat) (assignment : Nat × V → Bool) :
    Satisfies (unroll formula steps) assignment ↔
      ∀ time<steps, formula.Transition (fun v => assignment (time,v)) (fun v => assignment (time+1,v)) := by
  change (∀ clause∈(List.range steps).flatMap (atTime formula), Clause.Holds assignment clause) ↔ _
  simp only [List.mem_flatMap,List.mem_range,forall_exists_index,and_imp]
  constructor
  · intro h time ht
    exact (satisfies_atTime formula forward time assignment).mp (fun clause hc => h clause time ht hc)
  · intro h clause time ht hc
    exact (satisfies_atTime formula forward time assignment).mpr (h time ht) clause hc

theorem satisfiable_unroll {V : Type*} (formula : PeriodicCNF V)
    (forward : formula.IsForwardLocal) (steps : Nat) :
    Satisfiable (unroll formula steps) ↔
      ∃ trace : Nat → V → Bool, ∀ time<steps, formula.Transition (trace time) (trace (time+1)) := by
  constructor
  · rintro ⟨assignment,h⟩
    exact ⟨fun time v => assignment (time,v),(satisfies_unroll formula forward steps assignment).mp h⟩
  · rintro ⟨trace,h⟩
    exact ⟨fun p => trace p.1 p.2,(satisfies_unroll formula forward steps _).mpr h⟩

theorem unroll_length {V : Type*} (formula : PeriodicCNF V) (steps : Nat) :
    (unroll formula steps).length=steps*formula.clauses.length := by
  unfold unroll
  rw [List.length_flatMap]
  simp [atTime,List.map_map,Function.comp_def]

end LeanTrominoes.FiniteCNF
