/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCNFBounds
import LeanTrominoes.FiniteMachineTraceExpression

/-! # Absolute variables for finite transition tableaux

Each current/next wire is replaced by a single ordinary variable named by its
absolute time and source atom. This presents the whole tableau to one
structural Tseitin compiler invocation.
-/
namespace LeanTrominoes.FiniteCNF
open PeriodicCNF

def absoluteWire (time : Nat) (wire : TransitionWire) : TransitionWire :=
  ⟨.current,Nat.pair (match wire.slice with | .current => time | .next => time+1) wire.atom⟩

def absoluteExpression (time : Nat) : TransitionExpr → TransitionExpr
  | .constant b => .constant b
  | .wire w => .wire (absoluteWire time w)
  | .not e => .not (absoluteExpression time e)
  | .and e f => .and (absoluteExpression time e) (absoluteExpression time f)
  | .or e f => .or (absoluteExpression time e) (absoluteExpression time f)

theorem absoluteExpression_eval (time : Nat) (expression : TransitionExpr) (current next : Nat → Bool) :
    (absoluteExpression time expression).eval current next=
      expression.eval (fun atom => current (Nat.pair time atom))
        (fun atom => current (Nat.pair (time+1) atom)) := by
  induction expression with
  | constant b => rfl
  | wire w => cases w with | mk slice atom => cases slice <;> rfl
  | not e ih => simp [absoluteExpression,TransitionExpr.eval,ih]
  | and e f ih1 ih2 => simp [absoluteExpression,TransitionExpr.eval,ih1,ih2]
  | or e f ih1 ih2 => simp [absoluteExpression,TransitionExpr.eval,ih1,ih2]

theorem absoluteExpression_gateCount (time : Nat) (expression : TransitionExpr) :
    (absoluteExpression time expression).gateCount=expression.gateCount := by
  induction expression <;> simp_all [absoluteExpression,TransitionExpr.gateCount]

theorem absoluteExpression_atomsBelow (time : Nat) (expression : TransitionExpr) (fresh steps : Nat)
    (bound : expression.AtomsBelow fresh) (early : time < steps) :
    (absoluteExpression time expression).AtomsBelow ((steps+fresh+1)^2) := by
  induction expression with
  | constant b => trivial
  | wire w =>
    have small : w.atom < fresh := bound
    have timeBound : (match w.slice with | .current => time | .next => time+1) ≤ steps := by
      cases w.slice <;> dsimp <;> omega
    have maxBound : max (match w.slice with | .current => time | .next => time+1) w.atom+1 ≤ steps+fresh+1 := by omega
    exact (Nat.pair_lt_max_add_one_sq _ _).trans_le (Nat.pow_le_pow_left maxBound 2)
  | not e ih => exact ih bound
  | and e f ih1 ih2 => exact ⟨ih1 bound.1,ih2 bound.2⟩
  | or e f ih1 ih2 => exact ⟨ih1 bound.1,ih2 bound.2⟩

def tableauExpression (expressions : Nat → TransitionExpr) (steps : Nat) : TransitionExpr :=
  TransitionExpr.all ((List.range steps).map fun time => absoluteExpression time (expressions time))

theorem tableauExpression_eval (expressions : Nat → TransitionExpr) (steps : Nat) (current next : Nat → Bool) :
    (tableauExpression expressions steps).eval current next=true ↔
      ∀ time < steps, (expressions time).eval (fun atom => current (Nat.pair time atom))
        (fun atom => current (Nat.pair (time+1) atom))=true := by
  simp [tableauExpression,TransitionExpr.all_eval,absoluteExpression_eval]

theorem tableauExpression_atomsBelow (expressions : Nat → TransitionExpr) (fresh steps : Nat)
    (bounds : ∀ time < steps, (expressions time).AtomsBelow fresh) :
    (tableauExpression expressions steps).AtomsBelow ((steps+fresh+1)^2) := by
  apply TransitionExpr.all_atomsBelow
  intro expression member
  obtain ⟨time,ht,rfl⟩ := List.mem_map.mp member
  exact absoluteExpression_atomsBelow time _ fresh steps (bounds time (List.mem_range.mp ht)) (List.mem_range.mp ht)

theorem tableauExpression_gateCount_le (expressions : Nat → TransitionExpr) (steps gateBound : Nat)
    (bounds : ∀ time < steps, (expressions time).gateCount ≤ gateBound) :
    (tableauExpression expressions steps).gateCount ≤ steps*(gateBound+1)+1 := by
  have allBound (times : List Nat) (small : ∀ time∈times, (expressions time).gateCount ≤ gateBound) :
      (TransitionExpr.all (times.map fun time => absoluteExpression time (expressions time))).gateCount ≤
        times.length*(gateBound+1)+1 := by
    induction times with
    | nil => simp [TransitionExpr.all,TransitionExpr.gateCount]
    | cons time rest ih =>
      have head := small time (by simp)
      have tail := ih (fun t ht => small t (by simp [ht]))
      simp only [List.map_cons,TransitionExpr.all,TransitionExpr.gateCount,
        absoluteExpression_gateCount,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simpa [tableauExpression] using allBound (List.range steps) (fun time ht => bounds time (List.mem_range.mp ht))

theorem tableauExpression_correct (expressions : Nat → TransitionExpr) (fresh steps : Nat)
    (bounds : ∀ time < steps, (expressions time).AtomsBelow fresh) :
    (∃ assignment : Nat → Bool, (tableauExpression expressions steps).eval assignment assignment=true) ↔
      Satisfiable (traceFormula expressions fresh steps) := by
  rw [traceFormula_correct expressions fresh steps bounds]
  constructor
  · rintro ⟨assignment,truth⟩
    exact ⟨fun time atom => assignment (Nat.pair time atom),(tableauExpression_eval _ _ _ _).mp truth⟩
  · rintro ⟨trace,truth⟩
    refine ⟨fun atom => trace (Nat.unpair atom).1 (Nat.unpair atom).2,?_⟩
    apply (tableauExpression_eval _ _ _ _).mpr
    simpa only [Nat.unpair_pair] using truth

end LeanTrominoes.FiniteCNF
