/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTwoSATNormalization
import LeanTrominoes.FiniteReachHornQuery

/-! # Regression cases: alternation, anchoring, units, and finite query execution -/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph ImplicationGraph

def alternation : Formula (Fin 1) 1 :=
  [some (((0,true),0),((0,true),fun _ => 1)),
   some (((0,false),0),((0,false),fun _ => 1))]

theorem alternation_satisfiable : Satisfiable alternation := by
  refine ⟨fun _ z => z 0 % 2=0,?_⟩
  intro c member z
  simp only [alternation,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals simp only [Holds,Truth,Bool.false_eq_true,↓reduceIte,Pi.add_apply,Pi.zero_apply,add_zero]
  all_goals omega

theorem alternation_no_constant : ¬ ∃ model : Fin 1 → Prop, Satisfies alternation (fun a _ => model a) := by
  rintro ⟨model,satisfied⟩
  have positive := satisfied (some (((0,true),0),((0,true),fun _ => 1))) (by simp [alternation]) 0
  have negative := satisfied (some (((0,false),0),((0,false),fun _ => 1))) (by simp [alternation]) 0
  simp [Holds,Truth] at positive negative
  exact negative positive

theorem alternation_local : LocalDifferences alternation := by
  intro a b member i
  simp only [alternation,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal
  all_goals obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj equal)
  all_goals simp

-- The large common offset disappears before cover construction.
example : normalize ([some (((0,true),fun _ : Fin 1 => 1000000000),
    ((0,false),fun _ : Fin 1 => 1000000001))] : Formula (Fin 1) 1) =
    [some (((0,true),0),((0,false),fun _ => 1))] := by rfl

-- Kernel-evaluated queries exercise the indexed worklist implementation.
example : reachQuery (n := 3) [(0,1),(1,2)] 0 2=true := by decide +kernel
example : reachQuery (n := 3) [(0,1),(1,2)] 2 0=false := by decide +kernel
example : reachQuery (n := 1) [] 0 0=true := by decide +kernel

end LeanTrominoes.PeriodicTwoSAT
