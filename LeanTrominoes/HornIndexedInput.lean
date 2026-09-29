/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornSolver

/-! # Dense-index Horn input and its occurrence stream

Variables are explicit slots `Fin n`; rules are stored in a random-access
array. No arbitrary-name comparison, sorting, or free renaming is assumed.
`none` is a separate contradiction atom and has no premise occurrences.
-/
namespace LeanTrominoes.Horn.Indexed

structure Input (n : Nat) where
  rules : Array (Rule (Fin n))
  deriving Repr

abbrev RuleId {n : Nat} (input : Input n) := Fin input.rules.size

def edges {n : Nat} (input : Input n) : List (Option (Fin n) × RuleId input) :=
  (List.finRange input.rules.size).flatMap fun r => input.rules[r].premises.map fun a => (some a,r)

def head {n : Nat} (input : Input n) (r : RuleId input) : Option (Fin n) := input.rules[r].conclusion

theorem mem_edges {n : Nat} (input : Input n) (a : Option (Fin n)) (r : RuleId input) :
    (a,r) ∈ edges input ↔ ∃ v ∈ input.rules[r].premises, some v=a := by
  simp [edges,List.mem_flatMap,List.mem_map,Prod.mk.injEq,and_assoc,and_left_comm,and_comm]

def premiseCount {n : Nat} (input : Input n) : Nat :=
  (input.rules.toList.map (fun r => r.premises.length)).sum

theorem edges_length {n : Nat} (input : Input n) : (edges input).length=premiseCount input := by
  simp only [edges,List.length_flatMap,List.length_map,premiseCount]
  have array : input.rules.toList=(List.finRange input.rules.size).map (fun i => input.rules[i]) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp
  rw [array,List.map_map]
  rfl

end LeanTrominoes.Horn.Indexed
