/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMFreshResources
import LeanTrominoes.Tiling.Domino.DominoWordRAMProbeSemantics

/-! # Dimension-dependent constants for candidate decoding -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Candidate
variable {d : ℕ}

noncomputable def nodeCount (direction coordinate : Fin d) : ℕ :=
  ((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length
noncomputable def slots (direction coordinate : Fin d) : ℕ := d*d+2*d+nodeCount direction coordinate
noncomputable def slotBound (d : ℕ) : ℕ := d*d+2*d+∑ direction : Fin d, ∑ coordinate : Fin d, nodeCount direction coordinate
noncomputable def space (direction : Fin d) : ℕ := ∑ coordinate : Fin d, (slots direction coordinate+3)

theorem nodes_le (direction coordinate : Fin d) : nodeCount direction coordinate≤ slotBound d := by
  have inner := Finset.single_le_sum (s:=Finset.univ) (f:=fun coordinate : Fin d => nodeCount direction coordinate)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ coordinate)
  have outer := Finset.single_le_sum (s:=Finset.univ) (f:=fun direction : Fin d => ∑ coordinate : Fin d, nodeCount direction coordinate)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ direction)
  unfold slotBound
  omega

theorem slots_le (direction coordinate : Fin d) : slots direction coordinate≤ slotBound d := by
  have inner := Finset.single_le_sum (s:=Finset.univ) (f:=fun coordinate : Fin d => nodeCount direction coordinate)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ coordinate)
  have outer := Finset.single_le_sum (s:=Finset.univ) (f:=fun direction : Fin d => ∑ coordinate : Fin d, nodeCount direction coordinate)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ direction)
  unfold slotBound slots
  omega

theorem arity_le (d : ℕ) : d*d+2*d≤ slotBound d := by unfold slotBound; omega

theorem space_le (direction : Fin d) : space direction≤ d*(slotBound d+3) := by
  unfold space
  calc
    _≤∑ _ : Fin d, (slotBound d+3) := Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (slots_le direction i) 3)
    _=_ := by simp [Nat.mul_comm]

def coordinateCost (slots length : ℕ) : ℕ := (100*slots+1000)*(length+1)^2

theorem coordinate_cost (direction coordinate : Fin d) (length : ℕ) :
    4*((slots direction coordinate+3)*length)+
      (26*length^2+26*length+16)*nodeCount direction coordinate+
      29*length^2+65*length+107+(7*length+11)*(d*d+2*d)+7≤ coordinateCost (slotBound d) length := by
  have slots := slots_le direction coordinate
  have nodes := nodes_le direction coordinate
  have arity := arity_le d
  have first := Nat.mul_le_mul_right (4*length) (Nat.add_le_add_right slots 3)
  have second := Nat.mul_le_mul_right (26*length^2+26*length+16) nodes
  have third := Nat.mul_le_mul_right (7*length+11) arity
  unfold coordinateCost
  nlinarith only [first,second,third]

end LeanTrominoes.Domino.WordRAM.Binary.Candidate
