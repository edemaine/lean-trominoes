/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedMachineWangSeed
import Lean.Util.CollectAxioms

/-! # Finite prescriptions exactly characterize nonhalting

One fixed Wang palette simulates every supported finite input of its machine.
The prescribed prefix has `input.length + 3` tiles. No tile in the palette
depends on the input.
-/

namespace LeanTrominoes.FixedMachineWangSeed
open LeanWang MachineInput MachineInputTiles

theorem bottomTile_history (M : Machine) (input : List Nat) (p : Nat) :
    bottomTile M input p =
      toWangTile (if p < tailPosition input then 1 else 2)
        (if p + 1 < tailPosition input then 1 else 2)
        initialRowTag normalRowTag (historyTile M input 0 p) := by
  by_cases before : p < tailPosition input
  · simp [bottomTile, before]
  · have after : ¬ p + 1 < tailPosition input := by omega
    simp [bottomTile, before, after, tailTile,
      historyTile_zero_eq_blank_of_tailPosition_le M input (by omega : tailPosition input ≤ p)]

theorem bottomTile_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) (nonhalting : ¬ Halts M input) (p : Nat) :
    bottomTile M input p ∈ fixedTiles M := by
  by_cases before : p < tailPosition input
  · have history := historyTile_mem_machineHistoryTiles supported nonhalting 0 p
    rw [bottomTile, if_pos before, mem_fixedTiles_iff]
    by_cases further : p + 1 < tailPosition input
    · exact Or.inr (Or.inl ⟨_, history, by simp [further]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨_, history, by simp [further]⟩))
  · rw [bottomTile, if_neg before, mem_fixedTiles_iff]
    exact Or.inr (Or.inr (Or.inr rfl))

theorem bottomTile_hMatches (M : Machine) (input : List Nat) (p : Nat) :
    (bottomTile M input p).HMatches (bottomTile M input (p + 1)) := by
  rw [bottomTile_history, bottomTile_history, hMatches_toWangTile_iff]
  exact ⟨rfl, rfl, historyTile_hMatches M input 0 p⟩

def fixedRunTile (M : Machine) (input : List Nat) (time p : Nat) : WangTile :=
  if time = 0 then bottomTile M input p
  else toWangTile 0 0 normalRowTag normalRowTag (historyTile M input time p)

theorem fixedRunTile_mem {M : Machine} {input : List Nat}
    (supported : Supported M input) (nonhalting : ¬ Halts M input) (time p : Nat) :
    fixedRunTile M input time p ∈ fixedTiles M := by
  by_cases zero : time = 0
  · simp only [fixedRunTile, if_pos zero]
    exact bottomTile_mem supported nonhalting p
  · rw [fixedRunTile, if_neg zero, mem_fixedTiles_iff]
    exact Or.inl ⟨_, historyTile_mem_machineHistoryTiles supported nonhalting time p, rfl⟩

theorem fixedRunTile_hMatches (M : Machine) (input : List Nat) (time p : Nat) :
    (fixedRunTile M input time p).HMatches (fixedRunTile M input time (p + 1)) := by
  by_cases zero : time = 0
  · simp only [fixedRunTile, if_pos zero]
    exact bottomTile_hMatches M input p
  · simp only [fixedRunTile, if_neg zero, hMatches_toWangTile_iff]
    exact ⟨trivial, trivial, historyTile_hMatches M input time p⟩

theorem fixedRunTile_vMatches (M : Machine) (input : List Nat) (time p : Nat) :
    (fixedRunTile M input time p).VMatches (fixedRunTile M input (time + 1) p) := by
  cases time with
  | zero =>
      simp [fixedRunTile, bottomTile_history, vMatches_toWangTile_iff, historyTile]
  | succ time =>
      simp [fixedRunTile, vMatches_toWangTile_iff, historyTile]

theorem seeded_of_nonhalting {M : Machine} {input : List Nat}
    (supported : Supported M input) (nonhalting : ¬ Halts M input) :
    SeededQuarter (fixedTiles M) (bottomSeed M input) := by
  let plane : Nat × Nat → TileIn (fixedTiles M) := fun point =>
    ⟨fixedRunTile M input point.2 point.1,
      fixedRunTile_mem supported nonhalting point.2 point.1⟩
  refine ⟨plane, ⟨?_, ?_⟩, ?_⟩
  · intro point
    exact fixedRunTile_hMatches M input point.2 point.1
  · intro point
    exact fixedRunTile_vMatches M input point.2 point.1
  · apply (bottomSeed_iff M input plane).mpr
    intro p _
    rfl

theorem seeded_iff_nonhalting {M : Machine} {input : List Nat}
    (supported : Supported M input) :
    SeededQuarter (fixedTiles M) (bottomSeed M input) ↔ ¬ Halts M input :=
  ⟨fun completed halts => not_seeded_of_halts halts completed,
    seeded_of_nonhalting supported⟩

theorem bottomSeed_length (M : Machine) (input : List Nat) :
    (bottomSeed M input).length = input.length + 3 := by
  simp [bottomSeed, tailPosition]

open Lean Elab Command in
run_cmd do
  let name := ``seeded_iff_nonhalting
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do
    throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedMachineWangSeed
