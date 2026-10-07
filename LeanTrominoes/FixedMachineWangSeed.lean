/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanWang.Robinson.Machine.InputTiles

/-! # Fixed machine palettes with finite bottom-row prescriptions

Position tags in the input-dependent palette are replaced by two phases.
The finite prescription fixes the input prefix and a transition to the
unique blank-tail tile. The normal history palette is unchanged.
-/

namespace LeanTrominoes.FixedMachineWangSeed
open LeanWang MachineInput MachineInputTiles

def tailTile (M : Machine) : WangTile :=
  toWangTile 2 2 initialRowTag normalRowTag (blankHistoryTile M)

def fixedTiles (M : Machine) : TileSet :=
  normalTiles M ++
    (machineHistoryTiles M).map (toWangTile 1 1 initialRowTag normalRowTag) ++
    (machineHistoryTiles M).map (toWangTile 1 2 initialRowTag normalRowTag) ++
    [tailTile M]

def bottomTile (M : Machine) (input : List Nat) (position : Nat) : WangTile :=
  if position < tailPosition input then
    toWangTile 1 (if position + 1 < tailPosition input then 1 else 2)
      initialRowTag normalRowTag (historyTile M input 0 position)
  else tailTile M

def bottomSeed (M : Machine) (input : List Nat) : List (Nat × WangTile) :=
  (List.range (tailPosition input)).map fun p => (p, bottomTile M input p)

def SeededQuarter (T : TileSet) (seed : List (Nat × WangTile)) : Prop :=
  ∃ plane : Nat × Nat → TileIn T, ValidQuarterTiling T plane ∧
    ∀ p ∈ seed, (plane (p.1, 0)).1 = p.2

theorem bottomSeed_iff (M : Machine) (input : List Nat)
    (plane : Nat × Nat → TileIn (fixedTiles M)) :
    (∀ p ∈ bottomSeed M input, (plane (p.1, 0)).1 = p.2) ↔
      ∀ p < tailPosition input, (plane (p, 0)).1 = bottomTile M input p := by
  simp [bottomSeed]

theorem mem_fixedTiles_iff (M : Machine) (tile : WangTile) :
    tile ∈ fixedTiles M ↔
      (∃ h ∈ machineHistoryTiles M, toWangTile 0 0 normalRowTag normalRowTag h = tile) ∨
      (∃ h ∈ machineHistoryTiles M, toWangTile 1 1 initialRowTag normalRowTag h = tile) ∨
      (∃ h ∈ machineHistoryTiles M, toWangTile 1 2 initialRowTag normalRowTag h = tile) ∨
      tile = tailTile M := by
  simp [fixedTiles, normalTiles, List.mem_map, eq_comm]

theorem next_tail {M : Machine} {left right : WangTile}
    (east : left.e.unpair.1 = 2) (matched : left.HMatches right)
    (member : right ∈ fixedTiles M) : right = tailTile M := by
  have west : right.w.unpair.1 = 2 := by rw [← matched]; exact east
  rcases (mem_fixedTiles_iff M right).mp member with
    ⟨h, _, rfl⟩ | ⟨h, _, rfl⟩ | ⟨h, _, rfl⟩ | rfl
  · simp [toWangTile, horizontalColor] at west
  · simp [toWangTile, horizontalColor] at west
  · simp [toWangTile, horizontalColor] at west
  · rfl

theorem bottom_forced {M : Machine} {input : List Nat}
    {plane : Nat × Nat → TileIn (fixedTiles M)}
    (valid : ValidQuarterTiling (fixedTiles M) plane)
    (seeded : ∀ p ∈ bottomSeed M input, (plane (p.1, 0)).1 = p.2) :
    ∀ p, (plane (p, 0)).1 = bottomTile M input p := by
  have prescribed := (bottomSeed_iff M input plane).mp seeded
  have positive : 0 < tailPosition input := by simp [tailPosition]
  have atTail : (plane (tailPosition input, 0)).1 = tailTile M := by
    have previous := prescribed (tailPosition input - 1) (by omega)
    have east : (plane (tailPosition input - 1, 0)).1.e.unpair.1 = 2 := by
      rw [previous]
      simp [bottomTile, show tailPosition input - 1 < tailPosition input by omega,
        show ¬ tailPosition input - 1 + 1 < tailPosition input by omega,
        toWangTile, horizontalColor]
    exact next_tail east (by
      simpa only [show tailPosition input - 1 + 1 = tailPosition input by omega]
        using valid.1 (tailPosition input - 1, 0))
      (plane (tailPosition input, 0)).2
  have rest : ∀ p, tailPosition input ≤ p → (plane (p, 0)).1 = tailTile M := by
    intro p bound
    induction p, bound using Nat.le_induction with
    | base => exact atTail
    | succ p _ ih =>
        apply next_tail (left := (plane (p, 0)).1)
        · simp [ih, tailTile, toWangTile, horizontalColor]
        · exact valid.1 (p, 0)
        · exact (plane (p + 1, 0)).2
  intro p
  by_cases before : p < tailPosition input
  · exact prescribed p before
  · simpa [bottomTile, before] using rest p (by omega)

theorem positive_row_normal {M : Machine}
    {plane : Nat × Nat → TileIn (fixedTiles M)}
    (valid : ValidQuarterTiling (fixedTiles M) plane) (p time : Nat) :
    (plane (p, time + 1)).1 ∈ normalTiles M := by
  have lowerNorth : (plane (p, time)).1.n.unpair.1 = normalRowTag := by
    rcases (mem_fixedTiles_iff M _).mp (plane (p, time)).2 with
      ⟨h, _, equal⟩ | ⟨h, _, equal⟩ | ⟨h, _, equal⟩ | equal
    · simp [← equal, toWangTile, taggedTripleCellColor]
    · simp [← equal, toWangTile, taggedTripleCellColor]
    · simp [← equal, toWangTile, taggedTripleCellColor]
    · simp [equal, tailTile, toWangTile, taggedTripleCellColor]
  have upperSouth : (plane (p, time + 1)).1.s.unpair.1 = normalRowTag := by
    rw [← valid.2 (p, time)]
    exact lowerNorth
  rcases (mem_fixedTiles_iff M _).mp (plane (p, time + 1)).2 with
    ⟨h, member, equal⟩ | ⟨h, _, equal⟩ | ⟨h, _, equal⟩ | equal
  · exact List.mem_map.mpr ⟨h, member, equal⟩
  · have bad : initialRowTag = normalRowTag := by
      simpa [← equal, toWangTile, taggedTripleCellColor] using upperSouth
    exact (initialRowTag_ne_normalRowTag bad).elim
  · have bad : initialRowTag = normalRowTag := by
      simpa [← equal, toWangTile, taggedTripleCellColor] using upperSouth
    exact (initialRowTag_ne_normalRowTag bad).elim
  · have bad : initialRowTag = normalRowTag := by
      simpa [equal, tailTile, toWangTile, taggedTripleCellColor] using upperSouth
    exact (initialRowTag_ne_normalRowTag bad).elim

theorem bottom_north (M : Machine) (input : List Nat) (p : Nat) :
    (bottomTile M input p).n = (initialTile M input p).n := by
  by_cases before : p < tailPosition input
  · simp only [bottomTile, initialTile, if_pos before]
    split_ifs <;> rfl
  · simp only [bottomTile, initialTile, if_neg before]
    rw [historyTile_zero_eq_blank_of_tailPosition_le M input (le_refl _)]
    rfl

/-- Retagging the prescribed bottom row recovers the existing input machine
history reduction; all positive rows are literally unchanged. -/
theorem inputQuarter_of_seeded {M : Machine} {input : List Nat}
    (completed : SeededQuarter (fixedTiles M) (bottomSeed M input)) :
    TilesQuarterWithSeed (tiles M input) (seed M input) := by
  obtain ⟨plane, valid, seeded⟩ := completed
  let recovered : Nat × Nat → TileIn (tiles M input) := fun point =>
    if timeZero : point.2 = 0 then
      ⟨initialTile M input point.1, List.mem_append_left _ (initialTile_mem M input point.1)⟩
    else ⟨(plane point).1, List.mem_append_right _ (by
      rcases point with ⟨p, time⟩
      cases time with
      | zero => exact (timeZero rfl).elim
      | succ time => exact positive_row_normal valid p time)⟩
  refine ⟨recovered, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨p, time⟩
    cases time with
    | zero => exact initialTile_hMatches M input p
    | succ time => exact valid.1 (p, time + 1)
  · rintro ⟨p, time⟩
    cases time with
    | zero =>
        change (initialTile M input p).n = (plane (p, 1)).1.s
        rw [← bottom_north, ← bottom_forced valid seeded p]
        exact valid.2 (p, 0)
    | succ time => exact valid.2 (p, time + 1)
  · rfl

theorem not_seeded_of_halts {M : Machine} {input : List Nat} (halts : Halts M input) :
    ¬ SeededQuarter (fixedTiles M) (bottomSeed M input) :=
  fun completed => not_tilesQuarterWithSeed_of_halts halts (inputQuarter_of_seeded completed)

end LeanTrominoes.FixedMachineWangSeed
