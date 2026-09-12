/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55SourceMask
import LeanTrominoes.PlusRefinementMembership

/-! # An executable list of cells for the disconnected tile -/

namespace LeanTrominoes.Theorem55Compiler

abbrev Input := Nat × PeriodicRegion

instance paddingMembershipDecidable (n : Nat) (c : Cell) :
    Decidable (c ∈ PeriodicTrominoPadding.region n) :=
  inferInstanceAs (Decidable ((_ ∨ _) ∧ _ ∧ _))

def preparedContains (input : Input) (c : Cell) : Bool :=
  input.2.validContains (Cell.add (54, 18) c) ||
    decide (c ∈ PeriodicTrominoPadding.region input.1)

def refinedContains (input : Input) (c : Cell) : Bool :=
  preparedContains input (PlusRefinement.parent c) &&
    decide (PlusRefinement.subcell c ∈ PlusRefinement.cross)

def squareList (n : Nat) : List Cell :=
  ((List.range n).product (List.range n)).map (fun p : Nat × Nat => ((p.1 : Int), (p.2 : Int)))

theorem squareList_toFinset (n : Nat) : (squareList n).toFinset = KeyedPeriodicComplement.square n := by
  ext c
  simp [squareList, KeyedPeriodicComplement.square]

/-- Enumerate the unoccupied cells and transfer the two boundary keys. -/
def compile (input : Input) : List Cell :=
  ((squareList (3 * input.1)).filter (fun c => !refinedContains input c)).map
    (KeyedPeriodicComplement.repack (3 * input.1))

def sourceInput {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) : Input :=
  (Theorem55Source.period presentation,
    presentation.normalizedOrthogonalDrawing.periodicRegion .I)

theorem preparedContains_source {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (c : Cell) :
    preparedContains (sourceInput presentation) c = true ↔ c ∈ Theorem55Source.region presentation := by
  simp only [preparedContains, sourceInput, Bool.or_eq_true, decide_eq_true_eq,
    PeriodicRegion.validContains_eq_true_iff,
    Gadget.PeriodicOrthogonalDrawing.periodicRegion_fullRank, true_and]
  rfl

theorem refinedContains_source {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (c : Cell) :
    refinedContains (sourceInput presentation) c = true ↔
      c ∈ PlusRefinement.region (Theorem55Source.region presentation) := by
  rw [PlusRefinement.mem_region_iff]
  simp only [refinedContains, Bool.and_eq_true, decide_eq_true_eq, preparedContains_source]

theorem compile_eq_tile (input : Input) :
    (compile input).toFinset = KeyedPeriodicComplement.tile (3 * input.1)
      (KeyedPeriodicComplement.mask (3 * input.1) {c | refinedContains input c = true}) := by
  have background :
      ((squareList (3 * input.1)).filter (fun c => !refinedContains input c)).toFinset =
      KeyedPeriodicComplement.background (3 * input.1)
        (KeyedPeriodicComplement.mask (3 * input.1) {c | refinedContains input c = true}) := by
    ext c
    simp only [KeyedPeriodicComplement.background, Finset.mem_sdiff,
      KeyedPeriodicComplement.mem_mask, Set.mem_setOf_eq,
      ← squareList_toFinset (3 * input.1), List.mem_toFinset, List.mem_filter]
    cases refinedContains input c <;> simp
  ext c
  simp only [compile, List.mem_toFinset, List.mem_map, KeyedPeriodicComplement.tile,
    Finset.mem_image, ← background, List.mem_toFinset]

theorem compile_source {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    (compile (sourceInput presentation)).toFinset =
      KeyedPeriodicComplement.tile (3 * Theorem55Source.period presentation)
        (Theorem55Source.holes presentation) := by
  have source : {c | refinedContains (sourceInput presentation) c = true} =
      PlusRefinement.region (Theorem55Source.region presentation) := by
    ext c
    exact refinedContains_source presentation c
  rw [compile_eq_tile, source]
  rfl

theorem compile_source_correct {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    Theorem55.planeProblem (compile (sourceInput presentation)) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier :=
  Theorem55Source.planeProblem_iff presentation _ (compile_source presentation)

end LeanTrominoes.Theorem55Compiler
