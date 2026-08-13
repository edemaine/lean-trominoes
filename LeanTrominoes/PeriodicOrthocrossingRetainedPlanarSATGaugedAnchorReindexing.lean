/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedAutomaticReindexing

/-!
# Anchor-directed reindexing of final gauged segments

Source period translation adds the same lattice vector to the canonically
gauged clause anchor.  Thus the translation taking a source clause to a
desired anchor is the desired anchor minus its current anchor.

This module records the corresponding common-shift algebra.  In particular,
for two final occurrences with external shifts `firstShift` and
`secondShift`, reindexing their source clauses to anchors
`firstShift - secondShift` and zero places both finite representatives at
the common external shift `secondShift`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The canonically gauged anchor of the finite clause selected behind a
final segment occurrence. -/
def FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    Cell :=
  PeriodicCNF.clauseAnchor
    (metadataGaugedPositionedClause
      formula witness.routeWitness.metadata).literals

/-- Period translation needed to move the source clause's gauged anchor to
`targetAnchor`. -/
def FinalGaugedSegmentOccurrenceWitness.anchorReindexShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (targetAnchor : Cell) :
    Cell :=
  Cell.sub targetAnchor witness.sourceClauseAnchor

theorem FinalGaugedSegmentOccurrenceWitness.physicalShift_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    witness.physicalShift =
      Cell.sub shift witness.sourceClauseAnchor := by
  rfl

/-- Moving the finite source clause to `targetAnchor` changes its external
representative shift from `shift - sourceAnchor` to
`shift - targetAnchor`. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.physicalShift_sub_anchorReindexShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (targetAnchor : Cell) :
    Cell.sub witness.physicalShift
        (witness.anchorReindexShift targetAnchor) =
      Cell.sub shift targetAnchor := by
  rcases shift with ⟨shiftX, shiftY⟩
  rcases targetAnchor with ⟨targetX, targetY⟩
  rcases witness.sourceClauseAnchor with ⟨anchorX, anchorY⟩
  simp [FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
    FinalGaugedSegmentOccurrenceWitness.anchorReindexShift,
    Cell.sub]

/-- Once an anchor-directed translate has a component-equivalent retained
source, the generic reindexing bridge produces its finite representative at
the simpler shift `shift - targetAnchor`. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.exists_commonShiftRepresentative_at_anchor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (targetAnchor : Cell)
    (targetSource : DrawingPlanarSATClauseSource Variable)
    (targetSourceMember :
      targetSource.RetainedComponentMember formula)
    (targetComponentEq :
      targetSource.component =
        (witness.routeWitness.metadata.source.periodTranslate
          formula
          (witness.anchorReindexShift targetAnchor)).component)
    (targetLocalClauseIndexEq :
      targetSource.localClauseIndex =
        witness.routeWitness.metadata.source.localClauseIndex) :
    Nonempty
      (FinalGaugedSegmentCommonShiftRepresentative
        formula indexed shift (Cell.sub shift targetAnchor)) := by
  simpa only [
    witness.physicalShift_sub_anchorReindexShift targetAnchor] using
    witness.exists_commonShiftRepresentative_of_targetSource
      targetSource targetSourceMember targetComponentEq
      targetLocalClauseIndexEq

/-- The two anchor choices used by the contact proof give exactly the same
finite-drawing translate. -/
theorem anchorReindex_commonShift_pair
    {firstShift secondShift : Cell} :
    Cell.sub firstShift (Cell.sub firstShift secondShift) =
        secondShift ∧
      Cell.sub secondShift (0, 0) = secondShift := by
  rcases firstShift with ⟨firstX, firstY⟩
  rcases secondShift with ⟨secondX, secondY⟩
  simp [Cell.sub]

/-- Keeping the second finite source unchanged determines the anchor to
which the first source must be moved. -/
theorem anchorReindex_commonShift_keep_second
    {firstShift secondShift secondAnchor : Cell} :
    Cell.sub firstShift
        (Cell.add (Cell.sub firstShift secondShift) secondAnchor) =
      Cell.sub secondShift secondAnchor := by
  rcases firstShift with ⟨firstX, firstY⟩
  rcases secondShift with ⟨secondX, secondY⟩
  rcases secondAnchor with ⟨anchorX, anchorY⟩
  simp only [Cell.add, Cell.sub]
  apply Prod.ext <;> simp <;> ring

/-- The anchor-directed translation that keeps the second representative
fixed is exactly the difference between the two existing physical shifts. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.anchorReindexShift_keep_second_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift) :
    first.anchorReindexShift
        (Cell.add (Cell.sub firstShift secondShift)
          second.sourceClauseAnchor) =
      Cell.sub first.physicalShift second.physicalShift := by
  rcases firstShift with ⟨firstX, firstY⟩
  rcases secondShift with ⟨secondX, secondY⟩
  rcases firstAnchorEq : first.sourceClauseAnchor with
    ⟨firstAnchorX, firstAnchorY⟩
  rcases secondAnchorEq : second.sourceClauseAnchor with
    ⟨secondAnchorX, secondAnchorY⟩
  simp only [
    FinalGaugedSegmentOccurrenceWitness.anchorReindexShift,
    FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
    firstAnchorEq, secondAnchorEq, Cell.add, Cell.sub]
  apply Prod.ext <;> simp <;> ring

/-- Package the remaining orbit obligations for two final occurrences.
It is enough to retain a component-equivalent first source at anchor
`firstShift - secondShift` and a component-equivalent second source at
anchor zero; the resulting finite representatives share `secondShift`. -/
theorem exists_commonShiftRepresentative_pair_at_relative_and_zero
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstTargetSource : DrawingPlanarSATClauseSource Variable)
    (secondTargetSource : DrawingPlanarSATClauseSource Variable)
    (firstTargetMember :
      firstTargetSource.RetainedComponentMember formula)
    (secondTargetMember :
      secondTargetSource.RetainedComponentMember formula)
    (firstTargetComponentEq :
      firstTargetSource.component =
        (first.routeWitness.metadata.source.periodTranslate
          formula
          (first.anchorReindexShift
            (Cell.sub firstShift secondShift))).component)
    (secondTargetComponentEq :
      secondTargetSource.component =
        (second.routeWitness.metadata.source.periodTranslate
          formula
          (second.anchorReindexShift (0, 0))).component)
    (firstTargetLocalClauseIndexEq :
      firstTargetSource.localClauseIndex =
        first.routeWitness.metadata.source.localClauseIndex)
    (secondTargetLocalClauseIndexEq :
      secondTargetSource.localClauseIndex =
        second.routeWitness.metadata.source.localClauseIndex) :
    Nonempty
      (FinalGaugedSegmentCommonShiftRepresentative
          formula firstIndexed firstShift secondShift ×
        FinalGaugedSegmentCommonShiftRepresentative
          formula secondIndexed secondShift secondShift) := by
  rcases first.exists_commonShiftRepresentative_at_anchor
      (Cell.sub firstShift secondShift)
      firstTargetSource firstTargetMember
      firstTargetComponentEq firstTargetLocalClauseIndexEq with
    ⟨firstRepresentative⟩
  rcases second.exists_commonShiftRepresentative_at_anchor
      (0, 0) secondTargetSource secondTargetMember
      secondTargetComponentEq secondTargetLocalClauseIndexEq with
    ⟨secondRepresentative⟩
  have common := anchorReindex_commonShift_pair
    (firstShift := firstShift) (secondShift := secondShift)
  rw [common.1] at firstRepresentative
  rw [common.2] at secondRepresentative
  exact ⟨firstRepresentative, secondRepresentative⟩

/-- A one-sided form is often more convenient for orbit closure: leave the
second occurrence at its existing finite representative, and reindex only
the first source to the relative external shift plus the second source
anchor. -/
theorem exists_commonShiftRepresentative_pair_reindex_first
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstTargetSource : DrawingPlanarSATClauseSource Variable)
    (firstTargetMember :
      firstTargetSource.RetainedComponentMember formula)
    (firstTargetComponentEq :
      firstTargetSource.component =
        (first.routeWitness.metadata.source.periodTranslate
          formula
          (first.anchorReindexShift
            (Cell.add (Cell.sub firstShift secondShift)
              second.sourceClauseAnchor))).component)
    (firstTargetLocalClauseIndexEq :
      firstTargetSource.localClauseIndex =
        first.routeWitness.metadata.source.localClauseIndex) :
    Nonempty
      (FinalGaugedSegmentCommonShiftRepresentative
          formula firstIndexed firstShift second.physicalShift ×
        FinalGaugedSegmentCommonShiftRepresentative
          formula secondIndexed secondShift second.physicalShift) := by
  rcases first.exists_commonShiftRepresentative_at_anchor
      (Cell.add (Cell.sub firstShift secondShift)
        second.sourceClauseAnchor)
      firstTargetSource firstTargetMember
      firstTargetComponentEq firstTargetLocalClauseIndexEq with
    ⟨firstRepresentative⟩
  have common :=
    anchorReindex_commonShift_keep_second
      (firstShift := firstShift)
      (secondShift := secondShift)
      (secondAnchor := second.sourceClauseAnchor)
  rw [common] at firstRepresentative
  rw [second.physicalShift_eq]
  exact ⟨firstRepresentative,
    second.toCommonShiftRepresentative⟩

/-- The one-sided reindexing bridge stated directly in the coordinates used
by contact bounds: translate the first finite source by the difference of
the two physical shifts and leave the second source unchanged. -/
theorem exists_commonShiftRepresentative_pair_reindex_first_by_physicalShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstTargetSource : DrawingPlanarSATClauseSource Variable)
    (firstTargetMember :
      firstTargetSource.RetainedComponentMember formula)
    (firstTargetComponentEq :
      firstTargetSource.component =
        (first.routeWitness.metadata.source.periodTranslate
          formula
          (Cell.sub first.physicalShift
            second.physicalShift)).component)
    (firstTargetLocalClauseIndexEq :
      firstTargetSource.localClauseIndex =
        first.routeWitness.metadata.source.localClauseIndex) :
    Nonempty
      (FinalGaugedSegmentCommonShiftRepresentative
          formula firstIndexed firstShift second.physicalShift ×
        FinalGaugedSegmentCommonShiftRepresentative
          formula secondIndexed secondShift second.physicalShift) := by
  apply exists_commonShiftRepresentative_pair_reindex_first
    first second firstTargetSource firstTargetMember
  · rw [first.anchorReindexShift_keep_second_eq second]
    exact firstTargetComponentEq
  · exact firstTargetLocalClauseIndexEq

end PeriodicOrthocrossing
end LeanTrominoes
