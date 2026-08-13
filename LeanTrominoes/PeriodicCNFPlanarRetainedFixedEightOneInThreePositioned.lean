/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplitRoutes
import LeanTrominoes.PeriodicEightOccurrenceSplitLocalDistinctness
import LeanTrominoes.PeriodicCNFPlanarOneInThreeNoUnitsPositioned
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements

/-!
# Retained fixed-eight exact-one pipeline

This module threads the final retained fixed-eight planar-SAT formula through
the positioned Figure 9 reduction, opaque variable wrapping, and unit-clause
elimination.  It records the semantic and finite-presentation promises needed
by the subsequent planar 3DM construction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Direct positioned Figure 9 image of the retained fixed-eight split. -/
def retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.formula
    (retainedDrawingEightOccurrenceSplitPositionedFormula source)

/-- Placement of the unwrapped retained Figure 9 variables. -/
def retainedFixedEightPeriodicPlanarOneInThreeRawPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.placement
    (retainedDrawingEightOccurrenceSplitPositionedFormula source)
    (retainedDrawingEightOccurrenceSplitPlacement source)

/-- Opaque positioned exact-one output of the retained fixed-eight split. -/
def retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
    source).rename WrappedPeriodicVariable.mk

/-- Placement transported through the opaque exact-one wrapper. -/
def retainedFixedEightPeriodicPlanarOneInThreePlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) where
  period :=
    (retainedFixedEightPeriodicPlanarOneInThreeRawPlacement source).period
  position := fun wrapped =>
    (retainedFixedEightPeriodicPlanarOneInThreeRawPlacement
      source).position wrapped.original

/-- Final positioned unit-free exact-one formula over retained fixed-eight
geometry. -/
def retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.formula
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)

/-- Placement of the final retained unit-free exact-one formula. -/
def retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.placement
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
    (retainedFixedEightPeriodicPlanarOneInThreePlacement source)

@[simp]
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      source).erase =
      PeriodicOneInThree.formula
        (retainedDrawingEightOccurrenceSplitPositionedFormula
          source).erase := by
  simp [retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula]

@[simp]
theorem retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source).erase =
      wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (retainedDrawingEightOccurrenceSplitPositionedFormula
            source).erase) := by
  rw [retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    PositionedPeriodicCNF.erase_rename,
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase]
  rfl

@[simp]
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).erase =
      PeriodicOneInThreeNoUnits.formula
        (wrapPeriodicPlanarSATFormula
          (PeriodicOneInThree.formula
            (retainedDrawingEightOccurrenceSplitPositionedFormula
              source).erase)) := by
  simp
    [retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula]

/-- The positioned retained fixed-eight source has width at most three. -/
theorem
    retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3) :
    (retainedDrawingEightOccurrenceSplitPositionedFormula
      source).erase.WidthAtMost 3 := by
  rw [retainedDrawingEightOccurrenceSplitPositionedFormula_erase]
  exact retainedDrawingEightOccurrenceSplitFormula_widthAtMostThree
    sourceWidth

/-- Collision-free retained angular ports make every split clause
atom-distinct. -/
theorem retainedDrawingEightOccurrenceSplitPositionedFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedDrawingEightOccurrenceSplitPositionedFormula
      source).AllAtomsNodup := by
  unfold retainedDrawingEightOccurrenceSplitPositionedFormula
  apply PeriodicEightOccurrenceSplitPositioned.formula_allAtomsNodup
  exact retainedDrawingAngularOccurrencePorts_collisionFree
    sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty

/-- Figure 9 itself introduces no repeated atom within a generated clause. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      source).AllAtomsNodup :=
  PeriodicOneInThreePositioned.formula_allAtomsNodup
    (retainedDrawingEightOccurrenceSplitPositionedFormula source)

/-- Opaque wrapping preserves retained Figure 9 atom distinctness. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source).AllAtomsNodup := by
  apply PositionedPeriodicCNF.allAtomsNodup_rename
    WrappedPeriodicVariable.mk
  · intro first second equal
    exact WrappedPeriodicVariable.mk.inj equal
  · exact
      retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_allAtomsNodup
        source

/-- The wrapped retained Figure 9 source retains width three. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
      source).erase.WidthAtMost 3 := by
  rw [retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase]
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact PeriodicOneInThree.formula_widthAtMostThree _

/-- Unit elimination preserves retained Figure 9 atom distinctness. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).AllAtomsNodup :=
  PeriodicOneInThreeNoUnitsPositioned.formula_allAtomsNodup
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
      source)

/-- Figure 9 preserves satisfiability over the retained fixed-eight source. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source).erase ↔
      (retainedDrawingEightOccurrenceSplitPositionedFormula
        source).erase.Satisfiable := by
  rw [
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase]
  exact
    (PeriodicOneInThree.satisfiable_iff
      (retainedDrawingEightOccurrenceSplitPositionedFormula source).erase
      (retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)).symm

/-- Every final retained exact-one clause has arity two or three. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase := by
  rw [
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase]
  apply PeriodicOneInThreeNoUnits.formula_arityTwoOrThree
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact PeriodicOneInThree.formula_widthAtMostThree _

/-- The positioned retained split inherits its semantic occurrence-three
bound. -/
theorem
    retainedDrawingEightOccurrenceSplitPositionedFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedDrawingEightOccurrenceSplitPositionedFormula
      source).erase.OccurrencesAtMost 3 := by
  rw [retainedDrawingEightOccurrenceSplitPositionedFormula_erase]
  exact retainedDrawingEightOccurrenceSplitFormula_occurrencesAtMostThree
    sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty

/-- The final retained exact-one output preserves the degree-three promise. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source).erase.OccurrencesAtMost 3 := by
  rw [
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase]
  have splitWidth :=
    retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
      source sourceWidth
  have splitOccurrences :=
    retainedDrawingEightOccurrenceSplitPositionedFormula_occurrencesAtMostThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let splitDecEq :
      DecidableEq
        (PeriodicPlanarThreeSATThreeVariable Variable) :=
    inferInstance
  have splitOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        (PeriodicPlanarThreeSATThreeVariable Variable)
        (@instBEqOfDecidableEq
          (PeriodicPlanarThreeSATThreeVariable Variable)
          splitDecEq)
        (by infer_instance) 3
        (retainedDrawingEightOccurrenceSplitPositionedFormula
          source).erase :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (retainedDrawingEightOccurrenceSplitPositionedFormula source).erase
      splitOccurrences
  have exactOneOccurrences :=
    @PeriodicOneInThree.formula_occurrencesAtMostThree
      (PeriodicPlanarThreeSATThreeVariable Variable)
      splitDecEq
      (retainedDrawingEightOccurrenceSplitPositionedFormula source).erase
      splitWidth splitOccurrences'
  let exactOneDecEq :
      DecidableEq
        (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
    inferInstance
  have exactOneOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)
        (@instBEqOfDecidableEq
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)
          exactOneDecEq)
        (by infer_instance) 3
        (PeriodicOneInThree.formula
          (retainedDrawingEightOccurrenceSplitPositionedFormula
            source).erase) :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (PeriodicOneInThree.formula
        (retainedDrawingEightOccurrenceSplitPositionedFormula source).erase)
      exactOneOccurrences
  have wrappedOccurrences :=
    @wrapPeriodicPlanarSATFormula_occurrencesAtMost
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)
      exactOneDecEq
      (PeriodicOneInThree.formula
        (retainedDrawingEightOccurrenceSplitPositionedFormula source).erase)
      3 exactOneOccurrences'
  let wrappedDecEq :
      DecidableEq
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
    inferInstance
  have wrappedOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))
        (@instBEqOfDecidableEq
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          wrappedDecEq)
        (by infer_instance) 3
        (wrapPeriodicPlanarSATFormula
          (PeriodicOneInThree.formula
            (retainedDrawingEightOccurrenceSplitPositionedFormula
              source).erase)) :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (retainedDrawingEightOccurrenceSplitPositionedFormula source).erase))
      wrappedOccurrences
  have generatedOccurrences :=
    @PeriodicOneInThreeNoUnits.formula_occurrencesAtMostThree
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      wrappedDecEq
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (retainedDrawingEightOccurrenceSplitPositionedFormula source).erase))
      wrappedOccurrences'
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (PeriodicOneInThreeNoUnits.formula
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (retainedDrawingEightOccurrenceSplitPositionedFormula
            source).erase)))
    generatedOccurrences

/-- End-to-end semantics of the retained fixed-eight exact-one pipeline. -/
theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).erase ↔
      source.Satisfiable := by
  calc
    PeriodicOneInThree.Satisfiable
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).erase ↔
      PeriodicOneInThree.Satisfiable
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).erase := by
            rw [
              retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase,
              retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase]
            exact PeriodicOneInThreeNoUnits.satisfiable_iff _
    _ ↔ PeriodicOneInThree.Satisfiable
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source).erase := by
            rw [
              retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase,
              retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase]
            exact
              wrapPeriodicPlanarSATFormula_oneInThree_satisfiable_iff _
    _ ↔
      (retainedDrawingEightOccurrenceSplitPositionedFormula
        source).erase.Satisfiable :=
      retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_satisfiable_iff
        source sourceWidth
    _ ↔
      (retainedDrawingEightOccurrenceSplitFormula source).Satisfiable := by
        rw [retainedDrawingEightOccurrenceSplitPositionedFormula_erase]
    _ ↔ source.Satisfiable :=
      retainedDrawingEightOccurrenceSplitFormula_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences

/-- All retained fixed-eight refinement stages have positive physical period. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    0 <
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source).period := by
  unfold
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
    retainedFixedEightPeriodicPlanarOneInThreePlacement
    retainedFixedEightPeriodicPlanarOneInThreeRawPlacement
  apply PeriodicOneInThreeNoUnitsPositioned.placement_period_pos
  change
    0 <
      (PeriodicOneInThreePositioned.placement
        (retainedDrawingEightOccurrenceSplitPositionedFormula source)
        (retainedDrawingEightOccurrenceSplitPlacement source)).period
  apply PeriodicOneInThreePositioned.placement_period_pos
  exact retainedDrawingEightOccurrenceSplitPlacement_period_pos source

end PeriodicOrthocrossing
end LeanTrominoes
