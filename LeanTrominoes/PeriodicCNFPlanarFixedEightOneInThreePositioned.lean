import LeanTrominoes.PeriodicEightOccurrenceSplitCanonicalAngularRoutes
import LeanTrominoes.PeriodicEightOccurrenceSplitLocalDistinctness
import LeanTrominoes.PeriodicCNFPlanarOneInThreeNoUnitsPositioned
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements

/-!
# Positioned exact-one pipeline over the fixed-eight occurrence split

The semantic angular pipeline originally used the variable-size occurrence
cycle, while the certified Figure 7 geometry uses a uniform eight-port ring.
This module threads the positioned fixed-eight formula through Figure 9,
opaque wrapping, and unit elimination.  Thus the semantic and geometric
hardness pipelines now have one common intermediate presentation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Direct positioned Figure 9 image of the fixed-eight occurrence split. -/
def drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.formula
    (drawingAngularEightOccurrenceSplitPositionedFormula input)

/-- Placement of the unwrapped fixed-eight Figure 9 variables. -/
def drawingFixedEightPeriodicPlanarOneInThreeRawPlacement
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.placement
    (drawingAngularEightOccurrenceSplitPositionedFormula input)
    (drawingAngularEightOccurrenceSplitPlacement input)

/-- Opaque positioned exact-one output of the fixed-eight split. -/
def drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
    input).rename WrappedPeriodicVariable.mk

/-- Placement transported through the opaque exact-one wrapper. -/
def drawingFixedEightPeriodicPlanarOneInThreePlacement
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) where
  period :=
    (drawingFixedEightPeriodicPlanarOneInThreeRawPlacement input).period
  position := fun wrapped =>
    (drawingFixedEightPeriodicPlanarOneInThreeRawPlacement
      input).position wrapped.original

/-- Final positioned unit-free exact-one formula over fixed-eight geometry. -/
def drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.formula
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)

/-- Placement of the final fixed-eight unit-free exact-one formula. -/
def drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.placement
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
    (drawingFixedEightPeriodicPlanarOneInThreePlacement input)

@[simp]
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      input).erase =
      PeriodicOneInThree.formula
        (drawingAngularEightOccurrenceSplitPositionedFormula
          input).erase := by
  simp [drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula]

@[simp]
theorem drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
      input).erase =
      wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (drawingAngularEightOccurrenceSplitPositionedFormula
            input).erase) := by
  rw [drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    PositionedPeriodicCNF.erase_rename,
    drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase]
  rfl

@[simp]
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      input).erase =
      PeriodicOneInThreeNoUnits.formula
        (wrapPeriodicPlanarSATFormula
          (PeriodicOneInThree.formula
            (drawingAngularEightOccurrenceSplitPositionedFormula
              input).erase)) := by
  simp
    [drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula]

/-- The positioned fixed-eight occurrence split retains width three. -/
theorem drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceWidth : input.WidthAtMost 3) :
    (drawingAngularEightOccurrenceSplitPositionedFormula
      input).erase.WidthAtMost 3 := by
  rw [drawingAngularEightOccurrenceSplitPositionedFormula_erase]
  apply PeriodicEightOccurrenceSplit.formula_widthAtMostThree
  rw [
    deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  exact
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_widthAtMost
      input 3
      (drawingPeriodicPlanarSATFormula_widthAtMostThree
        input sourceWidth)

/-- Collision-free angular ports make every clause of the positioned
fixed-eight split atom-distinct. -/
theorem drawingAngularEightOccurrenceSplitPositionedFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    (drawingAngularEightOccurrenceSplitPositionedFormula
      input).AllAtomsNodup := by
  unfold drawingAngularEightOccurrenceSplitPositionedFormula
  apply PeriodicEightOccurrenceSplitPositioned.formula_allAtomsNodup
  apply
    PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder_collisionFree
  apply PeriodicEightOccurrenceSplit.fitsEightSlots_of_occurrencesAtMostEight
  rw [
    deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  exact
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight_of_source
      sourceLocal sourceWidth sourceOccurrences

/-- The raw fixed-eight Figure 9 output has distinct atoms in every
generated clause. -/
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      input).AllAtomsNodup :=
  PeriodicOneInThreePositioned.formula_allAtomsNodup
    (drawingAngularEightOccurrenceSplitPositionedFormula input)

/-- Opaque wrapping preserves fixed-eight Figure 9 atom distinctness. -/
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
      input).AllAtomsNodup := by
  apply PositionedPeriodicCNF.allAtomsNodup_rename
    WrappedPeriodicVariable.mk
  · intro first second equal
    exact WrappedPeriodicVariable.mk.inj equal
  · exact
      drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_allAtomsNodup
        input

/-- The wrapped fixed-eight Figure 9 source retains width three. -/
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
      input).erase.WidthAtMost 3 := by
  rw [drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase]
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact PeriodicOneInThree.formula_widthAtMostThree _

/-- Unit elimination preserves fixed-eight Figure 9 atom distinctness. -/
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      input).AllAtomsNodup :=
  PeriodicOneInThreeNoUnitsPositioned.formula_allAtomsNodup
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
      input)

/-- The positioned fixed-eight split has the semantics of the routed planar
SAT formula. -/
theorem
    drawingAngularEightOccurrenceSplitPositionedFormula_satisfiable_iff_planarSAT
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    (drawingAngularEightOccurrenceSplitPositionedFormula
      input).erase.Satisfiable ↔
      (drawingPeriodicPlanarSATFormula input).Satisfiable := by
  rw [drawingAngularEightOccurrenceSplitPositionedFormula_erase]
  exact
    (PeriodicEightOccurrenceSplit.satisfiable_iff
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        input).erase
      (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
        (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          input).erase
        (drawingOrderedAngularOccurrenceOrder input))).trans
      (by
        rw [
          deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
        exact
          deduplicatedWrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
            input)

/-- Figure 9 preserves satisfiability over the positioned fixed-eight
source. -/
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceWidth : input.WidthAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          input).erase ↔
      (drawingAngularEightOccurrenceSplitPositionedFormula
        input).erase.Satisfiable := by
  rw [
    drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase]
  exact
    (PeriodicOneInThree.satisfiable_iff
      (drawingAngularEightOccurrenceSplitPositionedFormula input).erase
      (drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
        input sourceWidth)).symm

/-- Every final fixed-eight exact-one clause has arity two or three. -/
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        input).erase := by
  rw [
    drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase]
  apply PeriodicOneInThreeNoUnits.formula_arityTwoOrThree
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact PeriodicOneInThree.formula_widthAtMostThree _

/-- The fixed-eight source has degree at most three when the input satisfies
the local width-three occurrence-three promises. -/
theorem
    drawingAngularEightOccurrenceSplitPositionedFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    (drawingAngularEightOccurrenceSplitPositionedFormula
      input).erase.OccurrencesAtMost 3 := by
  rw [drawingAngularEightOccurrenceSplitPositionedFormula_erase]
  apply PeriodicEightOccurrenceSplit.formula_occurrencesAtMostThree
  apply
    PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder_collisionFree
  apply PeriodicEightOccurrenceSplit.fitsEightSlots_of_occurrencesAtMostEight
  rw [
    deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  exact
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight_of_source
      sourceLocal sourceWidth sourceOccurrences

/-- The final fixed-eight exact-one output retains the degree-three promise
required by planar 3DM variable sites. -/
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      input).erase.OccurrencesAtMost 3 := by
  rw [
    drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase]
  have splitWidth :=
    drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
      input sourceWidth
  have splitOccurrences :=
    drawingAngularEightOccurrenceSplitPositionedFormula_occurrencesAtMostThree
      input sourceLocal sourceWidth sourceOccurrences
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
        (drawingAngularEightOccurrenceSplitPositionedFormula
          input).erase :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (drawingAngularEightOccurrenceSplitPositionedFormula input).erase
      splitOccurrences
  have exactOneOccurrences :=
    @PeriodicOneInThree.formula_occurrencesAtMostThree
      (PeriodicPlanarThreeSATThreeVariable Variable)
      splitDecEq
      (drawingAngularEightOccurrenceSplitPositionedFormula input).erase
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
          (drawingAngularEightOccurrenceSplitPositionedFormula
            input).erase) :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (PeriodicOneInThree.formula
        (drawingAngularEightOccurrenceSplitPositionedFormula input).erase)
      exactOneOccurrences
  have wrappedOccurrences :=
    @wrapPeriodicPlanarSATFormula_occurrencesAtMost
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)
      exactOneDecEq
      (PeriodicOneInThree.formula
        (drawingAngularEightOccurrenceSplitPositionedFormula input).erase)
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
            (drawingAngularEightOccurrenceSplitPositionedFormula
              input).erase)) :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (drawingAngularEightOccurrenceSplitPositionedFormula input).erase))
      wrappedOccurrences
  have generatedOccurrences :=
    @PeriodicOneInThreeNoUnits.formula_occurrencesAtMostThree
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      wrappedDecEq
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (drawingAngularEightOccurrenceSplitPositionedFormula input).erase))
      wrappedOccurrences'
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (PeriodicOneInThreeNoUnits.formula
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (drawingAngularEightOccurrenceSplitPositionedFormula input).erase)))
    generatedOccurrences

/-- End-to-end semantics of the fixed-eight, unit-free exact-one pipeline. -/
theorem
    drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          input).erase ↔
      input.Satisfiable := by
  calc
    PeriodicOneInThree.Satisfiable
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          input).erase ↔
      PeriodicOneInThree.Satisfiable
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
          input).erase := by
            rw [
              drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase,
              drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase]
            exact PeriodicOneInThreeNoUnits.satisfiable_iff _
    _ ↔ PeriodicOneInThree.Satisfiable
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          input).erase := by
            rw [
              drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_erase,
              drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_erase]
            exact
              wrapPeriodicPlanarSATFormula_oneInThree_satisfiable_iff _
    _ ↔
      (drawingAngularEightOccurrenceSplitPositionedFormula
        input).erase.Satisfiable :=
      drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_satisfiable_iff
        input sourceWidth
    _ ↔ (drawingPeriodicPlanarSATFormula input).Satisfiable :=
      drawingAngularEightOccurrenceSplitPositionedFormula_satisfiable_iff_planarSAT
        input
    _ ↔ input.Satisfiable :=
      drawingPeriodicPlanarSATFormula_satisfiable_iff
        input sourceOccurrences

/-- All fixed-eight refinement stages retain a positive physical period. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable) :
    0 <
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        input).period := by
  unfold
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
    drawingFixedEightPeriodicPlanarOneInThreePlacement
    drawingFixedEightPeriodicPlanarOneInThreeRawPlacement
  apply PeriodicOneInThreeNoUnitsPositioned.placement_period_pos
  change
    0 <
      (PeriodicOneInThreePositioned.placement
        (drawingAngularEightOccurrenceSplitPositionedFormula input)
        (drawingAngularEightOccurrenceSplitPlacement input)).period
  apply PeriodicOneInThreePositioned.placement_period_pos
  exact PeriodicEightOccurrenceSplitPositioned.placement_period_pos
    (wrappedDrawingPeriodicPlanarSATPlacement input)
    (drawingPeriodicPlanarSATPlacement_period_pos input)

end PeriodicOrthocrossing
end LeanTrominoes
