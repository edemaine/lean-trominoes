import LeanTrominoes.PeriodicThreeSATThreeOrderedPositioned
import LeanTrominoes.PeriodicCNFPlanarOneInThreeNoUnitsPositioned

/-!
# Geometry-ordered positioned planar exact-one pipeline

This file threads a chosen rotation order through the full positioned
post-planarization pipeline: occurrence splitting, Figure 9 exact-one
replacement, opaque wrapping, and unit-clause elimination.  The resulting
unit-free exact-one formula has the same variable type expected by the
planar 3DM construction, but its implication cycles may follow the actual
geometric order around every source variable.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Keep equality of wrapped routed variables opaque while elaborating the
geometry-ordered pipeline.  The underlying decision procedure is unchanged;
this prevents occurrence certificates from unfolding the complete routed
variable type at every use. -/
opaque drawingOrderedWrappedPeriodicPlanarSATVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq (WrappedPeriodicPlanarSATVariable Variable) := by
  infer_instance

instance drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq (WrappedPeriodicPlanarSATVariable Variable) :=
  drawingOrderedWrappedPeriodicPlanarSATVariableDecidableEq

/-- Opaque equality procedures for the three nested output layers keep the
generic occurrence-composition theorem below within elaborator depth. -/
opaque drawingOrderedThreeOccurrenceVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) := by
  infer_instance

instance drawingOrderedThreeOccurrenceVariableInstDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  drawingOrderedThreeOccurrenceVariableDecidableEq

opaque drawingOrderedOneInThreeVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeVariable
        (ThreeOccurrenceVariable Variable)) := by
  infer_instance

instance drawingOrderedOneInThreeVariableInstDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeVariable
        (ThreeOccurrenceVariable Variable)) :=
  drawingOrderedOneInThreeVariableDecidableEq

opaque drawingOrderedWrappedOneInThreeVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (WrappedPeriodicVariable
        (OneInThreeVariable
          (ThreeOccurrenceVariable Variable))) := by
  infer_instance

instance drawingOrderedWrappedOneInThreeVariableInstDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (WrappedPeriodicVariable
        (OneInThreeVariable
          (ThreeOccurrenceVariable Variable))) :=
  drawingOrderedWrappedOneInThreeVariableDecidableEq

opaque drawingOrderedOneInThreeNoUnitVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (OneInThreeVariable
            (ThreeOccurrenceVariable Variable)))) := by
  infer_instance

instance drawingOrderedOneInThreeNoUnitVariableInstDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (OneInThreeVariable
            (ThreeOccurrenceVariable Variable)))) :=
  drawingOrderedOneInThreeNoUnitVariableDecidableEq

/-- A lawful order of the routed planar SAT occurrences around every
wrapped source variable. -/
abbrev DrawingOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :=
  PeriodicThreeSATThree.OccurrenceOrder
    (wrappedDrawingPositionedPeriodicPlanarSATFormula formula).erase

/-- Positioned routed formula after geometry-ordered occurrence splitting. -/
def drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PositionedPeriodicCNF
      (PeriodicPlanarThreeSATThreeVariable Variable) :=
  PeriodicThreeSATThreePositioned.orderedFormula
    (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
    (fun wrapped =>
      drawingPeriodicPlanarSATVariablePosition
        formula wrapped.original)
    order

/-- Companion placement for the geometry-ordered occurrence split. -/
def drawingOrderedPeriodicPlanarThreeSATThreePlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PeriodicVariablePlacement
      (PeriodicPlanarThreeSATThreeVariable Variable) :=
  PeriodicThreeSATThreePositioned.orderedPlacement
    (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)
    order

/-- Direct positioned Figure 9 image of the geometry-ordered split. -/
def drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PositionedPeriodicCNF
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.formula
    (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
      formula order)

/-- Placement of the unwrapped Figure 9 variables. -/
def drawingOrderedPeriodicPlanarOneInThreeThreeRawPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PeriodicVariablePlacement
      (PeriodicPlanarOneInThreeThreeRawVariable Variable) :=
  PeriodicOneInThreePositioned.placement
    (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
      formula order)
    (drawingOrderedPeriodicPlanarThreeSATThreePlacement
      formula order)

/-- Opaque positioned exact-one output of the geometry-ordered split. -/
def drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PositionedPeriodicCNF
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula
    formula order).rename WrappedPeriodicVariable.mk

/-- Placement transported through the opaque exact-one wrapper. -/
def drawingOrderedPeriodicPlanarOneInThreeThreePlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PeriodicVariablePlacement
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) where
  period :=
    (drawingOrderedPeriodicPlanarOneInThreeThreeRawPlacement
      formula order).period
  position := fun wrapped =>
    (drawingOrderedPeriodicPlanarOneInThreeThreeRawPlacement
      formula order).position wrapped.original

/-- Final positioned unit-free exact-one formula using geometric rotation
orders. -/
def drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.formula
    (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula
      formula order)

/-- Companion placement of the final unit-free exact-one formula. -/
def drawingOrderedPeriodicPlanarOneInThreeNoUnitsPlacement
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PeriodicVariablePlacement
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))) :=
  PeriodicOneInThreeNoUnitsPositioned.placement
    (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula
      formula order)
    (drawingOrderedPeriodicPlanarOneInThreeThreePlacement
      formula order)

@[simp]
theorem drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
      formula order).erase =
      PeriodicThreeSATThree.orderedFormula
        (wrappedDrawingPositionedPeriodicPlanarSATFormula formula).erase
        order := by
  simp [drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula]

@[simp]
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula
      formula order).erase =
      PeriodicOneInThree.formula
        (PeriodicThreeSATThree.orderedFormula
          (wrappedDrawingPositionedPeriodicPlanarSATFormula formula).erase
          order) := by
  simp [drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula]

@[simp]
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula
      formula order).erase =
      wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (PeriodicThreeSATThree.orderedFormula
            (wrappedDrawingPositionedPeriodicPlanarSATFormula formula).erase
            order)) := by
  rw [drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula,
    PositionedPeriodicCNF.erase_rename,
    drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula_erase]
  rfl

@[simp]
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    (drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      formula order).erase =
      PeriodicOneInThreeNoUnits.formula
        (wrapPeriodicPlanarSATFormula
          (PeriodicOneInThree.formula
            (PeriodicThreeSATThree.orderedFormula
              (wrappedDrawingPositionedPeriodicPlanarSATFormula formula).erase
              order))) := by
  simp [drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula]

/-- Geometry-ordered occurrence splitting retains width three. -/
theorem
    drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula)
    (sourceWidth : formula.WidthAtMost 3) :
    (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
      formula order).erase.WidthAtMost 3 := by
  rw [
    drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula_erase]
  apply PeriodicThreeSATThree.orderedFormula_widthAtMostThree order
  rw [wrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact drawingPeriodicPlanarSATFormula_widthAtMostThree
    formula sourceWidth

/-- The occurrence-three bound survives the ordered split, Figure 9,
opaque wrapping, and unit elimination for any source type.  Stating the
composition generically keeps later geometric specializations from
normalizing their deeply nested variable types. -/
theorem orderedOneInThreeNoUnits_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : PeriodicThreeSATThree.OccurrenceOrder source)
    (sourceWidth : source.WidthAtMost 3) :
    (PeriodicOneInThreeNoUnits.formula
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (PeriodicThreeSATThree.orderedFormula
            source order)))).OccurrencesAtMost 3 := by
  have splitWidth :
      (PeriodicThreeSATThree.orderedFormula
        source order).WidthAtMost 3 :=
    PeriodicThreeSATThree.orderedFormula_widthAtMostThree
      order sourceWidth
  have splitOccurrences :
      (PeriodicThreeSATThree.orderedFormula
        source order).OccurrencesAtMost 3 :=
    PeriodicThreeSATThree.orderedFormula_occurrencesAtMostThree
      source order
  let splitDecEq :
      DecidableEq (ThreeOccurrenceVariable Variable) :=
    inferInstance
  have splitOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        (ThreeOccurrenceVariable Variable)
        (@instBEqOfDecidableEq
          (ThreeOccurrenceVariable Variable) splitDecEq)
        (by infer_instance) 3
        (PeriodicThreeSATThree.orderedFormula source order) :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (PeriodicThreeSATThree.orderedFormula source order)
      splitOccurrences
  have exactOneOccurrences :=
    @PeriodicOneInThree.formula_occurrencesAtMostThree
      (ThreeOccurrenceVariable Variable) splitDecEq
      (PeriodicThreeSATThree.orderedFormula source order)
      splitWidth splitOccurrences'
  let exactOneDecEq :
      DecidableEq
        (OneInThreeVariable
          (ThreeOccurrenceVariable Variable)) :=
    inferInstance
  have exactOneOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        (OneInThreeVariable
          (ThreeOccurrenceVariable Variable))
        (@instBEqOfDecidableEq
          (OneInThreeVariable
            (ThreeOccurrenceVariable Variable))
          exactOneDecEq)
        (by infer_instance) 3
        (PeriodicOneInThree.formula
          (PeriodicThreeSATThree.orderedFormula source order)) :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (PeriodicOneInThree.formula
        (PeriodicThreeSATThree.orderedFormula source order))
      exactOneOccurrences
  have wrappedOccurrences :=
    @wrapPeriodicPlanarSATFormula_occurrencesAtMost
      (OneInThreeVariable
        (ThreeOccurrenceVariable Variable))
      exactOneDecEq
      (PeriodicOneInThree.formula
        (PeriodicThreeSATThree.orderedFormula source order))
      3 exactOneOccurrences'
  let wrappedDecEq :
      DecidableEq
        (WrappedPeriodicVariable
          (OneInThreeVariable
            (ThreeOccurrenceVariable Variable))) :=
    inferInstance
  have wrappedOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        (WrappedPeriodicVariable
          (OneInThreeVariable
            (ThreeOccurrenceVariable Variable)))
        (@instBEqOfDecidableEq
          (WrappedPeriodicVariable
            (OneInThreeVariable
              (ThreeOccurrenceVariable Variable)))
          wrappedDecEq)
        (by infer_instance) 3
        (wrapPeriodicPlanarSATFormula
          (PeriodicOneInThree.formula
            (PeriodicThreeSATThree.orderedFormula source order))) :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (PeriodicThreeSATThree.orderedFormula source order)))
      wrappedOccurrences
  have generatedOccurrences :=
    @PeriodicOneInThreeNoUnits.formula_occurrencesAtMostThree
      (WrappedPeriodicVariable
        (OneInThreeVariable
          (ThreeOccurrenceVariable Variable)))
      wrappedDecEq
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (PeriodicThreeSATThree.orderedFormula source order)))
      wrappedOccurrences'
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (PeriodicOneInThreeNoUnits.formula
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (PeriodicThreeSATThree.orderedFormula source order))))
    generatedOccurrences

/-- The final ordered exact-one output retains the occurrence-three
restriction required by the planar 3DM variable sites. -/
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula)
    (sourceWidth : formula.WidthAtMost 3) :
    (drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      formula order).erase.OccurrencesAtMost 3 := by
  rw [
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase]
  have sourceWidth' :
      (wrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.WidthAtMost 3 := by
    rw [wrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
    apply wrapPeriodicPlanarSATFormula_widthAtMost
    exact drawingPeriodicPlanarSATFormula_widthAtMostThree
      formula sourceWidth
  have generatedOccurrences :=
    @orderedOneInThreeNoUnits_occurrencesAtMostThree
      (WrappedPeriodicPlanarSATVariable Variable)
      drawingOrderedWrappedPeriodicPlanarSATVariableDecidableEq
      (wrappedDrawingPositionedPeriodicPlanarSATFormula formula).erase
      order sourceWidth'
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (PeriodicOneInThreeNoUnits.formula
      (wrapPeriodicPlanarSATFormula
        (PeriodicOneInThree.formula
          (PeriodicThreeSATThree.orderedFormula
            (wrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).erase
            order))))
    generatedOccurrences

/-- Every final ordered exact-one clause has arity two or three, as required
by the clause sites of the planar 3DM replacement. -/
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        formula order).erase := by
  rw [
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase]
  apply PeriodicOneInThreeNoUnits.formula_arityTwoOrThree
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact PeriodicOneInThree.formula_widthAtMostThree _

/-- The geometry-ordered split is semantically equivalent to the routed
planar SAT formula. -/
theorem
    drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula_satisfiable_iff_planarSAT
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula) :
    (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
        formula order).erase.Satisfiable ↔
      (drawingPeriodicPlanarSATFormula formula).Satisfiable := by
  rw [
    drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula_erase]
  exact
    (PeriodicThreeSATThree.orderedSatisfiable_iff
      (wrappedDrawingPositionedPeriodicPlanarSATFormula formula).erase
      order).symm.trans
      (by
        rw [wrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
        exact
          wrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
            formula)

/-- Figure 9 preserves satisfiability for the geometry-ordered positioned
split.  Keeping the positioned source visible avoids expanding its nested
semantic variable type during later composition. -/
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula)
    (sourceWidth : formula.WidthAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula
          formula order).erase ↔
      (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
        formula order).erase.Satisfiable := by
  unfold
    drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula
  rw [PeriodicOneInThreePositioned.erase_formula]
  exact
    (@PeriodicOneInThree.satisfiable_iff
      (PeriodicPlanarThreeSATThreeVariable Variable)
      (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
        formula order).erase
      (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula_widthAtMostThree
        formula order sourceWidth)).symm

/-- End-to-end semantics of the geometry-ordered, unit-free exact-one
pipeline. -/
theorem
    drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (order : DrawingOccurrenceOrder formula)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          formula order).erase ↔
      formula.Satisfiable := by
  calc
    PeriodicOneInThree.Satisfiable
        (drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          formula order).erase ↔
      PeriodicOneInThree.Satisfiable
        (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula
          formula order).erase := by
            rw [
              drawingOrderedPositionedPeriodicPlanarOneInThreeNoUnitsFormula_erase,
              drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula_erase]
            exact PeriodicOneInThreeNoUnits.satisfiable_iff _
    _ ↔ PeriodicOneInThree.Satisfiable
        (drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula
          formula order).erase := by
            rw [
              drawingOrderedPositionedPeriodicPlanarOneInThreeThreeFormula_erase,
              drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula_erase]
            exact
              wrapPeriodicPlanarSATFormula_oneInThree_satisfiable_iff _
    _ ↔
      (drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula
        formula order).erase.Satisfiable := by
          exact
            drawingOrderedPositionedPeriodicPlanarOneInThreeThreeRawFormula_satisfiable_iff
              formula order sourceWidth
    _ ↔ (drawingPeriodicPlanarSATFormula formula).Satisfiable :=
      drawingOrderedPositionedPeriodicPlanarThreeSATThreeFormula_satisfiable_iff_planarSAT
        formula order
    _ ↔ formula.Satisfiable :=
      drawingPeriodicPlanarSATFormula_satisfiable_iff
        formula sourceOccurrences

end PeriodicOrthocrossing
end LeanTrominoes
