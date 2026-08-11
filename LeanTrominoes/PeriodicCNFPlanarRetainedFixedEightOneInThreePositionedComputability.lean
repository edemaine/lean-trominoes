import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightOneInThreePositioned
import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplitPositionedComputability
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedComputability

/-!
# Computability of the positioned retained Figure 9 pipeline

This module specializes the positioned Figure 9 and unit-elimination
compilers to the retained fixed-eight planar source.  It computes the exact
raw, wrapped, and unit-free positioned formulas together with every finite
period and variable-position query of their companion placements.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1600000

theorem retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula :
      PeriodicCNF Variable → _) := by
  unfold retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
  exact PeriodicOneInThreePositioned.formula_primrec.comp
    retainedDrawingEightOccurrenceSplitPositionedFormula_primrec

theorem retainedFixedEightPeriodicPlanarOneInThreeRawPlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedFixedEightPeriodicPlanarOneInThreeRawPlacement source).period := by
  unfold retainedFixedEightPeriodicPlanarOneInThreeRawPlacement
  exact PeriodicOneInThreePositioned.placement_period_primrec
    (source := retainedDrawingEightOccurrenceSplitPositionedFormula)
    (sourcePlacement := retainedDrawingEightOccurrenceSplitPlacement)
    retainedDrawingEightOccurrenceSplitPlacement_period_primrec

theorem retainedFixedEightPeriodicPlanarOneInThreeRawPlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        PeriodicPlanarOneInThreeThreeRawVariable Variable =>
      (retainedFixedEightPeriodicPlanarOneInThreeRawPlacement
        input.1).position input.2 := by
  unfold retainedFixedEightPeriodicPlanarOneInThreeRawPlacement
  exact PeriodicOneInThreePositioned.placement_position_primrec
    (source := retainedDrawingEightOccurrenceSplitPositionedFormula)
    (sourcePlacement := retainedDrawingEightOccurrenceSplitPlacement)
    retainedDrawingEightOccurrenceSplitPositionedFormula_primrec
    retainedDrawingEightOccurrenceSplitPlacement_period_primrec
    retainedDrawingEightOccurrenceSplitPlacement_position_primrec

theorem retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula :
      PeriodicCNF Variable → _) := by
  unfold retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
  exact PositionedPeriodicCNF.rename_primrec
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
    (fun _ => WrappedPeriodicVariable.mk)
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula_primrec
    (WrappedPeriodicVariable.mk_primrec.comp Primrec.snd)

theorem retainedFixedEightPeriodicPlanarOneInThreePlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedFixedEightPeriodicPlanarOneInThreePlacement source).period := by
  unfold retainedFixedEightPeriodicPlanarOneInThreePlacement
  exact retainedFixedEightPeriodicPlanarOneInThreeRawPlacement_period_primrec

theorem retainedFixedEightPeriodicPlanarOneInThreePlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable) =>
      (retainedFixedEightPeriodicPlanarOneInThreePlacement
        input.1).position input.2 := by
  have computed : Primrec fun input : PeriodicCNF Variable ×
      WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable) =>
      (retainedFixedEightPeriodicPlanarOneInThreeRawPlacement
        input.1).position input.2.original :=
    WrappedPeriodicVariable.position_primrec
      (Input := PeriodicCNF Variable)
      (Original := PeriodicPlanarOneInThreeThreeRawVariable Variable)
      (position := fun source atom =>
        (retainedFixedEightPeriodicPlanarOneInThreeRawPlacement
          source).position atom)
      retainedFixedEightPeriodicPlanarOneInThreeRawPlacement_position_primrec
  exact computed.of_eq fun _ => rfl

theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula :
        PeriodicCNF Variable → _) := by
  unfold retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
  exact PeriodicOneInThreeNoUnitsPositioned.formula_primrec.comp
    retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_primrec

theorem
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula :
        PeriodicCNF Variable → _) :=
  retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_primrec.to_comp

theorem retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source).period := by
  unfold retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
  exact PeriodicOneInThreeNoUnitsPositioned.placement_period_primrec
    (source := retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula)
    (sourcePlacement := retainedFixedEightPeriodicPlanarOneInThreePlacement)
    retainedFixedEightPeriodicPlanarOneInThreePlacement_period_primrec

theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)) =>
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        input.1).position input.2 := by
  unfold retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
  exact PeriodicOneInThreeNoUnitsPositioned.placement_position_primrec
    (source := retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula)
    (sourcePlacement := retainedFixedEightPeriodicPlanarOneInThreePlacement)
    retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_primrec
    retainedFixedEightPeriodicPlanarOneInThreePlacement_period_primrec
    retainedFixedEightPeriodicPlanarOneInThreePlacement_position_primrec

end PeriodicOrthocrossing
end LeanTrominoes
