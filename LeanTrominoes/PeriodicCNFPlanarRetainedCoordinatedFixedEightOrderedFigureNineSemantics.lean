/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineCompleteRouteSeparation
import LeanTrominoes.PeriodicOneInThreeNoUnitsOccurrences

/-!
# Semantics of the ribbon-ready ordered Figure 9 endpoint

The clockwise reordered retained source is passed directly through Figure 9
and unit elimination.  This module reconnects that positioned construction to
the already verified logical reductions and exposes its semantic promises
alongside the completed ribbon-ready drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1000000

/-- Variable type of the ordered retained unit-free exact-one endpoint. -/
abbrev RetainedOrderedFixedEightOneInThreeVariable
    (Variable : Type*) :=
  OneInThreeNoUnitVariable
    (PeriodicPlanarOneInThreeThreeRawVariable Variable)

/-- Opaque equality for the twice-replaced endpoint keeps the constructive
decision procedure without repeatedly unfolding its nested clause scopes. -/
opaque retainedOrderedFixedEightOneInThreeVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq (RetainedOrderedFixedEightOneInThreeVariable Variable) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

instance retainedOrderedFixedEightOneInThreeVariableInstDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq (RetainedOrderedFixedEightOneInThreeVariable Variable) :=
  retainedOrderedFixedEightOneInThreeVariableDecidableEq

/-- Named Boolean equality used by the endpoint occurrence certificate. -/
@[reducible] def retainedOrderedFixedEightOneInThreeVariableBEq
    {Variable : Type*} [DecidableEq Variable] :
    BEq (RetainedOrderedFixedEightOneInThreeVariable Variable) :=
  @instBEqOfDecidableEq
    (RetainedOrderedFixedEightOneInThreeVariable Variable)
    retainedOrderedFixedEightOneInThreeVariableDecidableEq

/-- Lawfulness of the named endpoint Boolean equality. -/
opaque retainedOrderedFixedEightOneInThreeVariableLawfulBEq
    {Variable : Type*} [DecidableEq Variable] :
    @LawfulBEq
      (RetainedOrderedFixedEightOneInThreeVariable Variable)
      retainedOrderedFixedEightOneInThreeVariableBEq := by
  unfold retainedOrderedFixedEightOneInThreeVariableBEq
  infer_instance

/-- Erased logical endpoint, named opaquely to keep the deeply nested output
variable type out of downstream typeclass normalization. -/
def retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF (RetainedOrderedFixedEightOneInThreeVariable Variable) :=
  (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
    source).erase

/-- Named occurrence-three promise for the erased endpoint.  This
proposition-level interface prevents clients from repeatedly elaborating the
two nested clause-scoped variable layers. -/
def RetainedOrderedFixedEightOccurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : Prop :=
  @PeriodicCNF.OccurrencesAtMost
    (RetainedOrderedFixedEightOneInThreeVariable Variable)
    retainedOrderedFixedEightOneInThreeVariableBEq
    retainedOrderedFixedEightOneInThreeVariableLawfulBEq 3
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFormula source)

@[simp]
theorem retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFormula_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFormula source =
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).erase := by
  rfl

/-- Erasing the final ordered positioned formula recovers the two verified
logical exact-one transformations applied to the clearance source. -/
@[simp]
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source).erase =
      PeriodicOneInThreeNoUnits.formula
        (PeriodicOneInThree.formula
          (retainedFigureNineClearancePositionedFormula source).erase) := by
  simp [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula]

/-- The ordered unit-free exact-one endpoint has only binary or ternary
clauses. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_arityTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).erase := by
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
  exact
    PeriodicOneInThreeNoUnits.formula_arityTwoOrThree
      (PeriodicOneInThree.formula
        (retainedFigureNineClearancePositionedFormula source).erase)
      (PeriodicOneInThree.formula_widthAtMostThree _)

/-- Binary-or-ternary arity supplies the final width-three promise. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source).erase.WidthAtMost 3 := by
  intro clause clauseMember
  rcases
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_arityTwoOrThree
        source clause clauseMember with arity | arity
  · exact arity.le.trans (by decide)
  · exact arity.le

/-- The occurrence-three theorem for Figure 9 followed by unit elimination,
stated over an arbitrary source type so geometric specializations need not
normalize their routed variable representation during the proof. -/
theorem oneInThreeThenNoUnits_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3) :
    (PeriodicOneInThreeNoUnits.formula
      (PeriodicOneInThree.formula source)).OccurrencesAtMost 3 := by
  have figureNineOccurrences :
      (PeriodicOneInThree.formula source).OccurrencesAtMost 3 :=
    PeriodicOneInThree.formula_occurrencesAtMostThree
      source sourceWidth sourceOccurrences
  let figureNineDecEq :
      DecidableEq (OneInThreeVariable Variable) :=
    inferInstance
  have figureNineOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        (OneInThreeVariable Variable)
        (@instBEqOfDecidableEq
          (OneInThreeVariable Variable) figureNineDecEq)
        (by infer_instance) 3
        (PeriodicOneInThree.formula source) :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (PeriodicOneInThree.formula source) figureNineOccurrences
  have generatedOccurrences :=
    @PeriodicOneInThreeNoUnits.formula_occurrencesAtMostThree
      (OneInThreeVariable Variable) figureNineDecEq
      (PeriodicOneInThree.formula source) figureNineOccurrences'
  exact
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (PeriodicOneInThreeNoUnits.formula
        (PeriodicOneInThree.formula source))
      generatedOccurrences

/-- Both exact-one transformations preserve the occurrence-three promise of
the reordered retained source. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_occurrencesAtMostThreeFor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    RetainedOrderedFixedEightOccurrencesAtMostThree source := by
  unfold RetainedOrderedFixedEightOccurrencesAtMostThree
  rw [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFormula_eq,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
  have clearanceWidth :
      (retainedFigureNineClearancePositionedFormula
        source).erase.WidthAtMost 3 :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  have clearanceOccurrences :
      (retainedFigureNineClearancePositionedFormula
        source).erase.OccurrencesAtMost 3 :=
    retainedFigureNineClearancePositionedFormula_occurrencesAtMostThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let clearanceDecEq :
      DecidableEq (PeriodicPlanarThreeSATThreeVariable Variable) :=
    inferInstance
  have clearanceOccurrences' :
      @PeriodicCNF.OccurrencesAtMost
        (PeriodicPlanarThreeSATThreeVariable Variable)
        (@instBEqOfDecidableEq
          (PeriodicPlanarThreeSATThreeVariable Variable)
          clearanceDecEq)
        (by infer_instance) 3
        (retainedFigureNineClearancePositionedFormula source).erase :=
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (retainedFigureNineClearancePositionedFormula source).erase
      clearanceOccurrences
  have finalOccurrences :=
    @oneInThreeThenNoUnits_occurrencesAtMostThree
      (PeriodicPlanarThreeSATThreeVariable Variable)
      clearanceDecEq
      (retainedFigureNineClearancePositionedFormula source).erase
      clearanceWidth clearanceOccurrences'
  exact
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ retainedOrderedFixedEightOneInThreeVariableBEq
      (by infer_instance)
      retainedOrderedFixedEightOneInThreeVariableLawfulBEq 3
      (PeriodicOneInThreeNoUnits.formula
        (PeriodicOneInThree.formula
          (retainedFigureNineClearancePositionedFormula source).erase))
      finalOccurrences

/-- The final ordered unit-free exact-one instance is satisfiable exactly
when the original local periodic CNF is satisfiable. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3) :
    PeriodicOneInThree.Satisfiable
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase ↔
      source.Satisfiable := by
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
  exact
    (PeriodicOneInThreeNoUnits.satisfiable_iff
      (PeriodicOneInThree.formula
        (retainedFigureNineClearancePositionedFormula source).erase)).trans
      ((PeriodicOneInThree.satisfiable_iff
        (retainedFigureNineClearancePositionedFormula source).erase
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)).symm.trans
        (retainedFigureNineClearancePositionedFormula_satisfiable_iff
          source sourceLocal sourceWidth sourceOccurrences))

end PeriodicOrthocrossing
end LeanTrominoes
