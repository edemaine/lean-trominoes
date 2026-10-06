/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderData
import LeanTrominoes.FiniteBoolCheck

/-! # Finite semantics of the final Figure 9 clause ordering -/


set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineFinalClauseOrdering

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open PlanarOneInThreeNoUnitsFigureNine
open UnaryProgramClauseProfile

/-- Attach the first direction of each finite template route to the literal
profile at the same generated-clause coordinate. -/
def embeddedDirectedClauseProfile
    (drawing : PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
      FigureNineNoUnitsVariable)
    (taggedClause :
      PlanarThreeSAT.EmbeddedClause FigureNineNoUnitsVariable × Nat) :
    DirectedClauseProfile :=
  DirectedClauseProfile.ofList
    (taggedClause.1.literals.zipIdx.map fun taggedLiteral =>
      (⟨false, taggedLiteral.1.2⟩,
        AxisDirection.polylineFirstDirection
          (drawing.routes taggedClause.2 taggedLiteral.2)))

/-- Direction-aware profiles of all generated clauses in the finite Figure 9
template, before the second clockwise sort. -/
def figureDirectedClauseProfiles (profile : DirectedClauseProfile) :
    List DirectedClauseProfile :=
  let drawing := templateDrawingOfClauseProfile (clauseProfile profile)
  drawing.formula.zipIdx.map (embeddedDirectedClauseProfile drawing)

/-- Original literal indices selected by the stable clockwise sort of one
finite generated clause. -/
def embeddedClauseSourceOrder
    (drawing : PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
      FigureNineNoUnitsVariable)
    (taggedClause :
      PlanarThreeSAT.EmbeddedClause FigureNineNoUnitsVariable × Nat) :
    List Nat :=
  (((List.range taggedClause.1.literals.length).map fun literalIndex =>
      (literalIndex,
        AxisDirection.polylineFirstDirection
          (drawing.routes taggedClause.2 literalIndex))).insertionSort
    (fun first second =>
      first.2.clockwiseRank ≤ second.2.clockwiseRank)).map Prod.fst

/-- Source-index permutations chosen by the final finite clockwise sort, one
row per generated clause. -/
def figureClauseSourceOrders (profile : DirectedClauseProfile) :
    List (List Nat) :=
  let drawing := templateDrawingOfClauseProfile (clauseProfile profile)
  drawing.formula.zipIdx.map (embeddedClauseSourceOrder drawing)

private def directionFreeProfile : ClauseProfile → DirectedClauseProfile
  | .unary first => .unary first .invalid
  | .binary first second => .binary first .invalid second .invalid
  | .ternary first second third => .ternary first .invalid second .invalid third .invalid

/-- Forgetting route directions recovers the original generated profile
column exactly. -/
theorem figureDirectedClauseProfiles_map_clauseProfile :
    ∀ profile : DirectedClauseProfile,
      (figureDirectedClauseProfiles profile).map clauseProfile =
        figureClauseProfiles profile := by
  have checked : (finiteAll fun profile : ClauseProfile => decide ((figureDirectedClauseProfiles (directionFreeProfile profile)).map clauseProfile =
        figureClauseProfiles (directionFreeProfile profile))) = true := by
    decide +kernel
  have casesChecked := (finiteAll_eq_true _).mp checked
  simp only [decide_eq_true_eq] at casesChecked
  intro profile
  cases profile with
  | unary first direction => exact casesChecked (.unary first)
  | binary first firstDirection second secondDirection => exact casesChecked (.binary first second)
  | ternary first firstDirection second secondDirection third thirdDirection =>
      exact casesChecked (.ternary first second third)

/-- Sorting every finite template clause by its route's first direction is
exactly the explicit final permutation: binary clauses use `1,0`, and ternary
clauses use `2,0,1`. -/
theorem figureDirectedClauseProfiles_map_orderedProfile :
    ∀ profile : DirectedClauseProfile,
      (figureDirectedClauseProfiles profile).map
          DirectedClauseProfile.orderedProfile =
        finalFigureClauseProfiles profile := by
  have checked : (finiteAll fun profile : ClauseProfile => decide ((figureDirectedClauseProfiles (directionFreeProfile profile)).map
          DirectedClauseProfile.orderedProfile =
        finalFigureClauseProfiles (directionFreeProfile profile))) = true := by
    decide +kernel
  have casesChecked := (finiteAll_eq_true _).mp checked
  simp only [decide_eq_true_eq] at casesChecked
  intro profile
  cases profile with
  | unary first direction => exact casesChecked (.unary first)
  | binary first firstDirection second secondDirection => exact casesChecked (.binary first second)
  | ternary first firstDirection second secondDirection third thirdDirection =>
      exact casesChecked (.ternary first second third)

/-- The stable sort selects old indices `1,0` in every binary generated
clause and `2,0,1` in every ternary generated clause.  This index-level form
retains occurrence identity even when two literal profiles are equal. -/
theorem figureClauseSourceOrders_eq_reorderList_range :
    ∀ profile : DirectedClauseProfile,
      figureClauseSourceOrders profile =
        let drawing :=
          templateDrawingOfClauseProfile (clauseProfile profile)
        drawing.formula.map fun clause =>
          reorderList (List.range clause.literals.length) := by
  have checked : (finiteAll fun profile : ClauseProfile => decide (figureClauseSourceOrders (directionFreeProfile profile) =
        let drawing :=
          templateDrawingOfClauseProfile (clauseProfile (directionFreeProfile profile))
        drawing.formula.map fun clause =>
          reorderList (List.range clause.literals.length))) = true := by
    decide +kernel
  have casesChecked := (finiteAll_eq_true _).mp checked
  simp only [decide_eq_true_eq] at casesChecked
  intro profile
  cases profile with
  | unary first direction => exact casesChecked (.unary first)
  | binary first firstDirection second secondDirection => exact casesChecked (.binary first second)
  | ternary first firstDirection second secondDirection third thirdDirection =>
      exact casesChecked (.ternary first second third)

end FormulaShapeFigureNineFinalClauseOrdering
end PeriodicCNF
end LeanTrominoes
