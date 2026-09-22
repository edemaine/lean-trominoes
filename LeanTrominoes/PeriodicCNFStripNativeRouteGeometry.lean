/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesSemanticBridge
import LeanTrominoes.PositionedPeriodicCNFPresentationCanonicalRoutes
import LeanTrominoes.CanonicalLiteralOffsetRecovery
import LeanTrominoes.PeriodicCNFStripNativePeriodCompiler

/-! # Canonical endpoints and unit steps of the executable routed source -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PositionedPeriodicCNF PeriodicOneInThreePolarityNormalizationRouteSubdivision
attribute [local instance] sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq
set_option maxHeartbeats 200000

def nativeRoutedPresentation (source : PeriodicCNF Nat) :
    PlanarIncidencePresentation (horizontalRoutedFormulaComputed source)
      (horizontalRoutedPlacementComputed source) where
  routes := horizontalRoutedRoutesComputed source
  periodPositive := nativeRoutedPeriod_positive source
  compatible := by
    rw [horizontalRoutedFormulaComputed_eq_semanticData,
      horizontalRoutedPlacementComputed_eq_semanticData, horizontalRoutedRoutesComputed_eq_semanticData]
    exact incidenceDrawing_isCompatible
      (horizontalSemanticFinalGaugedPresentation source).toContinuousPlanarIncidencePresentation
  orthogonal := by
    rw [horizontalRoutedFormulaComputed_eq_semanticData,
      horizontalRoutedPlacementComputed_eq_semanticData, horizontalRoutedRoutesComputed_eq_semanticData]
    exact incidenceDrawing_isOrthogonal
      (horizontalSemanticFinalGaugedPresentation source).toContinuousPlanarIncidencePresentation
  planar := by
    rw [horizontalRoutedFormulaComputed_eq_semanticData,
      horizontalRoutedPlacementComputed_eq_semanticData, horizontalRoutedRoutesComputed_eq_semanticData]
    exact incidenceDrawing_isPlanar
      (horizontalSemanticFinalGaugedPresentation source).toContinuousPlanarIncidencePresentation

@[simp] theorem nativeRoutedPresentation_routes (source : PeriodicCNF Nat) :
    (nativeRoutedPresentation source).routes = horizontalRoutedRoutesComputed source := by
  simp only [nativeRoutedPresentation]

private theorem unitSteps_members {V : Type*} [DecidableEq V]
    (source : PositionedPeriodicCNF V) (placement : PeriodicVariablePlacement V)
    (routes : IncidenceRoutes) (steps : (incidenceDrawing source placement routes).HasUnitSteps)
    {clause : PositionedPeriodicClause V} {ci : Nat} (hc : (clause, ci) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral V} {li : Nat} (hl : (literal, li) ∈ clause.literals.zipIdx) :
    (routes ci li).IsChain AxisDirection.IsUnitAxisStep := by
  apply steps (routes ci li)
  exact List.mem_flatMap.mpr ⟨(clause, ci), hc, List.mem_map.mpr ⟨(literal, li), hl, rfl⟩⟩

/-- Endpoint certificates for the exact route family consumed by the compiler. -/
theorem nativeRoutedRoute_endpoints (source : PeriodicCNF Nat)
    {clause : PositionedPeriodicClause RoutedVariable} {ci : Nat}
    (hc : (clause, ci) ∈ (horizontalRoutedFormulaComputed source).clauses.zipIdx)
    {literal : PeriodicLiteral RoutedVariable} {li : Nat}
    (hl : (literal, li) ∈ clause.literals.zipIdx) :
    (horizontalRoutedRoutesComputed source ci li).head? = some
      (canonicalClausePosition (horizontalRoutedPlacementComputed source) clause) ∧
    (horizontalRoutedRoutesComputed source ci li).getLast? = some
      (canonicalLiteralPosition (horizontalRoutedPlacementComputed source) clause literal) := by
  have endpoints := (nativeRoutedPresentation source).canonicalOrthogonalRoutes.endpoints clause ci hc literal li hl
  simpa only [PlanarIncidencePresentation.canonicalOrthogonalRoutes,
    nativeRoutedPresentation] using endpoints

/-- Every stored incidence route has unit cardinal steps. -/
theorem nativeRoutedDrawing_unitSteps (source : PeriodicCNF Nat) :
    (incidenceDrawing (horizontalRoutedFormulaComputed source)
      (horizontalRoutedPlacementComputed source) (horizontalRoutedRoutesComputed source)).HasUnitSteps := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData,
    horizontalRoutedPlacementComputed_eq_semanticData,
    horizontalRoutedRoutesComputed_eq_semanticData]
  exact incidenceDrawing_hasUnitSteps
    (horizontalSemanticFinalGaugedPresentation source).toContinuousPlanarIncidencePresentation

/-- Pointwise unit-step certificate in the compiler's clause/literal order. -/
theorem nativeRoutedRoute_unitSteps (source : PeriodicCNF Nat)
    {clause : PositionedPeriodicClause RoutedVariable} {ci : Nat}
    (hc : (clause, ci) ∈ (horizontalRoutedFormulaComputed source).clauses.zipIdx)
    {literal : PeriodicLiteral RoutedVariable} {li : Nat}
    (hl : (literal, li) ∈ clause.literals.zipIdx) :
    (horizontalRoutedRoutesComputed source ci li).IsChain AxisDirection.IsUnitAxisStep := by
  exact unitSteps_members (horizontalRoutedFormulaComputed source)
    (horizontalRoutedPlacementComputed source) (horizontalRoutedRoutesComputed source)
    (nativeRoutedDrawing_unitSteps source) hc hl

/-- Exact anchored offsets are recovered from the compiler's actual routes. -/
theorem nativeRoutedRoute_offset (source : PeriodicCNF Nat) (horizontal : Bool)
    {clause : PositionedPeriodicClause RoutedVariable} {ci : Nat}
    (hc : (clause, ci) ∈ (horizontalRoutedFormulaComputed source).clauses.zipIdx)
    {literal : PeriodicLiteral RoutedVariable} {li : Nat}
    (hl : (literal, li) ∈ clause.literals.zipIdx) :
    DelimitedDirectionDisplacement.component horizontal
        (canonicalClausePosition (horizontalRoutedPlacementComputed source) clause) +
      DelimitedDirectionDisplacement.displacement horizontal
        (Gadget.unitSubdivisionDirections (horizontalRoutedRoutesComputed source ci li)) -
      DelimitedDirectionDisplacement.component horizontal
        ((horizontalRoutedPlacementComputed source).position literal.atom) =
    ((horizontalRoutedPlacementComputed source).period : Int) *
      DelimitedDirectionDisplacement.component horizontal
        (Cell.sub literal.offset (PeriodicCNF.clauseAnchor clause.literals)) :=
  DelimitedDirectionDisplacement.canonical_offset_scaled horizontal
    (horizontalRoutedPlacementComputed source) clause literal
    (horizontalRoutedRoutesComputed source ci li)
    (nativeRoutedRoute_endpoints source hc hl).1
    (nativeRoutedRoute_endpoints source hc hl).2
    (nativeRoutedRoute_unitSteps source hc hl)

end LeanTrominoes.PeriodicCNFStripReduction
end
