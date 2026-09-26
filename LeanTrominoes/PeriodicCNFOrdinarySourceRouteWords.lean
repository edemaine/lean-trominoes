/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrdinarySourceRouteRecordCompiler
import LeanTrominoes.PeriodicCNFOrdinarySourceValueGeometry
import LeanTrominoes.PositionedIncidenceRowRanges

/-! # Selected route records cover precisely the ordinary incidence list -/
namespace LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
open FormulaShapeDirectionOrdering FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNinePolarityRouteTail FormulaShapeFigureNineSourceTail ClauseProfilePolarityRouteOperation

theorem selectedRouteWords_ofClause {Variable : Type}
    (source : PositionedPeriodicCNF Variable) (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (index : Nat)
    (clause : PositionedPeriodicClause Variable) (lookup : source.clauses[index]? = some clause)
    (nonempty : clause.literals ≠ []) (width : clause.literals.length ≤ 3)
    (steps : ∀ i < clause.literals.length,
      (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection source placement routes index i).IsChain AxisDirection.IsUnitAxisStep)
    (lengths : ∀ i < clause.literals.length,
      2 ≤ (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection source placement routes index i).length) :
    (slots (DirectedClauseProfile.ofClause routes index clause)).map (fun slot =>
      OrdinarySourceRouteRecord.directions (selectedHeader (DirectedClauseProfile.ofClause routes index clause) slot,
        selectedTailDirections (orderedTailDirections routes index clause)
          (selectedHeader (DirectedClauseProfile.ofClause routes index clause) slot))) =
      (List.range clause.literals.length).map (fun i => Gadget.unitSubdivisionDirections
        (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection source placement routes index i)) := by
  let profile := DirectedClauseProfile.ofClause routes index clause
  have len : profile.taggedLiterals.length = clause.literals.length := by
    rw [DirectedClauseProfile.ofClause_taggedLiterals routes index clause nonempty width]
    simp only [annotatedLiterals, List.length_map, List.length_zipIdx]
  rw [← len, ← slots_map_index, List.map_map]
  apply List.map_congr_left
  intro slot member
  have active : sourceSlotNat slot < clause.literals.length := by
    rw [← len]
    exact (slots_active profile slot).1 member
  exact selectedRoute_ofClause source placement routes index clause lookup nonempty width slot active
    (steps _ active) (lengths _ active)

end LeanTrominoes.PeriodicCNF.OrdinarySourceProjection
