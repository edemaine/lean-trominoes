/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler
import LeanTrominoes.GadgetSparseRouteDirectionReversal
import LeanTrominoes.GadgetSparseRouteDirectionSlices
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDirectionData

/-! # Direction data for polarity-normalized route subdivision -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open Gadget PeriodicOrthocrossing

/-- Every orthogonal source route becomes a unit-step route after threefold
refinement. -/
theorem refinedRoute_unitSteps
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (orthogonal : OrthogonalPolyline
      (routes clauseIndex literalIndex)) :
    (refinedRoute routes clauseIndex literalIndex).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold refinedRoute
  exact AxisDirection.unitSubdividePolyline_unitSteps
    (orthogonal.scalePolyline refinementFactor_positive)

/-- Threefold refinement is exactly fixed three-copy expansion at the
direction-stream boundary. -/
theorem refinedRoute_directionWord
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (orthogonal : OrthogonalPolyline
      (routes clauseIndex literalIndex)) :
    unitSubdivisionDirections
        (refinedRoute routes clauseIndex literalIndex) =
      repeatDirections refinementFactor
        (unitSubdivisionDirections
          (routes clauseIndex literalIndex)) := by
  unfold refinedRoute
  rw [unitSubdivisionDirections_unitSubdividePolyline]
  · exact unitSubdivisionDirections_scalePolyline
      refinementFactor refinementFactor_positive _
  · exact orthogonal.scalePolyline refinementFactor_positive

/-- The incompatible normalized incidence retains the first direction of the
threefold-expanded source word. -/
theorem refinedRoute_take_two_directionWord
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (orthogonal : OrthogonalPolyline
      (routes clauseIndex literalIndex)) :
    unitSubdivisionDirections
        ((refinedRoute routes clauseIndex literalIndex).take 2) =
      (repeatDirections refinementFactor
        (unitSubdivisionDirections
          (routes clauseIndex literalIndex))).take 1 := by
  rw [unitSubdivisionDirections_take_two_of_unitSteps]
  · exact congrArg (List.take 1)
      (refinedRoute_directionWord routes clauseIndex literalIndex orthogonal)
  · exact refinedRoute_unitSteps routes clauseIndex literalIndex orthogonal

/-- The original-variable complement incidence retains the source word after
discarding its first two refined directions. -/
theorem refinedRoute_drop_two_directionWord
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (orthogonal : OrthogonalPolyline
      (routes clauseIndex literalIndex)) :
    unitSubdivisionDirections
        ((refinedRoute routes clauseIndex literalIndex).drop 2) =
      (repeatDirections refinementFactor
        (unitSubdivisionDirections
          (routes clauseIndex literalIndex))).drop 2 := by
  rw [unitSubdivisionDirections_drop_of_unitSteps]
  · exact congrArg (List.drop 2)
      (refinedRoute_directionWord routes clauseIndex literalIndex orthogonal)
  · exact refinedRoute_unitSteps routes clauseIndex literalIndex orthogonal

/-- Points two and one of a unit route traverse its second direction
backward. -/
theorem unitSubdivisionDirections_reverse_middle
    (route : List Cell) (fallback : Cell)
    (length : 3 ≤ route.length)
    (unitSteps : route.IsChain AxisDirection.IsUnitAxisStep) :
    unitSubdivisionDirections
        [route.getD 2 fallback, route.getD 1 fallback] =
      reverseDirections
        ((unitSubdivisionDirections route).drop 1 |>.take 1) := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third tail =>
              have firstUnit :
                  AxisDirection.IsUnitAxisStep first second :=
                (List.isChain_cons_cons.mp unitSteps).1
              have secondUnit :
                  AxisDirection.IsUnitAxisStep second third :=
                (List.isChain_cons_cons.mp
                  (List.isChain_cons_cons.mp unitSteps).2).1
              have secondGenuine :=
                AxisDirection.between_isGenuine_of_unitAxisStep secondUnit
              simp [unitSubdivisionDirections, reverseDirections,
                segmentLength_comm,
                segmentLength_eq_one_of_unitAxisStep firstUnit,
                segmentLength_eq_one_of_unitAxisStep secondUnit,
                AxisDirection.between_reverse_eq_opposite secondGenuine]

/-- A compatible main incidence emits the complete expanded source word. -/
theorem rawRouteForMetadata_normalized_compatible_directionWord
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (literalIndex : Nat)
    (originEq : metadata.origin = .normalized)
    (literalLookup :
      metadata.sourceClause.literals[literalIndex]? = some sourceLiteral)
    (compatible :
      sourceLiteral.value =
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          literalIndex)
    (orthogonal : OrthogonalPolyline
      (sourceRoutes metadata.sourceClauseIndex literalIndex)) :
    unitSubdivisionDirections
        (rawRouteForMetadata sourcePlacement sourceRoutes metadata
          literalIndex) =
      repeatDirections refinementFactor
        (unitSubdivisionDirections
          (sourceRoutes metadata.sourceClauseIndex literalIndex)) := by
  rw [rawRouteForMetadata_normalized_compatible _ _ _ _ _
    originEq literalLookup compatible]
  exact refinedRoute_directionWord _ _ _ orthogonal

/-- An incompatible main incidence emits only the first expanded direction. -/
theorem rawRouteForMetadata_normalized_incompatible_directionWord
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (literalIndex : Nat)
    (originEq : metadata.origin = .normalized)
    (literalLookup :
      metadata.sourceClause.literals[literalIndex]? = some sourceLiteral)
    (incompatible :
      sourceLiteral.value ≠
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          literalIndex)
    (orthogonal : OrthogonalPolyline
      (sourceRoutes metadata.sourceClauseIndex literalIndex)) :
    unitSubdivisionDirections
        (rawRouteForMetadata sourcePlacement sourceRoutes metadata
          literalIndex) =
      (repeatDirections refinementFactor
        (unitSubdivisionDirections
          (sourceRoutes metadata.sourceClauseIndex literalIndex))).take 1 := by
  rw [rawRouteForMetadata_normalized_incompatible _ _ _ _ _
    originEq literalLookup incompatible]
  exact refinedRoute_take_two_directionWord _ _ _ orthogonal

/-- Translation and point-suffix selection disappear from the second
complement incidence's direction word. -/
theorem rawRouteForMetadata_complement_original_directionWord
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral)
    (orthogonal : OrthogonalPolyline
      (sourceRoutes metadata.sourceClauseIndex sourceLiteralIndex)) :
    unitSubdivisionDirections
        (rawRouteForMetadata sourcePlacement sourceRoutes metadata 1) =
      (repeatDirections refinementFactor
        (unitSubdivisionDirections
          (sourceRoutes metadata.sourceClauseIndex
            sourceLiteralIndex))).drop 2 := by
  rw [rawRouteForMetadata_complement_original _ _ _ _ _ originEq]
  rw [unitSubdivisionDirections_translatePolyline]
  exact refinedRoute_drop_two_directionWord _ _ _ orthogonal

/-- The fresh-variable complement incidence traverses the second expanded
source direction backward. -/
theorem rawRouteForMetadata_complement_fresh_directionWord
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral)
    (sourceLength : 2 ≤
      (sourceRoutes metadata.sourceClauseIndex sourceLiteralIndex).length)
    (orthogonal : OrthogonalPolyline
      (sourceRoutes metadata.sourceClauseIndex sourceLiteralIndex)) :
    unitSubdivisionDirections
        (rawRouteForMetadata sourcePlacement sourceRoutes metadata 0) =
      reverseDirections
        (((repeatDirections refinementFactor
          (unitSubdivisionDirections
            (sourceRoutes metadata.sourceClauseIndex
              sourceLiteralIndex))).drop 1).take 1) := by
  rw [rawRouteForMetadata_complement_fresh _ _ _ _ _ originEq]
  rw [unitSubdivisionDirections_translatePolyline]
  unfold routePoint
  let route := refinedRoute sourceRoutes
    metadata.sourceClauseIndex sourceLiteralIndex
  have routeLength : 3 ≤ route.length := by
    have atLeastFour := refinedRoute_length_ge_four sourceRoutes
      metadata.sourceClauseIndex sourceLiteralIndex sourceLength orthogonal
    have atLeastThree : 3 ≤
        (refinedRoute sourceRoutes metadata.sourceClauseIndex
          sourceLiteralIndex).length := by
      omega
    simpa [route] using atLeastThree
  have routeUnitSteps :
      route.IsChain AxisDirection.IsUnitAxisStep :=
    refinedRoute_unitSteps sourceRoutes metadata.sourceClauseIndex
      sourceLiteralIndex orthogonal
  rw [unitSubdivisionDirections_reverse_middle
    route (0, 0) routeLength routeUnitSteps]
  rw [show unitSubdivisionDirections route =
      repeatDirections refinementFactor
        (unitSubdivisionDirections
          (sourceRoutes metadata.sourceClauseIndex sourceLiteralIndex)) by
    exact refinedRoute_directionWord sourceRoutes
      metadata.sourceClauseIndex sourceLiteralIndex orthogonal]

/-- The final fresh-variable gauge is a common route translation and hence
disappears from every genuine output incidence's direction word. -/
theorem incidenceRoutes_directionWord_of_raw_clause_mem
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    {rawClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {clauseIndex literalIndex : Nat}
    (clauseMember :
      (rawClause, clauseIndex) ∈
        (rawFormula source sourcePlacement sourceRoutes).clauses.zipIdx) :
    unitSubdivisionDirections
        (incidenceRoutes source sourcePlacement sourceRoutes
          clauseIndex literalIndex) =
      unitSubdivisionDirections
        (rawIncidenceRoutes source sourcePlacement sourceRoutes
          clauseIndex literalIndex) := by
  exact
    PositionedPeriodicCNF.unitSubdivisionDirections_variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      (rawFormula source sourcePlacement sourceRoutes)
      (rawPlacement sourcePlacement sourceRoutes) freshGauge
      (rawIncidenceRoutes source sourcePlacement sourceRoutes) clauseMember

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
