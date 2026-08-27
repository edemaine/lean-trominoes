/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler
import LeanTrominoes.GadgetSparseRouteDirectionSlices
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

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

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
