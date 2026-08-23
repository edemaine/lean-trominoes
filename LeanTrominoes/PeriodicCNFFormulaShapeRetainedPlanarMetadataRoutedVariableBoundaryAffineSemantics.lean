/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairFieldSemantics

/-! # Affine semantics of routed-variable boundary pairs -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine

@[simp] theorem routedVariableNextBoundaryAffinePredicate_evalPair
    (pair : RouteDescriptor × RouteDescriptor) :
    routedVariableNextBoundaryAffinePredicate.evalPair pair =
      routedVariableNextBoundaryPair pair := by
  rcases pair with ⟨first, second⟩
  simp only [routedVariableNextBoundaryAffinePredicate, all,
    RouteDescriptorPairAffine.equal,
    RouteDescriptorPairAffine.compare,
    Predicate.evalPair, Predicate.eval, Atom.eval, Relation.eval,
    Bool.and_true]
  change
    (decide
        ((routedVariablePairEdgeIndex .first).evalPair (first, second) =
          (routedVariablePairEdgeIndex .second).evalPair (first, second)) &&
      (decide
          ((routedVariablePairTargetPortRank .first).evalPair
              (first, second) =
            (constant 0).evalPair (first, second)) &&
        (decide
            ((horizontalOffset .first).evalPair (first, second) =
              (constant 1).evalPair (first, second)) &&
          decide
            ((verticalOffset .first).evalPair (first, second) =
              (constant 0).evalPair (first, second))))) =
      routedVariableNextBoundaryPair (first, second)
  rw [routedVariablePairEdgeIndex_evalPair,
    routedVariablePairEdgeIndex_evalPair,
    routedVariablePairTargetPortRank_evalPair,
    evalPair_horizontalOffset, evalPair_verticalOffset]
  simp [constant, Expression.evalPair, Expression.eval,
    routedVariableNextBoundaryPair, descriptorAt, Prod.ext_iff]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
