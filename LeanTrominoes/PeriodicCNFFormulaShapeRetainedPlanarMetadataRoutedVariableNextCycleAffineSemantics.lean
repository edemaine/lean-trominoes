/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairFieldSemantics

/-! # Affine semantics of next-slice routed-variable cycle pairs -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine

@[simp] theorem routedVariableNextCycleAffinePredicate_evalPair
    (pair : RouteDescriptor × RouteDescriptor) :
    routedVariableNextCycleAffinePredicate.evalPair pair =
      routedVariableNextCyclePair pair := by
  rcases pair with ⟨first, second⟩
  simp only [routedVariableNextCycleAffinePredicate, all,
    RouteDescriptorPairAffine.equal,
    RouteDescriptorPairAffine.compare,
    Predicate.evalPair, Predicate.eval, Atom.eval, Relation.eval,
    Bool.and_true]
  change
    (decide
        ((routedVariablePairTargetPortRank .first).evalPair
            (first, second) =
          (constant 2).evalPair (first, second)) &&
      (decide
          ((routedVariablePairTargetPortRank .second).evalPair
              (first, second) =
            (constant 0).evalPair (first, second)) &&
        (decide
            ((routedVariablePairTargetVertexIndex .first).evalPair
                (first, second) =
              (routedVariablePairTargetVertexIndex .second).evalPair
                (first, second)) &&
          (decide
              ((horizontalOffset .second).evalPair (first, second) =
                (constant 1).evalPair (first, second)) &&
            decide
              ((verticalOffset .second).evalPair (first, second) =
                (constant 0).evalPair (first, second)))))) =
      routedVariableNextCyclePair (first, second)
  rw [routedVariablePairTargetPortRank_evalPair,
    routedVariablePairTargetPortRank_evalPair,
    routedVariablePairTargetVertexIndex_evalPair,
    routedVariablePairTargetVertexIndex_evalPair,
    evalPair_horizontalOffset, evalPair_verticalOffset]
  have rankTwo :
      ((first.targetPortRank : Int) = 2) ↔
        first.targetPortRank = 2 := by
    constructor
    · intro equality
      apply Int.ofNat_injective
      simpa using equality
    · intro equality
      simpa using congrArg Int.ofNat equality
  simp [constant, Expression.evalPair, Expression.eval,
    routedVariableNextCyclePair, descriptorAt, Prod.ext_iff, rankTwo]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
