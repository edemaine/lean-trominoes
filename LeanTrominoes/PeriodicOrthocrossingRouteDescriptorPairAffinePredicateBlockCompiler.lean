/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockSemantics

/-! # Compiler for affine-predicate-selected fixed blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairFieldTags

/-- Any fixed affine predicate list can select a corresponding list of fixed
output blocks in polynomial time. -/
noncomputable def predicateListBlocksComputableInPolyTime
    {Output : Type} [Fintype Output] [Inhabited Output]
    (predicates : List Predicate)
    (blocks : List (List Output)) :
    TM2ComputableInPolyTime id id
      (predicateListBlocks predicates blocks) := by
  let evaluate := predicateListTruthValuesComputableInPolyTime predicates
  let select := FixedLengthWordEvaluator.computableInPolyTime
    predicates.length (selectTruthBlocks blocks)
  let complete := TM2CompositionMachine.computableInPolyTime evaluate select
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
  intro tokens
  unfold predicateListBlocks
  rw [FixedLengthWordEvaluator.output_eq_of_length_eq]
  rw [predicateListTruthValues_eq, List.length_map]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

end
