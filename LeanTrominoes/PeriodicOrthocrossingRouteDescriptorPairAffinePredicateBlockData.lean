/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchCompiler

/-! # Fixed output blocks selected by affine predicate lists -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Select one fixed output block for every corresponding true Boolean.
Malformed unequal-length words stop at the shorter list; exact predicate
evaluation always supplies the intended fixed length. -/
def selectTruthBlocks {Output : Type} :
    List (List Output) → List Bool → List Output
  | block :: blocks, accepted :: acceptedRest =>
      (if accepted then block else []) ++
        selectTruthBlocks blocks acceptedRest
  | _, _ => []

/-- Evaluate a fixed affine predicate list and concatenate its corresponding
accepted output blocks in predicate order. -/
def predicateListBlocks {Output : Type}
    (predicates : List Predicate)
    (blocks : List (List Output))
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Output :=
  selectTruthBlocks blocks
    (predicateListTruthValues predicates tokens)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
