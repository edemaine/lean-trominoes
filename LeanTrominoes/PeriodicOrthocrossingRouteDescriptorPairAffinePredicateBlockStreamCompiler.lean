/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockStreamSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiler for pair-stream affine predicate block selection -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairFieldTags

/-- Mapping a fixed affine predicate/block selector over a complete tagged
pair stream is polynomial time. -/
noncomputable def predicateListBlockStreamComputableInPolyTime
    {Output : Type} [Fintype Output] [Inhabited Output]
    (predicates : List Predicate)
    (blocks : List (List Output)) :
    TM2ComputableInPolyTime id id
      (predicateListBlockStream predicates blocks) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (predicateListBlocksComputableInPolyTime predicates blocks)
    isPairEnd

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

end
