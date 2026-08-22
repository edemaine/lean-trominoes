/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairLengthComparisonTime
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineComparisonEmitterCompiler

/-! # Polynomial-time signed affine comparison -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags
open DelimitedBinaryWordPairLengthComparisonMachine

/-- Compare the positive and negative unary totals emitted for one fixed
affine expression. -/
def Expression.comparisonOrderings
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List LengthOrdering :=
  lengthOrderings (expression.comparisonInput tokens)

/-- A comparison input contains exactly one pair, whose ordering is the
ordering of the expression's positive and negative natural totals. -/
@[simp] theorem Expression.comparisonOrderings_eq
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    expression.comparisonOrderings tokens =
      [compareNats
        (expression.positiveCount (tokenFieldValue tokens))
        (expression.negativeCount (tokenFieldValue tokens))] := by
  unfold Expression.comparisonOrderings Expression.comparisonInput
    Expression.tokenCounts lengthOrderings compareLengths
  simp only [List.map_cons, List.map_nil, List.length_replicate]

/-- Every fixed signed affine expression can be compared in polynomial time
from the tagged unary descriptor-pair stream. -/
def Expression.comparisonOrderingsComputableInPolyTime
    (expression : Expression) :
    TM2ComputableInPolyTime id id expression.comparisonOrderings := by
  let composed := TM2CompositionMachine.computableInPolyTime
    expression.comparisonInputComputableInPolyTime
    DelimitedBinaryWordPairLengthComparisonMachine.computableInPolyTime
  unfold Expression.comparisonOrderings
  exact composed

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
