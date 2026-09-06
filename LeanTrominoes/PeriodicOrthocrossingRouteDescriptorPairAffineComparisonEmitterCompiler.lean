/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineComparisonEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagFintypeData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time compilation of signed affine comparison words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags
open PeriodicCNF
open PeriodicCNF.AffineEmitterPipeline

/-- The fixed five-symbol translation from program tokens to comparison
tokens is a polynomial-time finite block transducer. -/
def translateComparisonTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id translateComparisonTokens :=
  FiniteBlockTransducer.computableInPolyTime comparisonTokenBlock

/-- Each fixed affine expression can emit the delimiter encoding of its
positive and negative unary totals in polynomial time. -/
def Expression.comparisonTokensComputableInPolyTime
    (expression : Expression) :
    TM2ComputableInPolyTime id id expression.comparisonTokens := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (emittedAllComputableInPolyTime expression.comparisonPhases)
    translateComparisonTokensComputableInPolyTime
  unfold Expression.comparisonTokens
  exact composed

/-- Reinterpret the emitted physical word as its semantic singleton pair of
positive and negative unary words. -/
def Expression.comparisonInputComputableInPolyTime
    (expression : Expression) :
    @TM2ComputableInPolyTime
      (List RouteDescriptorPairFieldTags.Token)
      DelimitedBinaryWordPairs.Input
      RouteDescriptorPairFieldTags.Token DelimitedBinaryWordPairs.Token
      id DelimitedBinaryWordPairs.encode expression.comparisonInput :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    expression.comparisonTokensComputableInPolyTime
    expression.comparisonTokens_eq_encode

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
