/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAtomCompiler
import LeanTrominoes.TM2BooleanClosure

/-! # Polynomial-time evaluation of fixed affine predicates -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- Reinterpret the atom compiler's singleton list as the canonical encoding
of its Boolean truth value. -/
def Atom.evalTokensComputableInPolyTime (atom : Atom) :
    TM2ComputableInPolyTime id TM2BooleanClosure.booleanEncoding
      (fun tokens : List RouteDescriptorPairFieldTags.Token =>
        atom.eval (tokenFieldValue tokens)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    atom.truthResultsComputableInPolyTime atom.truthResults_eq

/-- Every fixed Boolean formula over signed affine comparisons is computable
in polynomial time from the tagged unary descriptor-pair fields. -/
def Predicate.evalTokensComputableInPolyTime :
    (predicate : Predicate) →
      TM2ComputableInPolyTime id TM2BooleanClosure.booleanEncoding
        predicate.evalTokens
  | .truth => by
      change TM2ComputableInPolyTime id
        TM2BooleanClosure.booleanEncoding
        (fun _ : List RouteDescriptorPairFieldTags.Token => true)
      exact TM2BooleanClosure.constantComputableInPolyTime id true
  | .falsity => by
      change TM2ComputableInPolyTime id
        TM2BooleanClosure.booleanEncoding
        (fun _ : List RouteDescriptorPairFieldTags.Token => false)
      exact TM2BooleanClosure.constantComputableInPolyTime id false
  | .atom comparison => by
      change TM2ComputableInPolyTime id
        TM2BooleanClosure.booleanEncoding
        (fun tokens : List RouteDescriptorPairFieldTags.Token =>
          comparison.eval (tokenFieldValue tokens))
      exact comparison.evalTokensComputableInPolyTime
  | .conjunction first second => by
      let combined := TM2BooleanClosure.forkComputableInPolyTime
        first.evalTokensComputableInPolyTime
        second.evalTokensComputableInPolyTime
        (fun firstValue secondValue => firstValue && secondValue)
      change TM2ComputableInPolyTime id
        TM2BooleanClosure.booleanEncoding
        (fun tokens : List RouteDescriptorPairFieldTags.Token =>
          first.eval (tokenFieldValue tokens) &&
            second.eval (tokenFieldValue tokens))
      exact combined
  | .disjunction first second => by
      let combined := TM2BooleanClosure.forkComputableInPolyTime
        first.evalTokensComputableInPolyTime
        second.evalTokensComputableInPolyTime
        (fun firstValue secondValue => firstValue || secondValue)
      change TM2ComputableInPolyTime id
        TM2BooleanClosure.booleanEncoding
        (fun tokens : List RouteDescriptorPairFieldTags.Token =>
          first.eval (tokenFieldValue tokens) ||
            second.eval (tokenFieldValue tokens))
      exact combined
  | .negation input => by
      let negated := TM2BooleanClosure.mapComputableInPolyTime
        input.evalTokensComputableInPolyTime (fun value => !value)
      change TM2ComputableInPolyTime id
        TM2BooleanClosure.booleanEncoding
        (fun tokens : List RouteDescriptorPairFieldTags.Token =>
          !(input.eval (tokenFieldValue tokens)))
      exact negated

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
