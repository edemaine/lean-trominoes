/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSignedCounts

/-! # Fixed emission of signed affine comparison words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PeriodicCNF
open PeriodicCNF.AffineTemplateEmitterMachine
open PeriodicCNF.AffineEmitterPipeline
open PeriodicCNF.UnaryProgramTokens

/-- A phase that emits a fixed ending word and selects no input tokens. -/
def fixedEndingPhase
    (ending : List PeriodicCNF.UnaryProgramTokens.Token) :
    AffineEmitterPipeline.Phase RouteDescriptorPairFieldTags.Token :=
  ⟨fun _ => false, [], ending⟩

/-- Emit a fixed number of one program token for every occurrence of a
selected tagged descriptor field. -/
def Term.countPhase
    (output : PeriodicCNF.UnaryProgramTokens.Token)
    (magnitude : Int → Nat) (expressionTerm : Term) :
    AffineEmitterPipeline.Phase RouteDescriptorPairFieldTags.Token :=
  ⟨fun token => decide
      (token = .unit expressionTerm.side expressionTerm.field),
    List.replicate (magnitude expressionTerm.coefficient) (.fixed output),
    []⟩

/-- Fixed phase sequence whose emitted program-token word consists of one
start marker, all positive units, one middle marker, all negative units, and
one end marker. -/
def Expression.comparisonPhases (expression : Expression) :
    List (AffineEmitterPipeline.Phase RouteDescriptorPairFieldTags.Token) :=
  [fixedEndingPhase
      ([.clauseMarker] ++
        List.replicate expression.constant.toNat .atomUnit)] ++
    expression.terms.map (Term.countPhase .atomUnit Int.toNat) ++
    [fixedEndingPhase [.freshEnd],
      fixedEndingPhase
        (List.replicate (-expression.constant).toNat .freshUnit)] ++
    expression.terms.map
      (Term.countPhase .freshUnit fun coefficient => (-coefficient).toNat) ++
    [fixedEndingPhase [.atomEnd]]

/-- Translate the five allocated program-token codes to one delimited pair of
unary Boolean words. -/
def comparisonTokenBlock :
    PeriodicCNF.UnaryProgramTokens.Token →
      List DelimitedBinaryWordPairs.Token
  | .clauseMarker => [.pairStart]
  | .atomUnit => [.firstBit false]
  | .freshEnd => [.middle]
  | .freshUnit => [.secondBit false]
  | .atomEnd => [.pairEnd]
  | _ => []

def translateComparisonTokens
    (tokens : List PeriodicCNF.UnaryProgramTokens.Token) :
    List DelimitedBinaryWordPairs.Token :=
  tokens.flatMap comparisonTokenBlock

/-- Physical comparison word emitted from arbitrary tagged unary fields. -/
def Expression.comparisonTokens
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWordPairs.Token :=
  translateComparisonTokens
    (AffineEmitterPipeline.emittedAll expression.comparisonPhases tokens)

/-- Semantic singleton pair of unary words represented by the emitted
comparison-token stream. -/
def Expression.comparisonInput
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    DelimitedBinaryWordPairs.Input :=
  let counts := expression.tokenCounts tokens
  ⟨[(List.replicate counts.1 false,
      List.replicate counts.2 false)]⟩

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
