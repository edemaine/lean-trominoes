/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler
import LeanTrominoes.SeparatedProductEncoding

/-! # Joining aligned route-delimited direction streams -/

namespace LeanTrominoes.DelimitedRouteJoin

abbrev Token :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

abbrev InputSymbol := SeparatedProductEncoding.Token Token Token

inductive Phase
  | prefix
  | suffix
  deriving DecidableEq, Fintype, Inhabited

structure Result where
  remainingPrefixes : List Token
  remainingSuffixes : List Token
  output : List Token

/-- Consume one prefix route without its delimiter, then one complete suffix
route, repeating until the prefix stream ends.  The residual fields make the
operational behavior explicit even on malformed or unaligned streams. -/
def resultAux : Phase → List Token → List Token → Result
  | .prefix, [], suffixes => ⟨[], suffixes, []⟩
  | .prefix, .direction direction :: prefixes, suffixes =>
      let result := resultAux .prefix prefixes suffixes
      { result with output := .direction direction :: result.output }
  | .prefix, .routeEnd :: prefixes, suffixes =>
      resultAux .suffix prefixes suffixes
  | .suffix, prefixes, [] => ⟨prefixes, [], []⟩
  | .suffix, prefixes, .direction direction :: suffixes =>
      let result := resultAux .suffix prefixes suffixes
      { result with output := .direction direction :: result.output }
  | .suffix, prefixes, .routeEnd :: suffixes =>
      let result := resultAux .prefix prefixes suffixes
      { result with output := .routeEnd :: result.output }
  termination_by _phase prefixes suffixes =>
    prefixes.length + suffixes.length
  decreasing_by
    all_goals simp_wf

def joinedAux (phase : Phase)
    (prefixes suffixes : List Token) : List Token :=
  (resultAux phase prefixes suffixes).output

def joined (prefixes suffixes : List Token) : List Token :=
  joinedAux .prefix prefixes suffixes

def encode (input : List Token × List Token) : List InputSymbol :=
  SeparatedProductEncoding.encode id id input

end LeanTrominoes.DelimitedRouteJoin
