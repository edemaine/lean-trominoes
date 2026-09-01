/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedDirectionTokenKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceKeySemantics

/-! # Data for sparse routed suffixes aligned with variable incidences -/

namespace LeanTrominoes.PeriodicCNFStripReduction

abbrev VariableIncidenceDirectionToken :=
  DirectFinalColoredOccurrenceDirectionToken

/-- Candidate payload distinguishes a routed block's own delimiter from the
single default delimiter installed for every full incidence key. -/
inductive VariableIncidenceSparseSuffixToken
  | routedDirection (direction : AxisDirection)
  | routedEnd
  | defaultEnd
  deriving DecidableEq, Fintype, Inhabited

namespace VariableIncidenceSparseSuffixToken

/-- Tag one token of a routed occurrence direction block. -/
def routedBlock : VariableIncidenceDirectionToken →
    List VariableIncidenceSparseSuffixToken
  | .value direction => [.routedDirection direction]
  | .blockEnd => [.routedEnd]

@[simp] theorem routedBlock_length (token : VariableIncidenceDirectionToken) :
    (routedBlock token).length = 1 := by
  cases token <;> rfl

/-- Erase routed delimiters while retaining routed directions and the one
default delimiter that closes every full incidence suffix block. -/
def outputBlock : VariableIncidenceSparseSuffixToken →
    List VariableIncidenceDirectionToken
  | .routedDirection direction => [.value direction]
  | .routedEnd => []
  | .defaultEnd => [.blockEnd]

def output (tokens : List VariableIncidenceSparseSuffixToken) :
    List VariableIncidenceDirectionToken :=
  tokens.flatMap outputBlock

end VariableIncidenceSparseSuffixToken

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Routed token keys followed by one default candidate key for every full
variable incidence. -/
noncomputable def directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalGroupedRoutedDirectionTokenKeys decider symbols ++
    directSourceFinalGroupedVariableIncidenceKeys decider symbols

/-- Tag every routed token and append one default delimiter candidate per
full variable incidence. -/
noncomputable def directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
    (symbols : List encoding.Γ) :
    List VariableIncidenceSparseSuffixToken :=
  (directSourceFinalGroupedColoredOccurrenceDirectionTokens
      decider symbols).flatMap
        VariableIncidenceSparseSuffixToken.routedBlock ++
    (directSourceFinalGroupedVariableIncidencePrefixQueries
      decider symbols).map fun _ => .defaultEnd

/-- Keyed sparse overlay before erasing the redundant routed delimiters. -/
noncomputable def directSourceFinalGroupedVariableIncidenceSparseSuffixTokens
    (symbols : List encoding.Γ) :
    List VariableIncidenceSparseSuffixToken :=
  FiniteAlphabetKeyedValueLookup.values
    (directSourceFinalGroupedVariableIncidenceKeys decider symbols)
    (directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
      decider symbols)
    (directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
      decider symbols)

/-- One complete suffix block per full variable incidence: routed direction
words at the three matching keys and an empty block everywhere else. -/
noncomputable def
    directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens
    (symbols : List encoding.Γ) :
    List VariableIncidenceDirectionToken :=
  VariableIncidenceSparseSuffixToken.output
    (directSourceFinalGroupedVariableIncidenceSparseSuffixTokens
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction
