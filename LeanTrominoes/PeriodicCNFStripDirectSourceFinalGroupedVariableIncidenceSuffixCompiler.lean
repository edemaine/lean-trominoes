/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixCandidateSemantics
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for full sparse variable-incidence suffix blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

namespace VariableIncidenceSparseSuffixToken

noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteBlockTransducer.computableInPolyTime outputBlock

end VariableIncidenceSparseSuffixToken

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedVariableSuffixStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Finite keyed lookup compiles the sparse suffix overlay in polynomial
time. -/
noncomputable def
    directSourceFinalGroupedVariableIncidenceSparseSuffixTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableIncidenceSparseSuffixTokens
        decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedVariableIncidenceSparseSuffixTokens
    exact FiniteAlphabetKeyedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalGroupedVariableIncidenceKeys decider)
      (directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys decider)
      (directSourceFinalGroupedVariableIncidenceSuffixCandidateValues decider)
      (fun symbols => by
        rw [directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys_length,
          directSourceFinalGroupedVariableIncidenceSuffixCandidateValues_length])
      (directSourceFinalGroupedVariableIncidenceKeysComputableInPolyTime
        decider)
      (directSourceFinalGroupedVariableIncidenceSuffixCandidateKeysComputableInPolyTime
        decider)
      (directSourceFinalGroupedVariableIncidenceSuffixCandidateValuesComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- Erasing routed delimiters leaves the exact aligned suffix-block stream
in polynomial time. -/
noncomputable def
    directSourceFinalGroupedVariableIncidenceSuffixDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens
        decider) := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableIncidenceSparseSuffixTokensComputableInPolyTime
      decider)
    VariableIncidenceSparseSuffixToken.outputComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
