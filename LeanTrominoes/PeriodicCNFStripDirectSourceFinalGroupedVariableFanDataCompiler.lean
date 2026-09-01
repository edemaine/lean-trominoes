/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanDataCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Final variable-fan records in stable identity order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedVariableFanDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Every active occurrence's complete variable-fan record, in stable
identity-major and occurrence-rank-minor order. -/
def directSourceFinalGroupedVariableFanData
    (symbols : List encoding.Γ) : List VariableRibbonFanData :=
  FiniteAlphabetKeyedValueLookup.values
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalOccurrenceCandidateKeys decider symbols)
    (directSourceFinalVariableFanData decider symbols)

/-- Finite keyed selection compiles the grouped variable-fan column in
polynomial time. -/
noncomputable def
    directSourceFinalGroupedVariableFanDataComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableFanData decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedVariableFanData
    exact FiniteAlphabetKeyedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalUniqueFanQueryKeys decider)
      (directSourceFinalOccurrenceCandidateKeys decider)
      (directSourceFinalVariableFanData decider)
      (fun symbols => by
        rw [directSourceFinalOccurrenceCandidateKeys_length,
          directSourceFinalVariableFanData_length])
      (directSourceFinalUniqueFanQueryKeysComputableInPolyTime decider)
      (directSourceFinalOccurrenceCandidateKeysComputableInPolyTime decider)
      (directSourceFinalVariableFanDataComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
