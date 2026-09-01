/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanQueryKeyCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldStableDedupCompiler

/-! # Stable distinct final fan-query keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalUniqueFanQueryKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One occurrence key per active final occurrence, grouped by the first
presentation of its atom identity and then by stable occurrence rank. -/
def directSourceFinalUniqueFanQueryKeys
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldStableDedup.values
    (directSourceFinalFanQueryKeys decider symbols)

/-- Stable deduplication compiles the distinct active fan keys in polynomial
time, including for the formally possible empty source alphabet. -/
noncomputable def
    directSourceFinalUniqueFanQueryKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalUniqueFanQueryKeys decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalUniqueFanQueryKeys
    exact UnaryFieldStableDedup.valuesComputableInPolyTime
      id (directSourceFinalFanQueryKeys decider)
      (directSourceFinalFanQueryKeysComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end
