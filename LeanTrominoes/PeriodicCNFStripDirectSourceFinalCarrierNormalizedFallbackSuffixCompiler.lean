/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackSuffixQueryCompiler
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixQueryColumnCompiler

/-! # Compiling normalized carrier fallback-suffix directions -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierNormalizedFallbackSuffixStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Route-delimited normalized direction words of all retained-carrier
fallback suffixes. -/
def directSourceFinalCarrierNormalizedFallbackSuffixDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  NormalizedFallbackSuffixDirectionCompiler.Batch.directions
    (directSourceFinalCarrierFallbackSuffixQueries decider symbols)

/-- Direct source symbols compile to all normalized retained-carrier
fallback suffix words in polynomial time. -/
noncomputable def
    directSourceFinalCarrierNormalizedFallbackSuffixDirectionsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FallbackSuffixDirectionCompiler.OutputToken)
      encoding.Γ FallbackSuffixDirectionCompiler.OutputToken
      id id
      (directSourceFinalCarrierNormalizedFallbackSuffixDirections decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    let directionsCompiler :=
      TM2CompositionMachine.computableInPolyTime
        (directSourceCarrierTerminalDirectionRanksComputableInPolyTime decider)
        RetainedTerminalDirectionRankDecoder.directionsOfRanksComputableInPolyTime
    let rolesCompiler :=
      TM2CompositionMachine.computableInPolyTime directionsCompiler
        FallbackSuffixHeaderRoles.carrierRolesComputableInPolyTime
    unfold directSourceFinalCarrierNormalizedFallbackSuffixDirections
      directSourceFinalCarrierFallbackSuffixQueries
    exact
      FallbackSuffixQueryColumns.normalizedDirectionsComputableInPolyTimeOf
        id
        (directSourceFinalCarrierFallbackHeaderRoles decider)
        (directSourceCarrierTerminalRadialLengths decider)
        (directSourceFinalCarrierOccurrenceSlots decider)
        (directSourceFinalCarrierFallbackRolesSlots_length decider)
        (directSourceFinalCarrierFallbackRolesRadials_length decider)
        rolesCompiler
        (directSourceCarrierTerminalRadialLengthsComputableInPolyTime decider)
        (directSourceFinalCarrierOccurrenceSlotsComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
