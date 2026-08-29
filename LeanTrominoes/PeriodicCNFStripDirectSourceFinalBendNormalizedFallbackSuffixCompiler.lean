/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixQueryCompiler
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixQueryColumnCompiler

/-! # Compiling normalized bend fallback-suffix directions -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendNormalizedFallbackSuffixStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Route-delimited normalized direction words of all retained-bend
fallback suffixes. -/
def directSourceFinalBendNormalizedFallbackSuffixDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  NormalizedFallbackSuffixDirectionCompiler.Batch.directions
    (directSourceFinalBendFallbackSuffixQueries decider symbols)

/-- Direct source symbols compile to all normalized retained-bend fallback
suffix words in polynomial time. -/
noncomputable def
    directSourceFinalBendNormalizedFallbackSuffixDirectionsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FallbackSuffixDirectionCompiler.OutputToken)
      encoding.Γ FallbackSuffixDirectionCompiler.OutputToken
      id id
      (directSourceFinalBendNormalizedFallbackSuffixDirections decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    let directionsCompiler :=
      TM2CompositionMachine.computableInPolyTime
        (directSourceBaseBendTerminalDirectionRanksComputableInPolyTime decider)
        RetainedTerminalDirectionRankDecoder.directionsOfRanksComputableInPolyTime
    let rolesCompiler :=
      TM2CompositionMachine.computableInPolyTime directionsCompiler
        FallbackSuffixHeaderRoles.bendRolesComputableInPolyTime
    unfold directSourceFinalBendNormalizedFallbackSuffixDirections
      directSourceFinalBendFallbackSuffixQueries
    exact
      FallbackSuffixQueryColumns.normalizedDirectionsComputableInPolyTimeOf
        id
        (directSourceFinalBendFallbackHeaderRoles decider)
        (directSourceBaseBendTerminalRadialLengths decider)
        (directSourceFinalBendOccurrenceSlots decider)
        (directSourceFinalBendFallbackRolesSlots_length decider)
        (directSourceFinalBendFallbackRolesRadials_length decider)
        rolesCompiler
        (directSourceBaseBendTerminalRadialLengthsComputableInPolyTime decider)
        (directSourceFinalBendOccurrenceSlotsComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
