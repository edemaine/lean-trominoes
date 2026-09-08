/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPrefixCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingMacroOriginCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedWordStreamNumericSemantics

/-! # Physical source-pair dictionary keys for crossing-origin coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierCrossingCoordinateKeys

open Computability Turing

/-- Boundary constructor followed by the complete physical source-pair identity.
Terminal candidates have distinct source-pair tags and zero crossing-origin data. -/
def nodeWord (node : CarrierNode) : List Bool :=
  [false, true] ++ CarrierNodeSourceKeys.word (CarrierNodeSourceKeys.pair node)

def words (descriptors : List RouteDescriptor) : DelimitedBinaryWords.Input :=
  ⟨(CarrierCrossingMacroOrigin.nodes descriptors).map nodeWord⟩

@[simp] theorem words_words (descriptors : List RouteDescriptor) :
    (words descriptors).words = (CarrierCrossingMacroOrigin.nodes descriptors).map nodeWord := rfl

def tokens (descriptors : List RouteDescriptor) : List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordGuardedPrefix.tokens [false, true]
    (CarrierSourceKeyRankOrderedWordStream.emittedTokens descriptors)

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime CarrierSourceKeyRankOrderedWordStream.descriptorInputEncoding id
      tokens := by
  unfold tokens
  exact TM2CompositionMachine.computableInPolyTime
    CarrierSourceKeyRankOrderedWordStream.emittedTokensComputableInPolyTime
    (DelimitedBinaryWordGuardedPrefix.tokensComputableInPolyTime [false, true])

private theorem words_sourcePairs (prefixBits : List Bool)
    (pairs : List CarrierNodeSourceKeys.SourceKeyPair) :
    DelimitedBinaryWordGuardedPrefix.words prefixBits (CarrierSourcePairFieldFormatter.words pairs) =
      ⟨pairs.map fun pair => prefixBits ++ CarrierNodeSourceKeys.word pair⟩ := by
  unfold DelimitedBinaryWordGuardedPrefix.words CarrierSourcePairFieldFormatter.words
  apply congrArg DelimitedBinaryWords.Input.mk
  rw [List.flatMap_map]
  simp only [DelimitedBinaryWordGuardedPrefix.word]
  exact List.map_eq_flatMap.symm

/-- On actual numeric routes, the physical key compiler emits one key per
crossing-origin column entry in precisely the same global carrier order. -/
theorem tokens_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable] (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    tokens (PeriodicCNF.numericRouteDescriptors formula) =
      DelimitedBinaryWords.encode (words (PeriodicCNF.numericRouteDescriptors formula)) := by
  unfold tokens
  rw [CarrierSourceKeyRankOrderedWordStream.emittedTokens_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  dsimp only
  rw [DelimitedBinaryWordGuardedPrefix.tokens_encode]
  rw [words_sourcePairs]
  unfold words CarrierCrossingMacroOrigin.nodes nodeWord
  simp [CarrierNodeSourceKeys.datumPair, List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicOrthocrossing.CarrierCrossingCoordinateKeys

end
