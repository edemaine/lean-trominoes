/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingCoordinateKeySemantics
import LeanTrominoes.DelimitedBinaryWordAffixCompiler
import LeanTrominoes.FiniteFamilyColumnConcatCompiler

/-! # Crossing dictionaries indexed by the nine internal gadget roles -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing.InternalCrossingCoordinateKeys
open Computability Turing
open PeriodicCNFStripReduction.DirectSourceFinalAtomWords

abbrev Candidate := PlanarThreeSAT.CrossoverInternal × CarrierNode

def roles : List PlanarThreeSAT.CrossoverInternal := Finset.univ.toList

@[simp] theorem mem_roles (role : PlanarThreeSAT.CrossoverInternal) : role ∈ roles := by
  simp [roles]

/-- Role-major order keeps each coordinate column aligned with its word dictionary. -/
def candidates (descriptors : List RouteDescriptor) : List Candidate :=
  roles.flatMap fun role => (CarrierCrossingMacroOrigin.nodes descriptors).map (role, ·)

def nodeWord (candidate : Candidate) : List Bool :=
  [true, true] ++ CarrierNodeSourceKeys.word (CarrierNodeSourceKeys.pair candidate.2) ++
    crossoverInternalWord candidate.1

def baseWords (descriptors : List RouteDescriptor) : DelimitedBinaryWords.Input :=
  ⟨(CarrierCrossingMacroOrigin.nodes descriptors).map fun node =>
    [true, true] ++ CarrierNodeSourceKeys.word (CarrierNodeSourceKeys.pair node)⟩

def words (descriptors : List RouteDescriptor) : DelimitedBinaryWords.Input :=
  ⟨roles.flatMap fun role =>
    (DelimitedBinaryWordAffix.words [] (crossoverInternalWord role) (baseWords descriptors)).words⟩

theorem words_eq_candidates (descriptors : List RouteDescriptor) :
    (words descriptors).words = (candidates descriptors).map nodeWord := by
  simp [words, candidates, baseWords, nodeWord, DelimitedBinaryWordAffix.words,
    List.map_flatMap, List.map_map, Function.comp_def]

def baseTokens (descriptors : List RouteDescriptor) : List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordGuardedPrefix.tokens [true, true]
    (CarrierSourceKeyRankOrderedWordStream.emittedTokens descriptors)

noncomputable def baseTokensComputableInPolyTime :
    TM2ComputableInPolyTime CarrierSourceKeyRankOrderedWordStream.descriptorInputEncoding id
      baseTokens := by
  unfold baseTokens
  exact TM2CompositionMachine.computableInPolyTime
    CarrierSourceKeyRankOrderedWordStream.emittedTokensComputableInPolyTime
    (DelimitedBinaryWordGuardedPrefix.tokensComputableInPolyTime [true, true])

private theorem words_sourcePairs (pairs : List CarrierNodeSourceKeys.SourceKeyPair) :
    DelimitedBinaryWordGuardedPrefix.words [true, true] (CarrierSourcePairFieldFormatter.words pairs) =
      ⟨pairs.map fun pair => [true, true] ++ CarrierNodeSourceKeys.word pair⟩ := by
  unfold DelimitedBinaryWordGuardedPrefix.words CarrierSourcePairFieldFormatter.words
  apply congrArg DelimitedBinaryWords.Input.mk
  rw [List.flatMap_map]
  simp only [DelimitedBinaryWordGuardedPrefix.word]
  exact List.map_eq_flatMap.symm

theorem baseTokens_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable] (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    baseTokens (PeriodicCNF.numericRouteDescriptors formula) =
      DelimitedBinaryWords.encode (baseWords (PeriodicCNF.numericRouteDescriptors formula)) := by
  unfold baseTokens
  rw [CarrierSourceKeyRankOrderedWordStream.emittedTokens_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  dsimp only
  rw [DelimitedBinaryWordGuardedPrefix.tokens_encode, words_sourcePairs]
  unfold baseWords CarrierCrossingMacroOrigin.nodes
  simp [CarrierNodeSourceKeys.datumPair, List.map_map, Function.comp_def]

/-- Once the base dictionary is compiled, each fixed role adds only a word suffix. -/
noncomputable def wordsComputableInPolyTime
    {InputSymbol : Type} [Fintype InputSymbol]
    (descriptors : List InputSymbol → List RouteDescriptor)
    (baseCompiler : TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode
      (fun input => baseWords (descriptors input))) :
    TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode
      (fun input => words (descriptors input)) := by
  exact DelimitedBinaryWords.flatMapComputableInPolyTime roles
    (fun role input => DelimitedBinaryWordAffix.words [] (crossoverInternalWord role)
      (baseWords (descriptors input)))
    (fun role => TM2CompositionMachine.computableInPolyTime baseCompiler
      (DelimitedBinaryWordAffix.computableInPolyTime [] (crossoverInternalWord role)))

end LeanTrominoes.PeriodicOrthocrossing.InternalCrossingCoordinateKeys
end
