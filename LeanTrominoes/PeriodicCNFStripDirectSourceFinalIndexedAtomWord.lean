/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomWord

/-! # Compact indexed words for direct-source atoms -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace DirectSourceFinalIndexedAtomWords

open PeriodicOrthocrossing
open PeriodicOrthocrossing.CarrierKeyWords
open PeriodicOrthocrossing.CarrierNodeCodeWords
open DirectSourceFinalAtomWords

/-- Source variables occurring in the formula use their canonical dedup index;
off-formula variables use the complete fallback structural word. -/
def sourceVariableWord
    (source : PeriodicCNF Variable) (atom : Variable) : List Bool :=
  if atom ∈ source.variableOccurrences.dedup then
    false :: natField (source.variableOccurrences.dedup.idxOf atom)
  else
    true :: DirectSourceFinalAtomWords.sourceVariableWord atom

/-- Decode one compact source-variable word while retaining its suffix. -/
def decodeSourceVariable
    (source : PeriodicCNF Variable) :
    List Bool → Option (Variable × List Bool)
  | false :: bits => do
      let (index, bits) ← decodeNat bits
      let atom ← source.variableOccurrences.dedup[index]?
      pure (atom, bits)
  | true :: bits =>
      DirectSourceFinalAtomWords.decodeSourceVariable bits
  | [] => none

/-- Final atom word specialized to one direct source: only the source-atom
branch changes, replacing its full occurrence triple by a member index. -/
def word
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable) : List Bool :=
  match atom.original with
  | .terminal indexed endpoint =>
      false :: CarrierNodeCodeWords.word
        (DirectSourceFinalAtomWords.terminalCode indexed endpoint)
  | .boundary boundary =>
      false :: CarrierNodeCodeWords.word (.boundary boundary.code)
  | .atom sourceAtom =>
      true :: false :: sourceVariableWord source sourceAtom
  | .crossoverInternal (crossing, internal) =>
      true :: true ::
        crossingRecordWord crossing.code ++
          DirectSourceFinalAtomWords.crossoverInternalWord internal

/-- Decode one source-specialized final atom word while retaining its suffix. -/
def decode
    (source : PeriodicCNF Variable) :
    List Bool → Option
      (WrappedPeriodicPlanarSATVariable Variable × List Bool)
  | false :: bits => do
      let (code, bits) ← CarrierNodeCodeWords.decode bits
      pure (⟨DirectSourceFinalAtomWords.periodicVariableOfCarrierCode code⟩,
        bits)
  | true :: false :: bits => do
      let (sourceAtom, bits) ← decodeSourceVariable source bits
      pure (⟨.atom sourceAtom⟩, bits)
  | true :: true :: bits => do
      let (crossing, bits) ← decodeCrossingRecord bits
      let (internal, bits) ←
        DirectSourceFinalAtomWords.decodeCrossoverInternal bits
      pure (⟨.crossoverInternal (crossing.record, internal)⟩, bits)
  | _ => none

@[simp] theorem decodeSourceVariable_word_append
    (source : PeriodicCNF Variable)
    (atom : Variable) (suffix : List Bool) :
    decodeSourceVariable source
        (sourceVariableWord source atom ++ suffix) =
      some (atom, suffix) := by
  by_cases member : atom ∈ source.variableOccurrences.dedup
  · simp [sourceVariableWord, decodeSourceVariable, member,
      List.getElem?_idxOf member]
  · simp [sourceVariableWord, decodeSourceVariable, member]

@[simp] theorem decode_word_append
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (suffix : List Bool) :
    decode source (word source atom ++ suffix) = some (atom, suffix) := by
  rcases atom with ⟨atom⟩
  cases atom with
  | terminal indexed endpoint =>
      simp [word, decode]
  | boundary boundary =>
      simp [word, decode]
  | atom sourceAtom =>
      simp [word, decode]
  | crossoverInternal internal =>
      rcases internal with ⟨crossing, internal⟩
      simp [word, decode, List.append_assoc]

@[simp] theorem decode_word
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    decode source (word source atom) = some (atom, []) := by
  simpa using decode_word_append source atom []

/-- For every fixed source, compact final atom words remain globally
injective, including on variables absent from that source. -/
theorem word_injective (source : PeriodicCNF Variable) :
    Function.Injective (word source) := by
  intro first second wordsEq
  have decodedEq := congrArg (decode source) wordsEq
  simpa using decodedEq

end DirectSourceFinalIndexedAtomWords
end PeriodicCNFStripReduction
end LeanTrominoes

end
