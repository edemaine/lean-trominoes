/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomCode
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeWordSemantics

/-! # Self-delimiting structural words for final direct-source atoms -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace DirectSourceFinalAtomWords

open PeriodicOrthocrossing
open PeriodicOrthocrossing.CarrierKeyWords
open PeriodicOrthocrossing.CarrierNodeCodeWords

/-- Self-delimiting word for a possible width-three source atom.  The
auxiliary branch is retained for global injectivity, although valid direct
sources only use the original-atom branch. -/
def threeCNFAtomWord : ThreeCNFVariable Nat → List Bool
  | .inl atom => false :: natField atom
  | .inr auxiliary => true :: natField (Encodable.encode auxiliary)

/-- Decode one possible width-three source atom and retain its suffix. -/
def decodeThreeCNFAtom :
    List Bool → Option (ThreeCNFVariable Nat × List Bool)
  | false :: bits => do
      let (atom, bits) ← decodeNat bits
      pure (.inl atom, bits)
  | true :: bits => do
      let (code, bits) ← decodeNat bits
      let auxiliary ← Encodable.decode code
      pure (.inr auxiliary, bits)
  | [] => none

/-- The direct occurrence-split source variable is its underlying atom,
clause index, and literal index, in that order. -/
def sourceVariableWord (atom : Variable) : List Bool :=
  threeCNFAtomWord atom.1 ++
    natField atom.2.1 ++ natField atom.2.2

/-- Decode one direct occurrence-split source variable and retain its
suffix. -/
def decodeSourceVariable : List Bool → Option (Variable × List Bool)
  | bits => do
      let (atom, bits) ← decodeThreeCNFAtom bits
      let (clauseIndex, bits) ← decodeNat bits
      let (literalIndex, bits) ← decodeNat bits
      pure ((atom, clauseIndex, literalIndex), bits)

/-- A periodic terminal discards its physical translate, so its carrier-node
identity word uses the canonical zero translate. -/
def terminalCode
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    CarrierNodeCode :=
  .terminal
    { indexed := indexedGridSegmentCode indexed
      translate := (0, 0)
      endpoint := endpoint }

/-- Recover the periodic routed variable represented by a carrier-node code.
The terminal translate is deliberately ignored. -/
def periodicVariableOfCarrierCode
    (code : CarrierNodeCode) : PeriodicPlanarSATVariable Variable :=
  match code with
  | .boundary boundary => .boundary boundary.boundary
  | .terminal terminal =>
      .terminal terminal.indexed.indexed terminal.endpoint

/-- Fixed finite word for one crossover-internal constructor. -/
def crossoverInternalWord
    (internal : PlanarThreeSAT.CrossoverInternal) : List Bool :=
  natField internal.toFin.1

/-- Decode one crossover-internal constructor and retain its suffix. -/
def decodeCrossoverInternal :
    List Bool → Option (PlanarThreeSAT.CrossoverInternal × List Bool)
  | bits => do
      let (code, bits) ← decodeNat bits
      if codeLt : code < 9 then
        pure (PlanarThreeSAT.CrossoverInternal.ofFin ⟨code, codeLt⟩, bits)
      else
        none

/-- Constructor-tagged word of one final wrapped routed atom.  Carrier
terminals and boundaries share their established reversible carrier-node
format; source atoms and crossover internals have disjoint two-bit tags. -/
def word (atom : WrappedPeriodicPlanarSATVariable Variable) : List Bool :=
  match atom.original with
  | .terminal indexed endpoint =>
      false :: CarrierNodeCodeWords.word (terminalCode indexed endpoint)
  | .boundary boundary =>
      false :: CarrierNodeCodeWords.word (.boundary boundary.code)
  | .atom sourceAtom =>
      true :: false :: sourceVariableWord sourceAtom
  | .crossoverInternal (crossing, internal) =>
      true :: true ::
        crossingRecordWord crossing.code ++ crossoverInternalWord internal

/-- Decode one final atom word while retaining its suffix. -/
def decode :
    List Bool → Option
      (WrappedPeriodicPlanarSATVariable Variable × List Bool)
  | false :: bits => do
      let (code, bits) ← CarrierNodeCodeWords.decode bits
      pure (⟨periodicVariableOfCarrierCode code⟩, bits)
  | true :: false :: bits => do
      let (sourceAtom, bits) ← decodeSourceVariable bits
      pure (⟨.atom sourceAtom⟩, bits)
  | true :: true :: bits => do
      let (crossing, bits) ← decodeCrossingRecord bits
      let (internal, bits) ← decodeCrossoverInternal bits
      pure (⟨.crossoverInternal (crossing.record, internal)⟩, bits)
  | _ => none

@[simp] theorem decodeThreeCNFAtom_word_append
    (atom : ThreeCNFVariable Nat) (suffix : List Bool) :
    decodeThreeCNFAtom (threeCNFAtomWord atom ++ suffix) =
      some (atom, suffix) := by
  cases atom with
  | inl atom => simp [threeCNFAtomWord, decodeThreeCNFAtom]
  | inr auxiliary =>
      simp only [threeCNFAtomWord, List.cons_append,
        decodeThreeCNFAtom]
      rw [decodeNat_natField_append]
      change (Encodable.decode (Encodable.encode auxiliary)).bind
        (fun decoded => some (Sum.inr decoded, suffix)) =
          some (Sum.inr auxiliary, suffix)
      rw [Encodable.encodek]
      rfl

@[simp] theorem decodeSourceVariable_word_append
    (atom : Variable) (suffix : List Bool) :
    decodeSourceVariable (sourceVariableWord atom ++ suffix) =
      some (atom, suffix) := by
  rcases atom with ⟨atom, clauseIndex, literalIndex⟩
  simp [sourceVariableWord, decodeSourceVariable, List.append_assoc]

@[simp] theorem decodeCrossoverInternal_word_append
    (internal : PlanarThreeSAT.CrossoverInternal)
    (suffix : List Bool) :
    decodeCrossoverInternal (crossoverInternalWord internal ++ suffix) =
      some (internal, suffix) := by
  cases internal <;>
    simp [crossoverInternalWord, decodeCrossoverInternal,
      PlanarThreeSAT.CrossoverInternal.toFin,
      PlanarThreeSAT.CrossoverInternal.ofFin]

@[simp] theorem periodicVariableOfCarrierCode_terminalCode
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    periodicVariableOfCarrierCode (terminalCode indexed endpoint) =
      .terminal indexed endpoint := by
  simp [periodicVariableOfCarrierCode, terminalCode]

@[simp] theorem periodicVariableOfCarrierCode_boundary
    (boundary : CrossingBoundary) :
    periodicVariableOfCarrierCode (.boundary boundary.code) =
      .boundary boundary := by
  simp [periodicVariableOfCarrierCode]

@[simp] theorem decode_word_append
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (suffix : List Bool) :
    decode (word atom ++ suffix) = some (atom, suffix) := by
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
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    decode (word atom) = some (atom, []) := by
  simpa using decode_word_append atom []

/-- Final structural atom words are globally injective. -/
theorem word_injective : Function.Injective word := by
  intro first second wordsEq
  have decodedEq := congrArg decode wordsEq
  simpa using decodedEq

end DirectSourceFinalAtomWords
end PeriodicCNFStripReduction
end LeanTrominoes

end
