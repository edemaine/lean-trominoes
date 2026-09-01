/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteIndexSlotUnaryDecoderCompiler
import LeanTrominoes.PeriodicCNFStripKeyedContractedIncidenceCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldBooleanFilterCompiler
import LeanTrominoes.UnaryFieldStableOccurrenceKeyCompiler
import LeanTrominoes.UnaryFieldThreeBlockOrdinalCompiler

/-! # Counted contraction plans for keyed incidence directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace CountedContractedIncidence

open Computability Turing
open PeriodicThreeDM

abbrev SizeCode := FiniteIndexSlotUnaryDecoder.Pair 1
abbrev DirectionToken := KeyedContractedIncidence.DirectionToken

/-- Decode each unary degree into finite control.  Semantic callers use only
the exact degree-two and degree-three cases. -/
def decodedSizes (sizes : List Nat) : List SizeCode :=
  FiniteIndexSlotUnaryDecoder.pairs 1 sizes

/-- Three candidate slots per element; the first two are always active and
the third is active exactly for degree three. -/
def activeBlock (code : SizeCode) : List Bool :=
  [true, true, code.2.val == 3]

def activeControls (sizes : List Nat) : List Bool :=
  (decodedSizes sizes).flatMap activeBlock

/-- Degree-two elements consume two incidence words as a through edge;
degree-three elements retain all three incidence edges. -/
def roleBlock (code : SizeCode) : List ContractedDirectionAssembler.Role :=
  if code.2.val = 3 then
    [.retained, .retained, .retained]
  else
    [.throughFirst, .throughSecond]

def roles (sizes : List Nat) : List ContractedDirectionAssembler.Role :=
  (decodedSizes sizes).flatMap roleBlock

/-- Candidate base-three keys in canonical element order, filtered to the
two or three actual incidences prescribed by the aligned degree column. -/
def queryKeys (elementCodes sizes : List Nat) : List Nat :=
  UnaryFieldBooleanFilter.selectedValues
    (activeControls sizes)
    (UnaryFieldThreeBlockOrdinals.values elementCodes)

/-- Candidate keys of incidence blocks in their independently compiled
presentation order. -/
def incidenceBlockKeys (incidenceElementCodes : List Nat) : List Nat :=
  UnaryFieldStableOccurrenceKeys.keys incidenceElementCodes

/-- Select, role-tag, and assemble incidence directions from two compact
numeric descriptions: canonical element codes with degrees, and incidence
element codes in direction-block order. -/
noncomputable def output
    (elementCodes sizes incidenceElementCodes : List Nat)
    (incidences : List DirectionToken) :
    List NormalizationDirectionRequest.Batch.NormalizedToken :=
  KeyedContractedIncidence.output
    (queryKeys elementCodes sizes)
    (roles sizes)
    (incidenceBlockKeys incidenceElementCodes)
    incidences

noncomputable def decodedSizesComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id decodedSizes := by
  unfold decodedSizes
  exact FiniteIndexSlotUnaryDecoder.computableInPolyTime 1

noncomputable def activeControlsComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id activeControls := by
  unfold activeControls
  exact TM2CompositionMachine.computableInPolyTime
    decodedSizesComputableInPolyTime
    (FiniteBlockTransducer.computableInPolyTime activeBlock)

noncomputable def rolesComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id roles := by
  unfold roles
  exact TM2CompositionMachine.computableInPolyTime
    decodedSizesComputableInPolyTime
    (FiniteBlockTransducer.computableInPolyTime roleBlock)

/-- Canonical element codes and their aligned degree column compile the
complete ordered query-key stream in polynomial time. -/
noncomputable def queryKeysComputableInPolyTimeOf
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (elementCodes sizes : Source → List Nat)
    (elementCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields elementCodes)
    (sizeCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields sizes) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => queryKeys (elementCodes source) (sizes source)) := by
  let controlCompiler := TM2CompositionMachine.computableInPolyTime
    sizeCompiler activeControlsComputableInPolyTime
  let candidateCompiler := TM2CompositionMachine.computableInPolyTime
    elementCompiler UnaryFieldThreeBlockOrdinals.computableInPolyTime
  unfold queryKeys
  exact UnaryFieldBooleanFilter.selectedValuesComputableInPolyTime
    encodeSource
    (fun source => activeControls (sizes source))
    (fun source => UnaryFieldThreeBlockOrdinals.values
      (elementCodes source))
    controlCompiler candidateCompiler

noncomputable def rolesComputableInPolyTimeOf
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (sizes : Source → List Nat)
    (sizeCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields sizes) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => roles (sizes source)) :=
  TM2CompositionMachine.computableInPolyTime
    sizeCompiler rolesComputableInPolyTime

noncomputable def incidenceBlockKeysComputableInPolyTimeOf
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (incidenceElementCodes : Source → List Nat)
    (incidenceElementCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields incidenceElementCodes) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => incidenceBlockKeys (incidenceElementCodes source)) := by
  unfold incidenceBlockKeys
  exact TM2CompositionMachine.computableInPolyTime
    incidenceElementCompiler
    UnaryFieldStableOccurrenceKeys.computableInPolyTime

/-- Any polynomial-time canonical element, degree, incidence identity, and
direction-block compilers instantiate the complete counted contraction
pipeline. -/
noncomputable def outputComputableInPolyTimeOf
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (elementCodes sizes incidenceElementCodes : Source → List Nat)
    (incidences : Source → List DirectionToken)
    (elementCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields elementCodes)
    (sizeCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields sizes)
    (incidenceElementCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields incidenceElementCodes)
    (incidenceCompiler : TM2ComputableInPolyTime encodeSource id incidences) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => output
        (elementCodes source) (sizes source)
        (incidenceElementCodes source) (incidences source)) := by
  unfold output
  exact KeyedContractedIncidence.outputComputableInPolyTimeOf
    encodeSource
    (fun source => queryKeys (elementCodes source) (sizes source))
    (fun source => incidenceBlockKeys (incidenceElementCodes source))
    (fun source => roles (sizes source))
    incidences
    (queryKeysComputableInPolyTimeOf encodeSource
      elementCodes sizes elementCompiler sizeCompiler)
    (rolesComputableInPolyTimeOf encodeSource sizes sizeCompiler)
    (incidenceBlockKeysComputableInPolyTimeOf encodeSource
      incidenceElementCodes incidenceElementCompiler)
    incidenceCompiler

end CountedContractedIncidence
end PeriodicCNFStripReduction
end LeanTrominoes

end
