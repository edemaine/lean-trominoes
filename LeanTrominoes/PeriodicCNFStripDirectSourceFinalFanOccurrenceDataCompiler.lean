/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanQueryKeyCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryKeyedValueLookupSemantics

/-! # Finite occurrence records selected for final variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

abbrev FinalFanOccurrenceData :=
  HorizontalRoutedRouteHeader.OccurrenceData

/-- Encode one finite occurrence record as role number with reserved slot
zero in the generic role/slot unary code. -/
def finalFanOccurrenceDataCode (data : FinalFanOccurrenceData) : Nat :=
  8 * (Fintype.equivFin FinalFanOccurrenceData data).val + 0

/-- Recover only the finite occurrence-record component of every generic
role/slot decoding. -/
def decodedFinalFanOccurrenceData (codes : List Nat) :
    List FinalFanOccurrenceData :=
  (FiniteRoleSlotUnaryDecoder.pairs
    (Role := FinalFanOccurrenceData) codes).map Prod.fst

@[simp] theorem decodedFinalFanOccurrenceData_map_code
    (data : List FinalFanOccurrenceData) :
    decodedFinalFanOccurrenceData (data.map finalFanOccurrenceDataCode) =
      data := by
  induction data with
  | nil => rfl
  | cons occurrence data induction =>
      simp only [List.map_cons, decodedFinalFanOccurrenceData,
        FiniteRoleSlotUnaryDecoder.pairs]
      have decodedOccurrence :
          FiniteRoleSlotUnaryDecoder.decode
              (FiniteRoleSlotUnaryDecoder.boundedCode
                (finalFanOccurrenceDataCode occurrence)) =
            (occurrence, (0 : FiniteRoleSlotUnaryDecoder.Slot)) :=
        FiniteRoleSlotUnaryDecoder.decode_role_slot_index
          occurrence (0 : FiniteRoleSlotUnaryDecoder.Slot)
      have headEq :
          (FiniteRoleSlotUnaryDecoder.decode
              (FiniteRoleSlotUnaryDecoder.boundedCode
                (finalFanOccurrenceDataCode occurrence))).1 = occurrence :=
        congrArg Prod.fst decodedOccurrence
      rw [headEq]
      change occurrence ::
          decodedFinalFanOccurrenceData
            (data.map finalFanOccurrenceDataCode) = occurrence :: data
      rw [induction]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFanOccurrenceDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Unary candidate values aligned with all final occurrence keys. -/
def directSourceFinalFanOccurrenceCandidateCodes
    (symbols : List encoding.Γ) : List Nat :=
  (directSourceFinalCompiledOccurrenceData decider symbols).map
    finalFanOccurrenceDataCode

/-- Three selected finite-record codes per final occurrence, one for each fan
slot after the inactive-slot fallback policy. -/
def directSourceFinalFanSelectedOccurrenceCodes
    (symbols : List encoding.Γ) : List Nat :=
  UnaryKeyedValueLookup.values
    (directSourceFinalFanQueryKeys decider symbols)
    (directSourceFinalOccurrenceCandidateKeys decider symbols)
    (directSourceFinalFanOccurrenceCandidateCodes decider symbols)

/-- Decoded connector kind, polarity, and first direction for the three
finite fan slots of every final occurrence. -/
def directSourceFinalFanSelectedOccurrenceData
    (symbols : List encoding.Γ) : List FinalFanOccurrenceData :=
  decodedFinalFanOccurrenceData
    (directSourceFinalFanSelectedOccurrenceCodes decider symbols)

@[simp] theorem directSourceFinalFanOccurrenceCandidateCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanOccurrenceCandidateCodes decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  simp [directSourceFinalFanOccurrenceCandidateCodes]

@[simp] theorem directSourceFinalFanSelectedOccurrenceCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanSelectedOccurrenceCodes decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalFanSelectedOccurrenceCodes
  rw [UnaryKeyedValueLookup.values_length,
    directSourceFinalFanQueryKeys_length]

@[simp] theorem directSourceFinalFanSelectedOccurrenceData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalFanSelectedOccurrenceData decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalFanSelectedOccurrenceData
    decodedFinalFanOccurrenceData FiniteRoleSlotUnaryDecoder.pairs
  rw [List.length_map, List.length_map,
    directSourceFinalFanSelectedOccurrenceCodes_length]

noncomputable def
    directSourceFinalFanOccurrenceCandidateCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFanOccurrenceCandidateCodes decider) := by
  unfold directSourceFinalFanOccurrenceCandidateCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCompiledOccurrenceDataComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime finalFanOccurrenceDataCode)

/-- Keyed lookup compiles the three selected occurrence-record codes per
final occurrence in polynomial time. -/
noncomputable def
    directSourceFinalFanSelectedOccurrenceCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalFanSelectedOccurrenceCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalFanSelectedOccurrenceCodes
    exact UnaryKeyedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalFanQueryKeys decider)
      (directSourceFinalOccurrenceCandidateKeys decider)
      (directSourceFinalFanOccurrenceCandidateCodes decider)
      (fun symbols => by
        rw [directSourceFinalFanOccurrenceCandidateCodes_length,
          directSourceFinalOccurrenceCandidateKeys_length])
      (directSourceFinalFanQueryKeysComputableInPolyTime decider)
      (directSourceFinalOccurrenceCandidateKeysComputableInPolyTime decider)
      (directSourceFinalFanOccurrenceCandidateCodesComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

private noncomputable def decodedFinalFanOccurrenceDataComputableInPolyTime :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id
      decodedFinalFanOccurrenceData := by
  let decoded := FiniteRoleSlotUnaryDecoder.computableInPolyTime
    (Role := FinalFanOccurrenceData)
  let projected := TM2CompositionMachine.computableInPolyTime decoded
    (FiniteBlockTransducer.computableInPolyTime
      fun pair : FiniteRoleSlotUnaryDecoder.Pair FinalFanOccurrenceData =>
        [pair.1])
  have flatMapSingletons (pairs :
      List (FiniteRoleSlotUnaryDecoder.Pair FinalFanOccurrenceData)) :
      pairs.flatMap (fun pair => [pair.1]) = pairs.map Prod.fst := by
    induction pairs with
    | nil => rfl
    | cons pair pairs induction => simp [induction]
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq projected
  intro codes
  unfold decodedFinalFanOccurrenceData
  exact flatMapSingletons
    (FiniteRoleSlotUnaryDecoder.pairs
      (Role := FinalFanOccurrenceData) codes)

/-- The three decoded finite occurrence records per final occurrence are
polynomial-time computable. -/
noncomputable def
    directSourceFinalFanSelectedOccurrenceDataComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalFanSelectedOccurrenceData decider) := by
  unfold directSourceFinalFanSelectedOccurrenceData
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalFanSelectedOccurrenceCodesComputableInPolyTime decider)
    decodedFinalFanOccurrenceDataComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
