/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordFormatterCompiler
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoderData
import LeanTrominoes.PeriodicOrthocrossingCarrierSpanRouteDirectionDecoder
import LeanTrominoes.SeparatedBooleanGuardCompiler
import LeanTrominoes.TM2BooleanClosure
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for packed retained carrier Figure 9 tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierPackedSpanRouteTailRecords

open Computability Turing

noncomputable def reducedOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id reducedOutput :=
  FiniteStateTransducer.computableInPolyTime
    ReductionControl.zero reducedTransition reducedFinish

private def ResidueControl.outputLength : ResidueControl → Nat
  | .residue _ => 1
  | .done => 0

private theorem residue_output_cons (target : Residue)
    (control : ResidueControl) (symbol : SourceSymbol)
    (block : List SourceSymbol) :
    FiniteStateTransducer.output control (residueTransition target)
        (residueFinish target) (symbol :: block) =
      (residueTransition target control symbol).2 ++
        FiniteStateTransducer.output
          (residueTransition target control symbol).1
          (residueTransition target) (residueFinish target) block := by
  unfold FiniteStateTransducer.output
  simp only [FiniteStateTransducer.scan]
  rw [List.append_assoc]

private theorem residueOutput_length_from (target : Residue) :
    ∀ control block,
      (FiniteStateTransducer.output control (residueTransition target)
        (residueFinish target) block).length = control.outputLength
  | .residue value, [] => rfl
  | .done, [] => rfl
  | control, symbol :: block => by
      rw [residue_output_cons]
      cases control <;> cases symbol <;>
        simp [residueTransition, ResidueControl.outputLength,
          residueOutput_length_from target]

theorem residueOutput_eq_singleton (target : Residue)
    (block : List SourceSymbol) :
    residueOutput target block = [hasResidue target block] := by
  have lengthEq : (residueOutput target block).length = 1 := by
    exact residueOutput_length_from target (.residue .zero) block
  unfold hasResidue
  cases outputEq : residueOutput target block with
  | nil => simp [outputEq] at lengthEq
  | cons residue remaining =>
      cases remaining with
      | nil => rfl
      | cons other remaining => simp [outputEq] at lengthEq

private noncomputable def residueOutputComputableInPolyTime
    (target : Residue) :
    TM2ComputableInPolyTime id id (residueOutput target) := by
  unfold residueOutput
  exact FiniteStateTransducer.computableInPolyTime
    (ResidueControl.residue .zero)
    (residueTransition target) (residueFinish target)

noncomputable def hasResidueComputableInPolyTime (target : Residue) :
    TM2ComputableInPolyTime id TM2BooleanClosure.booleanEncoding
      (hasResidue target) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (residueOutputComputableInPolyTime target)
    (residueOutput_eq_singleton target)

noncomputable def candidateComputableInPolyTime
    (horizontal nextSlice : Bool) :
    TM2ComputableInPolyTime id id (candidate horizontal nextSlice) := by
  change TM2ComputableInPolyTime id id (fun block =>
    BinaryRouteTailRecordFormatter.output
      (BinaryRouteTailRecordFormatter.descriptorProfile
        (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierClauseDescriptor
          horizontal nextSlice true))
      (BinaryRouteTailRecordFormatter.descriptorProfile
        (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierClauseDescriptor
          horizontal nextSlice false))
      (CarrierSpanRouteDirections.blockOutput horizontal
        (reducedOutput block)))
  let directions := TM2CompositionMachine.computableInPolyTime
    reducedOutputComputableInPolyTime
    (CarrierSpanRouteDirections.blockOutputComputableInPolyTime horizontal)
  exact TM2CompositionMachine.computableInPolyTime directions
    (BinaryRouteTailRecordFormatter.outputComputableInPolyTime
      (BinaryRouteTailRecordFormatter.descriptorProfile
        (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierClauseDescriptor
          horizontal nextSlice true))
      (BinaryRouteTailRecordFormatter.descriptorProfile
        (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierClauseDescriptor
          horizontal nextSlice false)))

noncomputable def guardedCandidateComputableInPolyTime
    (residue : Residue) (horizontal nextSlice : Bool) :
    TM2ComputableInPolyTime id id
      (guardedCandidate residue horizontal nextSlice) := by
  change TM2ComputableInPolyTime id id (fun block =>
    SeparatedBooleanGuard.guarded
      (hasResidue residue block, candidate horizontal nextSlice block))
  let paired := TM2ForkMachine.computableInPolyTime
    (hasResidueComputableInPolyTime residue)
    (candidateComputableInPolyTime horizontal nextSlice)
  exact TM2CompositionMachine.computableInPolyTime paired
    (SeparatedBooleanGuard.computableInPolyTime (Symbol := Token))

noncomputable def blockOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id blockOutput := by
  exact TM2ListAppend.computableInPolyTime
    (TM2ListAppend.computableInPolyTime
      (TM2ListAppend.computableInPolyTime
        (guardedCandidateComputableInPolyTime .zero false false)
        (guardedCandidateComputableInPolyTime .one false true))
      (guardedCandidateComputableInPolyTime .two true false))
    (guardedCandidateComputableInPolyTime .three true true)

noncomputable def streamComputableInPolyTime :
    TM2ComputableInPolyTime id id stream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    blockOutputComputableInPolyTime
    CarrierSpanRouteDirections.isFieldEnd

end CarrierPackedSpanRouteTailRecords
end LeanTrominoes.PeriodicOrthocrossing

end
