/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMGeometry
import LeanTrominoes.PeriodicThreeDMFieldsCompiler
import LeanTrominoes.UnaryColumnSignedCoordinateSum

/-! # Complete native fields of the actual periodic 3DM instance -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget UnaryColumn DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

def nativeThreeDMOffsetCompiler (horizontal : Bool) :
    Compiler (nativeThreeDMIncidences decider) (fun s tag =>
      Encodable.encode (component horizontal (nativeThreeDMReference decider s tag).offset)) := by
  let physical := signedSumQuotient
    (nativeThreeDMSourcePointCompiler decider horizontal true)
    (nativeThreeDMSourcePointCompiler decider horizontal false)
    (nativeThreeDMDisplacementCompiler decider horizontal true)
    (nativeThreeDMDisplacementCompiler decider horizontal false)
    (nativeThreeDMPeriodCompiler decider) (nativeThreeDMPeriod_positive decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro tag ht
  exact congrArg Encodable.encode (nativeThreeDMOffset_recovery decider s tag ht horizontal)

def nativeThreeDMTripleCountCompiler : ScalarCompiler (fun s => (nativeThreeDMProblem decider s).triples.length) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalTripleCoordinatesComputableInPolyTime decider true true) UnaryFieldAggregate.countCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [directSourceFinalTripleCoordinates_length,nativeThreeDMTriplePositions_length]

def nativeThreeDMFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => PeriodicThreeDM.FlatEncoding.fields (nativeThreeDMProblem decider s)) :=
  PeriodicThreeDM.FlatEncoding.fieldsCompiler (problem := nativeThreeDMProblem decider)
    (nativeThreeDMElementCountCompiler decider .red) (nativeThreeDMElementCountCompiler decider .green)
    (nativeThreeDMElementCountCompiler decider .blue) (nativeThreeDMTripleCountCompiler decider)
    (PeriodicThreeDM.FlatEncoding.bodyCompiler (problem := nativeThreeDMProblem decider)
      (nativeThreeDMIncidenceAtomCompiler decider) (nativeThreeDMOffsetCompiler decider true)
      (nativeThreeDMOffsetCompiler decider false))

def nativeThreeDMProblemEncodingCompiler : TM2ComputableInPolyTime id PeriodicThreeDM.FlatEncoding.finEncoding.encode
    (nativeThreeDMProblem decider) :=
  PeriodicThreeDM.FlatEncoding.encodingCompiler (problem := nativeThreeDMProblem decider) (nativeThreeDMFieldsCompiler decider)

end LeanTrominoes.PeriodicCNFStripReduction
end
