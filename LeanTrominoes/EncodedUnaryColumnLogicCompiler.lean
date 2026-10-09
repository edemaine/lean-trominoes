/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.EncodedUnaryColumnCompiler
import LeanTrominoes.FiniteIndexSlotUnaryDecoderCompiler

/-! # Polynomial-time zero tests and comparisons on unary columns -/
noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
open UnaryFieldEncoderMachine (unaryFields unaryField)

def zeroIndicators (values : List Nat) : List Nat := values.map fun n => (decide (n=0)).toNat

def zeroIndicatorsCompiler : TM2ComputableInPolyTime unaryFields unaryFields zeroIndicators := by
  let physical := TM2CompositionMachine.computableInPolyTime (FiniteIndexSlotUnaryDecoder.computableInPolyTime 1)
    (FiniteBlockTransducer.computableInPolyTime (fun code : FiniteIndexSlotUnaryDecoder.Pair 1 =>
      unaryField ((decide (code.2.val=0)).toNat)))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro values
  simp only [FiniteIndexSlotUnaryDecoder.pairs,List.flatMap_map]
  change values.flatMap (fun n => unaryField ((decide ((FiniteIndexSlotUnaryDecoder.boundedCode 1 n).2.val=0)).toNat)) = _
  have zeroTest (n : Nat) : ((FiniteIndexSlotUnaryDecoder.boundedCode 1 n).2.val=0) ↔ n=0 := by
    simp only [FiniteIndexSlotUnaryDecoder.boundedCode,FiniteIndexSlotUnaryDecoder.codeBound]
    omega
  simp only [zeroTest,zeroIndicators,unaryFields,List.flatMap_map]

variable {Input Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {encodeInput : Input → List Symbol} {rows : Input → List Index} {f g : Input → Index → Nat}

def zeroIndicator (column : Compiler encodeInput rows f) :
    Compiler encodeInput rows (fun s row => (decide (f s row=0)).toNat) := by
  let physical := TM2CompositionMachine.computableInPolyTime column zeroIndicatorsCompiler
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by simp [zeroIndicators,List.map_map])

def equalIndicator (first : Compiler encodeInput rows f) (second : Compiler encodeInput rows g) :
    Compiler encodeInput rows (fun s row => (decide (f s row=g s row)).toNat) := by
  let physical := zeroIndicator (add (sub first second) (sub second first))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row _
  have equivalent : f s row-g s row+(g s row-f s row)=0 ↔ f s row=g s row := by omega
  simp only [equivalent]

def lessIndicator (first : Compiler encodeInput rows f) (second : Compiler encodeInput rows g) :
    Compiler encodeInput rows (fun s row => (decide (f s row<g s row)).toNat) := by
  let differenceZero := zeroIndicator (sub second first)
  let physical := sub (constant differenceZero 1) differenceZero
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro row _
  by_cases smaller : f s row<g s row
  · have nonzero : g s row-f s row ≠ 0 := by omega
    simp [smaller,nonzero]
  · have zero : g s row-f s row = 0 := by omega
    simp [smaller,zero]

end LeanTrominoes.EncodedUnaryColumn
end
