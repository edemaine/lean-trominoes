/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsEncoding
import LeanTrominoes.BoolSquareRowsTime
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Row reconstruction for compiled carrier-key equality -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyEqualityRows

open Computability Turing

abbrev InputEncoding := CarrierRankKeyEquality.InputEncoding

def side (descriptors : List RouteDescriptor) : Nat :=
  (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length

@[simp] theorem bits_length (descriptors : List RouteDescriptor) :
    (CarrierRankKeyEquality.bits descriptors).length =
      side descriptors ^ 2 := by
  simp [CarrierRankKeyEquality.bits,
    CarrierRankKeyEquality.indexBits,
    CarrierRankKeyEquality.translationBits,
    CarrierRankKeyEquality.combined, side]

/-- The flat compiled key-equality list equipped with its square promise. -/
def squareInput (descriptors : List RouteDescriptor) :
    BoolSquareRows.Input where
  bits := CarrierRankKeyEquality.bits descriptors
  square := by
    rw [bits_length, Nat.sqrt_eq']

@[simp] theorem squareInput_side (descriptors : List RouteDescriptor) :
    (squareInput descriptors).side = side descriptors := by
  unfold BoolSquareRows.Input.side squareInput
  rw [bits_length, Nat.sqrt_eq']

/-- Equality rows in compact representative order. -/
def rows (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  (squareInput descriptors).delimitedRows

noncomputable def squareInputComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      BoolSquareRows.finEncoding.encode squareInput :=
  @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (List RouteDescriptor) (List Bool) BoolSquareRows.Input
    DelimitedBinaryWords.Token Bool InputEncoding id
    BoolSquareRows.finEncoding.encode CarrierRankKeyEquality.bits squareInput
    CarrierRankKeyEquality.bitsComputableInPolyTime (fun input => by
      rw [BoolSquareRows.finEncoding_encode_eq_bits]
      rfl)

/-- The compiled flat equality square is reconstructed into delimited rows
in polynomial time. -/
noncomputable def rowsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      DelimitedBinaryWords.finEncoding.encode rows := by
  let composed := TM2CompositionMachine.computableInPolyTime
    squareInputComputableInPolyTime
    BoolSquareRowsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun _ => rfl)

end CarrierRankKeyEqualityRows
end LeanTrominoes.PeriodicOrthocrossing

end
