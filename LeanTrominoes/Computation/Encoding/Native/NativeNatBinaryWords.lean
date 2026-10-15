/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.TM2.TM2ComputableInPolyTimeCongr
import LeanTrominoes.Computation.Encoding.Binary.BinaryFieldWords
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldEncoderMachine
import LeanTrominoes.Complexity.FiniteStateTransducerSemantics
import LeanTrominoes.Complexity.FiniteStateTransducerTime

/-! # Streaming native natural fields into delimited binary words -/
noncomputable section
namespace LeanTrominoes.NativeNatBinaryWords
open _root_.Computability Turing
open FiniteStateTransducer

/-- `true` marks the beginning of a field. Zero is the empty binary word. -/
def transition : Bool → PartrecToTM2.Γ' → Bool × List DelimitedBinaryWords.Token
  | start, .bit0 => (false, (if start then [.wordStart] else []) ++ [.bit false])
  | start, .bit1 => (false, (if start then [.wordStart] else []) ++ [.bit true])
  | start, .cons | start, .consₗ =>
      (true, (if start then [.wordStart] else []) ++ [.wordEnd])

def tokens := FiniteStateTransducer.output true transition (fun _ => [])

private theorem scan_bits (start : Bool) (bits : List Bool) :
    scan transition start (bits.map BinaryFieldWords.bitSymbol ++ [PartrecToTM2.Γ'.cons]) =
      (true, (if start then [DelimitedBinaryWords.Token.wordStart] else []) ++
        bits.map DelimitedBinaryWords.Token.bit ++ [.wordEnd]) := by
  induction bits generalizing start with
  | nil => cases start <;> rfl
  | cons bit bits ih =>
    cases bit <;> cases start <;>
      simp [BinaryFieldWords.bitSymbol,scan,transition,ih]

private theorem scan_fields (fields : List Nat) :
    scan transition true (PartrecToTM2.trList fields) =
      (true, DelimitedBinaryWords.encode ⟨fields.map encodeNat⟩) := by
  induction fields with
  | nil => rfl
  | cons n ns ih =>
    have bits : PartrecToTM2.trNat n = (encodeNat n).map BinaryFieldWords.bitSymbol := by
      rw [Complexity.partrec_trNat_eq_map_encodeNat]
      apply List.map_congr_left
      intro b _
      cases b <;> rfl
    change scan transition true (PartrecToTM2.trNat n ++ .cons :: PartrecToTM2.trList ns) = _
    rw [bits, show (encodeNat n).map BinaryFieldWords.bitSymbol ++
      .cons :: PartrecToTM2.trList ns =
      ((encodeNat n).map BinaryFieldWords.bitSymbol ++ [.cons]) ++ PartrecToTM2.trList ns
      by simp, scan_append, scan_bits]
    dsimp only
    rw [ih]
    simp [DelimitedBinaryWords.encode,DelimitedBinaryWords.wordTokens]

theorem tokens_fields (fields : List Nat) :
    tokens (PartrecToTM2.trList fields) = DelimitedBinaryWords.encode ⟨fields.map encodeNat⟩ := by
  unfold tokens FiniteStateTransducer.output
  rw [scan_fields]
  simp

def nativeComputableInPolyTime :
    TM2ComputableInPolyTime PartrecToTM2.trList DelimitedBinaryWords.encode
      (fun fields : List Nat => ⟨fields.map encodeNat⟩) := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare PartrecToTM2.trList
    (FiniteStateTransducer.computableInPolyTime true transition (fun _ => []))
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared tokens_fields

def unaryComputableInPolyTime :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields DelimitedBinaryWords.encode
      (fun fields : List Nat => ⟨fields.map encodeNat⟩) :=
  (TM2CompositionMachine.computableInPolyTime UnaryFieldEncoderMachine.computableInPolyTime
    nativeComputableInPolyTime).of_eq (fun _ => rfl)

end LeanTrominoes.NativeNatBinaryWords
