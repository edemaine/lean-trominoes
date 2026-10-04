/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoNativeVerifier
import LeanTrominoes.FiniteCoordinateEncoding
import LeanTrominoes.NP

/-! # Finite-region tromino tiling is in NP

This theorem uses the explicit unary signed-coordinate encoding. The verifier
is an actual polynomial-time finite-alphabet machine, including candidate
footprint generation and canonical deduplication.
-/
noncomputable section
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing
open Complexity

def witnessToken : Sum Token (Option Bool) → List Token
  | .inl token => [token]
  | .inr none => []
  | .inr (some bit) => [.bit bit]

theorem witnessToken_encoded (source : List Token) (bits : List Bool) :
    (source.map Sum.inl ++ Sum.inr none :: bits.map (fun b => Sum.inr (some b))).flatMap witnessToken =
      source ++ bits.map Token.bit := by
  simp [List.flatMap_map,witnessToken,← List.map_eq_flatMap]

def booleanOutput : TM2ComputableInPolyTime (fun bit : Bool => [bit])
    (primcodableFinEncoding Bool).encode id := by
  letI : Inhabited (primcodableFinEncoding Bool).Γ := ⟨PartrecToTM2.Γ'.cons⟩
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare (fun bit : Bool => [bit])
    (FiniteBlockTransducer.computableInPolyTime (primcodableFinEncoding Bool).encode)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared (fun _ => by simp)

private def regionWitnessInput :
    TM2ComputableInPolyTime (encodeWitness regionEncoding) encode
      (fun input : List Cell × List Bool => (Input.mk input.1 [],input.2)) := by
  letI : Inhabited regionEncoding.Γ := ⟨Token.bit false⟩
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare (encodeWitness regionEncoding)
    (FiniteBlockTransducer.computableInPolyTime witnessToken)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared (fun input => by
    change ((encodeInput ⟨input.1,[]⟩).map Sum.inl ++
      Sum.inr none :: input.2.map (fun b => Sum.inr (some b))).flatMap witnessToken = _
    exact witnessToken_encoded _ _)

private def regionVerify (t : Tromino) (cells : List Cell) (bits : List Bool) : Bool :=
  FiniteVerifier.check true t cells [] bits

private def regionVerifierComputer (t : Tromino) :
    FiniteAlphabetComputableInPolyTime (encodeWitness regionEncoding)
      (primcodableFinEncoding Bool).encode
      (fun input => regionVerify t input.1 input.2) := by
  let native := TM2CompositionMachine.computableInPolyTime regionWitnessInput
    (nativeComputableInPolyTime true t)
  let finished := TM2CompositionMachine.computableInPolyTime native booleanOutput
  exact FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
    (finished.of_eq (fun _ => rfl))

theorem regionEncoding_length_ge (cells : List Cell) :
    cells.length≤(regionEncoding.encode cells).length := by
  simp [regionEncoding,encodeInput,fields,values,UnaryFieldEncoderMachine.unaryFields_length]
  omega

private theorem regionVerify_sound (t : Tromino) (cells : List Cell) (bits : List Bool)
    (checked : regionVerify t cells bits=true) : t.Tileable (cells.toFinset : Set Cell) := by
  obtain ⟨valid,inside⟩ := (FiniteVerifier.check_correct true t cells [] bits).mp checked
  apply (FiniteRegion.tileable_iff_valid t cells.toFinset).mpr
  exact ⟨_,valid,fun tile ht => inside rfl tile (List.mem_toFinset.mp ht)⟩

/-- Candidate generation, verification time, and the linear witness bound are
all included in the membership certificate. -/
def regionVerifier (t : Tromino) :
    VerifierInPolyTime regionEncoding (fun cells => t.Tileable (cells.toFinset : Set Cell)) where
  verify := regionVerify t
  computer := regionVerifierComputer t
  witnessBound := Polynomial.C 24 * Polynomial.X
  correct cells := by
    constructor
    · intro tileable
      obtain ⟨bits,bounded,checked⟩ := (FiniteVerifier.tileable_iff_certificate t cells).mp tileable
      refine ⟨bits,?_,checked⟩
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      exact bounded.trans (Nat.mul_le_mul_left _ (regionEncoding_length_ge cells))
    · rintro ⟨bits,_,checked⟩
      exact regionVerify_sound t cells bits checked

theorem region_inNP (t : Tromino) :
    InNP regionEncoding (fun cells => t.Tileable (cells.toFinset : Set Cell)) :=
  ⟨regionVerifier t⟩

end LeanTrominoes.Tromino.FiniteCoordinateColumns
