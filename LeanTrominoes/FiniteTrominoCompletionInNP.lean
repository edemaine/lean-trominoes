/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoRegionInNP

/-! # Finite-preplacement completion is in NP with a listed bounding box

The input encoding lists the canonical witness box as well as the preplacements.
Its size therefore charges for the bounding box, as required by the polynomial
bounding-box qualification of the finite completion theorem.
-/
noncomputable section
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing
open Complexity FiniteWitness

def completionFootprints (t : Tromino) (prefill : List (Placement Unit)) : List (Finset Cell) :=
  prefill.map fun p => p.cells (fun _ => t.cells)

def completionView (t : Tromino) (prefill : List (Placement Unit)) : Input where
  cells := boxList (radius (completionFootprints t prefill).toFinset)
  prefill := prefill

def completionEncoding (t : Tromino) : FinEncoding (List (Placement Unit)) where
  Γ := Token
  ΓFin := inferInstance
  encode prefill := encodeInput (completionView t prefill)
  decode source := (decodeInput source).map Input.prefill
  decode_encode prefill := by simp [completionView]

private def completionWitnessInput (t : Tromino) :
    TM2ComputableInPolyTime (encodeWitness (completionEncoding t)) encode
      (fun input => (completionView t input.1,input.2)) := by
  letI : Inhabited (completionEncoding t).Γ := ⟨Token.bit false⟩
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare (encodeWitness (completionEncoding t))
    (FiniteBlockTransducer.computableInPolyTime witnessToken)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared (fun input => by
    change ((encodeInput (completionView t input.1)).map Sum.inl ++
      Sum.inr none :: input.2.map (fun b => Sum.inr (some b))).flatMap witnessToken = _
    exact witnessToken_encoded _ _)

private def completionVerify (t : Tromino) (prefill : List (Placement Unit)) (bits : List Bool) : Bool :=
  FiniteExactCoverVerifier.check false (geometricRequest t (completionView t prefill,bits))

private def completionVerifierComputer (t : Tromino) :
    FiniteAlphabetComputableInPolyTime (encodeWitness (completionEncoding t))
      (primcodableFinEncoding Bool).encode
      (fun input => completionVerify t input.1 input.2) := by
  let native := TM2CompositionMachine.computableInPolyTime (completionWitnessInput t)
    (nativeComputableInPolyTime false t)
  let finished := TM2CompositionMachine.computableInPolyTime native booleanOutput
  exact FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
    (finished.of_eq (fun _ => rfl))

theorem encodeInput_length_ge_cells (input : Input) :
    input.cells.length≤(encodeInput input).length := by
  simp [encodeInput,fields,values,UnaryFieldEncoderMachine.unaryFields_length]
  omega

/-- The polynomial witness budget counts the box already listed in the input. -/
def completionVerifier (t : Tromino) :
    VerifierInPolyTime (completionEncoding t)
      (fun prefill => t.Completable Set.univ ((completionFootprints t prefill).toFinset : Set (Finset Cell))) where
  verify := completionVerify t
  computer := completionVerifierComputer t
  witnessBound := Polynomial.C 24 * Polynomial.X
  correct prefill := by
    have characterization := FiniteVerifier.completion_iff_bounded_certificate t (completionFootprints t prefill)
    constructor
    · intro completable
      obtain ⟨bits,bounded,checked⟩ := characterization.mp completable
      refine ⟨bits,?_,checked⟩
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      have listed := encodeInput_length_ge_cells (completionView t prefill)
      have size : (2*radius (completionFootprints t prefill).toFinset+1)^2≤
          ((completionEncoding t).encode prefill).length := by
        simpa [completionView,completionEncoding] using listed
      exact bounded.trans (Nat.mul_le_mul_left _ size)
    · rintro ⟨bits,_,checked⟩
      have valid := ((FiniteVerifier.check_correct false t
        (completionView t prefill).cells (completionFootprints t prefill) bits).mp checked).1
      exact completion_of_witness t (by simpa [completionView] using valid)

theorem completion_inNP (t : Tromino) :
    InNP (completionEncoding t)
      (fun prefill => t.Completable Set.univ ((completionFootprints t prefill).toFinset : Set (Finset Cell))) :=
  ⟨completionVerifier t⟩

end LeanTrominoes.Tromino.FiniteCoordinateColumns
