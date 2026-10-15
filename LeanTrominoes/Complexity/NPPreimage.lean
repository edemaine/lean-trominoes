/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.NP
import LeanTrominoes.Computation.TM2.TM2ForkMachineTime
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.Computation.TM2.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Pulling NP verifiers back through polynomial-time machines

The new verifier computes the reduction while retaining the certificate.
Its witness polynomial composes the target bound with the machine's proved
output-length polynomial.
-/
noncomputable section
namespace LeanTrominoes.Complexity
open _root_.Computability Turing

variable {A B : Type} {ea : FiniteEncoding A} {eb : FiniteEncoding B}
  [Inhabited ea.Γ] [Inhabited eb.Γ]

private def inputSymbol : Sum ea.Γ (Option Bool) → List ea.Γ
  | .inl s => [s]
  | .inr _ => []

private def certificateSymbol : Sum ea.Γ (Option Bool) → List Bool
  | .inl _ => []
  | .inr none => []
  | .inr (some b) => [b]

private def projectInput : TM2ComputableInPolyTime (encodeWitness ea) ea.encode
    (fun p : A × List Bool => p.1) := by
  letI : Fintype ea.Γ := ea.ΓFin
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare (encodeWitness ea)
    (FiniteBlockTransducer.computableInPolyTime (inputSymbol (ea := ea)))
    (fun _ => rfl) (fun _ => rfl)
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared
  intro p
  simp [encodeWitness,List.flatMap_map,inputSymbol]

private def projectCertificate : TM2ComputableInPolyTime (encodeWitness ea) id
    (fun p : A × List Bool => p.2) := by
  letI : Fintype ea.Γ := ea.ΓFin
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare (encodeWitness ea)
    (FiniteBlockTransducer.computableInPolyTime (certificateSymbol (ea := ea)))
    (fun _ => rfl) (fun _ => rfl)
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared
  intro p
  simp [encodeWitness,List.flatMap_map,certificateSymbol]

private def witnessSymbol : SeparatedProductEncoding.Token eb.Γ Bool →
    List (Sum eb.Γ (Option Bool))
  | .left s => [.inl s]
  | .separator => [.inr none]
  | .right b => [.inr (some b)]

/-- Run the reduction on the input and preserve every certificate bit. -/
def witnessReductionComputer {f : A → B}
    (computer : TM2ComputableInPolyTime ea.encode eb.encode f) :
    TM2ComputableInPolyTime (encodeWitness ea) (encodeWitness eb)
      (fun p : A × List Bool => (f p.1,p.2)) := by
  letI : Fintype ea.Γ := ea.ΓFin
  letI : Fintype eb.Γ := eb.ΓFin
  let reduced := TM2CompositionMachine.computableInPolyTime projectInput computer
  let paired := TM2ForkMachine.computableInPolyTime reduced projectCertificate
  let tagger := TM2PolyTimeInputEncodingTransport.of_prepare
    (SeparatedProductEncoding.encode eb.encode id)
    (FiniteBlockTransducer.computableInPolyTime (witnessSymbol (eb := eb)))
    (fun _ => rfl) (fun _ => rfl)
  let tagged := TM2CompositionMachine.computableInPolyTime paired tagger
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq tagged
  intro p
  simp [SeparatedProductEncoding.encode,encodeWitness,List.flatMap_map,
    witnessSymbol,← List.map_eq_flatMap]

/-- Pull back a verifier that is sound on certificates of every length.
The polynomial bound is needed only for completeness. -/
def VerifierInPolyTime.preimage {language : B → Prop} {f : A → B}
    (verifier : VerifierInPolyTime eb language)
    (sound : ∀ b bits, verifier.verify b bits = true → language b)
    (computer : TM2ComputableInPolyTime ea.encode eb.encode f) :
    VerifierInPolyTime ea (fun a => language (f a)) where
  verify a bits := verifier.verify (f a) bits
  computer := FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
    (TM2CompositionMachine.computableInPolyTime (witnessReductionComputer computer)
      verifier.computer.toTM2ComputableInPolyTime)
  witnessBound := verifier.witnessBound.comp (TM2OutputLength.outputLengthPolynomial computer)
  correct a := by
    constructor
    · intro h
      obtain ⟨bits,bound,checked⟩ := (verifier.correct (f a)).mp h
      refine ⟨bits,bound.trans ?_,checked⟩
      rw [Polynomial.eval_comp]
      exact TM2CompositionMachine.polynomial_eval_monotone verifier.witnessBound
        (TM2OutputLength.output_length_le_polynomial_eval computer a)
    · rintro ⟨bits,_,checked⟩
      exact sound (f a) bits checked

end LeanTrominoes.Complexity
