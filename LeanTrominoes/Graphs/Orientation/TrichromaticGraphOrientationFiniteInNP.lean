/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFiniteCertificates

/-! # Finite orientation is in NP under lossless unary graph records -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open _root_.Computability Turing Complexity

def booleanOutput : TM2ComputableInPolyTime (fun bit : Bool => [bit])
    (primcodableFinEncoding Bool).encode id := by
  letI : Inhabited (primcodableFinEncoding Bool).Γ := ⟨PartrecToTM2.Γ'.cons⟩
  let physical := TM2PolyTimeInputEncodingTransport.of_prepare (fun bit : Bool => [bit])
    (FiniteBlockTransducer.computableInPolyTime (primcodableFinEncoding Bool).encode)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq physical (fun _ => by simp)

def verifier : VerifierInPolyTime UnaryEncoding.finEncoding FiniteProblem where
  verify graph bits := check (graph,bits)
  computer := by
    let finished := TM2CompositionMachine.computableInPolyTime FiniteVerifier.computer booleanOutput
    exact FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (finished.of_eq (fun _ => rfl))
  witnessBound := Polynomial.X
  correct graph := by
    constructor
    · intro accepted
      obtain ⟨bits,bound,checked⟩ := (finiteProblem_iff_certificate graph).mp accepted
      exact ⟨bits,by simpa using bound.trans (UnaryEncoding.edgeCount_le_length graph),checked⟩
    · rintro ⟨bits,_,checked⟩
      obtain ⟨wellFormed,zero,oriented⟩ := (check_correct _).mp checked
      exact ⟨wellFormed,zero,_,oriented⟩

end FiniteVerifier

theorem finiteProblem_unary_inNP : Complexity.InNP UnaryEncoding.finEncoding FiniteProblem :=
  ⟨FiniteVerifier.verifier⟩

end LeanTrominoes.TrichromaticGraphOrientation
end
