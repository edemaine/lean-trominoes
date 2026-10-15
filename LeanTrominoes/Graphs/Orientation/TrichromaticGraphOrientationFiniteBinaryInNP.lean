/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFiniteBinaryPrepare
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFiniteHardness

/-! # NP completeness under native binary graph records -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.BinaryVerifier
open _root_.Computability Turing Complexity

theorem binary_fields_length_ge (fields : List Nat) :
    fields.length≤(PeriodicCNFFlatEncoding.encodeNatFields fields).length := by
  rw [PeriodicCNFFlatEncoding.encodeNatFields_length]
  induction fields with
  | nil => simp
  | cons value rest ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem edgeCount_le_length (graph : Input) : graph.2.length≤(FlatEncoding.finEncoding.encode graph).length := by
  have fields := binary_fields_length_ge (FlatEncoding.fields graph)
  have length := FlatEncoding.fields_length graph
  change graph.2.length≤(PeriodicCNFFlatEncoding.encodeNatFields (FlatEncoding.fields graph)).length
  omega

def verifier : VerifierInPolyTime FlatEncoding.finEncoding FiniteProblem where
  verify graph bits := check (graph,bits)
  computer := by
    let finished := TM2CompositionMachine.computableInPolyTime BinaryVerifier.computer FiniteVerifier.booleanOutput
    exact FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime (finished.of_eq (fun _ => rfl))
  witnessBound := Polynomial.X
  correct graph := by
    constructor
    · intro accepted
      obtain ⟨bits,bounded,checked⟩ := (FiniteVerifier.finiteProblem_iff_certificate graph).mp accepted
      refine ⟨bits,by simpa using bounded.trans (edgeCount_le_length graph),?_⟩
      exact (check_correct _).mpr ((FiniteVerifier.check_correct _).mp checked)
    · rintro ⟨bits,_,checked⟩
      obtain ⟨wellFormed,zero,oriented⟩ := (check_correct _).mp checked
      exact ⟨wellFormed,zero,_,oriented⟩

end BinaryVerifier

theorem finiteProblem_inNP : Complexity.InNP FlatEncoding.finEncoding FiniteProblem := ⟨BinaryVerifier.verifier⟩

theorem finiteProblem_npComplete : Complexity.NPComplete FlatEncoding.finEncoding FiniteProblem :=
  ⟨finiteProblem_inNP,finiteProblem_npHard⟩

end LeanTrominoes.TrichromaticGraphOrientation
end
