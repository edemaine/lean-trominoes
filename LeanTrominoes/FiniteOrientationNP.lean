/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteOrientationEncoding
import LeanTrominoes.FiniteGadgetRegionCompiler
import LeanTrominoes.FiniteTrominoRegionInNP
import LeanTrominoes.NPPreimage

/-! # NP membership for finite normalized orientation drawings -/
noncomputable section
namespace LeanTrominoes.Gadget.FiniteOrientation
open _root_.Computability Turing Complexity

def regionComputer : TM2ComputableInPolyTime finEncoding.encode
    Tromino.FiniteCoordinateColumns.regionEncoding.encode region := by
  letI : Inhabited finEncoding.Γ := ⟨GadgetSparseAssignmentTokens.Token.fieldEnd⟩
  let emitter : TM2ComputableInPolyTime finEncoding.encode id
      (fun input => GadgetSparseAssignmentTokens.assignmentsTokens (entries input.1)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare finEncoding.encode
      (FiniteBlockTransducer.computableInPolyTime (fun symbol => [symbol]))
      (fun _ => rfl) (fun _ => by simp [finEncoding])
  exact FiniteRegionCompiler.computableInPolyTime .I emitter nonnegative

def verifier : VerifierInPolyTime finEncoding Problem := by
  letI : Inhabited finEncoding.Γ := ⟨GadgetSparseAssignmentTokens.Token.fieldEnd⟩
  letI : Inhabited Tromino.FiniteCoordinateColumns.regionEncoding.Γ :=
    ⟨Tromino.FiniteCoordinateColumns.Token.bit false⟩
  let pulled := (Tromino.FiniteCoordinateColumns.regionVerifier .I).preimage
    (Tromino.FiniteCoordinateColumns.regionVerifier_sound .I) regionComputer
  exact { pulled with correct := fun input => (problem_iff input).trans (pulled.correct input) }

theorem inNP : InNP finEncoding Problem := ⟨verifier⟩

end LeanTrominoes.Gadget.FiniteOrientation
