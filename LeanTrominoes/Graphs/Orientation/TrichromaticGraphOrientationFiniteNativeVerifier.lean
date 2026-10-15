/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFiniteCheckSemantics
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFiniteRecordSemantics
import LeanTrominoes.Computation.Encoding.Unary.UnaryAllOnesCompiler

/-! # An actual polynomial-time verifier on native unary graph records -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open Gadget Turing EncodedUnaryColumn

def checks (s : WitnessInput) : List Nat :=
  ((List.range s.1.1.length).map fun vertex => (vertexCheck s vertex).toNat) ++
    (((List.range (2*s.1.2.length)).map fun index =>
      (decide ((incidenceAt s.1 index).1<s.1.1.length)).toNat) ++
    ((List.range (2*s.1.2.length)).map fun index => (offsetCheck s index).toNat))

def check (s : WitnessInput) : Bool := UnaryAllOnes.allOnes (checks s)

def offsetChecksCompiler : Compiler encode (fun s : WitnessInput => List.range (2*s.1.2.length))
    (fun s index => (offsetCheck s index).toNat) := by
  let physical := multiply (offsetCheckCompiler 2) (offsetCheckCompiler 3)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro index _
  dsimp only
  dsimp only [offsetCheck]
  have product (a b : Bool) : a.toNat*b.toNat=(a && b).toNat := by cases a <;> cases b <;> rfl
  exact product _ _

def checksCompiler : TM2ComputableInPolyTime encode UnaryFieldEncoderMachine.unaryFields checks :=
  UnaryFieldClosure.appendCompiler encode _ _ vertexCheckCompiler
    (UnaryFieldClosure.appendCompiler encode _ _ endpointCheckCompiler offsetChecksCompiler)

def computer : TM2ComputableInPolyTime encode (fun bit => [bit]) check := by
  let physical := TM2CompositionMachine.computableInPolyTime checksCompiler UnaryAllOnes.compiler
  exact physical.of_eq (fun _ => rfl)

private theorem bool_nat_one (bit : Bool) : bit.toNat=1 ↔ bit=true := by cases bit <;> decide

theorem check_parts (s : WitnessInput) : check s=true ↔
    (∀ vertex < s.1.1.length, vertexCheck s vertex=true) ∧
    (∀ index < 2*s.1.2.length, (incidenceAt s.1 index).1<s.1.1.length) ∧
    (∀ index < 2*s.1.2.length, offsetCheck s index=true) := by
  simp only [check,UnaryAllOnes.allOnes,decide_eq_true_eq,checks,List.forall_mem_append,
    List.forall_mem_map,List.mem_range,bool_nat_one]

theorem check_correct (s : WitnessInput) : check s=true ↔
    IsWellFormed s.1 ∧ ZeroOffsets s.1 ∧ FiniteIsOrientation s.1 (fun edge => s.2.getD edge false) := by
  rw [check_parts,vertexCheck_correct,endpoint_checks_iff,offset_checks_iff]
  constructor
  · rintro ⟨⟨formed,counted⟩,bounds,zero⟩
    have wellFormed : IsWellFormed s.1 := ⟨bounds,formed⟩
    exact ⟨wellFormed,zero,(finiteIsOrientation_iff_counts _ wellFormed _).mpr counted⟩
  · rintro ⟨wellFormed,zero,oriented⟩
    exact ⟨⟨wellFormed.2,(finiteIsOrientation_iff_counts _ wellFormed _).mp oriented⟩,
      wellFormed.1,zero⟩

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
end
