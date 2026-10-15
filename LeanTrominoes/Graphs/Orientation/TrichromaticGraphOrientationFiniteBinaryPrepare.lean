/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFiniteBinaryFields
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFiniteInNP

/-! # Preparing normalized records and rejecting oversized binary fields -/
noncomputable section
namespace LeanTrominoes.TrichromaticGraphOrientation.BinaryVerifier
open _root_.Computability Turing EncodedUnaryColumn

def unaryTag (symbol : UnaryFieldEncoderMachine.Symbol) :
    List (Sum UnaryFieldEncoderMachine.Symbol (Option Bool)) := [.inl symbol]

def witnessProjection : Sum PeriodicCNFFlatEncoding.Symbol (Option Bool) →
    List (Sum UnaryFieldEncoderMachine.Symbol (Option Bool))
  | .inl _ => []
  | .inr bit => [.inr bit]

def prepareComputer : TM2ComputableInPolyTime encode FiniteVerifier.encode
    (fun s : WitnessInput => (normalize s.1,s.2)) := by
  let fields := TM2CompositionMachine.computableInPolyTime normalizedFieldsCompiler
    (TM2PolyTimeInputEncodingTransport.of_prepare UnaryFieldEncoderMachine.unaryFields
      (FiniteBlockTransducer.computableInPolyTime unaryTag) (fun _ => rfl) (fun _ => rfl))
  let witness := TM2PolyTimeInputEncodingTransport.of_prepare encode
    (FiniteBlockTransducer.computableInPolyTime witnessProjection) (fun _ => rfl) (fun _ => rfl)
  let physical := TM2ListAppend.computableInPolyTime fields witness
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  change (UnaryFieldEncoderMachine.unaryFields (FlatEncoding.fields (normalize s.1))).flatMap unaryTag ++
    (((PeriodicCNFFlatEncoding.encodeNatFields (FlatEncoding.fields s.1)).map Sum.inl) ++
      Sum.inr none::s.2.map (fun bit => Sum.inr (some bit))).flatMap witnessProjection =
    (UnaryFieldEncoderMachine.unaryFields (FlatEncoding.fields (normalize s.1))).map Sum.inl ++
      Sum.inr none::s.2.map (fun bit => Sum.inr (some bit))
  have tagged (symbols : List UnaryFieldEncoderMachine.Symbol) :
      symbols.flatMap unaryTag=symbols.map Sum.inl := by rw [List.map_eq_flatMap]; rfl
  have erased (symbols : List PeriodicCNFFlatEncoding.Symbol) :
      symbols.flatMap (fun _ => ([] : List (Sum UnaryFieldEncoderMachine.Symbol (Option Bool))))=[] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  rw [tagged]
  simp [witnessProjection,List.flatMap_map,erased]
  rw [List.map_eq_flatMap]

def fieldsSmall (graph : Input) : Bool := decide (∀ value ∈ FlatEncoding.fields graph, value<bound graph)

def fieldsSmallComputer : TM2ComputableInPolyTime encode (fun bit => [bit])
    (fun s : WitnessInput => fieldsSmall s.1) := by
  let values : Compiler encode decodedFields (fun _ value => value) :=
    decodedFieldsCompiler.of_eq (fun _ => by simp)
  let nonzero := sub (constant values 1) (zeroIndicator values)
  let physical := TM2CompositionMachine.computableInPolyTime nonzero UnaryAllOnes.compiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  unfold fieldsSmall UnaryAllOnes.allOnes
  congr 1
  apply propext
  have positive : 0<bound s.1 := by have := (bound_counts s.1).2.2; omega
  have capNonzero (value : Nat) :
      1-(decide (BinaryFieldBoundedDecoder.cap (bound s.1) value=0)).toNat=1 ↔ value<bound s.1 := by
    by_cases small : value<bound s.1 <;> simp [BinaryFieldBoundedDecoder.cap,small]
  simp only [decodedFields,List.map_map,Function.comp_def,List.forall_mem_map,
    List.forall_mem_append,List.forall_mem_cons,capNonzero]
  simp [positive]

def check (s : WitnessInput) : Bool := fieldsSmall s.1 && FiniteVerifier.check (normalize s.1,s.2)

def computer : TM2ComputableInPolyTime encode (fun bit => [bit]) check := by
  let normalized := TM2CompositionMachine.computableInPolyTime prepareComputer FiniteVerifier.computer
  let first : TM2ComputableInPolyTime encode id (fun s : WitnessInput => [fieldsSmall s.1]) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq fieldsSmallComputer (fun _ => rfl)
  let second : TM2ComputableInPolyTime encode id
      (fun s : WitnessInput => [FiniteVerifier.check (normalize s.1,s.2)]) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq normalized (fun _ => rfl)
  let physical := AlignedBooleanListClosure.combinedComputableInPolyTime encode .conjunction
    (fun s : WitnessInput => [fieldsSmall s.1])
    (fun s : WitnessInput => [FiniteVerifier.check (normalize s.1,s.2)])
    (fun _ => rfl) first second
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical (fun _ => rfl)

theorem check_correct (s : WitnessInput) : check s=true ↔
    IsWellFormed s.1 ∧ ZeroOffsets s.1 ∧ FiniteIsOrientation s.1 (fun edge => s.2.getD edge false) := by
  constructor
  · intro checked
    have h : fieldsSmall s.1=true ∧ FiniteVerifier.check (normalize s.1,s.2)=true := by
      simpa only [check,Bool.and_eq_true] using checked
    have small := of_decide_eq_true h.1
    have normalized := normalize_eq_of_bounded s.1 small
    rw [normalized] at h
    exact (FiniteVerifier.check_correct _).mp h.2
  · intro valid
    have accepted : FiniteProblem s.1 := ⟨valid.1,valid.2.1,_,valid.2.2⟩
    have small := finiteProblem_fields_bounded s.1 accepted
    simp only [check,fieldsSmall,decide_eq_true small,Bool.true_and,normalize_eq_of_bounded s.1 small]
    exact (FiniteVerifier.check_correct _).mpr valid

end LeanTrominoes.TrichromaticGraphOrientation.BinaryVerifier
end
