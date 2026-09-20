/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeSATThreePolyTimeColumns
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # A native flat-output polynomial-time 1D three-occurrence reduction -/
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanTrominoes.PeriodicThreeSATThree.PolyTime
open Computability Turing PeriodicCNF PeriodicCNF.UnaryProgramClauseProfile
open PeriodicCNF.SplitLiteralPrinter

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private theorem zip_projections {A B : Type} (ps : List (A × B)) :
    (ps.map Prod.fst).zip (ps.map Prod.snd)=ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

theorem clauses_nonempty [Inhabited encoding.Γ] (symbols : List encoding.Γ) :
    ∀ c∈(formula decider symbols).clauses,c≠[] := by
  intro c hc eq
  subst c
  have h : [] ∈ (formula decider symbols).clauses.map (List.map LiteralProfile.ofLiteral) :=
    List.mem_map.mpr ⟨[],hc,rfl⟩
  rw [← profiles_correct] at h
  obtain ⟨p,_,eq⟩ := List.mem_map.mp h
  cases p <;> simp [ClauseProfile.literals] at eq

def body (symbols : List encoding.Γ) : List UnaryProgramTokens.Token :=
  (records (formula decider symbols)).flatMap (fun p => literalBlock p.1 p.2)

noncomputable def bodyComputableInPolyTime [Inhabited encoding.Γ] : TM2ComputableInPolyTime id id (body decider) := by
  let physical := assembleComputableInPolyTime id (metadata decider) (atoms decider) (aligned decider)
    (metadataComputableInPolyTime decider) (atomsComputableInPolyTime decider)
  refine TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical ?_
  intro symbols
  rw [metadata_correct,atoms,← records_atoms,zip_projections]
  rfl

noncomputable def fieldsComputableInPolyTime [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => PeriodicCNFFlatEncoding.formulaFields (formula decider symbols)) := by
  let physical := TM2CompositionMachine.computableInPolyTime (bodyComputableInPolyTime decider)
    UnaryProgramTokenFinalizer.countAndFinalizeComputableInPolyTime
  refine TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical ?_
  intro symbols
  exact finalize_records _ (clauses_nonempty decider symbols)
    (Numeric.width_three _ (PeriodicCNFStripReduction.formulaOfSymbols_widthAtMostThree decider symbols))
    (Numeric.forward _ (PeriodicCNFStripReduction.formulaOfSymbols_isForwardLocal decider symbols))

noncomputable def formulaComputableInPolyTimeOfInhabited [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id PeriodicCNFFlatEncoding.finEncoding.encode (formula decider) := by
  let physical := TM2CompositionMachine.computableInPolyTime (fieldsComputableInPolyTime decider)
    UnaryFieldEncoderMachine.computableInPolyTime
  refine TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical ?_
  intro symbols
  exact PolySpaceNativeCompiler.trList_formulaFields_eq_finEncoding_encode _

noncomputable def formulaComputableInPolyTime :
    TM2ComputableInPolyTime id PeriodicCNFFlatEncoding.finEncoding.encode (formula decider) := by
  classical
  by_cases nonemptyAlphabet : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact formulaComputableInPolyTimeOfInhabited decider
  · letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    letI : Inhabited PeriodicCNFFlatEncoding.finEncoding.Γ := ⟨.bit0⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      PeriodicCNFFlatEncoding.finEncoding.encode (formula decider)

end LeanTrominoes.PeriodicThreeSATThree.PolyTime
end
