/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreeNumeric
import LeanTrominoes.PeriodicThreeSATThreePolyTimeCompiler
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineProfileSemantics

/-! # Compiled finite metadata for the numeric exact-one hardness reduction -/
noncomputable section
namespace LeanTrominoes.PeriodicOneInThree.PolyTime
open Turing PeriodicCNF PeriodicCNF.UnaryProgramClauseProfile
open PeriodicCNF.SplitLiteralPrinter
set_option maxHeartbeats 1000000

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance exactOneProfilesStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def source (symbols : List encoding.Γ) := PeriodicThreeSATThree.PolyTime.formula decider symbols

def formula (symbols : List encoding.Γ) := Numeric.formula (source decider symbols)

def profiles (symbols : List encoding.Γ) : List ClauseProfile :=
  (PeriodicThreeSATThree.PolyTime.profiles decider symbols).flatMap ClauseProfileFigureNine.oneInThreeProfiles

private theorem renamed_profiles {V : Type} (g : V → Nat) (f : PeriodicCNF V) :
    (f.rename g).clauses.map (List.map LiteralProfile.ofLiteral) =
      f.clauses.map ClauseProfileOccurrenceSplit.literalProfiles := by
  simp only [PeriodicCNF.rename,List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_def,PeriodicCNF.renameClause,List.map_map]
  rfl

variable [Inhabited encoding.Γ]

theorem profiles_correct (symbols : List encoding.Γ) :
    (profiles decider symbols).map ClauseProfile.literals =
      (formula decider symbols).clauses.map (List.map LiteralProfile.ofLiteral) := by
  have base := PeriodicThreeSATThree.PolyTime.profiles_correct decider symbols
  have transformed := ClauseProfileFigureNine.oneInThree_profiles_literals_eq_formula
    (source decider symbols) (PeriodicThreeSATThree.PolyTime.profiles decider symbols) base
  have renamed : (formula decider symbols).clauses.map (List.map LiteralProfile.ofLiteral) =
      (PeriodicOneInThree.formula (source decider symbols)).clauses.map
        ClauseProfileOccurrenceSplit.literalProfiles :=
    renamed_profiles (Numeric.atomMap (source decider symbols))
      (PeriodicOneInThree.formula (source decider symbols))
  rw [renamed]
  exact transformed

noncomputable def profilesComputableInPolyTime : TM2ComputableInPolyTime id id (profiles decider) := by
  let result := TM2CompositionMachine.computableInPolyTime
    (PeriodicThreeSATThree.PolyTime.profilesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime ClauseProfileFigureNine.oneInThreeProfiles)
  exact result

def metadata (symbols : List encoding.Γ) : List Metadata :=
  (profiles decider symbols).flatMap (fun p => clauseMetadata p.literals)

theorem metadata_correct (symbols : List encoding.Γ) :
    metadata decider symbols = (records (formula decider symbols)).map Prod.fst := by
  rw [records_metadata]
  have h := congrArg (List.flatMap clauseMetadata) (profiles_correct decider symbols)
  simpa only [List.flatMap_map,metadata] using h

noncomputable def metadataComputableInPolyTime : TM2ComputableInPolyTime id id (metadata decider) := by
  let result := TM2CompositionMachine.computableInPolyTime (profilesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime fun p : ClauseProfile => clauseMetadata p.literals)
  exact result

def atoms (symbols : List encoding.Γ) := (formula decider symbols).variableOccurrences

theorem aligned (symbols : List encoding.Γ) :
    (metadata decider symbols).length = (atoms decider symbols).length := by
  rw [metadata_correct,atoms,← records_atoms]
  simp only [List.length_map]

theorem clauses_nonempty (symbols : List encoding.Γ) :
    ∀ c∈(formula decider symbols).clauses,c≠[] := by
  intro c hc eq
  subst c
  have h : [] ∈ (formula decider symbols).clauses.map (List.map LiteralProfile.ofLiteral) :=
    List.mem_map.mpr ⟨[],hc,rfl⟩
  rw [← profiles_correct] at h
  obtain ⟨p,_,eq⟩ := List.mem_map.mp h
  cases p <;> simp [ClauseProfile.literals] at eq

end LeanTrominoes.PeriodicOneInThree.PolyTime
