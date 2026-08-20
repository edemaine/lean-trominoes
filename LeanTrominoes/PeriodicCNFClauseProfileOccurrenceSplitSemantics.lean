/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitData
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileSemantics
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Semantic correctness of finite clause-profile occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileOccurrenceSplit

open UnaryProgramClauseProfile

def literalProfiles {Variable : Type}
    (clause : PeriodicClause Variable) : List LiteralProfile :=
  clause.map fun literal =>
    { nextSlice := decide (literal.offset = ((1, 0) : Cell))
      value := literal.value }

@[simp] theorem literalProfiles_implicationClause
    {Variable : Type} (first second : ThreeOccurrenceVariable Variable) :
    literalProfiles
        (PeriodicThreeSATThree.implicationClause first second) =
      implicationProfile.literals := by
  simp [literalProfiles, PeriodicThreeSATThree.implicationClause,
    implicationProfile, ClauseProfile.literals, current]

@[simp] theorem literalProfiles_occurrenceClause
    {Variable : Type} (clauseIndex : Nat)
    (clause : PeriodicClause Variable) :
    literalProfiles
        (PeriodicThreeSATThree.occurrenceClause clauseIndex clause) =
      literalProfiles clause := by
  unfold literalProfiles PeriodicThreeSATThree.occurrenceClause
    PeriodicThreeSATThree.occurrenceLiteral
  rw [List.map_map]
  calc
    clause.zipIdx.map
          ((fun literal =>
            ({ nextSlice := decide
                (literal.offset = ((1, 0) : Cell))
               value := literal.value } : LiteralProfile)) ∘
            fun tagged =>
              PeriodicThreeSATThree.occurrenceLiteral
                clauseIndex tagged.2 tagged.1) =
        clause.zipIdx.map (fun tagged =>
          ({ nextSlice := decide
              (tagged.1.offset = ((1, 0) : Cell))
             value := tagged.1.value } : LiteralProfile)) := by
      apply List.map_congr_left
      rintro ⟨literal, literalIndex⟩ _
      rfl
    _ = clause.map (fun literal =>
          ({ nextSlice := decide
              (literal.offset = ((1, 0) : Cell))
             value := literal.value } : LiteralProfile)) := by
      let profile := fun literal : PeriodicLiteral Variable =>
          ({ nextSlice := decide
              (literal.offset = ((1, 0) : Cell))
             value := literal.value } : LiteralProfile)
      have functionEq :
          (fun tagged : PeriodicLiteral Variable × Nat =>
            profile tagged.1) = profile ∘ Prod.fst := by
        funext tagged
        rfl
      rw [functionEq]
      simpa only [List.map_map] using congrArg
        (List.map profile) (List.zipIdx_map_fst 0 clause)

theorem cycleFrom_literalProfiles
    {Variable : Type}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ PeriodicThreeSATThree.cycleFrom first current rest,
      literalProfiles clause = implicationProfile.literals := by
  induction rest generalizing current with
  | nil =>
      intro clause member
      simp only [PeriodicThreeSATThree.cycleFrom,
        List.mem_singleton] at member
      subst clause
      exact literalProfiles_implicationClause current first
  | cons next rest induction =>
      intro clause member
      simp only [PeriodicThreeSATThree.cycleFrom,
        List.mem_cons] at member
      rcases member with rfl | member
      · exact literalProfiles_implicationClause current next
      · exact induction next clause member

theorem cycleClauses_literalProfiles
    {Variable : Type}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ PeriodicThreeSATThree.cycleClauses copies,
      literalProfiles clause = implicationProfile.literals := by
  cases copies with
  | nil => simp [PeriodicThreeSATThree.cycleClauses]
  | cons first rest =>
      exact cycleFrom_literalProfiles first first rest

theorem allCycleClauses_literalProfiles
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicThreeSATThree.allCycleClauses source).map literalProfiles =
      List.replicate (PeriodicCNF.presentationLiteralCount source)
        implicationProfile.literals := by
  calc
    (PeriodicThreeSATThree.allCycleClauses source).map literalProfiles =
        List.replicate
          (PeriodicThreeSATThree.allCycleClauses source).length
          implicationProfile.literals := by
      have constant :
          (PeriodicThreeSATThree.allCycleClauses source).map
              literalProfiles =
            List.replicate
              ((PeriodicThreeSATThree.allCycleClauses source).map
                literalProfiles).length
              implicationProfile.literals := by
        apply List.eq_replicate_length.mpr
        intro profile member
        obtain ⟨clause, clauseMember, rfl⟩ := List.mem_map.mp member
        unfold PeriodicThreeSATThree.allCycleClauses at clauseMember
        obtain ⟨atom, _, cycleMember⟩ := List.mem_flatMap.mp clauseMember
        exact cycleClauses_literalProfiles
          (PeriodicThreeSATThree.occurrenceVariables source atom)
          clause cycleMember
      simpa using constant
    _ = List.replicate (PeriodicCNF.presentationLiteralCount source)
          implicationProfile.literals := by
      rw [PeriodicThreeSATThree.allCycleClauses_length]

@[simp] theorem occurrenceClauses_literalProfiles
    {Variable : Type} (source : PeriodicCNF Variable) :
    (PeriodicThreeSATThree.occurrenceClauses source).map literalProfiles =
      source.clauses.map literalProfiles := by
  unfold PeriodicThreeSATThree.occurrenceClauses
  rw [List.map_map]
  calc
    source.clauses.zipIdx.map
          (fun tagged => literalProfiles
            (PeriodicThreeSATThree.occurrenceClause
              tagged.2 tagged.1)) =
        source.clauses.zipIdx.map
          (fun tagged => literalProfiles tagged.1) := by
      apply List.map_congr_left
      intro tagged _
      exact literalProfiles_occurrenceClause tagged.2 tagged.1
    _ = source.clauses.map literalProfiles := by
      have functionEq :
          (fun tagged : PeriodicClause Variable × Nat =>
            literalProfiles tagged.1) = literalProfiles ∘ Prod.fst := by
        funext tagged
        rfl
      rw [functionEq]
      simpa only [List.map_map] using congrArg (List.map literalProfiles)
        (List.zipIdx_map_fst 0 source.clauses)

/-- At the profile-of-literals interface, occurrence splitting copies every
source clause and then appends one identical implication profile per source
literal. -/
theorem formula_literalProfiles
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicThreeSATThree.formula source).clauses.map literalProfiles =
      source.clauses.map literalProfiles ++
        List.replicate (PeriodicCNF.presentationLiteralCount source)
          implicationProfile.literals := by
  unfold PeriodicThreeSATThree.formula
  rw [List.map_append, occurrenceClauses_literalProfiles,
    allCycleClauses_literalProfiles]

/-- Any exact finite profile stream is transformed into the exact semantic
occurrence-split clause-profile stream. -/
theorem profiles_literals_eq_formula
    {Variable : Type} [DecidableEq Variable]
    (sourceProfiles : List ClauseProfile)
    (source : PeriodicCNF Variable)
    (sourceCorrect :
      sourceProfiles.map ClauseProfile.literals =
        source.clauses.map literalProfiles) :
    (profiles sourceProfiles).map ClauseProfile.literals =
      (PeriodicThreeSATThree.formula source).clauses.map
        literalProfiles := by
  have literalCount :
      (sourceProfiles.map fun profile => profile.literals.length).sum =
        PeriodicCNF.presentationLiteralCount source := by
    have lengths := congrArg (fun clauses =>
      (clauses.map List.length).sum) sourceCorrect
    calc
      (sourceProfiles.map fun profile => profile.literals.length).sum =
          ((sourceProfiles.map ClauseProfile.literals).map
            List.length).sum := by
        rw [List.map_map]
        rfl
      _ = ((source.clauses.map literalProfiles).map List.length).sum :=
        lengths
      _ = PeriodicCNF.presentationLiteralCount source := by
        have profileLength :
            List.length ∘
                (literalProfiles : PeriodicClause Variable →
                  List LiteralProfile) =
              List.length := by
          funext clause
          simp [literalProfiles]
        rw [List.map_map, profileLength]
        simp [PeriodicCNF.presentationLiteralCount]
  rw [formula_literalProfiles]
  unfold profiles
  rw [List.map_append, sourceCorrect, cycleProfiles_eq_replicate,
    List.map_replicate, literalCount]

end ClauseProfileOccurrenceSplit
end PeriodicCNF
end LeanTrominoes
