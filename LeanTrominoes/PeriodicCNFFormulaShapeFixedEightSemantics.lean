/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightData
import LeanTrominoes.PeriodicEightOccurrenceSplitExactVariableCount
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Exact semantics of fixed-eight formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFixedEight

open UnaryProgramClauseProfile
open ClauseProfileOccurrenceSplit

/-- Fixed-slot occurrence renaming preserves every literal's polarity and
current/next-slice offset profile. -/
@[simp] theorem literalProfiles_occurrenceClause
    {Variable : Type}
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts)
    (clauseIndex : Nat) (clause : PeriodicClause Variable) :
    literalProfiles
        (PeriodicEightOccurrenceSplit.occurrenceClause
          occurrencePorts clauseIndex clause) =
      literalProfiles clause := by
  unfold literalProfiles
    PeriodicEightOccurrenceSplit.occurrenceClause
    PeriodicEightOccurrenceSplit.occurrenceLiteral
  rw [List.map_map]
  calc
    clause.zipIdx.map
          ((fun literal =>
            ({ nextSlice := decide
                (literal.offset = ((1, 0) : Cell))
               value := literal.value } : LiteralProfile)) ∘
            fun tagged =>
              PeriodicEightOccurrenceSplit.occurrenceLiteral
                occurrencePorts clauseIndex tagged.2 tagged.1) =
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

@[simp] theorem occurrenceClauses_literalProfiles
    {Variable : Type} (source : PeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts) :
    (PeriodicEightOccurrenceSplit.occurrenceClauses
        source occurrencePorts).map literalProfiles =
      source.clauses.map literalProfiles := by
  unfold PeriodicEightOccurrenceSplit.occurrenceClauses
  rw [List.map_map]
  calc
    source.clauses.zipIdx.map
          (fun tagged => literalProfiles
            (PeriodicEightOccurrenceSplit.occurrenceClause
              occurrencePorts tagged.2 tagged.1)) =
        source.clauses.zipIdx.map
          (fun tagged => literalProfiles tagged.1) := by
      apply List.map_congr_left
      intro tagged _
      exact literalProfiles_occurrenceClause
        occurrencePorts tagged.2 tagged.1
    _ = source.clauses.map literalProfiles := by
      have functionEq :
          (fun tagged : PeriodicClause Variable × Nat =>
            literalProfiles tagged.1) = literalProfiles ∘ Prod.fst := by
        funext tagged
        rfl
      rw [functionEq]
      simpa only [List.map_map] using congrArg (List.map literalProfiles)
        (List.zipIdx_map_fst 0 source.clauses)

/-- Every clause in one fixed ring has the common implication profile. -/
theorem cycleClausesFor_literalProfiles
    {Variable : Type} (atom : Variable) :
    ∀ clause ∈ PeriodicEightOccurrenceSplit.cycleClausesFor atom,
      literalProfiles clause =
        ClauseProfileOccurrenceSplit.implicationProfile.literals := by
  exact ClauseProfileOccurrenceSplit.cycleClauses_literalProfiles
    (PeriodicEightOccurrenceSplit.copies atom)

@[simp] theorem allCycleClauses_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicEightOccurrenceSplit.allCycleClauses source).length =
      copiesPerVariable * source.variableOccurrences.dedup.length := by
  calc
    (PeriodicEightOccurrenceSplit.allCycleClauses source).length =
        (PeriodicEightOccurrenceSplit.allCopies source).length := by
      unfold PeriodicEightOccurrenceSplit.allCycleClauses
        PeriodicEightOccurrenceSplit.allCopies
        PeriodicEightOccurrenceSplit.cycleClausesFor
      rw [List.length_flatMap, List.length_flatMap]
      simp_rw [PeriodicThreeSATThree.cycleClauses_length]
    _ = copiesPerVariable * source.variableOccurrences.dedup.length :=
      PeriodicEightOccurrenceSplit.allCopies_length source

/-- The complete fixed-ring suffix has one identical implication profile per
output copy. -/
theorem allCycleClauses_literalProfiles
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicEightOccurrenceSplit.allCycleClauses source).map
        literalProfiles =
      List.replicate
        (copiesPerVariable * source.variableOccurrences.dedup.length)
        ClauseProfileOccurrenceSplit.implicationProfile.literals := by
  calc
    (PeriodicEightOccurrenceSplit.allCycleClauses source).map
          literalProfiles =
        List.replicate
          (PeriodicEightOccurrenceSplit.allCycleClauses source).length
          ClauseProfileOccurrenceSplit.implicationProfile.literals := by
      have constant :
          (PeriodicEightOccurrenceSplit.allCycleClauses source).map
                literalProfiles =
            List.replicate
              ((PeriodicEightOccurrenceSplit.allCycleClauses source).map
                literalProfiles).length
              ClauseProfileOccurrenceSplit.implicationProfile.literals := by
        apply List.eq_replicate_length.mpr
        intro profile member
        rcases List.mem_map.mp member with
          ⟨clause, clauseMember, rfl⟩
        unfold PeriodicEightOccurrenceSplit.allCycleClauses at clauseMember
        rcases List.mem_flatMap.mp clauseMember with
          ⟨atom, _, cycleMember⟩
        exact cycleClausesFor_literalProfiles atom clause cycleMember
      simpa using constant
    _ = List.replicate
          (copiesPerVariable * source.variableOccurrences.dedup.length)
          ClauseProfileOccurrenceSplit.implicationProfile.literals := by
      rw [allCycleClauses_length]

/-- The semantic fixed-eight formula copies every source profile and appends
the common nine-ring implication profiles. -/
theorem formula_literalProfiles
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts) :
    (PeriodicEightOccurrenceSplit.formula
        source occurrencePorts).clauses.map literalProfiles =
      source.clauses.map literalProfiles ++
        List.replicate
          (copiesPerVariable * source.variableOccurrences.dedup.length)
          ClauseProfileOccurrenceSplit.implicationProfile.literals := by
  unfold PeriodicEightOccurrenceSplit.formula
  rw [List.map_append, occurrenceClauses_literalProfiles,
    allCycleClauses_literalProfiles]

/-- An exact input formula shape becomes the exact semantic fixed-eight
clause-and-variable shape. -/
theorem shape_correct
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts)
    (sourceShape : List FormulaShape.Token)
    (sourceClausesCorrect :
      (FormulaShape.clauseProfiles sourceShape).map
          ClauseProfile.literals =
        source.clauses.map literalProfiles)
    (sourceVariablesCorrect :
      FormulaShape.variableCount sourceShape =
        source.variableOccurrences.dedup.length) :
    (FormulaShape.clauseProfiles (shape sourceShape)).map
          ClauseProfile.literals =
        (PeriodicEightOccurrenceSplit.formula
          source occurrencePorts).clauses.map literalProfiles ∧
      FormulaShape.variableCount (shape sourceShape) =
        (PeriodicCNF.variableOccurrences
          (PeriodicEightOccurrenceSplit.formula
            source occurrencePorts)).dedup.length := by
  constructor
  · rw [clauseProfiles_shape, List.map_append,
      cycleProfiles_eq_replicate, List.map_replicate,
      sourceVariablesCorrect, sourceClausesCorrect,
      formula_literalProfiles]
  · rw [variableCount_shape, sourceVariablesCorrect,
      PeriodicEightOccurrenceSplit.formula_variableOccurrences_dedup_length]

end FormulaShapeFixedEight
end PeriodicCNF
end LeanTrominoes
