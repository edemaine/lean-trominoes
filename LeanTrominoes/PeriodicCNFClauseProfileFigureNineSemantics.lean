/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineData
import LeanTrominoes.PeriodicOneInThreeNoUnits

/-! # Exact Figure 9 clause-arity semantics -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileFigureNine

open UnaryProgramClauseArity
open UnaryProgramClauseProfile

/-- The finite first-stage table agrees with the clauses emitted by the
Figure 9 disjunction gadget. -/
theorem oneInThree_clauseClauses_lengths
    {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (profile : ClauseProfile)
    (lengthEq : source.length = profile.literals.length) :
    (PeriodicOneInThree.clauseClauses clauseIndex source).map List.length =
      (oneInThreeArities profile).map Arity.value := by
  cases profile with
  | unary literalProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals] at lengthEq
      · cases rest with
        | nil =>
            simp [PeriodicOneInThree.clauseClauses,
              PeriodicOneInThree.disjunctionGadget,
              PeriodicOneInThree.forcePaddingFalse,
              oneInThreeArities, Arity.value]
        | cons second tail =>
            simp [ClauseProfile.literals] at lengthEq
  | binary firstProfile secondProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals] at lengthEq
      · cases rest with
        | nil =>
            simp [ClauseProfile.literals] at lengthEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp [PeriodicOneInThree.clauseClauses,
                  PeriodicOneInThree.disjunctionGadget,
                  PeriodicOneInThree.forcePaddingFalse,
                  oneInThreeArities, Arity.value]
            | cons third tail =>
                simp [ClauseProfile.literals] at lengthEq
  | ternary firstProfile secondProfile thirdProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals] at lengthEq
      · cases rest with
        | nil =>
            simp [ClauseProfile.literals] at lengthEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp [ClauseProfile.literals] at lengthEq
            | cons third tail =>
                cases tail with
                | nil =>
                    simp [PeriodicOneInThree.clauseClauses,
                      PeriodicOneInThree.disjunctionGadget,
                      oneInThreeArities, Arity.value]
                | cons fourth tail =>
                    simp [ClauseProfile.literals] at lengthEq

/-- The finite second-stage table agrees with unit-clause elimination. -/
theorem noUnit_clauseClauses_lengths
    {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (arity : Arity)
    (lengthEq : source.length = arity.value) :
    (PeriodicOneInThreeNoUnits.clauseClauses
        clauseIndex source).map List.length =
      (noUnitArities arity).map Arity.value := by
  cases arity with
  | unary =>
      rcases source with _ | ⟨first, rest⟩
      · simp [Arity.value] at lengthEq
      · cases rest with
        | nil =>
            simp [PeriodicOneInThreeNoUnits.clauseClauses,
              noUnitArities, Arity.value]
        | cons second tail =>
            simp [Arity.value] at lengthEq
  | binary =>
      rcases source with _ | ⟨first, rest⟩
      · simp [Arity.value] at lengthEq
      · cases rest with
        | nil =>
            simp [Arity.value] at lengthEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp [PeriodicOneInThreeNoUnits.clauseClauses,
                  noUnitArities, Arity.value]
            | cons third tail =>
                simp [Arity.value] at lengthEq
  | ternary =>
      rcases source with _ | ⟨first, rest⟩
      · simp [Arity.value] at lengthEq
      · cases rest with
        | nil =>
            simp [Arity.value] at lengthEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp [Arity.value] at lengthEq
            | cons third tail =>
                cases tail with
                | nil =>
                    simp [PeriodicOneInThreeNoUnits.clauseClauses,
                      noUnitArities, Arity.value]
                | cons fourth tail =>
                    simp [Arity.value] at lengthEq

private theorem oneInThree_blocks_lengths
    {Variable : Type*} (clauses : List (PeriodicClause Variable))
    (profiles : List ClauseProfile) (start : Nat)
    (lengthsEq :
      profiles.map (fun profile => profile.literals.length) =
        clauses.map List.length) :
    ((clauses.zipIdx start).flatMap fun tagged =>
        PeriodicOneInThree.clauseClauses tagged.2 tagged.1).map List.length =
      (profiles.flatMap oneInThreeArities).map Arity.value := by
  induction clauses generalizing profiles start with
  | nil =>
      cases profiles <;> simp_all
  | cons clause clauses induction =>
      cases profiles with
      | nil => simp at lengthsEq
      | cons profile profiles =>
          simp only [List.map_cons, List.cons.injEq] at lengthsEq
          rw [List.zipIdx_cons, List.flatMap_cons, List.map_append,
            oneInThree_clauseClauses_lengths start clause profile
              lengthsEq.1.symm,
            induction profiles (start + 1) lengthsEq.2]
          simp [List.map_append]

private theorem noUnit_blocks_lengths
    {Variable : Type*} (clauses : List (PeriodicClause Variable))
    (sourceArities : List Arity) (start : Nat)
    (lengthsEq :
      sourceArities.map Arity.value = clauses.map List.length) :
    ((clauses.zipIdx start).flatMap fun tagged =>
        PeriodicOneInThreeNoUnits.clauseClauses
          tagged.2 tagged.1).map List.length =
      (sourceArities.flatMap noUnitArities).map Arity.value := by
  induction clauses generalizing sourceArities start with
  | nil =>
      cases sourceArities <;> simp_all
  | cons clause clauses induction =>
      cases sourceArities with
      | nil => simp at lengthsEq
      | cons arity sourceArities =>
          simp only [List.map_cons, List.cons.injEq] at lengthsEq
          rw [List.zipIdx_cons, List.flatMap_cons, List.map_append,
            noUnit_clauseClauses_lengths start clause arity lengthsEq.1.symm,
            induction sourceArities (start + 1) lengthsEq.2]
          simp [List.map_append]

/-- Given exact source profiles, the finite expansion computes the exact
clause arities after both logical Figure 9 transformations, in order. -/
theorem arities_eq_formula_lengths
    {Variable : Type*} (source : PeriodicCNF Variable)
    (profiles : List ClauseProfile)
    (profilesCorrect :
      profiles.map (fun profile => profile.literals.length) =
        source.clauses.map List.length) :
    (arities profiles).map Arity.value =
      (PeriodicOneInThreeNoUnits.formula
        (PeriodicOneInThree.formula source)).clauses.map List.length := by
  have firstStage := oneInThree_blocks_lengths
    source.clauses profiles 0 profilesCorrect
  have secondStage := noUnit_blocks_lengths
    (PeriodicOneInThree.formula source).clauses
    (profiles.flatMap oneInThreeArities) 0 firstStage.symm
  calc
    (arities profiles).map Arity.value =
        ((profiles.flatMap oneInThreeArities).flatMap
          noUnitArities).map Arity.value := by
      unfold arities clauseArities
      rw [List.flatMap_assoc]
    _ = (PeriodicOneInThreeNoUnits.formula
          (PeriodicOneInThree.formula source)).clauses.map List.length := by
      simpa only [PeriodicOneInThreeNoUnits.formula] using
        secondStage.symm

end ClauseProfileFigureNine
end PeriodicCNF
end LeanTrominoes
