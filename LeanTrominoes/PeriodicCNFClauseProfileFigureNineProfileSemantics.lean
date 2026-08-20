/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineProfileData
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicOneInThreeNoUnits

/-! # Exact semantic profiles through the Figure 9 transformations -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileFigureNine

open UnaryProgramClauseProfile
open ClauseProfileOccurrenceSplit

/-- The first finite profile table agrees with one semantic Figure 9 clause
gadget. -/
theorem oneInThree_clauseClauses_literalProfiles
    {Variable : Type} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (profile : ClauseProfile)
    (profileEq : profile.literals = literalProfiles source) :
    (PeriodicOneInThree.clauseClauses clauseIndex source).map
        literalProfiles =
      (oneInThreeProfiles profile).map ClauseProfile.literals := by
  cases profile with
  | unary literalProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil =>
            simp_all [PeriodicOneInThree.clauseClauses,
              PeriodicOneInThree.disjunctionGadget,
              PeriodicOneInThree.forcePaddingFalse,
              PeriodicOneInThree.liftLiteral,
              PeriodicOneInThree.padding,
              PeriodicOneInThree.auxiliary,
              PeriodicOneInThree.anchor,
              oneInThreeProfiles, ClauseProfile.literals,
              literalProfiles, anchoredProfile]
        | cons second tail =>
            simp [ClauseProfile.literals, literalProfiles] at profileEq
  | binary firstProfile secondProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil =>
            simp [ClauseProfile.literals, literalProfiles] at profileEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp_all [PeriodicOneInThree.clauseClauses,
                  PeriodicOneInThree.disjunctionGadget,
                  PeriodicOneInThree.forcePaddingFalse,
                  PeriodicOneInThree.liftLiteral,
                  PeriodicOneInThree.padding,
                  PeriodicOneInThree.auxiliary,
                  PeriodicOneInThree.anchor,
                  PeriodicOneInThree.negate,
                  oneInThreeProfiles, ClauseProfile.literals,
                  literalProfiles, negateProfile, anchoredProfile]
            | cons third tail =>
                simp [ClauseProfile.literals, literalProfiles] at profileEq
  | ternary firstProfile secondProfile thirdProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil =>
            simp [ClauseProfile.literals, literalProfiles] at profileEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp [ClauseProfile.literals, literalProfiles] at profileEq
            | cons third tail =>
                cases tail with
                | nil =>
                    simp_all [PeriodicOneInThree.clauseClauses,
                      PeriodicOneInThree.disjunctionGadget,
                      PeriodicOneInThree.liftLiteral,
                      PeriodicOneInThree.auxiliary,
                      PeriodicOneInThree.anchor,
                      PeriodicOneInThree.negate,
                      oneInThreeProfiles, ClauseProfile.literals,
                      literalProfiles, negateProfile, anchoredProfile]
                | cons fourth tail =>
                    simp [ClauseProfile.literals, literalProfiles] at profileEq

/-- The second finite profile table agrees with one semantic unit-elimination
gadget. -/
theorem noUnit_clauseClauses_literalProfiles
    {Variable : Type} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (profile : ClauseProfile)
    (profileEq : profile.literals = literalProfiles source) :
    (PeriodicOneInThreeNoUnits.clauseClauses clauseIndex source).map
        literalProfiles =
      (noUnitProfiles profile).map ClauseProfile.literals := by
  cases profile with
  | unary literalProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil =>
            simp_all [PeriodicOneInThreeNoUnits.clauseClauses,
              PeriodicOneInThreeNoUnits.auxiliary,
              PeriodicOneInThreeNoUnits.liftLiteral,
              PeriodicOneInThree.anchor,
              PeriodicOneInThree.negate,
              noUnitProfiles, ClauseProfile.literals,
              literalProfiles, negateProfile, anchoredProfile]
        | cons second tail =>
            simp [ClauseProfile.literals, literalProfiles] at profileEq
  | binary firstProfile secondProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil =>
            simp [ClauseProfile.literals, literalProfiles] at profileEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp_all [PeriodicOneInThreeNoUnits.clauseClauses,
                  PeriodicOneInThreeNoUnits.liftLiteral,
                  noUnitProfiles, ClauseProfile.literals,
                  literalProfiles]
            | cons third tail =>
                simp [ClauseProfile.literals, literalProfiles] at profileEq
  | ternary firstProfile secondProfile thirdProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil =>
            simp [ClauseProfile.literals, literalProfiles] at profileEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp [ClauseProfile.literals, literalProfiles] at profileEq
            | cons third tail =>
                cases tail with
                | nil =>
                    simp_all [PeriodicOneInThreeNoUnits.clauseClauses,
                      PeriodicOneInThreeNoUnits.liftLiteral,
                      noUnitProfiles, ClauseProfile.literals,
                      literalProfiles]
                | cons fourth tail =>
                    simp [ClauseProfile.literals, literalProfiles] at profileEq

private theorem oneInThree_blocks_literalProfiles
    {Variable : Type} (clauses : List (PeriodicClause Variable))
    (sourceProfiles : List ClauseProfile) (start : Nat)
    (profilesEq : sourceProfiles.map ClauseProfile.literals =
      clauses.map literalProfiles) :
    ((clauses.zipIdx start).flatMap fun tagged =>
        PeriodicOneInThree.clauseClauses tagged.2 tagged.1).map
          literalProfiles =
      (sourceProfiles.flatMap oneInThreeProfiles).map
        ClauseProfile.literals := by
  induction clauses generalizing sourceProfiles start with
  | nil =>
      cases sourceProfiles <;> simp_all
  | cons clause clauses induction =>
      cases sourceProfiles with
      | nil => simp at profilesEq
      | cons profile sourceProfiles =>
          simp only [List.map_cons, List.cons.injEq] at profilesEq
          rw [List.zipIdx_cons, List.flatMap_cons, List.map_append,
            oneInThree_clauseClauses_literalProfiles
              start clause profile profilesEq.1,
            induction sourceProfiles (start + 1) profilesEq.2]
          simp [List.map_append]

private theorem noUnit_blocks_literalProfiles
    {Variable : Type} (clauses : List (PeriodicClause Variable))
    (sourceProfiles : List ClauseProfile) (start : Nat)
    (profilesEq : sourceProfiles.map ClauseProfile.literals =
      clauses.map literalProfiles) :
    ((clauses.zipIdx start).flatMap fun tagged =>
        PeriodicOneInThreeNoUnits.clauseClauses tagged.2 tagged.1).map
          literalProfiles =
      (sourceProfiles.flatMap noUnitProfiles).map
        ClauseProfile.literals := by
  induction clauses generalizing sourceProfiles start with
  | nil =>
      cases sourceProfiles <;> simp_all
  | cons clause clauses induction =>
      cases sourceProfiles with
      | nil => simp at profilesEq
      | cons profile sourceProfiles =>
          simp only [List.map_cons, List.cons.injEq] at profilesEq
          rw [List.zipIdx_cons, List.flatMap_cons, List.map_append,
            noUnit_clauseClauses_literalProfiles
              start clause profile profilesEq.1,
            induction sourceProfiles (start + 1) profilesEq.2]
          simp [List.map_append]

/-- Exact source profiles become the exact semantic profile stream after the
Figure 9 exact-one gadget alone. -/
theorem oneInThree_profiles_literals_eq_formula
    {Variable : Type} (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect : sourceProfiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (sourceProfiles.flatMap oneInThreeProfiles).map
        ClauseProfile.literals =
      (PeriodicOneInThree.formula source).clauses.map literalProfiles := by
  exact (oneInThree_blocks_literalProfiles
    source.clauses sourceProfiles 0 sourceCorrect).symm

/-- Exact source profiles become the exact semantic profile stream after
unit-clause elimination alone. -/
theorem noUnit_profiles_literals_eq_formula
    {Variable : Type} (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect : sourceProfiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (sourceProfiles.flatMap noUnitProfiles).map
        ClauseProfile.literals =
      (PeriodicOneInThreeNoUnits.formula source).clauses.map
        literalProfiles := by
  exact (noUnit_blocks_literalProfiles
    source.clauses sourceProfiles 0 sourceCorrect).symm

/-- Any exact source profile stream is transformed into the exact semantic
profile stream after Figure 9 and unit elimination. -/
theorem profiles_literals_eq_formula
    {Variable : Type} (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect : sourceProfiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (profiles sourceProfiles).map ClauseProfile.literals =
      (PeriodicOneInThreeNoUnits.formula
        (PeriodicOneInThree.formula source)).clauses.map
          literalProfiles := by
  have firstStage := oneInThree_blocks_literalProfiles
    source.clauses sourceProfiles 0 sourceCorrect
  have secondStage := noUnit_blocks_literalProfiles
    (PeriodicOneInThree.formula source).clauses
    (sourceProfiles.flatMap oneInThreeProfiles) 0 firstStage.symm
  calc
    (profiles sourceProfiles).map ClauseProfile.literals =
        ((sourceProfiles.flatMap oneInThreeProfiles).flatMap
          noUnitProfiles).map ClauseProfile.literals := by
      unfold profiles clauseProfiles
      rw [List.flatMap_assoc]
    _ = (PeriodicOneInThreeNoUnits.formula
          (PeriodicOneInThree.formula source)).clauses.map
            literalProfiles := by
      simpa only [PeriodicOneInThreeNoUnits.formula] using
        secondStage.symm

end ClauseProfileFigureNine
end PeriodicCNF
end LeanTrominoes
