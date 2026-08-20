/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfilePolarityNormalizationData
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicOneInThreePolarityNormalization

/-! # Exact semantic profiles of polarity normalization -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfilePolarityNormalization

open UnaryProgramClauseProfile
open ClauseProfileOccurrenceSplit

@[simp] theorem normalizedPolarity_eq_semantic (literalIndex : Nat) :
    normalizedPolarity literalIndex =
      PeriodicOneInThreePolarityNormalization.normalizedPolarity
        literalIndex := by
  cases literalIndex with
  | zero => rfl
  | succ literalIndex =>
      cases literalIndex with
      | zero => rfl
      | succ literalIndex => rfl

/-- The finite table for one clause agrees with the semantic normalization
and its occurrence-local complement clauses. -/
theorem clauseClauses_literalProfiles
    {Variable : Type} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (profile : ClauseProfile)
    (profileEq : profile.literals = literalProfiles source) :
    (PeriodicOneInThreePolarityNormalization.clauseClauses
        clauseIndex source).map literalProfiles =
      (clauseProfiles profile).map ClauseProfile.literals := by
  cases profile with
  | unary firstProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil =>
            by_cases firstCompatible :
              first.value =
                PeriodicOneInThreePolarityNormalization.normalizedPolarity 0
            · simp_all [PeriodicOneInThreePolarityNormalization.clauseClauses,
                PeriodicOneInThreePolarityNormalization.normalizeClause,
                PeriodicOneInThreePolarityNormalization.normalizeClauseFrom,
                PeriodicOneInThreePolarityNormalization.normalizeLiteral,
                PeriodicOneInThreePolarityNormalization.liftLiteral,
                PeriodicOneInThreePolarityNormalization.complementClauses,
                PeriodicOneInThreePolarityNormalization.complementClausesFrom,
                PeriodicOneInThreePolarityNormalization.normalizedPolarity,
                clauseProfiles, complementProfiles,
                normalizedLiteral, normalizedPolarity, withValue,
                ClauseProfile.literals, literalProfiles]
            · simp_all [PeriodicOneInThreePolarityNormalization.clauseClauses,
                PeriodicOneInThreePolarityNormalization.normalizeClause,
                PeriodicOneInThreePolarityNormalization.normalizeClauseFrom,
                PeriodicOneInThreePolarityNormalization.normalizeLiteral,
                PeriodicOneInThreePolarityNormalization.complementLiteral,
                PeriodicOneInThreePolarityNormalization.complementClause,
                PeriodicOneInThreePolarityNormalization.complementFalseLiteral,
                PeriodicOneInThreePolarityNormalization.originalFalseLiteral,
                PeriodicOneInThreePolarityNormalization.complementClauses,
                PeriodicOneInThreePolarityNormalization.complementClausesFrom,
                PeriodicOneInThreePolarityNormalization.normalizedPolarity,
                clauseProfiles, complementProfiles, complementProfile,
                normalizedLiteral, normalizedPolarity, withValue,
                ClauseProfile.literals, literalProfiles]
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
                by_cases firstCompatible :
                  first.value =
                    PeriodicOneInThreePolarityNormalization.normalizedPolarity 0
                <;> by_cases secondCompatible :
                  second.value =
                    PeriodicOneInThreePolarityNormalization.normalizedPolarity 1
                <;> simp_all [
                  PeriodicOneInThreePolarityNormalization.clauseClauses,
                  PeriodicOneInThreePolarityNormalization.normalizeClause,
                  PeriodicOneInThreePolarityNormalization.normalizeClauseFrom,
                  PeriodicOneInThreePolarityNormalization.normalizeLiteral,
                  PeriodicOneInThreePolarityNormalization.liftLiteral,
                  PeriodicOneInThreePolarityNormalization.complementLiteral,
                  PeriodicOneInThreePolarityNormalization.complementClause,
                  PeriodicOneInThreePolarityNormalization.complementFalseLiteral,
                  PeriodicOneInThreePolarityNormalization.originalFalseLiteral,
                  PeriodicOneInThreePolarityNormalization.complementClauses,
                  PeriodicOneInThreePolarityNormalization.complementClausesFrom,
                  PeriodicOneInThreePolarityNormalization.normalizedPolarity,
                  clauseProfiles, complementProfiles, complementProfile,
                  normalizedLiteral, normalizedPolarity, withValue,
                  ClauseProfile.literals, literalProfiles]
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
                    by_cases firstCompatible :
                      first.value =
                        PeriodicOneInThreePolarityNormalization.normalizedPolarity 0
                    <;> by_cases secondCompatible :
                      second.value =
                        PeriodicOneInThreePolarityNormalization.normalizedPolarity 1
                    <;> by_cases thirdCompatible :
                      third.value =
                        PeriodicOneInThreePolarityNormalization.normalizedPolarity 2
                    <;> simp_all [
                      PeriodicOneInThreePolarityNormalization.clauseClauses,
                      PeriodicOneInThreePolarityNormalization.normalizeClause,
                      PeriodicOneInThreePolarityNormalization.normalizeClauseFrom,
                      PeriodicOneInThreePolarityNormalization.normalizeLiteral,
                      PeriodicOneInThreePolarityNormalization.liftLiteral,
                      PeriodicOneInThreePolarityNormalization.complementLiteral,
                      PeriodicOneInThreePolarityNormalization.complementClause,
                      PeriodicOneInThreePolarityNormalization.complementFalseLiteral,
                      PeriodicOneInThreePolarityNormalization.originalFalseLiteral,
                      PeriodicOneInThreePolarityNormalization.complementClauses,
                      PeriodicOneInThreePolarityNormalization.complementClausesFrom,
                      PeriodicOneInThreePolarityNormalization.normalizedPolarity,
                      clauseProfiles, complementProfiles, complementProfile,
                      normalizedLiteral, normalizedPolarity, withValue,
                      ClauseProfile.literals, literalProfiles]
                | cons fourth tail =>
                    simp [ClauseProfile.literals, literalProfiles] at profileEq

private theorem blocks_literalProfiles
    {Variable : Type} (clauses : List (PeriodicClause Variable))
    (sourceProfiles : List ClauseProfile) (start : Nat)
    (profilesEq : sourceProfiles.map ClauseProfile.literals =
      clauses.map literalProfiles) :
    ((clauses.zipIdx start).flatMap fun tagged =>
        PeriodicOneInThreePolarityNormalization.clauseClauses
          tagged.2 tagged.1).map literalProfiles =
      (sourceProfiles.flatMap clauseProfiles).map
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
            clauseClauses_literalProfiles start clause profile profilesEq.1,
            induction sourceProfiles (start + 1) profilesEq.2]
          simp [List.map_append]

/-- Any exact finite profile stream becomes the exact semantic profile stream
of the polarity-normalized formula. -/
theorem profiles_literals_eq_formula
    {Variable : Type} (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect : sourceProfiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (profiles sourceProfiles).map ClauseProfile.literals =
      (PeriodicOneInThreePolarityNormalization.formula source).clauses.map
        literalProfiles := by
  have transformed := blocks_literalProfiles
    source.clauses sourceProfiles 0 sourceCorrect
  simpa only [profiles,
    PeriodicOneInThreePolarityNormalization.formula] using transformed.symm

end ClauseProfilePolarityNormalization
end PeriodicCNF
end LeanTrominoes
