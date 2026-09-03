/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineProfileSemantics

/-! # Ternary tail polarities after the Figure 9 transformations -/

namespace LeanTrominoes.PeriodicCNF.ClauseProfileFigureNine

open ClauseProfileOccurrenceSplit
open UnaryProgramClauseProfile

/-- A ternary profile has the same polarity in its final two positions. -/
def TernaryTailValuesEqual (profile : ClauseProfile) : Prop :=
  ∀ first second third,
    profile.literals = [first, second, third] →
      second.value = third.value

/-- Every unit-free profile produced by one Figure 9 block has equal final
two polarities whenever it is ternary. -/
theorem clauseProfiles_ternaryTailValuesEqual (profile : ClauseProfile) :
    ∀ generated ∈ clauseProfiles profile,
      TernaryTailValuesEqual generated := by
  unfold TernaryTailValuesEqual
  native_decide +revert

/-- The property holds throughout the complete unit-free profile stream. -/
theorem profiles_ternaryTailValuesEqual
    (source : List ClauseProfile) :
    ∀ generated ∈ profiles source,
      TernaryTailValuesEqual generated := by
  intro generated generatedMember
  rcases List.mem_flatMap.mp generatedMember with
    ⟨profile, profileMember, generatedMember⟩
  exact clauseProfiles_ternaryTailValuesEqual
    profile generated generatedMember

/-- Exact profile semantics transfer the finite tail-polarity invariant to
the logical Figure 9 and unit-elimination output. -/
theorem formula_ternaryTailValuesEqual
    {Variable : Type} (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect :
      sourceProfiles.map ClauseProfile.literals =
        source.clauses.map literalProfiles) :
    ∀ clause ∈
        (PeriodicOneInThreeNoUnits.formula
          (PeriodicOneInThree.formula source)).clauses,
      ∀ first second third,
        clause = [first, second, third] →
          second.value = third.value := by
  have profilesCorrect := profiles_literals_eq_formula
    source sourceProfiles sourceCorrect
  intro clause clauseMember first second third clauseEq
  have literalProfilesMember :
      literalProfiles clause ∈
        ((PeriodicOneInThreeNoUnits.formula
          (PeriodicOneInThree.formula source)).clauses.map
            literalProfiles) :=
    List.mem_map.mpr ⟨clause, clauseMember, rfl⟩
  rw [← profilesCorrect] at literalProfilesMember
  rcases List.mem_map.mp literalProfilesMember with
    ⟨profile, profileMember, profileEq⟩
  have tailValues := profiles_ternaryTailValuesEqual
    sourceProfiles profile profileMember
  apply tailValues
    { nextSlice := decide (first.offset = ((1, 0) : Cell))
      value := first.value }
    { nextSlice := decide (second.offset = ((1, 0) : Cell))
      value := second.value }
    { nextSlice := decide (third.offset = ((1, 0) : Cell))
      value := third.value }
  rw [profileEq]
  simp [clauseEq, literalProfiles]

end LeanTrominoes.PeriodicCNF.ClauseProfileFigureNine
