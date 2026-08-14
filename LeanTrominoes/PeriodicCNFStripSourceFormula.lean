/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicThreeCNFCorrectness
import LeanTrominoes.PeriodicThreeSATThreeNonempty

/-!
# Guarded 3SAT-3 source for the strip reduction

The planar drawing pipeline consumes a local periodic formula with width and
occurrence bounds three and with no empty clauses.  A valid one-dimensional
source is first converted to 3CNF and then occurrence-split.  Malformed
sources, including sources with an empty clause, are sent to two contradictory
unit clauses satisfying all syntactic promises.
-/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

noncomputable section

/-- Variables after width-three conversion and occurrence splitting. -/
abbrev Variable := ThreeOccurrenceVariable (ThreeCNFVariable Nat)

local instance variableDecidableEq : DecidableEq Variable :=
  Classical.decEq _

local instance variableBEq : BEq Variable :=
  instBEqOfDecidableEq

/-- The ordinary semantic normalization used on admissible sources. -/
def normalizedFormula (source : PeriodicCNF Nat) : PeriodicCNF Variable :=
  PeriodicThreeSATThree.formula (PeriodicThreeCNF.formula source)

/-- A fixed atom for the contradictory fallback formula. -/
def fallbackAtom : Variable :=
  (Sum.inl 0, 0, 0)

/-- A nonempty-clause, width-one, visibly unsatisfiable fallback. -/
def fallbackFormula : PeriodicCNF Variable where
  clauses :=
    [[⟨fallbackAtom, (0, 0), true⟩],
      [⟨fallbackAtom, (0, 0), false⟩]]

/-- The decidable syntactic promise needed before entering the planar
pipeline.  Plane locality is used because it is the pipeline's native form. -/
def SourceAdmissible (source : PeriodicCNF Nat) : Prop :=
  source.IsOneDimensional ∧
    source.IsLocal ∧
      ∀ clause ∈ source.clauses, clause ≠ []

def clauseIsLocal (clause : PeriodicClause Nat) : Bool :=
  clause.all fun first =>
    clause.all fun second =>
      decide (PeriodicClause.offsetDistance first second ≤ 1)

@[simp] theorem clauseIsLocal_eq_true_iff
    (clause : PeriodicClause Nat) :
    clauseIsLocal clause = true ↔ clause.IsLocal := by
  simp [clauseIsLocal, PeriodicClause.IsLocal]

def formulaIsLocal (source : PeriodicCNF Nat) : Bool :=
  source.clauses.all clauseIsLocal

@[simp] theorem formulaIsLocal_eq_true_iff (source : PeriodicCNF Nat) :
    formulaIsLocal source = true ↔ source.IsLocal := by
  simp [formulaIsLocal, PeriodicCNF.IsLocal]

def allClausesNonempty : List (PeriodicClause Nat) → Bool
  | [] => true
  | clause :: clauses => !clause.isEmpty && allClausesNonempty clauses

@[simp] theorem allClausesNonempty_eq_true_iff
    (clauses : List (PeriodicClause Nat)) :
    allClausesNonempty clauses = true ↔
      ∀ clause ∈ clauses, clause ≠ [] := by
  induction clauses with
  | nil => simp [allClausesNonempty]
  | cons clause clauses induction =>
      cases clause <;> simp [allClausesNonempty, induction]

def sourceAdmissible (source : PeriodicCNF Nat) : Bool :=
  source.isOneDimensional && formulaIsLocal source &&
    allClausesNonempty source.clauses

@[simp] theorem sourceAdmissible_eq_true_iff (source : PeriodicCNF Nat) :
    sourceAdmissible source = true ↔ SourceAdmissible source := by
  simp [sourceAdmissible, SourceAdmissible, and_assoc]

instance (source : PeriodicCNF Nat) : Decidable (SourceAdmissible source) := by
  exact decidable_of_iff (sourceAdmissible source = true)
    (sourceAdmissible_eq_true_iff source)

/-- Select semantic normalization on promised input and the contradictory
fallback otherwise. -/
def sourceFormula (source : PeriodicCNF Nat) : PeriodicCNF Variable :=
  if SourceAdmissible source then normalizedFormula source
  else fallbackFormula

theorem fallbackFormula_isLocal : fallbackFormula.IsLocal := by
  simp [fallbackFormula, PeriodicCNF.IsLocal, PeriodicClause.IsLocal,
    PeriodicClause.offsetDistance]

theorem fallbackFormula_widthAtMostThree :
    fallbackFormula.WidthAtMost 3 := by
  simp [fallbackFormula, PeriodicCNF.WidthAtMost,
    PeriodicClause.WidthAtMost]

theorem fallbackFormula_occurrencesAtMostThree :
    fallbackFormula.OccurrencesAtMost 3 := by
  intro atom
  calc
    (PeriodicCNF.variableOccurrences fallbackFormula).count atom ≤
        (PeriodicCNF.variableOccurrences fallbackFormula).length :=
      List.count_le_length
    _ ≤ 3 := by
      simp [fallbackFormula, PeriodicCNF.variableOccurrences]

theorem fallbackFormula_clausesNonempty :
    ∀ clause ∈ fallbackFormula.clauses, clause ≠ [] := by
  simp [fallbackFormula]

theorem fallbackFormula_not_satisfiable :
    ¬ fallbackFormula.Satisfiable := by
  rintro ⟨assignment, satisfies⟩
  have positive :=
    satisfies (0, 0) [⟨fallbackAtom, (0, 0), true⟩] (by
      simp [fallbackFormula])
  have negative :=
    satisfies (0, 0) [⟨fallbackAtom, (0, 0), false⟩] (by
      simp [fallbackFormula])
  simp [PeriodicClause.Holds, PeriodicLiteral.Holds, Cell.add] at positive negative
  simp [positive] at negative

/-- A satisfiable line formula cannot contain an empty clause. -/
theorem clausesNonempty_of_satisfiableOnLine
    {source : PeriodicCNF Nat}
    (satisfiable : source.SatisfiableOnLine) :
    ∀ clause ∈ source.clauses, clause ≠ [] := by
  obtain ⟨assignment, satisfies⟩ := satisfiable
  intro clause clauseMembership clauseEmpty
  subst clause
  simpa [PeriodicClause.HoldsOnLine] using
    satisfies 0 [] clauseMembership

/-- Every yes-instance of the source language satisfies the syntactic guard. -/
theorem sourceAdmissible_of_localPeriodicCNF1DSAT
    {source : PeriodicCNF Nat}
    (holds : PeriodicCNF.LocalPeriodicCNF1DSAT source) :
    SourceAdmissible source := by
  refine ⟨holds.1,
    (PeriodicCNF.isLocal_iff_isLocalOnLine holds.1).mpr holds.2.1,
    clausesNonempty_of_satisfiableOnLine holds.2.2⟩

theorem normalizedFormula_isLocal
    (source : PeriodicCNF Nat) (sourceLocal : source.IsLocal) :
    (normalizedFormula source).IsLocal :=
  PeriodicThreeSATThree.formula_isLocal
    (PeriodicThreeCNF.formula_isLocal sourceLocal)

theorem normalizedFormula_widthAtMostThree
    (source : PeriodicCNF Nat) :
    (normalizedFormula source).WidthAtMost 3 :=
  PeriodicThreeSATThree.formula_widthAtMostThree
    (PeriodicThreeCNF.formula_widthAtMostThree source)

theorem normalizedFormula_occurrencesAtMostThree
    (source : PeriodicCNF Nat) :
    (normalizedFormula source).OccurrencesAtMost 3 := by
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3
    (normalizedFormula source)
    (PeriodicThreeSATThree.formula_occurrencesAtMostThree
      (PeriodicThreeCNF.formula source))

theorem normalizedFormula_clausesNonempty
    (source : PeriodicCNF Nat)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause ∈ (normalizedFormula source).clauses, clause ≠ [] :=
  PeriodicThreeSATThree.formula_clausesNonempty
    (PeriodicThreeCNF.formula source)
    (PeriodicThreeCNF.formula_clausesNonempty source nonempty)

theorem normalizedFormula_satisfiable_iff
    (source : PeriodicCNF Nat) :
    (normalizedFormula source).Satisfiable ↔ source.Satisfiable := by
  exact (PeriodicThreeSATThree.satisfiable_iff
    (PeriodicThreeCNF.formula source)).symm.trans
      (PeriodicThreeCNF.satisfiable_iff source).symm

theorem sourceFormula_isLocal (source : PeriodicCNF Nat) :
    (sourceFormula source).IsLocal := by
  by_cases admissible : SourceAdmissible source
  · simpa [sourceFormula, admissible] using
      normalizedFormula_isLocal source admissible.2.1
  · simpa [sourceFormula, admissible] using fallbackFormula_isLocal

theorem sourceFormula_widthAtMostThree (source : PeriodicCNF Nat) :
    (sourceFormula source).WidthAtMost 3 := by
  by_cases admissible : SourceAdmissible source
  · simpa [sourceFormula, admissible] using
      normalizedFormula_widthAtMostThree source
  · simpa [sourceFormula, admissible] using
      fallbackFormula_widthAtMostThree

theorem sourceFormula_occurrencesAtMostThree (source : PeriodicCNF Nat) :
    (sourceFormula source).OccurrencesAtMost 3 := by
  by_cases admissible : SourceAdmissible source
  · simpa [sourceFormula, admissible] using
      normalizedFormula_occurrencesAtMostThree source
  · simpa [sourceFormula, admissible] using
      fallbackFormula_occurrencesAtMostThree

theorem sourceFormula_clausesNonempty (source : PeriodicCNF Nat) :
    ∀ clause ∈ (sourceFormula source).clauses, clause ≠ [] := by
  by_cases admissible : SourceAdmissible source
  · simpa [sourceFormula, admissible] using
      normalizedFormula_clausesNonempty source admissible.2.2
  · simpa [sourceFormula, admissible] using
      fallbackFormula_clausesNonempty

/-- The guarded bounded-occurrence formula has exactly the source language's
semantics. -/
theorem sourceFormula_correct (source : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT source ↔
      (sourceFormula source).Satisfiable := by
  by_cases admissible : SourceAdmissible source
  · rw [sourceFormula, if_pos admissible,
      normalizedFormula_satisfiable_iff]
    constructor
    · intro holds
      exact (PeriodicCNF.satisfiable_iff_satisfiableOnLine holds.1).mpr
        holds.2.2
    · intro satisfiable
      exact ⟨admissible.1,
        (PeriodicCNF.isLocal_iff_isLocalOnLine admissible.1).mp
          admissible.2.1,
        (PeriodicCNF.satisfiable_iff_satisfiableOnLine admissible.1).mp
          satisfiable⟩
  · rw [sourceFormula, if_neg admissible]
    exact iff_of_false
      (fun holds => admissible
        (sourceAdmissible_of_localPeriodicCNF1DSAT holds))
      fallbackFormula_not_satisfiable

end
end PeriodicCNFStripReduction
end LeanTrominoes
