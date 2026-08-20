/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaSemantics

/-! # Uniqueness of canonical finite formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF

open UnaryProgramClauseProfile
open ClauseProfileOccurrenceSplit

/-- A clause profile is uniquely determined by its nonempty list of at most
three literal profiles. -/
theorem ClauseProfile.literals_injective :
    Function.Injective ClauseProfile.literals := by
  intro first second literalsEqual
  cases first <;> cases second <;>
    simp_all [ClauseProfile.literals]

namespace FormulaShape

/-- Canonical shape streams put every clause token first and then every
distinct-variable marker. -/
def IsCanonical (candidate : List Token) : Prop :=
  candidate =
    (clauseProfiles candidate).map Token.clause ++
      List.replicate (variableCount candidate) Token.variable

end FormulaShape

namespace FormulaShapeOfFormula

/-- The concrete formula shape is canonical by construction. -/
theorem shape_isCanonical
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaShape.IsCanonical (shape formula) := by
  unfold FormulaShape.IsCanonical
  rw [clauseProfiles_shape, variableCount_shape]
  rfl

/-- Exact semantics uniquely determine a canonical shape stream. -/
theorem eq_shape_of_correct
    {Variable : Type} [DecidableEq Variable]
    {candidate : List FormulaShape.Token}
    (formula : PeriodicCNF Variable)
    (candidateCanonical : FormulaShape.IsCanonical candidate)
    (candidateCorrect : CorrectFor candidate formula)
    (width : formula.WidthAtMost 3)
    (nonempty : ∀ clause ∈ formula.clauses, clause ≠ []) :
    candidate = shape formula := by
  have referenceCorrect := shape_correct formula width nonempty
  have mappedProfiles :
      (FormulaShape.clauseProfiles candidate).map ClauseProfile.literals =
        (profiles formula).map ClauseProfile.literals := by
    calc
      _ = formula.clauses.map literalProfiles := candidateCorrect.1
      _ = _ := by
        simpa only [clauseProfiles_shape] using
          referenceCorrect.1.symm
  have profilesEqual :
      FormulaShape.clauseProfiles candidate = profiles formula :=
    ClauseProfile.literals_injective.list_map mappedProfiles
  calc
    candidate =
        (FormulaShape.clauseProfiles candidate).map FormulaShape.Token.clause ++
          List.replicate (FormulaShape.variableCount candidate)
            FormulaShape.Token.variable :=
      candidateCanonical
    _ = (profiles formula).map FormulaShape.Token.clause ++
          List.replicate formula.variableOccurrences.dedup.length
            FormulaShape.Token.variable := by
      rw [profilesEqual, candidateCorrect.2]
    _ = shape formula := rfl

end FormulaShapeOfFormula
end PeriodicCNF
end LeanTrominoes
