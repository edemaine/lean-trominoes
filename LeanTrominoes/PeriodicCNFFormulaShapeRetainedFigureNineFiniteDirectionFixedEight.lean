/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineFiniteDirectionCount

/-! # Fixed-eight generation of finite retained Figure 9 descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicThreeSATThree

/-- Canonical finite input to the existing fixed-eight descriptor expander:
the new copied-clause lookup prefix followed by one marker per stable retained
source variable. -/
def finiteSourceDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  copiedClauseDescriptors source ++
    List.replicate
      (sourceVariables
        (sourceScaledForFigureSeven source).erase).length
      .variable

private theorem copiedClauseDescriptors_flatMap_copiedClauseBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (copiedClauseDescriptors source).flatMap
        FormulaShapeFixedEightDirection.copiedClauseBlock =
      copiedClauseDescriptors source := by
  unfold copiedClauseDescriptors
  let taggedClauses :=
    (PeriodicOrthocrossing.finalCoordinatedSource source).clauses.zipIdx
  change (taggedClauses.map fun taggedClause =>
      FormulaShapeDirectionOrdering.Token.clause
        (copiedClauseProfile source taggedClause.2 taggedClause.1)).flatMap
        FormulaShapeFixedEightDirection.copiedClauseBlock =
    taggedClauses.map fun taggedClause =>
      FormulaShapeDirectionOrdering.Token.clause
        (copiedClauseProfile source taggedClause.2 taggedClause.1)
  induction taggedClauses with
  | nil => rfl
  | cons taggedClause taggedClauses induction =>
      simp [FormulaShapeFixedEightDirection.copiedClauseBlock, induction]

private theorem copiedClauseDescriptors_flatMap_cycleClauseBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (copiedClauseDescriptors source).flatMap
        FormulaShapeFixedEightDirection.cycleClauseBlock = [] := by
  unfold copiedClauseDescriptors
  rw [List.flatMap_map]
  simp [FormulaShapeFixedEightDirection.cycleClauseBlock]

private theorem copiedClauseDescriptors_flatMap_copiedVariableBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (copiedClauseDescriptors source).flatMap
        FormulaShapeFixedEightDirection.copiedVariableBlock = [] := by
  unfold copiedClauseDescriptors
  rw [List.flatMap_map]
  simp [FormulaShapeFixedEightDirection.copiedVariableBlock]

private theorem variableMarkers_flatMap_copiedClauseBlock
    (count : Nat) :
    (List.replicate count
        FormulaShapeDirectionOrdering.Token.variable).flatMap
        FormulaShapeFixedEightDirection.copiedClauseBlock = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp [FormulaShapeFixedEightDirection.copiedClauseBlock,
        List.replicate_succ, induction]

private theorem variableMarkers_flatMap_cycleClauseBlock
    {Variable : Type}
    (atoms : List Variable) :
    (List.replicate atoms.length
        FormulaShapeDirectionOrdering.Token.variable).flatMap
        FormulaShapeFixedEightDirection.cycleClauseBlock =
      atoms.flatMap fun _ =>
        FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
  induction atoms with
  | nil => rfl
  | cons atom atoms induction =>
      simp [FormulaShapeFixedEightDirection.cycleClauseBlock,
        List.replicate_succ, induction]

private theorem variableMarkers_flatMap_copiedVariableBlock
    (count : Nat) :
    (List.replicate count
        FormulaShapeDirectionOrdering.Token.variable).flatMap
        FormulaShapeFixedEightDirection.copiedVariableBlock =
      List.replicate
        (FormulaShapeFixedEight.copiesPerVariable * count)
        FormulaShapeDirectionOrdering.Token.variable := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.flatMap_cons, induction]
      simp only [FormulaShapeFixedEightDirection.copiedVariableBlock]
      rw [show FormulaShapeFixedEight.copiesPerVariable * (count + 1) =
          FormulaShapeFixedEight.copiesPerVariable +
            FormulaShapeFixedEight.copiesPerVariable * count by
          simp [Nat.mul_succ, Nat.add_comm],
        List.replicate_add]

/-- The existing fixed-eight phase expander turns the finite copied-source
stream into the complete finite copied/cycle/variable target. -/
theorem fixedEightDescriptors_finiteSourceDescriptors_eq_finiteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShapeFixedEightDirection.descriptors
        (finiteSourceDescriptors source) =
      finiteDescriptors source := by
  unfold FormulaShapeFixedEightDirection.descriptors
    finiteSourceDescriptors
  simp only [List.flatMap_append]
  rw [copiedClauseDescriptors_flatMap_copiedClauseBlock,
    copiedClauseDescriptors_flatMap_cycleClauseBlock,
    copiedClauseDescriptors_flatMap_copiedVariableBlock,
    variableMarkers_flatMap_copiedClauseBlock,
    variableMarkers_flatMap_cycleClauseBlock
      (sourceVariables (sourceScaledForFigureSeven source).erase),
    variableMarkers_flatMap_copiedVariableBlock]
  simp only [List.append_nil, List.nil_append]
  unfold finiteDescriptors finiteCycleClauseDescriptors
  rw [finalVariableCount_eq_copiesPerVariable_mul_sourceVariables]

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
