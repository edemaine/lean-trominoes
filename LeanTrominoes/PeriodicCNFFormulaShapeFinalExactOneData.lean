/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFinalExactOneData
import LeanTrominoes.PeriodicCNFFormulaShapeData

/-! # Finite formula shapes after the final exact-one reductions -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFinalExactOne

open UnaryProgramClauseProfile

/-- Figure 9 introduces four core variables and enough padding variables to
complete a source clause to arity three. -/
def figureNineFreshVariableCount : ClauseProfile → Nat
  | .unary _ => 6
  | .binary _ _ => 5
  | .ternary _ _ _ => 4

/-- Eliminating a unit exact-one clause introduces two fresh variables.
Binary and ternary clauses are only embedded. -/
def noUnitFreshVariableCount : ClauseProfile → Nat
  | .unary _ => 2
  | .binary _ _ => 0
  | .ternary _ _ _ => 0

/-- Polarity normalization introduces exactly one complement variable for
each incompatible literal occurrence, equivalently for each appended binary
complement profile. -/
def polarityFreshVariableCount (profile : ClauseProfile) : Nat :=
  (ClauseProfilePolarityNormalization.clauseProfiles profile).length - 1

/-- Total number of fresh variables introduced by Figure 9, unit-clause
elimination, and polarity normalization for one input clause. -/
def clauseFreshVariableCount (profile : ClauseProfile) : Nat :=
  figureNineFreshVariableCount profile +
    ((ClauseProfileFigureNine.oneInThreeProfiles profile).map
      noUnitFreshVariableCount).sum +
    ((ClauseProfileFigureNine.clauseProfiles profile).map
      polarityFreshVariableCount).sum

/-- Transform one finite formula-shape token.  An existing distinct variable
survives all three reductions; a clause expands to its exact final clause
profiles and the precise number of newly introduced variables. -/
def tokenBlock : FormulaShape.Token → List FormulaShape.Token
  | .variable => [.variable]
  | .clause profile =>
      (ClauseProfileFinalExactOne.profiles [profile]).map .clause ++
        List.replicate (clauseFreshVariableCount profile) .variable

/-- Complete finite formula shape after Figure 9, unit elimination, and
terminal-polarity normalization. -/
def shape (source : List FormulaShape.Token) : List FormulaShape.Token :=
  source.flatMap tokenBlock

@[simp] theorem clauseProfiles_tokenBlock (token : FormulaShape.Token) :
    FormulaShape.clauseProfiles (tokenBlock token) =
      ClauseProfileFinalExactOne.profiles
        (FormulaShape.clauseProfiles [token]) := by
  cases token <;>
    simp [tokenBlock, ClauseProfileFinalExactOne.profiles,
      ClauseProfileFigureNine.profiles,
      ClauseProfilePolarityNormalization.profiles,
      FormulaShape.clauseProfiles]

@[simp] theorem clauseProfiles_shape
    (source : List FormulaShape.Token) :
    FormulaShape.clauseProfiles (shape source) =
      ClauseProfileFinalExactOne.profiles
        (FormulaShape.clauseProfiles source) := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      change
        FormulaShape.clauseProfiles (tokenBlock token ++ shape source) = _
      rw [FormulaShape.clauseProfiles_append,
        clauseProfiles_tokenBlock, induction]
      cases token <;>
        simp [ClauseProfileFinalExactOne.profiles,
          ClauseProfileFigureNine.profiles,
          ClauseProfilePolarityNormalization.profiles,
          FormulaShape.clauseProfiles]

@[simp] theorem variableCount_tokenBlock
    (token : FormulaShape.Token) :
    FormulaShape.variableCount (tokenBlock token) =
      match token with
      | .variable => 1
      | .clause profile => clauseFreshVariableCount profile := by
  cases token <;>
    simp [tokenBlock, FormulaShape.variableCount,
      FormulaShape.variableMarkers]

@[simp] theorem variableCount_append
    (first second : List FormulaShape.Token) :
    FormulaShape.variableCount (first ++ second) =
      FormulaShape.variableCount first +
        FormulaShape.variableCount second := by
  simp [FormulaShape.variableCount]

/-- The final shape retains every source variable and adds the sum of the
clause-local fresh-variable counts. -/
@[simp] theorem variableCount_shape (source : List FormulaShape.Token) :
    FormulaShape.variableCount (shape source) =
      FormulaShape.variableCount source +
        ((FormulaShape.clauseProfiles source).map
          clauseFreshVariableCount).sum := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      change
        FormulaShape.variableCount (tokenBlock token ++ shape source) = _
      rw [variableCount_append, variableCount_tokenBlock, induction]
      cases token <;>
        simp [FormulaShape.variableCount, FormulaShape.variableMarkers,
          FormulaShape.clauseProfiles, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]

end FormulaShapeFinalExactOne
end PeriodicCNF
end LeanTrominoes
