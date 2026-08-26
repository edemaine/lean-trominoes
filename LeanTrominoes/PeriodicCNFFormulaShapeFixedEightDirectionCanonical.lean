/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCanonical
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionSemantics

/-! # Canonical phase-major fixed-eight direction shapes -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFixedEightDirection

open OccurrenceSplitRing

/-- The copied-clause phase contains only ordinary clause tokens. -/
private theorem shape_copiedClauseBlocks_onlyClauses
    (source : List FormulaShapeDirectionOrdering.Token) :
    let output := FormulaShapeDirectionOrdering.shape
      (source.flatMap copiedClauseBlock)
    output = (FormulaShape.clauseProfiles output).map
      FormulaShape.Token.clause := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      dsimp only at induction ⊢
      cases token with
      | clause profile =>
          simpa [FormulaShapeDirectionOrdering.shape,
            FormulaShapeDirectionOrdering.tokenBlock,
            copiedClauseBlock, FormulaShape.clauseProfiles] using
            congrArg
              (List.cons (FormulaShape.Token.clause profile.orderedProfile))
              induction
      | «variable» =>
          simpa [FormulaShapeDirectionOrdering.shape,
            copiedClauseBlock] using induction

/-- The closed ring's clause-only descriptor subblock remains clause-only
after direction sorting. -/
private theorem cycleClauseShape_onlyClauses :
    let output := FormulaShapeDirectionOrdering.shape cycleClauseDescriptors
    output = (FormulaShape.clauseProfiles output).map
      FormulaShape.Token.clause := by
  unfold cycleClauseDescriptors
  induction localCycleFormula.clauses.zipIdx with
  | nil => rfl
  | cons taggedClause clauses induction =>
      simpa [FormulaShapeDirectionOrdering.shape,
        FormulaShapeDirectionOrdering.tokenBlock,
        FormulaShape.clauseProfiles] using
        congrArg
          (List.cons (FormulaShape.Token.clause
            (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
              cycleRoutes taggedClause.2 taggedClause.1).orderedProfile))
          induction

/-- The complete ring-clause phase contains only ordinary clause tokens. -/
private theorem shape_cycleClauseBlocks_onlyClauses
    (source : List FormulaShapeDirectionOrdering.Token) :
    let output := FormulaShapeDirectionOrdering.shape
      (source.flatMap cycleClauseBlock)
    output = (FormulaShape.clauseProfiles output).map
      FormulaShape.Token.clause := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      dsimp only at induction ⊢
      cases token with
      | clause profile =>
          simpa [FormulaShapeDirectionOrdering.shape,
            cycleClauseBlock] using induction
      | «variable» =>
          have combined := congrArg₂ (fun first second => first ++ second)
            cycleClauseShape_onlyClauses induction
          simpa only [List.flatMap_cons, cycleClauseBlock,
            FormulaShapeDirectionOrdering.shape, List.flatMap_append,
            FormulaShape.clauseProfiles_append, List.map_append] using combined

private theorem shape_replicate_variable (count : Nat) :
    FormulaShapeDirectionOrdering.shape
        (List.replicate count FormulaShapeDirectionOrdering.Token.variable) =
      List.replicate count FormulaShape.Token.variable := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.replicate_succ]
      change FormulaShape.Token.variable ::
          FormulaShapeDirectionOrdering.shape
            (List.replicate count
              FormulaShapeDirectionOrdering.Token.variable) = _
      rw [induction]

/-- The copied-variable phase contains only ordinary variable markers. -/
private theorem shape_copiedVariableBlocks_onlyVariables
    (source : List FormulaShapeDirectionOrdering.Token) :
    let output := FormulaShapeDirectionOrdering.shape
      (source.flatMap copiedVariableBlock)
    output = List.replicate (FormulaShape.variableCount output)
      FormulaShape.Token.variable := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      dsimp only at induction ⊢
      cases token with
      | clause profile =>
          simpa [FormulaShapeDirectionOrdering.shape,
            copiedVariableBlock] using induction
      | «variable» =>
          let rest := FormulaShapeDirectionOrdering.shape
            (source.flatMap copiedVariableBlock)
          have outputEq :
              FormulaShapeDirectionOrdering.shape
                  ((List.replicate FormulaShapeFixedEight.copiesPerVariable
                      FormulaShapeDirectionOrdering.Token.variable) ++
                    source.flatMap copiedVariableBlock) =
                List.replicate FormulaShapeFixedEight.copiesPerVariable
                    FormulaShape.Token.variable ++ rest := by
            dsimp only [rest]
            rw [FormulaShapeDirectionOrdering.shape]
            rw [List.flatMap_append]
            change FormulaShapeDirectionOrdering.shape
                (List.replicate FormulaShapeFixedEight.copiesPerVariable
                  FormulaShapeDirectionOrdering.Token.variable) ++ _ = _
            rw [shape_replicate_variable]
            rfl
          rw [List.flatMap_cons, copiedVariableBlock, outputEq]
          dsimp only [rest]
          rw [induction]
          simp only [FormulaShape.variableCount,
            FormulaShape.variableMarkers_replicate_variable,
            List.length_replicate,
            ← List.replicate_add]

/-- A clause-only prefix followed by a variable-only suffix is canonical. -/
private theorem isCanonical_append
    (clauses suffix : List FormulaShape.Token)
    (clausesOnly : clauses =
      (FormulaShape.clauseProfiles clauses).map FormulaShape.Token.clause)
    (suffixOnly : suffix =
      List.replicate (FormulaShape.variableCount suffix)
        FormulaShape.Token.variable) :
    FormulaShape.IsCanonical (clauses ++ suffix) := by
  unfold FormulaShape.IsCanonical
  rw [FormulaShape.clauseProfiles_append,
    FormulaShape.variableCount, FormulaShape.variableMarkers_append]
  rw [clausesOnly, suffixOnly]
  simp [FormulaShape.variableCount]

/-- The phase-major descriptor expansion becomes a canonical ordinary shape:
all copied and ring clauses precede all output-variable markers. -/
theorem shape_descriptors_isCanonical
    (source : List FormulaShapeDirectionOrdering.Token) :
    FormulaShape.IsCanonical
      (FormulaShapeDirectionOrdering.shape (descriptors source)) := by
  let copiedClauses := FormulaShapeDirectionOrdering.shape
    (source.flatMap copiedClauseBlock)
  let ringClauses := FormulaShapeDirectionOrdering.shape
    (source.flatMap cycleClauseBlock)
  let variableSuffix := FormulaShapeDirectionOrdering.shape
    (source.flatMap copiedVariableBlock)
  have copiedClausesOnly := shape_copiedClauseBlocks_onlyClauses source
  have ringClausesOnly := shape_cycleClauseBlocks_onlyClauses source
  have clausePrefixOnly : copiedClauses ++ ringClauses =
      (FormulaShape.clauseProfiles
        (copiedClauses ++ ringClauses)).map FormulaShape.Token.clause := by
    rw [FormulaShape.clauseProfiles_append, List.map_append]
    exact congrArg₂ (fun first second => first ++ second)
      copiedClausesOnly ringClausesOnly
  have variableSuffixOnly := shape_copiedVariableBlocks_onlyVariables source
  have canonical := isCanonical_append
    (copiedClauses ++ ringClauses) variableSuffix
    clausePrefixOnly variableSuffixOnly
  simpa only [descriptors, FormulaShapeDirectionOrdering.shape,
    List.flatMap_append, List.append_assoc,
    copiedClauses, ringClauses, variableSuffix] using canonical

end LeanTrominoes.PeriodicCNF.FormulaShapeFixedEightDirection
