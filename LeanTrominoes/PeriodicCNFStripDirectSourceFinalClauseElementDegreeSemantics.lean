/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDegreePattern
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceArity
import LeanTrominoes.PeriodicCNFStripHorizontalTypedElementDegreePattern
import LeanTrominoes.PeriodicCNFStripHorizontalTypedSourceFinalClauseAritySemantics

/-! # Direct final clause-element degree semantics -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseElementDegreeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance]
  directFinalClauseDegreePatternVariableDecidableEq
  horizontalThreeDMTripleVariableDecidableEq

private def clauseElementDegreesOfTernary (ternary : Bool) : List Nat :=
  if ternary = true then [3, 3, 3, 3] else [3, 3, 3, 2]

/-- Replacing stable numeric clause indices by their total lookups exposes
the typed clause-degree suffix as an ordinary clause-order flat map. -/
theorem horizontalTypedClauseElementDegrees_eq_clauseFlatMap
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    horizontalTypedClauseElementDegrees source =
      source.clauses.flatMap fun clause =>
        if clause.length = 3 then [3, 3, 3, 3] else [3, 3, 3, 2] := by
  unfold horizontalTypedClauseElementDegrees
    horizontalTypedClauseElementDegreeBlock
  have enumerated := List.map_range_getD source.clauses []
  have flattened := congrArg
    (List.flatMap fun clause =>
      if clause.length = 3 then [3, 3, 3, 3] else [3, 3, 3, 2])
    enumerated
  simpa only [List.flatMap_map, Function.comp_def] using flattened

/-- The direct clause-fan Boolean column says exactly which clauses of the
actual typed horizontal source are ternary. -/
theorem directSourceFinalClauseFans_hasRight_eq_typedClauseTernary
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFans decider symbols).map
        PeriodicPlanarOneInThreeToThreeDM.ClauseRibbonFanData.hasRight =
      (horizontalThreeDMTypedSourceComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.map
          fun clause => decide (clause.length = 3) := by
  let source := PolySpaceCompiler.formulaOfSymbols decider symbols
  let typed := horizontalThreeDMTypedSourceComputed source
  have lengthEq :
      (FormulaShape.clauseProfiles
        (FormulaShapeFinalExactOne.shape
          (FormulaShapeRetainedFigureNineSource.shape
            (directSourceFormula decider symbols)))).map
            (fun profile => profile.literals.length) =
        typed.clauses.map List.length := by
    have shapeEq :
        @FormulaShapeRetainedFigureNineSource.shape Variable
            directFinalClauseDegreePatternVariableDecidableEq
            (directSourceFormula decider symbols) =
          @FormulaShapeRetainedFigureNineSource.shape Variable
            sourceVariableDecidableEq
            (directSourceFormula decider symbols) := by
      have instanceEq :
          directFinalClauseDegreePatternVariableDecidableEq =
            sourceVariableDecidableEq :=
        Subsingleton.elim _ _
      cases instanceEq
      rfl
    rw [shapeEq]
    simpa only [source, typed, directSourceFormula] using
      retainedFinalExactOneShape_clauseLengths_eq_horizontalThreeDMTypedSourceComputed
        source
  have atLeastThreeEq :
      (FormulaShape.clauseProfiles
        (FormulaShapeFinalExactOne.shape
          (FormulaShapeRetainedFigureNineSource.shape
            (directSourceFormula decider symbols)))).map
            (fun profile => decide (3 ≤ profile.literals.length)) =
        typed.clauses.map (fun clause => decide (3 ≤ clause.length)) := by
    have mapped := congrArg
      (List.map fun length => decide (3 ≤ length)) lengthEq
    simpa only [List.map_map, Function.comp_def] using mapped
  calc
    _ =
        (FormulaShape.clauseProfiles
          (FormulaShapeFinalExactOne.shape
            (FormulaShapeRetainedFigureNineSource.shape
              (directSourceFormula decider symbols)))).map
                (fun profile =>
                  decide (3 ≤ profile.literals.length)) :=
      directSourceFinalClauseFans_hasRight_eq_finalShape
        decider symbols
    _ = typed.clauses.map
          (fun clause => decide (3 ≤ clause.length)) := atLeastThreeEq
    _ = typed.clauses.map
          (fun clause => decide (clause.length = 3)) := by
      apply List.map_congr_left
      intro clause clauseMember
      rcases horizontalThreeDMTypedSourceComputed_arityTwoOrThree
          source clause clauseMember with lengthTwo | lengthThree
      · simp [lengthTwo]
      · simp [lengthThree]

/-- The directly compiled one-color clause degree suffix is exactly the
degree suffix of the typed horizontal 3DM source. -/
theorem directSourceFinalClauseElementDegrees_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalClauseElementDegrees decider symbols =
      horizontalTypedClauseElementDegrees
        (horizontalThreeDMTypedSourceComputed
          (PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  let typed := horizontalThreeDMTypedSourceComputed
    (PolySpaceCompiler.formulaOfSymbols decider symbols)
  have booleans :=
    directSourceFinalClauseFans_hasRight_eq_typedClauseTernary
      decider symbols
  have blocks := congrArg
    (List.flatMap clauseElementDegreesOfTernary) booleans
  rw [horizontalTypedClauseElementDegrees_eq_clauseFlatMap]
  unfold directSourceFinalClauseElementDegrees
    FiniteUnaryFieldBlockMap.values
  change
    (directSourceFinalClauseFans decider symbols).flatMap
        (fun fan => clauseElementDegreesOfTernary fan.hasRight) = _
  simpa only [clauseElementDegreesOfTernary,
    List.flatMap_map, Function.comp_def,
    decide_eq_true_eq] using blocks

end LeanTrominoes.PeriodicCNFStripReduction
