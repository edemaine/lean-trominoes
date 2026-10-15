/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Canonical.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Variable.PeriodicCNFStripDirectSourceFinalVariableElementDegreeSemantics

/-! # Horizontal semantics of direct final canonical element degrees -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


attribute [local instance]
  directFinalClauseDegreePatternVariableDecidableEq
  horizontalThreeDMTripleVariableDecidableEq

private theorem threeCopies_congr
    {Value : Type*} {first second : List Value}
    (equal : first = second) :
    first ++ first ++ first = second ++ second ++ second := by
  rw [equal]

private theorem horizontalTypedElementDegrees_instances_eq
    {Variable : Type*}
    (first second : DecidableEq Variable)
    (source : PeriodicCNF Variable) :
    @horizontalTypedElementDegrees Variable first source =
      @horizontalTypedElementDegrees Variable second source := by
  have instanceEq : first = second := Subsingleton.elim _ _
  cases instanceEq
  rfl

/-- The direct variable prefix and clause suffix together recover the common
one-color typed degree pattern. -/
theorem directSourceFinalOneColorElementDegrees_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalOneColorElementDegrees decider symbols =
      horizontalTypedOneColorElementDegrees
        (horizontalThreeDMTypedSourceComputed
          (ProgramSource.formulaOfSymbols decider symbols)) := by
  unfold directSourceFinalOneColorElementDegrees
    horizontalTypedOneColorElementDegrees
  rw [directSourceFinalVariableElementDegrees_eq_horizontalTyped,
    directSourceFinalClauseElementDegrees_eq_horizontalTyped]

private theorem directSourceFinalThreeColors_eq_horizontalTypedThreeColors
    (symbols : List encoding.Γ) :
    directSourceFinalOneColorElementDegrees decider symbols ++
        directSourceFinalOneColorElementDegrees decider symbols ++
        directSourceFinalOneColorElementDegrees decider symbols =
      horizontalTypedOneColorElementDegrees
        (horizontalThreeDMTypedSourceComputed
          (ProgramSource.formulaOfSymbols decider symbols)) ++
      horizontalTypedOneColorElementDegrees
        (horizontalThreeDMTypedSourceComputed
          (ProgramSource.formulaOfSymbols decider symbols)) ++
      horizontalTypedOneColorElementDegrees
        (horizontalThreeDMTypedSourceComputed
          (ProgramSource.formulaOfSymbols decider symbols)) :=
  threeCopies_congr
    (directSourceFinalOneColorElementDegrees_eq_horizontalTyped
      decider symbols)

private theorem horizontalTypedThreeColors_eq_horizontalTypedElementDegrees
    (symbols : List encoding.Γ) :
    horizontalTypedOneColorElementDegrees
          (horizontalThreeDMTypedSourceComputed
            (ProgramSource.formulaOfSymbols decider symbols)) ++
        horizontalTypedOneColorElementDegrees
          (horizontalThreeDMTypedSourceComputed
            (ProgramSource.formulaOfSymbols decider symbols)) ++
        horizontalTypedOneColorElementDegrees
          (horizontalThreeDMTypedSourceComputed
            (ProgramSource.formulaOfSymbols decider symbols)) =
      horizontalTypedElementDegrees
        (horizontalThreeDMTypedSourceComputed
          (ProgramSource.formulaOfSymbols decider symbols)) :=
  (horizontalTypedElementDegrees_eq_threeCopies
    (horizontalThreeDMTypedSourceComputed
      (ProgramSource.formulaOfSymbols decider symbols))
    (horizontalThreeDMTypedSourceComputed_occurrencesAtMostThree
      (ProgramSource.formulaOfSymbols decider symbols))
    (horizontalThreeDMTypedSourceComputed_arityTwoOrThree
      (ProgramSource.formulaOfSymbols decider symbols))).symm

private theorem directSourceFinalCanonicalElementDegrees_eq_typedThreeColors
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementDegrees decider symbols =
      horizontalTypedOneColorElementDegrees
          (horizontalThreeDMTypedSourceComputed
            (ProgramSource.formulaOfSymbols decider symbols)) ++
        horizontalTypedOneColorElementDegrees
          (horizontalThreeDMTypedSourceComputed
            (ProgramSource.formulaOfSymbols decider symbols)) ++
        horizontalTypedOneColorElementDegrees
          (horizontalThreeDMTypedSourceComputed
            (ProgramSource.formulaOfSymbols decider symbols)) :=
  (directSourceFinalCanonicalElementDegrees_eq_three_colors
    decider symbols).trans
      (directSourceFinalThreeColors_eq_horizontalTypedThreeColors
        decider symbols)

/-- The complete directly compiled RGB degree column agrees with the typed
horizontal source before its element names are encoded. -/
theorem directSourceFinalCanonicalElementDegrees_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementDegrees decider symbols =
      horizontalTypedElementDegrees
        (horizontalThreeDMTypedSourceComputed
          (ProgramSource.formulaOfSymbols decider symbols)) :=
  (directSourceFinalCanonicalElementDegrees_eq_typedThreeColors
    decider symbols).trans
      (horizontalTypedThreeColors_eq_horizontalTypedElementDegrees
        decider symbols)

private theorem directSourceFinalCanonicalElementDegrees_eq_encodedHorizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementDegrees decider symbols =
      @horizontalTypedElementDegrees RoutedVariable
        horizontalRibbonRoutedVariableDecidableEq
        (horizontalThreeDMTypedSourceComputed
          (ProgramSource.formulaOfSymbols decider symbols)) :=
  (directSourceFinalCanonicalElementDegrees_eq_horizontalTyped
    decider symbols).trans
      (horizontalTypedElementDegrees_instances_eq
        horizontalThreeDMTripleVariableDecidableEq
        horizontalRibbonRoutedVariableDecidableEq
        (horizontalThreeDMTypedSourceComputed
          (ProgramSource.formulaOfSymbols decider symbols)))

/-- The complete directly compiled RGB degree column is the actual canonical
element-degree column of the computed horizontal 3DM instance. -/
theorem directSourceFinalCanonicalElementDegrees_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementDegrees decider symbols =
      CountedContractedIncidence.horizontalElementDegrees
        (horizontalThreeDMProblemComputed
          (ProgramSource.formulaOfSymbols decider symbols)) :=
  (directSourceFinalCanonicalElementDegrees_eq_encodedHorizontalTyped
    decider symbols).trans
      (horizontalElementDegrees_computed
        (ProgramSource.formulaOfSymbols decider symbols)).symm

end LeanTrominoes.PeriodicCNFStripReduction
