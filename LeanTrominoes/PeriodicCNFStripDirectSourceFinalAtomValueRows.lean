/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSourceOccurrenceAtomValueRows
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedRingVariableSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorSourceSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRingAtomMembership

/-! # Actual parent rows underlying the complete inherited code column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicEightOccurrenceSplit PeriodicOrthocrossing OccurrenceSplitRing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance atomValueRowsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance atomValueRowsVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq

/-- Copied parents use their actual literal row, with the first literal's
code as the inherited column's unused parent-local fallback. -/
def directSourceFinalCopiedAtomValueBlocks (symbols : List encoding.Γ) :
    List (DirectedClauseProfile × SourceOccurrenceAtomValueRow) :=
  let source := directSourceFormula decider symbols
  (finalCoordinatedSource source).clauses.zipIdx.map fun tagged =>
    let values := (copiedOccurrenceClause source tagged.2 tagged.1).literals.map
      (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom)
    (copiedClauseProfile source tagged.2 tagged.1,
      { literals := values, localFallback := values.getD 0 0 })

/-- Each retained atom contributes the nine actual local cycle literal rows.
Parent-local fallback entries retain the cycle compiler's angular slot zero. -/
def directSourceFinalCycleAtomValueBlocks (symbols : List encoding.Γ) :
    List (DirectedClauseProfile × SourceOccurrenceAtomValueRow) :=
  (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase.variableOccurrences.dedup.flatMap
    (fun atom => PeriodicCNF.FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx.map
      (fun tagged =>
        (DirectedClauseProfile.ofClause cycleRoutes tagged.2 tagged.1,
          { literals := tagged.1.literals.map
              (fun literal => directSourceFinalRingVariableCode decider symbols (ringCopy atom literal.atom)),
            localFallback := directSourceFinalInheritedRingCode decider symbols atom 0 })))

def directSourceFinalAtomValueBlocks (symbols : List encoding.Γ) :
    List (DirectedClauseProfile × SourceOccurrenceAtomValueRow) :=
  directSourceFinalCopiedAtomValueBlocks decider symbols ++ directSourceFinalCycleAtomValueBlocks decider symbols

theorem directSourceFinalCopiedAtomValueBlocks_profiles (symbols : List encoding.Γ) :
    (directSourceFinalCopiedAtomValueBlocks decider symbols).map (fun block => Token.clause block.1) =
      directRetainedFigureNineCopiedClauseDescriptors decider symbols := by
  change _ = copiedClauseDescriptors (directSourceFormula decider symbols)
  simp only [directSourceFinalCopiedAtomValueBlocks, copiedClauseDescriptors, List.map_map, Function.comp_def]

theorem directSourceFinalCycleAtomValueBlocks_profiles (symbols : List encoding.Γ) :
    (directSourceFinalCycleAtomValueBlocks decider symbols).map (fun block => Token.clause block.1) =
      directSourceFinalCycleClauseDescriptors decider symbols := by
  rw [directSourceFinalCycleClauseDescriptors_eq_finiteCycle]
  unfold finiteCycleClauseDescriptors
  rw [sourceVariables_eq_variableOccurrences_dedup]
  change _ = (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase.variableOccurrences.dedup.flatMap _
  simp only [directSourceFinalCycleAtomValueBlocks, List.map_flatMap, List.map_map, Function.comp_def,
    PeriodicCNF.FormulaShapeFixedEightDirection.cycleClauseDescriptors]

/-- Both phase projections recover exactly the existing compiled parent list. -/
theorem directSourceFinalAtomValueBlocks_profiles (symbols : List encoding.Γ) :
    (directSourceFinalAtomValueBlocks decider symbols).map (fun block => Token.clause block.1) =
      directSourceFinalClauseDescriptors decider symbols := by
  rw [directSourceFinalAtomValueBlocks, List.map_append, directSourceFinalCopiedAtomValueBlocks_profiles,
    directSourceFinalCycleAtomValueBlocks_profiles]
  rfl

theorem directSourceFinalCopiedAtomValueBlocks_literals (symbols : List encoding.Γ) :
    (directSourceFinalCopiedAtomValueBlocks decider symbols).map (fun block => block.2.literals) =
      (copiedOccurrenceClauses (directSourceFormula decider symbols)).map
        (fun clause => clause.literals.map (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom)) := by
  simp only [directSourceFinalCopiedAtomValueBlocks, copiedOccurrenceClauses, List.map_map, Function.comp_def]

theorem directSourceFinalCycleAtomValueBlocks_literals (symbols : List encoding.Γ) :
    (directSourceFinalCycleAtomValueBlocks decider symbols).map (fun block => block.2.literals) =
      (finalCycleClauses (directSourceFormula decider symbols)).map
        (fun clause => clause.literals.map (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom)) := by
  have mapped := congrArg (List.map (List.map (directSourceFinalRingVariableCode decider symbols)))
    (finalCycleClauses_atom_rows (directSourceFormula decider symbols))
  calc
    _ = (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase.variableOccurrences.dedup.flatMap
        (fun atom => PeriodicCNF.FormulaShapeFixedEightDirection.localCycleFormula.clauses.map
          (fun clause => clause.literals.map
            (fun literal => directSourceFinalRingVariableCode decider symbols (ringCopy atom literal.atom)))) := by
      simp only [directSourceFinalCycleAtomValueBlocks, List.map_flatMap, List.map_map, Function.comp_def]
      apply List.flatMap_congr
      intro atom _member
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun clause => clause.literals.map
          (fun literal => directSourceFinalRingVariableCode decider symbols (ringCopy atom literal.atom))))
          (List.zipIdx_map_fst 0 PeriodicCNF.FormulaShapeFixedEightDirection.localCycleFormula.clauses)
    _ = _ := by
      simpa only [List.map_map, List.map_flatMap, Function.comp_def] using mapped.symm

/-- Literal fields of the parent rows are precisely the complete actual
pre-Figure 9 formula's literal-code rows, in its original parent order. -/
theorem directSourceFinalAtomValueBlocks_literals (symbols : List encoding.Γ) :
    (directSourceFinalAtomValueBlocks decider symbols).map (fun block => block.2.literals) =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.map
        (fun clause => clause.literals.map (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom)) := by
  rw [directSourceFinalAtomValueBlocks, List.map_append, directSourceFinalCopiedAtomValueBlocks_literals,
    directSourceFinalCycleAtomValueBlocks_literals, finalPositionedFormula_clauses_eq_descriptorBlocks, List.map_append]

end LeanTrominoes.PeriodicCNFStripReduction

end
