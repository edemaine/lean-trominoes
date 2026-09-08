/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceBlocks
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorSourceSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceWitness
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedRingAtomCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedRingVariableSemantics

/-! # Copied and cycle blocks of the complete direct occurrence stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directOccurrenceBlocksStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance directOccurrenceBlocksVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The copied prefix keeps its actual tail-table rows and starts both parent
and generated-clause indices at zero. -/
def directSourceFinalCopiedOccurrences (symbols : List encoding.Γ) : List SourceOccurrence :=
  sourceOccurrences (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
    (tailTables (directSourceFormula decider symbols))

/-- The cycle suffix starts after the copied parents and generated clauses,
consuming exactly the remaining rows of the actual source tail table. -/
def directSourceFinalCycleOccurrences (symbols : List encoding.Γ) : List SourceOccurrence :=
  let copied := directRetainedFigureNineCopiedClauseDescriptors decider symbols
  sourceOccurrencesFrom (sourceOccurrenceProfiles copied).length
    ((sourceOccurrenceProfiles copied).map generatedClauseCount).sum
    (directSourceFinalCycleClauseDescriptors decider symbols)
    ((tailTables (directSourceFormula decider symbols)).drop (sourceOccurrenceProfiles copied).length)

/-- The complete witness stream is exactly its copied prefix followed by its
cycle suffix; trailing variable markers contribute no records. -/
theorem directSourceFinalOccurrences_eq_copied_cycle (symbols : List encoding.Γ) :
    directSourceFinalOccurrences decider symbols =
      directSourceFinalCopiedOccurrences decider symbols ++ directSourceFinalCycleOccurrences decider symbols := by
  unfold directSourceFinalOccurrences occurrences
  rw [directSourceFinalClauseDescriptors_eq_source_prefix, sourceOccurrences_append_variables]
  unfold directSourceFinalClauseDescriptors sourceOccurrences
  rw [sourceOccurrencesFrom_append]
  simp only [Nat.zero_add, directSourceFinalCopiedOccurrences, directSourceFinalCycleOccurrences, sourceOccurrences]

/-- The copied occurrence boundary is also the compiled inherited-code
boundary, so prefix lookup uses the same global output index. -/
theorem directSourceFinalCopiedOccurrences_length_eq_codes (symbols : List encoding.Γ) :
    (directSourceFinalCopiedOccurrences decider symbols).length =
      (directSourceFinalCopiedInheritedRingAtomCodes decider symbols).length := by
  have lengthEq := congrArg List.length
    (directSourceFinalCopiedInheritedRingAtomCodes_eq_occurrence_values decider symbols
      (tailTables (directSourceFormula decider symbols)))
  simpa only [List.length_map, directSourceFinalCopiedOccurrences] using lengthEq.symm

private theorem copiedParentCount_eq (symbols : List encoding.Γ) :
    (sourceOccurrenceProfiles (directRetainedFigureNineCopiedClauseDescriptors decider symbols)).length =
      (copiedOccurrenceClauses (directSourceFormula decider symbols)).length := by
  change (sourceOccurrenceProfiles (copiedClauseDescriptors (directSourceFormula decider symbols))).length = _
  simp only [copiedClauseDescriptors, sourceOccurrenceProfiles_map_clauses,
    List.length_map, List.length_zipIdx, copiedOccurrenceClauses]

/-- The parent of a copied record lies in the actual copied-clause prefix. -/
theorem directSourceFinalCopiedOccurrences_parent_lt
    (symbols : List encoding.Γ) (occurrence : SourceOccurrence)
    (member : occurrence ∈ directSourceFinalCopiedOccurrences decider symbols) :
    occurrence.parentClauseIndex < (copiedOccurrenceClauses (directSourceFormula decider symbols)).length := by
  have bound := sourceOccurrencesFrom_parent_lt 0 0
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
    (tailTables (directSourceFormula decider symbols)) occurrence member
  simpa only [Nat.zero_add, copiedParentCount_eq] using bound

/-- A global occurrence lookup in the copied prefix retrieves the identical
coherent record from that prefix. -/
theorem directSourceFinalOccurrences_copied_lookup
    (symbols : List encoding.Γ) (index : Nat) (occurrence : SourceOccurrence)
    (copiedLt : index < (directSourceFinalCopiedOccurrences decider symbols).length)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence) :
    (directSourceFinalCopiedOccurrences decider symbols)[index]? = some occurrence := by
  rwa [directSourceFinalOccurrences_eq_copied_cycle, List.getElem?_append_left copiedLt] at lookup

/-- The complete inherited column agrees with its copied literal-value row
at every lookup in the copied occurrence prefix. -/
theorem directSourceFinalInheritedRingAtomCodes_copied_lookup
    (symbols : List encoding.Γ) (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalCopiedOccurrences decider symbols)[index]? = some occurrence) :
    (directSourceFinalInheritedRingAtomCodes decider symbols)[index]? =
      some (sourceOccurrenceCopiedValue
        ((copiedOccurrenceClauses (directSourceFormula decider symbols)).map
          (fun clause => clause.literals.map
            (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom))) occurrence) := by
  have indexLt := (List.getElem?_eq_some_iff.mp lookup).1
  have codeLt : index < (directSourceFinalCopiedInheritedRingAtomCodes decider symbols).length := by
    rw [← directSourceFinalCopiedOccurrences_length_eq_codes]
    exact indexLt
  rw [directSourceFinalInheritedRingAtomCodes, List.getElem?_append_left codeLt,
    directSourceFinalCopiedInheritedRingAtomCodes_eq_occurrence_values decider symbols
      (tailTables (directSourceFormula decider symbols))]
  change ((directSourceFinalCopiedOccurrences decider symbols).map _)[index]? = _
  simp only [List.getElem?_map, lookup, Option.map_some]

end LeanTrominoes.PeriodicCNFStripReduction

end
