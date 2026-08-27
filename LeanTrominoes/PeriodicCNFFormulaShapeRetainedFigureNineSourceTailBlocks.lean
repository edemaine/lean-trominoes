/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceTailRecordData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRoutedDescriptorBlocks

/-! # Copied and cycle phases of retained Figure Nine source tails -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNineSourceTail
open FormulaShapeRetainedFigureNineDirection
open PeriodicOrthocrossing

/-- Dynamic tail rows belonging to the copied retained planar clauses. -/
def copiedTailTables {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (List (List AxisDirection)) :=
  let routes :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source
  (copiedOccurrenceClauses source).zipIdx.map fun taggedClause =>
    orderedTailDirections routes taggedClause.2 taggedClause.1

/-- Tail rows belonging to the fixed Figure Seven implication-cycle suffix,
indexed after the copied-clause prefix exactly as in the public route family. -/
def cycleTailTables {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (List (List AxisDirection)) :=
  let routes :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source
  (finalCycleClauses source).zipIdx (copiedClauseCount source) |>.map
    fun taggedClause =>
      orderedTailDirections routes taggedClause.2 taggedClause.1

/-- One positioned implication-cycle tail block at its stable source-variable
index.  This form exposes the fixed-width outer scan before the local Figure
Seven geometry is reduced to a finite table. -/
def indexedCycleTailTableBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedAtom :
      WrappedPeriodicPlanarSATVariable Variable × Nat) :
    List (List (List AxisDirection)) :=
  let routes :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source
  let clauses :=
    (PeriodicEightOccurrenceSplitPositioned.cycleClausesFor
      (placementScaledForFigureSeven source) taggedAtom.1).map
        (PositionedPeriodicClause.scale
          PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement)
  (clauses.zipIdx
    (copiedClauseCount source +
      FormulaShapeFixedEight.copiesPerVariable * taggedAtom.2)).map
        fun taggedClause =>
          orderedTailDirections routes taggedClause.2 taggedClause.1

@[simp] theorem copiedTailTables_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (copiedTailTables source).length =
      (copiedOccurrenceClauses source).length := by
  simp [copiedTailTables]

@[simp] theorem cycleTailTables_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleTailTables source).length =
      (finalCycleClauses source).length := by
  simp [cycleTailTables]

/-- The semantic tail table is phase-major: copied retained clauses first,
then the fixed implication-cycle clauses. -/
theorem tailTables_eq_blocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    tailTables source = copiedTailTables source ++ cycleTailTables source := by
  simp only [tailTables, copiedTailTables, cycleTailTables]
  rw [finalPositionedFormula_clauses_eq_descriptorBlocks,
    List.zipIdx_append, List.map_append,
    copiedOccurrenceClauses_length_eq_copiedClauseCount]
  simp only [Nat.zero_add]

/-- The complete cycle tail suffix is a fixed-width indexed scan over the
stable retained source-variable enumeration. -/
theorem cycleTailTables_eq_indexedBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    cycleTailTables source =
      (PeriodicThreeSATThree.sourceVariables
        (sourceScaledForFigureSeven source).erase).zipIdx.flatMap
          (indexedCycleTailTableBlock source) := by
  let atoms := PeriodicThreeSATThree.sourceVariables
    (sourceScaledForFigureSeven source).erase
  let block := fun atom =>
    (PeriodicEightOccurrenceSplitPositioned.cycleClausesFor
      (placementScaledForFigureSeven source) atom).map
        (PositionedPeriodicClause.scale
          PeriodicEightOccurrenceSplit.retainedTerminalFanRoutingRefinement)
  have blockLength : ∀ atom, (block atom).length =
      FormulaShapeFixedEight.copiesPerVariable := by
    intro atom
    simp [block,
      PeriodicEightOccurrenceSplitPositioned.cycleClausesFor]
  unfold cycleTailTables
  rw [finalCycleClauses_eq_flatMap_scaledCycleBlocks]
  change ((atoms.flatMap block).zipIdx (copiedClauseCount source)).map _ = _
  rw [IndexedListScan.flatMap_zipIdx_eq_zipIdx_flatMap_fixed_zero
    atoms block FormulaShapeFixedEight.copiesPerVariable
    (copiedClauseCount source) blockLength]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  rintro ⟨atom, atomIndex⟩ atomMember
  rfl

end FormulaShapeRetainedFigureNineSourceTail

namespace FormulaShapeRetainedFigureNineSourceTailRecord

open FormulaShapeFigureNinePolarityRouteTailRecord
open FormulaShapeRetainedFigureNineDirection
open FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNFStripReduction
open PeriodicOrthocrossing

/-- Flat records for copied retained clauses, kept separate because their
tails inherit the dynamic orthocrossing source routes. -/
def copiedRecordTokens {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List HorizontalRoutedRouteTailRecord.Token :=
  sourceRecordTokens
    (routedCopiedClauseDescriptors source)
    (copiedTailTables source)

/-- Flat records for the fixed Figure Seven implication-cycle suffix. -/
def cycleRecordTokens {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List HorizontalRoutedRouteTailRecord.Token :=
  sourceRecordTokens
    (routedCycleClauseDescriptors source)
    (cycleTailTables source)

private theorem copiedTailTables_length_eq_clauseCount
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (copiedTailTables source).length =
      sourceClauseCount (routedCopiedClauseDescriptors source) := by
  rw [copiedTailTables_length]
  unfold routedCopiedClauseDescriptors copiedOccurrenceClauses
  simp

private theorem cycleTailTables_length_eq_clauseCount
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleTailTables source).length =
      sourceClauseCount (routedCycleClauseDescriptors source) := by
  rw [cycleTailTables_length]
  unfold routedCycleClauseDescriptors
  simp

/-- The retained flat record stream splits exactly into its dynamic copied
prefix and fixed implication-cycle suffix; trailing variable markers consume
neither a tail row nor an output record. -/
theorem recordTokens_eq_blocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    recordTokens source =
      copiedRecordTokens source ++ cycleRecordTokens source := by
  unfold recordTokens copiedRecordTokens cycleRecordTokens
  rw [FormulaShapeRetainedFigureNineDirection.descriptors_eq_routedDescriptors,
    FormulaShapeRetainedFigureNineDirection.routedDescriptors,
    FormulaShapeRetainedFigureNineSourceTail.tailTables_eq_blocks]
  rw [List.append_assoc]
  let variableCount :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source).erase.variableOccurrences.dedup.length
  let variableTokens := List.replicate variableCount
    FormulaShapeDirectionOrdering.Token.variable
  change sourceRecordTokens
      (routedCopiedClauseDescriptors source ++
        (routedCycleClauseDescriptors source ++ variableTokens))
      (copiedTailTables source ++ cycleTailTables source) = _
  calc
    _ = sourceRecordTokens
          (routedCopiedClauseDescriptors source)
          (copiedTailTables source) ++
        sourceRecordTokens
          (routedCycleClauseDescriptors source ++ variableTokens)
          (cycleTailTables source) := by
      exact sourceRecordTokens_append
        (routedCopiedClauseDescriptors source)
        (routedCycleClauseDescriptors source ++ variableTokens)
        (copiedTailTables source) (cycleTailTables source)
        (copiedTailTables_length_eq_clauseCount source)
    _ = sourceRecordTokens
          (routedCopiedClauseDescriptors source)
          (copiedTailTables source) ++
        sourceRecordTokens
          (routedCycleClauseDescriptors source)
          (cycleTailTables source) := by
      have split := sourceRecordTokens_append
        (routedCycleClauseDescriptors source) variableTokens
        (cycleTailTables source) []
        (cycleTailTables_length_eq_clauseCount source)
      simp only [List.append_nil] at split
      rw [split, sourceRecordTokens_replicate_variable]
      simp

end FormulaShapeRetainedFigureNineSourceTailRecord
end PeriodicCNF
end LeanTrominoes
