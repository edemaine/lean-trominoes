/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRoutedDescriptorBlocks
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCycleDrawing
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOccurrenceStableRank
import LeanTrominoes.PeriodicEightOccurrenceSplitExactVariableCount

/-! # Actual ring atoms of the retained Figure 9 source -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplit PeriodicOrthocrossing PeriodicThreeSATThree
open OccurrenceSplitRing

/-- The positioned cycle suffix keeps the local template's literal rows,
renaming each ring vertex by its retained source atom in stable atom order. -/
theorem finalCycleClauses_atom_rows
    {Variable : Type} [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (finalCycleClauses source).map (fun clause => clause.literals.map PeriodicLiteral.atom) =
      (retainedFinalCoordinatedScaledSource source).erase.variableOccurrences.dedup.flatMap
        (fun atom => FormulaShapeFixedEightDirection.localCycleFormula.clauses.map
          (fun clause => clause.literals.map (fun literal => ringCopy atom literal.atom))) := by
  unfold finalCycleClauses PeriodicEightOccurrenceSplitPositioned.allCycleClauses
  simp only [List.map_map, List.map_flatMap, Function.comp_def, PositionedPeriodicClause.scale_literals]
  rw [sourceVariables_eq_variableOccurrences_dedup]
  change ((retainedFinalCoordinatedScaledSource source).erase.variableOccurrences.dedup.flatMap _) = _
  apply congrArg (fun block =>
    (retainedFinalCoordinatedScaledSource source).erase.variableOccurrences.dedup.flatMap block)
  funext atom
  rw [PeriodicEightOccurrenceSplitPositioned.cycleClausesFor_eq_cycleFormula]
  simp only [List.map_map, PeriodicEightOccurrenceSplitPositioned.positionedLocalCycleClause,
    periodicCycleClause, FormulaShapeFixedEightDirection.localCycleFormula,
    FormulaShapeFixedEightDirection.localCycleClause, Function.comp_def]

/-- Every copied literal names a compass copy of an atom occurring in the
actual retained source. -/
theorem copiedOccurrenceClauses_atom_is_ringCopy
    {Variable : Type} [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable))
    (member : atom ∈ (copiedOccurrenceClauses source).flatMap
      (fun clause => clause.literals.map PeriodicLiteral.atom)) :
    ∃ original vertex,
      original ∈ (retainedFinalCoordinatedScaledSource source).erase.variableOccurrences ∧
      atom = ringCopy original vertex := by
  unfold copiedOccurrenceClauses at member
  rw [List.flatMap_map] at member
  obtain ⟨taggedClause, clauseMember, member⟩ := List.mem_flatMap.mp member
  obtain ⟨literal, literalMember, rfl⟩ := List.mem_map.mp member
  change literal ∈ taggedClause.1.literals.zipIdx.map
    (fun tagged => occurrenceLiteral (occurrencePortsForFigureSeven source) taggedClause.2 tagged.2 tagged.1) at literalMember
  obtain ⟨taggedLiteral, sourceLiteralMember, rfl⟩ := List.mem_map.mp literalMember
  refine ⟨taggedLiteral.1.atom,
    RingVertex.port ((occurrencePortsForFigureSeven source).port taggedClause.2 taggedLiteral.2), ?_, rfl⟩
  unfold retainedFinalCoordinatedScaledSource
  rw [PositionedPeriodicCNF.erase_scale]
  simp only [PeriodicCNF.variableOccurrences, PositionedPeriodicCNF.erase, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨taggedClause.1, List.fst_mem_of_mem_zipIdx clauseMember,
    List.mem_map.mpr ⟨taggedLiteral.1, List.fst_mem_of_mem_zipIdx sourceLiteralMember, rfl⟩⟩

/-- Every cycle literal names a compass or separator copy of an atom
occurring in the actual retained source. -/
theorem finalCycleClauses_atom_is_ringCopy
    {Variable : Type} [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable))
    (member : atom ∈ (finalCycleClauses source).flatMap
      (fun clause => clause.literals.map PeriodicLiteral.atom)) :
    ∃ original vertex,
      original ∈ (retainedFinalCoordinatedScaledSource source).erase.variableOccurrences ∧
      atom = ringCopy original vertex := by
  obtain ⟨clause, clauseMember, atomMember⟩ := List.mem_flatMap.mp member
  have rowMember : clause.literals.map PeriodicLiteral.atom ∈
      (finalCycleClauses source).map (fun entry => entry.literals.map PeriodicLiteral.atom) :=
    List.mem_map.mpr ⟨clause, clauseMember, rfl⟩
  rw [finalCycleClauses_atom_rows] at rowMember
  obtain ⟨original, originalMember, rowMember⟩ := List.mem_flatMap.mp rowMember
  obtain ⟨localClause, _localMember, rowEq⟩ := List.mem_map.mp rowMember
  rw [← rowEq] at atomMember
  obtain ⟨literal, _literalMember, atomEq⟩ := List.mem_map.mp atomMember
  exact ⟨original, literal.atom, List.mem_dedup.mp originalMember, atomEq.symm⟩

/-- All atoms in the complete pre-Figure 9 formula are genuine fixed-ring
copies of represented retained source atoms. -/
theorem finalPositionedFormula_atom_is_ringCopy
    {Variable : Type} [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable))
    (member : atom ∈
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source).erase.variableOccurrences) :
    ∃ original vertex,
      original ∈ (retainedFinalCoordinatedScaledSource source).erase.variableOccurrences ∧
      atom = ringCopy original vertex := by
  simp only [PeriodicCNF.variableOccurrences, PositionedPeriodicCNF.erase, List.flatMap_map] at member
  rw [finalPositionedFormula_clauses_eq_descriptorBlocks, List.flatMap_append, List.mem_append] at member
  exact member.elim (copiedOccurrenceClauses_atom_is_ringCopy source atom)
    (finalCycleClauses_atom_is_ringCopy source atom)

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineDirection
