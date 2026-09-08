/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATMacrocellCoordinates
import LeanTrominoes.PeriodicCNFIncidenceVertexIndices
import LeanTrominoes.PeriodicCNFFormulaShapeSourceAtomCoordinateCompiler
import LeanTrominoes.ListMapIdxOfSelfBEq
import LeanTrominoes.PeriodicOrthocrossingCorrectness

/-! # Closed-form positions of original atoms in the retained planar drawing -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The duplicator center for the source variable with deduplicated index i. -/
def retainedSourceAtomPosition (index : Nat) : Cell :=
  ((index * 160 + 86 : Nat), 47)

private theorem sourceAtom_vertex_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable)
    (member : atom ∈ formula.variableOccurrences.dedup) :
    CNFVertex.variable atom ∈ formula.incidenceGraph.vertices := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨atom, member, rfl⟩)

/-- Original atoms retain the incidence drawing's explicit protovertex point. -/
theorem periodicPlanarSATVariableDrawingPoint_sourceAtom
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable)
    (member : atom ∈ formula.variableOccurrences.dedup) :
    periodicPlanarSATVariableDrawingPoint formula (.atom atom) =
      (8 * (formula.variableOccurrences.dedup.idxOf atom : Int) + 4, 2) := by
  dsimp only [periodicPlanarSATVariableDrawingPoint, liftedIncidenceVertexPosition]
  rw [drawing_vertexPosition_of_mem formula.incidenceGraph
    (sourceAtom_vertex_mem formula atom member)]
  rw [PeriodicCNF.incidenceGraph_variable_vertexIndex formula atom member]
  simp [vertexPosition, vertexX, PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale]

/-- The protovertex point is already strictly inside the drawing period. -/
theorem sourceAtom_drawingPoint_bounds
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable)
    (member : atom ∈ formula.variableOccurrences.dedup) :
    let index := formula.variableOccurrences.dedup.idxOf atom
    let period : Int := drawingGridSize formula.incidenceGraph
    0 ≤ 8 * (index : Int) + 4 ∧ 8 * (index : Int) + 4 < period ∧
      0 ≤ (2 : Int) ∧ 2 < period := by
  have indexLt := List.idxOf_lt_length_iff.mpr
    (sourceAtom_vertex_mem formula atom member)
  rw [PeriodicCNF.incidenceGraph_variable_vertexIndex formula atom member] at indexLt
  dsimp only
  simp only [drawingGridSize, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  omega

/-- Canonical gauging does not move the original source-atom centers. -/
theorem retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_sourceAtom
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable)
    (member : atom ∈ formula.variableOccurrences.dedup) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
        ⟨.atom atom⟩ =
      retainedSourceAtomPosition (formula.variableOccurrences.dedup.idxOf atom) := by
  rw [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_eq_macrocell]
  unfold periodicPlanarSATVariableCanonicalDrawingPoint
  rw [periodicPlanarSATVariableDrawingPoint_sourceAtom formula atom member]
  have bounds := sourceAtom_drawingPoint_bounds formula atom member
  dsimp only
  rw [Int.emod_eq_of_lt bounds.1 bounds.2.1,
    Int.emod_eq_of_lt bounds.2.2.1 bounds.2.2.2]
  apply Prod.ext <;>
    simp [retainedSourceAtomPosition, periodicPlanarSATVariableLocalPosition,
      PlanarThreeSAT.duplicatorArmCenterPosition, planarMacroScale, Cell.add, Cell.scale]; ring

/-- The finite formula-shape coordinate compiler agrees with the canonical
placement whenever its variable count matches the source formula. -/
theorem retainedSourceAtomCoordinateFields_eq_positions
    {Variable : Type} [DecidableEq Variable]
    (horizontal keepPositive : Bool) (formula : PeriodicCNF Variable)
    (shape : List PeriodicCNF.FormulaShape.Token)
    (countEq : PeriodicCNF.FormulaShape.variableCount shape =
      formula.variableOccurrences.dedup.length) :
    PeriodicCNF.FormulaShapeSourceAtomCoordinates.values horizontal keepPositive shape =
      formula.variableOccurrences.dedup.map fun atom =>
        let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).position ⟨.atom atom⟩
        let coordinate := if horizontal then position.1 else position.2
        if keepPositive then coordinate.toNat else (-coordinate).toNat := by
  rw [PeriodicCNF.FormulaShapeSourceAtomCoordinates.values_eq_map, countEq]
  rw [← List.map_idxOf_self_eq_range_beq _ (List.nodup_dedup _), List.map_map]
  apply List.map_congr_left
  intro atom atomMember
  rw [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_sourceAtom _ atom atomMember]
  cases horizontal <;> cases keepPositive <;>
    simp [PeriodicCNF.FormulaShapeSourceAtomCoordinates.coordinate,
      PeriodicCNF.FormulaShapeSourceAtomCoordinates.factor,
      PeriodicCNF.FormulaShapeSourceAtomCoordinates.offset, retainedSourceAtomPosition] <;> omega

end LeanTrominoes.PeriodicOrthocrossing
