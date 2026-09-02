/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceHorizontalEdgeBlockSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedElementDegrees
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodedDegree

/-! # Canonical element-degree lists of encoded horizontal 3DM -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- Typed red, green, and blue element degrees in the exact order retained by
the natural-number encoding. -/
def horizontalTypedElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Nat :=
  ((redElements source).map fun atom =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).redIncidences
        atom).length) ++
    ((greenElements source).map fun atom =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).greenIncidences
        atom).length) ++
    ((blueElements source).map fun atom =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).blueIncidences
        atom).length)

private theorem range_encodedProblem_red_degrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((List.range (redElements source).length).map fun index =>
        (encodedProblem source).degree .red index) =
      ((redElements source).map fun atom =>
        ((PeriodicPlanarOneInThreeToThreeDM.problem source).redIncidences
          atom).length) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound _rightBound
    have indexLt : index < (redElements source).length := by
      simpa using leftBound
    simp only [List.getElem_map, List.getElem_range]
    let atom := (redElements source)[index]'indexLt
    have atomMember : atom ∈ redElements source :=
      List.getElem_mem indexLt
    have indexEq : (redElements source).idxOf atom = index :=
      (redElements_nodup source).idxOf_getElem index indexLt
    change (encodedProblem source).degree .red index =
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).redIncidences
        atom).length
    rw [← indexEq]
    exact encodedProblem_red_degree source atom atomMember

private theorem range_encodedProblem_green_degrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((List.range (greenElements source).length).map fun index =>
        (encodedProblem source).degree .green index) =
      ((greenElements source).map fun atom =>
        ((PeriodicPlanarOneInThreeToThreeDM.problem source).greenIncidences
          atom).length) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound _rightBound
    have indexLt : index < (greenElements source).length := by
      simpa using leftBound
    simp only [List.getElem_map, List.getElem_range]
    let atom := (greenElements source)[index]'indexLt
    have atomMember : atom ∈ greenElements source :=
      List.getElem_mem indexLt
    have indexEq : (greenElements source).idxOf atom = index :=
      (greenElements_nodup source).idxOf_getElem index indexLt
    change (encodedProblem source).degree .green index =
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).greenIncidences
        atom).length
    rw [← indexEq]
    exact encodedProblem_green_degree source atom atomMember

private theorem range_encodedProblem_blue_degrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((List.range (blueElements source).length).map fun index =>
        (encodedProblem source).degree .blue index) =
      ((blueElements source).map fun atom =>
        ((PeriodicPlanarOneInThreeToThreeDM.problem source).blueIncidences
          atom).length) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound _rightBound
    have indexLt : index < (blueElements source).length := by
      simpa using leftBound
    simp only [List.getElem_map, List.getElem_range]
    let atom := (blueElements source)[index]'indexLt
    have atomMember : atom ∈ blueElements source :=
      List.getElem_mem indexLt
    have indexEq : (blueElements source).idxOf atom = index :=
      (blueElements_nodup source).idxOf_getElem index indexLt
    change (encodedProblem source).degree .blue index =
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).blueIncidences
        atom).length
    rw [← indexEq]
    exact encodedProblem_blue_degree source atom atomMember

/-- The numeric problem's canonical color-major degree column is exactly the
degree column of its typed element presentation. -/
theorem horizontalElementDegrees_encodedProblem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    CountedContractedIncidence.horizontalElementDegrees
        (encodedProblem source) =
      horizontalTypedElementDegrees source := by
  unfold CountedContractedIncidence.horizontalElementDegrees
    CountedContractedIncidence.horizontalElementPairs
    horizontalTypedElementDegrees
  simp only [incidenceColors, List.flatMap_cons, List.flatMap_nil,
    List.map_append, List.map_map, Function.comp_def,
    List.append_nil]
  rw [show (encodedProblem source).elementCount .red =
      (redElements source).length by rfl,
    show (encodedProblem source).elementCount .green =
      (greenElements source).length by rfl,
    show (encodedProblem source).elementCount .blue =
      (blueElements source).length by rfl]
  rw [range_encodedProblem_red_degrees,
    range_encodedProblem_green_degrees,
    range_encodedProblem_blue_degrees]
  simp only [List.append_assoc]

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Specialization to the proof-free normalized horizontal source used by the
strip reduction. -/
theorem horizontalElementDegrees_computed
    (source : PeriodicCNF Nat) :
    CountedContractedIncidence.horizontalElementDegrees
        (horizontalThreeDMProblemComputed source) =
      horizontalTypedElementDegrees
        (horizontalThreeDMTypedSourceComputed source) := by
  exact horizontalElementDegrees_encodedProblem
    (horizontalThreeDMTypedSourceComputed source)

end LeanTrominoes.PeriodicCNFStripReduction

end
