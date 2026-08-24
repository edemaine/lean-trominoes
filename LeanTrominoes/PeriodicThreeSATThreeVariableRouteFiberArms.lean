/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleVariableRouteFiberArms
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceVariableRouteFiberArms
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteOccurrenceFiberSplit

/-! # Numeric target arms in split-formula variable-route fibers -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT

/-- At a site of a selected copied occurrence, its optional left copied arm
precedes the always-paired middle/right cycle arms. -/
theorem variableRouteOccurrenceNumericArmsAt_formula_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (selected : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (selectedMember : selected ∈ (occurrenceIncidences source).zipIdx)
    (position : Cell) :
    (variableRouteOccurrencesAt (formula source)
        (selected.1.literal.atom, position)).map
        (fun occurrence =>
          targetDuplicatorArm
            (occurrence.incidence.numericRouteDescriptor
              (formula source) occurrence.edgeIndex).targetPortRank) =
      (if Cell.sub position selected.1.edge.offset ∈ neighborTranslations then
          [.left]
        else
          []) ++
      (if position ∈ neighborTranslations then
          [.middle, .right]
        else
          []) := by
  have atomMember : selected.1.literal.atom ∈
      allOccurrenceVariables source := by
    rw [← occurrenceIncidences_atoms]
    exact List.mem_map_of_mem (List.fst_mem_of_mem_zipIdx selectedMember)
  rw [variableRouteOccurrencesAt_formula_eq_occurrence_append_cycle_fibers,
    List.map_append,
    occurrenceIncidenceFiberNumericArmsAt_eq
      source selected selectedMember position,
    cycleLinkIncidenceFiberNumericArmsAt_eq
      source selected.1.literal.atom atomMember position]

/-- The routed-variable construction's three-occurrence truncation does not
discard anything from a split-formula variable-site fiber. -/
theorem variableRouteOccurrenceNumericArmsTakeThreeAt_formula_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (selected : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (selectedMember : selected ∈ (occurrenceIncidences source).zipIdx)
    (position : Cell) :
    ((variableRouteOccurrencesAt (formula source)
        (selected.1.literal.atom, position)).take 3).map
        (fun occurrence =>
          targetDuplicatorArm
            (occurrence.incidence.numericRouteDescriptor
              (formula source) occurrence.edgeIndex).targetPortRank) =
      (if Cell.sub position selected.1.edge.offset ∈ neighborTranslations then
          [.left]
        else
          []) ++
      (if position ∈ neighborTranslations then
          [.middle, .right]
        else
          []) := by
  rw [List.map_take,
    variableRouteOccurrenceNumericArmsAt_formula_eq
      source selected selectedMember position]
  split <;> split <;> rfl

end LeanTrominoes.PeriodicThreeSATThree
