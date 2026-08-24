/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmScanData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceBoundaryVariableRouteSiteData
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteFiberArms

/-! # Exact site-arm blocks of split-formula occurrences -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- A current-slice copied occurrence contributes nine full three-arm sites. -/
theorem currentOccurrenceVariableRouteSiteArmBlock_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (selected : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (selectedMember : selected ∈ (occurrenceIncidences source).zipIdx)
    (offsetZero : selected.1.edge.offset = (0, 0)) :
    (variableRouteSiteBlock selected.1.literal.atom (0, 0)).map
        (fun site =>
          ((variableRouteOccurrencesAt (formula source) site).take 3).map
            (fun occurrence =>
              targetDuplicatorArm
                (occurrence.incidence.numericRouteDescriptor
                  (formula source) occurrence.edgeIndex).targetPortRank)) =
      routedVariableCurrentCycleSiteArmBlocks := by
  unfold variableRouteSiteBlock
  simp only [List.map_map, Function.comp_def]
  simp_rw [variableRouteOccurrenceNumericArmsTakeThreeAt_formula_eq
    source selected selectedMember]
  rw [offsetZero]
  native_decide

/-- The zero-offset cycle block of a next-slice occurrence starts with three
cycle-only sites and ends with six full sites. -/
theorem nextOccurrenceVariableRouteCycleSiteArmBlock_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (selected : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (selectedMember : selected ∈ (occurrenceIncidences source).zipIdx)
    (offsetOne : selected.1.edge.offset = (1, 0)) :
    (variableRouteSiteBlock selected.1.literal.atom (0, 0)).map
        (fun site =>
          ((variableRouteOccurrencesAt (formula source) site).take 3).map
            (fun occurrence =>
              targetDuplicatorArm
                (occurrence.incidence.numericRouteDescriptor
                  (formula source) occurrence.edgeIndex).targetPortRank)) =
      routedVariableNextCycleSiteArmBlocks := by
  unfold variableRouteSiteBlock
  simp only [List.map_map, Function.comp_def]
  simp_rw [variableRouteOccurrenceNumericArmsTakeThreeAt_formula_eq
    source selected selectedMember]
  rw [offsetOne]
  native_decide

/-- The three sites beyond a next-slice occurrence's cycle block contain
only its copied left arm. -/
theorem nextOccurrenceVariableRouteBoundarySiteArmBlock_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (selected : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (selectedMember : selected ∈ (occurrenceIncidences source).zipIdx)
    (offsetOne : selected.1.edge.offset = (1, 0)) :
    (nextBoundaryVariableRouteSiteBlock selected.1.literal.atom).map
        (fun site =>
          ((variableRouteOccurrencesAt (formula source) site).take 3).map
            (fun occurrence =>
              targetDuplicatorArm
                (occurrence.incidence.numericRouteDescriptor
                  (formula source) occurrence.edgeIndex).targetPortRank)) =
      routedVariableNextBoundarySiteArmBlocks := by
  rw [nextBoundaryVariableRouteSiteBlock_eq]
  simp only [List.map_cons, List.map_nil]
  simp_rw [variableRouteOccurrenceNumericArmsTakeThreeAt_formula_eq
    source selected selectedMember]
  rw [offsetOne]
  native_decide

end LeanTrominoes.PeriodicThreeSATThree
