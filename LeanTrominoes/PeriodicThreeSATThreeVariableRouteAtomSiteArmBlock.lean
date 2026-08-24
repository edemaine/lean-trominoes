/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtomLookup

/-! # Semantic routed-variable arm blocks at occurrence atoms -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT

/-- The semantic zero-offset site block of one occurrence atom is exactly
the current/next arm block selected by its copied incidence. -/
theorem variableRouteSiteArmBlockAtAtom_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ rotatedOccurrenceVariables source) :
    (variableRouteSiteBlock atom (0, 0)).map
        (fun site =>
          ((variableRouteOccurrencesAt (formula source) site).take 3).map
            (fun occurrence =>
              targetDuplicatorArm
                (occurrence.incidence.numericRouteDescriptor
                  (formula source) occurrence.edgeIndex).targetPortRank)) =
      routedVariableCycleSiteArmBlocksAtAtom source atom := by
  have atomAllMember :=
    (mem_rotatedOccurrenceVariables_iff_allOccurrenceVariables
      source atom).mp atomMember
  rcases occurrenceIncidenceAtAtom_eq_some source atom atomAllMember with
    ⟨selected, selectedMember, selectedAtom, lookup⟩
  have offsetCases := positiveOffsets selected.1
    (List.fst_mem_of_mem_zipIdx selectedMember)
  unfold routedVariableCycleSiteArmBlocksAtAtom
  rw [lookup]
  rcases offsetCases with offsetZero | offsetOne
  · rw [← selectedAtom]
    have offsetZero' : Cell.sub selected.1.literal.offset
        (PeriodicCNF.clauseAnchor selected.1.clause) = (0, 0) := by
      simpa only [CNFIncidence.edge_offset] using offsetZero
    simpa [offsetZero'] using
      currentOccurrenceVariableRouteSiteArmBlock_eq
        source selected selectedMember offsetZero
  · rw [← selectedAtom]
    have offsetOne' : Cell.sub selected.1.literal.offset
        (PeriodicCNF.clauseAnchor selected.1.clause) = (1, 0) := by
      simpa only [CNFIncidence.edge_offset] using offsetOne
    simpa [offsetOne'] using
      nextOccurrenceVariableRouteCycleSiteArmBlock_eq
        source selected selectedMember offsetOne

end LeanTrominoes.PeriodicThreeSATThree
