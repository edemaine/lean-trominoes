/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteAtomSiteArmBlock

/-! # Semantic routed-variable arm scan over rotated cycle sites -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- The rotated zero-offset site stream expands atom by atom to the
current/next cycle arm blocks selected by copied incidences. -/
theorem rotatedVariableRouteSiteBlocks_numericArms_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (rotatedVariableRouteSiteBlocks source).map
        (fun site =>
          ((variableRouteOccurrencesAt (formula source) site).take 3).map
            (fun occurrence =>
              targetDuplicatorArm
                (occurrence.incidence.numericRouteDescriptor
                  (formula source) occurrence.edgeIndex).targetPortRank)) =
      (rotatedOccurrenceVariables source).flatMap
        (routedVariableCycleSiteArmBlocksAtAtom source) := by
  unfold rotatedVariableRouteSiteBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro atom atomMember
  exact variableRouteSiteArmBlockAtAtom_eq
    source positiveOffsets atom atomMember

end LeanTrominoes.PeriodicThreeSATThree
