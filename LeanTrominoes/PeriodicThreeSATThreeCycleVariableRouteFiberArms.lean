/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkNumericTargetArmFiber
import LeanTrominoes.PeriodicThreeSATThreeCycleVariableRouteFibers

/-! # Numeric target arms in cycle-link route fibers -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT

/-- At any neighboring translate of a copied occurrence, the cycle suffix
contributes its middle and right target arms. -/
theorem cycleLinkIncidenceFiberNumericArmsAt_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source)
    (position : Cell) :
    (((cycleLinkIncidences source).zipIdx
          (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun taggedIncidence =>
          translatedIncidenceOccurrencesAt taggedIncidence
            (atom, position))).map
        (fun occurrence =>
          targetDuplicatorArm
            (occurrence.incidence.numericRouteDescriptor
              (formula source) occurrence.edgeIndex).targetPortRank) =
      if position ∈ neighborTranslations then
        [.middle, .right]
      else
        [] := by
  rw [cycleLinkIncidenceFibersAt_eq_filter_map]
  by_cases positionMember : position ∈ neighborTranslations
  · simpa only [if_pos positionMember, List.map_map,
        Function.comp_def] using
      cycleLinkIncidenceNumericTargetArms_fiber_eq_middle_right
        source atom atomMember
  · simp [positionMember]

end LeanTrominoes.PeriodicThreeSATThree
