/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapFilterSingleton
import LeanTrominoes.PeriodicCNFPlanarVariablePortGeometry
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkNumericTargetRankLight

/-! # Target arms within one cycle-link occurrence fiber -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT

/-- The two globally ordered cycle incidences at one copied occurrence use
the middle and right duplicator arms. -/
theorem cycleLinkIncidenceNumericTargetArms_fiber_eq_middle_right
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source) :
    ((((cycleLinkIncidences source).zipIdx
          (PeriodicCNF.presentationLiteralCount source)).filter
        fun taggedIncidence =>
          taggedIncidence.1.literal.atom = atom).map
        fun taggedIncidence =>
          targetDuplicatorArm
            (taggedIncidence.1.numericRouteDescriptor
              (formula source) taggedIncidence.2).targetPortRank) =
      [.middle, .right] := by
  have ranks := cycleLinkIncidenceNumericTargetRanks_fiber_eq_one_two
    source atom atomMember
  have arms := congrArg (List.map targetDuplicatorArm) ranks
  simp only [List.map_flatMap, apply_ite, List.map_cons, List.map_nil,
    targetDuplicatorArm] at arms
  change (((cycleLinkIncidences source).zipIdx
      (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun taggedIncidence =>
          if taggedIncidence.1.literal.atom = atom then
            [targetDuplicatorArm
              (taggedIncidence.1.numericRouteDescriptor
                (formula source) taggedIncidence.2).targetPortRank]
          else [])) = [.middle, .right] at arms
  rw [flatMap_if_singleton_eq_filter_map] at arms
  exact arms

end LeanTrominoes.PeriodicThreeSATThree
