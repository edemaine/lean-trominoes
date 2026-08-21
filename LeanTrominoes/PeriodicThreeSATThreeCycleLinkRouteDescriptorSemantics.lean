/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceLiteralPortRank
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorExt
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceRankPrefix
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorData
import LeanTrominoes.PeriodicThreeSATThreeRouteDescriptorHeader

/-! # Correctness of explicit cycle-link route descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The explicit cycle-suffix record is exactly the semantic numeric route
descriptor at full-formula edge index `n+j`. -/
theorem cycleLinkIncidence_numericRouteDescriptor_eq
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (tagged : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (taggedMember : tagged ∈ (cycleLinkIncidences source).zipIdx) :
    tagged.1.numericRouteDescriptor (formula source)
        (PeriodicCNF.presentationLiteralCount source + tagged.2) =
      cycleLinkRouteDescriptor source tagged.1 tagged.2 := by
  have formulaMember :=
    cycleLinkIncidence_tagged_mem_formula source tagged taggedMember
  apply PeriodicOrthocrossing.RouteDescriptor.ext
  · simp [cycleLinkRouteDescriptor]
  · simp [cycleLinkRouteDescriptor]
  · simp [CNFIncidence.numericRouteDescriptor,
      cycleLinkRouteDescriptor]
  · simp [cycleLinkRouteDescriptor]
  · simp [CNFIncidence.numericRouteDescriptor,
      cycleLinkRouteDescriptor,
      formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables]
  · simpa [cycleLinkRouteDescriptor] using
      CNFIncidence.numericRouteDescriptor_sourcePortRank_eq_literalIndex
        (formula source)
        (tagged.1,
          PeriodicCNF.presentationLiteralCount source + tagged.2)
        formulaMember
  · simpa [cycleLinkRouteDescriptor] using
      cycleLinkIncidence_numericRouteDescriptor_targetPortRank
        source tagged taggedMember
  · simp [CNFIncidence.numericRouteDescriptor,
      cycleLinkRouteDescriptor]

end PeriodicThreeSATThree
end LeanTrominoes
