/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankComparisonComponents
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateScaling

/-! # Scaling global retained-terminal comparison streams -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

variable {Variable : Type*} [DecidableEq Variable]

private theorem retained_of_mem_allOccurrenceVariables
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ allOccurrenceVariables source) :
    RetainedTerminalRayVector
      (occurrenceTerminalVector routes copy) := by
  apply certificate copy.1 copy
  rw [occurrenceVariables_eq_filter]
  simp [copyMember]

/-- Positive uniform route scaling leaves the complete target-major strict
terminal comparison stream unchanged. -/
theorem retainedOccurrenceGlobalTerminalStrictLowerBits_scaleIncidenceRoutes
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    {factor : Nat} (factorPositive : 0 < factor) :
    retainedOccurrenceGlobalTerminalStrictLowerBits source
        (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes) =
      retainedOccurrenceGlobalTerminalStrictLowerBits source routes := by
  unfold retainedOccurrenceGlobalTerminalStrictLowerBits
    retainedOccurrenceGlobalOrderedPairs
  dsimp only
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro target targetMember
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro candidate candidateMember
  simp only [Function.comp_apply]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact
    retainedOccurrenceTerminalCoordinate_lt_scaleIncidenceRoutes_iff
      factorPositive routes candidate target
      (retained_of_mem_allOccurrenceVariables
        source routes certificate candidate candidateMember)
      (retained_of_mem_allOccurrenceVariables
        source routes certificate target targetMember)

/-- Positive uniform route scaling leaves the complete target-major terminal
equality stream unchanged. -/
theorem retainedOccurrenceGlobalTerminalEqualityBits_scaleIncidenceRoutes
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    {factor : Nat} (factorPositive : 0 < factor) :
    retainedOccurrenceGlobalTerminalEqualityBits source
        (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes) =
      retainedOccurrenceGlobalTerminalEqualityBits source routes := by
  unfold retainedOccurrenceGlobalTerminalEqualityBits
    retainedOccurrenceGlobalOrderedPairs
  dsimp only
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro target targetMember
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro candidate candidateMember
  simp only [Function.comp_apply]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact
    retainedOccurrenceTerminalCoordinate_eq_scaleIncidenceRoutes_iff
      factorPositive routes candidate target
      (retained_of_mem_allOccurrenceVariables
        source routes certificate candidate candidateMember)
      (retained_of_mem_allOccurrenceVariables
        source routes certificate target targetMember)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
