/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalBoundedStableRankPairNodup
import LeanTrominoes.RetainedAngularOccurrenceStableRank
import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPortGeometry

/-! # Actual compass copies selected by bounded stable ranks -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- On a genuine occurrence, the bounded numeric rank selects its actual
compass port. The angular index starts at east, not at the variable encoding's
northwest port. -/
theorem occurrencePortsOfAngularOrder_eq_boundedGlobalStableRank
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate : RetainedOccurrenceTerminalCertificate source routes)
    (occurrences : source.OccurrencesAtMost 8)
    (tagged : PeriodicLiteral Variable × Nat × Nat)
    (member : tagged ∈ taggedLiterals source) :
    (occurrencePortsOfAngularOrder source (angularOccurrenceOrder source routes)).port
        tagged.2.1 tagged.2.2 =
      angularPortOfIndex (boundedRetainedTerminalSlot
        (retainedOccurrenceGlobalStableTerminalRank source routes
          (tagged.1.atom, tagged.2.1, tagged.2.2))).val := by
  have fiberMember := occurrenceVariables_mem source member
  have copyMember : (tagged.1.atom, tagged.2.1, tagged.2.2) ∈ allOccurrenceVariables source :=
    List.mem_map.mpr ⟨tagged, member, rfl⟩
  have rankEq := (angularOccurrenceVariables_idxOf_eq_stableTerminalRank
    source routes certificate tagged.1 tagged.2.1 tagged.2.2 member).trans
      (retainedOccurrenceStableTerminalRank_eq_global source routes tagged.1.atom
        (tagged.1.atom, tagged.2.1, tagged.2.2) fiberMember)
  have rankLt : retainedOccurrenceGlobalStableTerminalRank source routes
      (tagged.1.atom, tagged.2.1, tagged.2.2) < 8 :=
    (retainedOccurrenceGlobalStableTerminalRank_lt_count source routes _ copyMember).trans_le
      (occurrences tagged.1.atom)
  rw [occurrencePortsOfAngularOrder_eq source _ tagged member,
    boundedRetainedTerminalSlot_val_of_lt rankLt]
  change angularPortOfIndex ((angularOccurrenceVariables source routes tagged.1.atom).idxOf
    (tagged.1.atom, tagged.2.1, tagged.2.2)) = _
  rw [rankEq]

/-- The complete bounded atom/rank column decodes to the actual copied
variables in source occurrence order. -/
theorem selectedCopies_eq_boundedGlobalStableAtomRankPairs
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate : RetainedOccurrenceTerminalCertificate source routes)
    (occurrences : source.OccurrencesAtMost 8) :
    selectedCopies source (occurrencePortsOfAngularOrder source (angularOccurrenceOrder source routes)) =
      (retainedOccurrenceGlobalBoundedStableAtomRankPairs source routes).map
        (fun pair => copy pair.1 (angularPortOfIndex pair.2)) := by
  simp only [selectedCopies, retainedOccurrenceGlobalBoundedStableAtomRankPairs,
    allOccurrenceVariables, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro tagged member
  rw [occurrencePortsOfAngularOrder_eq_boundedGlobalStableRank source routes certificate
    occurrences tagged member]

end LeanTrominoes.PeriodicEightOccurrenceSplit
