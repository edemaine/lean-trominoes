import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSoundness

/-!
# Terminal values of arbitrary planar 3DM matchings

After recovering a source assignment from the variable cycles, every
variable-side incidence of a merged clause terminal carries exactly the
truth value of its tagged source literal.  This is the arbitrary-matching
counterpart of the canonical terminal-value calculation.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM Gadget

/-- The connector boundary of a genuine occurrence reads the corresponding
source literal under the assignment recovered from the matching. -/
theorem occurrenceBoundary_connector_eq_literalTruth
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (translate : Cell) (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    (occurrenceBoundary source matching atom slot
        (Cell.add translate tagged.1.offset)).connector =
      PeriodicOneInThree.literalTruth
        (assignmentOfMatching source matching) translate tagged.1 := by
  have taggedData :=
    PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source atom slot tagged lookup
  have atomMember : atom ∈ occurringVariables source := by
    simpa [occurringVariables, taggedData.2] using
      (PeriodicOneInThreeToThreeDM.atom_mem_occurringVariables_of_tagged_mem
        source tagged taggedData.1)
  have slotMember : slot ∈ usedSlots source atom := by
    simp only [usedSlots, List.mem_filter]
    refine ⟨?_, Option.isSome_iff_exists.mpr ⟨tagged, lookup⟩⟩
    cases slot <;>
      simp [allOccurrenceSlots,
        PeriodicOneInThreeToThreeDM.OccurrenceSlot.all]
  have connector :=
    occurrenceBoundary_connector_eq_literalSignal
      source matching satisfies atom atomMember slot slotMember
        (Cell.add translate tagged.1.offset)
  have atomEq := taggedData.2
  subst atom
  simpa [assignmentOfMatching, occurrencePolarity, lookup,
    variableConnectorLiteralSignal,
    PeriodicOneInThree.literalTruth] using connector

/- One listed occurrence module contributes its recovered source-literal
truth value precisely when it belongs to the requested clause terminal. -/
set_option maxHeartbeats 1000000 in
theorem occurrenceBlock_terminalIncidentValues_ofMatching
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (entry : Variable × OccurrenceSlot)
    (entryMember : entry ∈ occurrenceEntries source)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) (cell : Cell) :
    (((occurrenceTriples source entry.1 entry.2).filterMap fun triple =>
      if terminalReferenceMatches
          source color clauseIndex group triple then
        some
          (⟨triple, terminalReferenceOffset source color triple⟩ :
            Incidence Variable)
      else none).map fun incidence =>
        (problem source).incidenceValue matching incidence cell) =
      (((occurrenceAt source entry.1 entry.2).toList.filter fun tagged =>
        tagged.2.1 = clauseIndex ∧
          terminalGroupOfLiteralIndex tagged.2.2 = group).map fun tagged =>
            PeriodicOneInThree.literalTruth
              (assignmentOfMatching source matching) cell tagged.1) := by
  rcases occurrenceAt_exists_of_entry_mem
      source entry entryMember with ⟨tagged, lookup⟩
  have entryData :=
    PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source entry.1 entry.2 tagged lookup
  have atomMember : entry.1 ∈ occurringVariables source := by
    simpa [occurringVariables, entryData.2] using
      (PeriodicOneInThreeToThreeDM.atom_mem_occurringVariables_of_tagged_mem
        source tagged entryData.1)
  have slotMember :=
    (mem_occurrenceEntries_iff
      source entry.1 entry.2).mp entryMember |>.2
  have connectorTruth :=
    occurrenceBoundary_connector_eq_literalTruth
      source matching satisfies cell entry.1 entry.2 tagged lookup
  by_cases terminalMatch :
      tagged.2.1 = clauseIndex ∧
        terminalGroupOfLiteralIndex tagged.2.2 = group
  · rcases terminalMatch with ⟨clauseEq, groupEq⟩
    cases polarityEq :
        occurrencePolarity source entry.1 entry.2 <;>
      cases color with
    | red =>
      cases kindEq :
          occurrenceConnectorKind source entry.1 entry.2 with
      | fixedRed =>
          have holds :=
            fixedRed_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember kindEq
                (Cell.add cell tagged.1.offset)
          have behavior :=
            fixedRedConnector_port_behavior _ holds
          simp_all [occurrenceTriples, allFixedRedTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, fixedRedTripleReferences,
            FixedRedConnectorTriple.references,
            fixedRedRedElement, redClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
      | fixedGreen =>
          have holds :=
            ordinary_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember .fixedGreen
                kindEq (Cell.add cell tagged.1.offset)
          have behavior :=
            variableOccurrence_port_behavior _ holds
          have secondTruth :
              matching
                  (.ordinary entry.1 entry.2 .fixedGreen .second)
                  (Cell.add cell tagged.1.offset) =
                !PeriodicOneInThree.literalTruth
                  (assignmentOfMatching source matching) cell tagged.1 := by
            calc
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedGreen .first)
                  (Cell.add cell tagged.1.offset) := by
                    rw [behavior.1]
                    simp
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedGreen .auxiliary)
                  (Cell.add cell tagged.1.offset) :=
                congrArg (fun value => !value) behavior.2
              _ = _ := by
                apply congrArg (fun value => !value)
                simpa [occurrenceBoundary, kindEq, polarityEq] using
                  connectorTruth
          simp_all [occurrenceTriples, allOrdinaryTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, ordinaryTripleReferences,
            VariableOccurrenceTriple.references,
            ordinaryRedElement, redClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
      | fixedBlue =>
          have holds :=
            ordinary_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember .fixedBlue
                kindEq (Cell.add cell tagged.1.offset)
          have behavior :=
            variableOccurrence_port_behavior _ holds
          have secondTruth :
              matching
                  (.ordinary entry.1 entry.2 .fixedBlue .second)
                  (Cell.add cell tagged.1.offset) =
                !PeriodicOneInThree.literalTruth
                  (assignmentOfMatching source matching) cell tagged.1 := by
            calc
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedBlue .first)
                  (Cell.add cell tagged.1.offset) := by
                    rw [behavior.1]
                    simp
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedBlue .auxiliary)
                  (Cell.add cell tagged.1.offset) :=
                congrArg (fun value => !value) behavior.2
              _ = _ := by
                apply congrArg (fun value => !value)
                simpa [occurrenceBoundary, kindEq, polarityEq] using
                  connectorTruth
          simp_all [occurrenceTriples, allOrdinaryTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, ordinaryTripleReferences,
            VariableOccurrenceTriple.references,
            ordinaryRedElement, redClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
    | green =>
      cases kindEq :
          occurrenceConnectorKind source entry.1 entry.2 with
      | fixedRed =>
          have holds :=
            fixedRed_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember kindEq
                (Cell.add cell tagged.1.offset)
          have behavior :=
            fixedRedConnector_port_behavior _ holds
          simp_all [occurrenceTriples, allFixedRedTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, fixedRedTripleReferences,
            FixedRedConnectorTriple.references,
            fixedRedGreenElement, greenClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
      | fixedGreen =>
          have holds :=
            ordinary_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember .fixedGreen
                kindEq (Cell.add cell tagged.1.offset)
          have behavior :=
            variableOccurrence_port_behavior _ holds
          have secondTruth :
              matching
                  (.ordinary entry.1 entry.2 .fixedGreen .second)
                  (Cell.add cell tagged.1.offset) =
                !PeriodicOneInThree.literalTruth
                  (assignmentOfMatching source matching) cell tagged.1 := by
            calc
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedGreen .first)
                  (Cell.add cell tagged.1.offset) := by
                    rw [behavior.1]
                    simp
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedGreen .auxiliary)
                  (Cell.add cell tagged.1.offset) :=
                congrArg (fun value => !value) behavior.2
              _ = _ := by
                apply congrArg (fun value => !value)
                simpa [occurrenceBoundary, kindEq, polarityEq] using
                  connectorTruth
          simp_all [occurrenceTriples, allOrdinaryTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, ordinaryTripleReferences,
            VariableOccurrenceTriple.references,
            ordinaryGreenElement, greenClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
      | fixedBlue =>
          have holds :=
            ordinary_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember .fixedBlue
                kindEq (Cell.add cell tagged.1.offset)
          have behavior :=
            variableOccurrence_port_behavior _ holds
          have secondTruth :
              matching
                  (.ordinary entry.1 entry.2 .fixedBlue .second)
                  (Cell.add cell tagged.1.offset) =
                !PeriodicOneInThree.literalTruth
                  (assignmentOfMatching source matching) cell tagged.1 := by
            calc
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedBlue .first)
                  (Cell.add cell tagged.1.offset) := by
                    rw [behavior.1]
                    simp
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedBlue .auxiliary)
                  (Cell.add cell tagged.1.offset) :=
                congrArg (fun value => !value) behavior.2
              _ = _ := by
                apply congrArg (fun value => !value)
                simpa [occurrenceBoundary, kindEq, polarityEq] using
                  connectorTruth
          simp_all [occurrenceTriples, allOrdinaryTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, ordinaryTripleReferences,
            VariableOccurrenceTriple.references,
            ordinaryGreenElement, greenClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
    | blue =>
      cases kindEq :
          occurrenceConnectorKind source entry.1 entry.2 with
      | fixedRed =>
          have holds :=
            fixedRed_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember kindEq
                (Cell.add cell tagged.1.offset)
          have behavior :=
            fixedRedConnector_port_behavior _ holds
          simp_all [occurrenceTriples, allFixedRedTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, fixedRedTripleReferences,
            FixedRedConnectorTriple.references,
            fixedRedBlueElement, blueClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
      | fixedGreen =>
          have holds :=
            ordinary_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember .fixedGreen
                kindEq (Cell.add cell tagged.1.offset)
          have behavior :=
            variableOccurrence_port_behavior _ holds
          simp_all [occurrenceTriples, allOrdinaryTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, ordinaryTripleReferences,
            VariableOccurrenceTriple.references,
            ordinaryBlueElement, blueClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
      | fixedBlue =>
          have holds :=
            ordinary_holds_of_satisfies source matching satisfies
              entry.1 atomMember entry.2 slotMember .fixedBlue
                kindEq (Cell.add cell tagged.1.offset)
          have behavior :=
            variableOccurrence_port_behavior _ holds
          have secondTruth :
              matching
                  (.ordinary entry.1 entry.2 .fixedBlue .second)
                  (Cell.add cell tagged.1.offset) =
                !PeriodicOneInThree.literalTruth
                  (assignmentOfMatching source matching) cell tagged.1 := by
            calc
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedBlue .first)
                  (Cell.add cell tagged.1.offset) := by
                    rw [behavior.1]
                    simp
              _ = !matching
                  (.ordinary entry.1 entry.2 .fixedBlue .auxiliary)
                  (Cell.add cell tagged.1.offset) :=
                congrArg (fun value => !value) behavior.2
              _ = _ := by
                apply congrArg (fun value => !value)
                simpa [occurrenceBoundary, kindEq, polarityEq] using
                  connectorTruth
          simp_all [occurrenceTriples, allOrdinaryTriples,
            terminalReferenceMatches, terminalReferenceOffset,
            tripleReferences, ordinaryTripleReferences,
            VariableOccurrenceTriple.references,
            ordinaryBlueElement, blueClauseTerminal,
            occurrenceClauseIndex, occurrenceLiteralIndex,
            TypedProblem.incidenceValue,
            sub_occurrenceReverseOffset,
            occurrenceBoundary]
  · have incidenceLength :=
      occurrenceBlock_terminalIncidences_length
        source entry entryMember color clauseIndex group
    have incidenceNil :
        ((occurrenceTriples source entry.1 entry.2).filterMap fun triple =>
          if terminalReferenceMatches
              source color clauseIndex group triple then
            some
              (⟨triple, terminalReferenceOffset source color triple⟩ :
                Incidence Variable)
          else none) = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [lookup, terminalMatch] using incidenceLength
    rw [incidenceNil]
    simp [lookup, terminalMatch]

/-- The terminal-value correspondence extends over any list of assembled
occurrence entries. -/
theorem occurrenceEntries_terminalIncidentValues_ofMatching
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (entries : List (Variable × OccurrenceSlot))
    (entriesSubset :
      ∀ entry ∈ entries, entry ∈ occurrenceEntries source)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) (cell : Cell) :
    (((entries.flatMap fun entry =>
      occurrenceTriples source entry.1 entry.2).filterMap fun triple =>
        if terminalReferenceMatches
            source color clauseIndex group triple then
          some
            (⟨triple, terminalReferenceOffset source color triple⟩ :
              Incidence Variable)
        else none).map (fun incidence =>
          (problem source).incidenceValue matching incidence cell)) =
      (((entries.filterMap fun entry =>
        occurrenceAt source entry.1 entry.2).filter fun tagged =>
          tagged.2.1 = clauseIndex ∧
            terminalGroupOfLiteralIndex tagged.2.2 = group).map
              (fun tagged =>
                PeriodicOneInThree.literalTruth
                  (assignmentOfMatching source matching)
                  cell tagged.1)) := by
  induction entries with
  | nil => rfl
  | cons entry rest induction =>
      have entryMember := entriesSubset entry (by simp)
      have restSubset :
          ∀ current ∈ rest, current ∈ occurrenceEntries source :=
        fun current currentMember =>
          entriesSubset current (by simp [currentMember])
      rw [List.flatMap_cons, List.filterMap_append, List.map_append,
        occurrenceBlock_terminalIncidentValues_ofMatching
          source matching satisfies entry entryMember
            color clauseIndex group cell,
        induction restSubset]
      cases lookup : occurrenceAt source entry.1 entry.2 with
      | none =>
          rcases occurrenceAt_exists_of_entry_mem
              source entry entryMember with ⟨tagged, taggedLookup⟩
          rw [lookup] at taggedLookup
          contradiction
      | some tagged =>
          by_cases terminalMatch :
              tagged.2.1 = clauseIndex ∧
                terminalGroupOfLiteralIndex tagged.2.2 = group
          · simp [lookup, terminalMatch]
          · simp [lookup, terminalMatch]

/-- All variable-side incidences of an arbitrary perfect matching at one
colored terminal enumerate the corresponding recovered source-literal truth
values. -/
theorem variableTerminalIncidentValues_ofMatching
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (color : WireColor) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) (cell : Cell) :
    ((variableTerminalIncidences
      source color clauseIndex group).map (fun incidence =>
        (problem source).incidenceValue matching incidence cell)) =
      (terminalOccurrenceEnumeration
        source clauseIndex group).map (fun tagged =>
          PeriodicOneInThree.literalTruth
            (assignmentOfMatching source matching) cell tagged.1) := by
  unfold variableTerminalIncidences terminalOccurrenceEnumeration
    occurrenceEnumeration
  rw [variableTriples_eq_occurrenceEntries_flatMap]
  exact occurrenceEntries_terminalIncidentValues_ofMatching
    source matching satisfies (occurrenceEntries source) (by simp)
      color clauseIndex group cell

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
