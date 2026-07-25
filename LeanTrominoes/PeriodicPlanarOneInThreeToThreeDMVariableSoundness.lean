import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMLocalSoundness

/-!
# Recovering source-variable phases from planar 3DM matchings

The private constraints classify each occurrence module as a common signed
connector boundary.  Exact cover of the red links then synchronizes those
boundaries around every one-, two-, or three-occurrence variable cycle.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/-- The logical boundary read from one occurrence module in an arbitrary
matching.  Negative occurrences exchange the two physical continuation
ports, so `first` always denotes the source-variable phase at this slot. -/
def occurrenceBoundary {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (atom : Variable) (slot : OccurrenceSlot) (cell : Cell) :
    VariableConnectorBoundary :=
  let polarity := occurrencePolarity source atom slot
  match occurrenceConnectorKind source atom slot with
  | .fixedRed =>
      let selected := fun triple =>
        matching (.fixedRed atom slot triple) cell
      if polarity then
        ⟨selected .bottomLeft, selected .topLeft, selected .auxiliary⟩
      else
        ⟨selected .topLeft, selected .bottomLeft, selected .auxiliary⟩
  | .fixedGreen =>
      let selected := fun triple =>
        matching (.ordinary atom slot .fixedGreen triple) cell
      if polarity then
        ⟨selected .first, selected .second, selected .auxiliary⟩
      else
        ⟨selected .second, selected .first, selected .auxiliary⟩
  | .fixedBlue =>
      let selected := fun triple =>
        matching (.ordinary atom slot .fixedBlue triple) cell
      if polarity then
        ⟨selected .first, selected .second, selected .auxiliary⟩
      else
        ⟨selected .second, selected .first, selected .auxiliary⟩

/-- A perfect matching realizes the common signed boundary contract at every
listed occurrence module. -/
theorem occurrenceBoundary_realizableFor_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (cell : Cell) :
    (occurrenceBoundary source matching atom slot cell).RealizableFor
      (occurrenceConnectorKind source atom slot)
      (occurrencePolarity source atom slot) := by
  cases kindEq :
      occurrenceConnectorKind source atom slot with
  | fixedRed =>
      have holds :=
        fixedRed_holds_of_satisfies source matching satisfies
          atom atomMember slot slotMember kindEq cell
      cases polarityEq : occurrencePolarity source atom slot <;>
        simp [occurrenceBoundary, kindEq, polarityEq,
          VariableConnectorBoundary.RealizableFor,
          VariableConnectorBoundary.Realizable,
          VariableConnectorBoundary.swapContinuations] <;>
        exact ⟨_, holds, rfl, rfl, rfl⟩
  | fixedGreen =>
      have holds :=
        ordinary_holds_of_satisfies source matching satisfies
          atom atomMember slot slotMember .fixedGreen kindEq cell
      cases polarityEq : occurrencePolarity source atom slot <;>
        simp [occurrenceBoundary, kindEq, polarityEq,
          VariableConnectorBoundary.RealizableFor,
          VariableConnectorBoundary.Realizable,
          VariableConnectorBoundary.swapContinuations] <;>
        exact ⟨_, holds, rfl, rfl, rfl⟩
  | fixedBlue =>
      have holds :=
        ordinary_holds_of_satisfies source matching satisfies
          atom atomMember slot slotMember .fixedBlue kindEq cell
      cases polarityEq : occurrencePolarity source atom slot <;>
        simp [occurrenceBoundary, kindEq, polarityEq,
          VariableConnectorBoundary.RealizableFor,
          VariableConnectorBoundary.Realizable,
          VariableConnectorBoundary.swapContinuations] <;>
        exact ⟨_, holds, rfl, rfl, rfl⟩

/-- Every occurring variable uses exactly the first one, two, or three
slots.  Occurrences beyond the reduction's promised bound are irrelevant to
this structural prefix fact. -/
theorem usedSlots_cases_of_atom_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source) :
    usedSlots source atom = [.first] ∨
      usedSlots source atom = [.first, .second] ∨
      usedSlots source atom = [.first, .second, .third] := by
  have atomOccurs :
      atom ∈ PeriodicCNF.variableOccurrences source := by
    simpa [occurringVariables,
      PeriodicOneInThreeToThreeDM.occurringVariables] using atomMember
  have nonempty : occurrencesOf source atom ≠ [] := by
    intro empty
    have positive := List.count_pos_iff.mpr atomOccurs
    rw [← PeriodicOneInThreeToThreeDM.occurrencesOf_length
      source atom] at positive
    change
      PeriodicOneInThreeToThreeDM.occurrencesOf source atom = [] at empty
    rw [empty] at positive
    simp at positive
  generalize occurrencesEq :
      occurrencesOf source atom = occurrences at nonempty
  cases occurrences with
  | nil => contradiction
  | cons first rest =>
      cases rest with
      | nil =>
          left
          change
            PeriodicOneInThreeToThreeDM.occurrencesOf source atom =
              [first] at occurrencesEq
          have firstLookup :
              occurrenceAt source atom .first = some first := by
            change
              (PeriodicOneInThreeToThreeDM.occurrencesOf
                source atom)[0]? = some first
            simp [occurrencesEq]
          have secondLookup :
              occurrenceAt source atom .second = none := by
            change
              (PeriodicOneInThreeToThreeDM.occurrencesOf
                source atom)[1]? = none
            simp [occurrencesEq]
          have thirdLookup :
              occurrenceAt source atom .third = none := by
            change
              (PeriodicOneInThreeToThreeDM.occurrencesOf
                source atom)[2]? = none
            simp [occurrencesEq]
          simp [usedSlots, allOccurrenceSlots,
            PeriodicOneInThreeToThreeDM.OccurrenceSlot.all,
            firstLookup, secondLookup, thirdLookup]
      | cons second rest =>
          cases rest with
          | nil =>
              right
              left
              change
                PeriodicOneInThreeToThreeDM.occurrencesOf source atom =
                  [first, second] at occurrencesEq
              have firstLookup :
                  occurrenceAt source atom .first = some first := by
                change
                  (PeriodicOneInThreeToThreeDM.occurrencesOf
                    source atom)[0]? = some first
                simp [occurrencesEq]
              have secondLookup :
                  occurrenceAt source atom .second = some second := by
                change
                  (PeriodicOneInThreeToThreeDM.occurrencesOf
                    source atom)[1]? = some second
                simp [occurrencesEq]
              have thirdLookup :
                  occurrenceAt source atom .third = none := by
                change
                  (PeriodicOneInThreeToThreeDM.occurrencesOf
                    source atom)[2]? = none
                simp [occurrencesEq]
              simp [usedSlots, allOccurrenceSlots,
                PeriodicOneInThreeToThreeDM.OccurrenceSlot.all,
                firstLookup, secondLookup, thirdLookup]
          | cons third rest =>
              right
              right
              change
                PeriodicOneInThreeToThreeDM.occurrencesOf source atom =
                  first :: second :: third :: rest at occurrencesEq
              have firstLookup :
                  occurrenceAt source atom .first = some first := by
                change
                  (PeriodicOneInThreeToThreeDM.occurrencesOf
                    source atom)[0]? = some first
                simp [occurrencesEq]
              have secondLookup :
                  occurrenceAt source atom .second = some second := by
                change
                  (PeriodicOneInThreeToThreeDM.occurrencesOf
                    source atom)[1]? = some second
                simp [occurrencesEq]
              have thirdLookup :
                  occurrenceAt source atom .third = some third := by
                change
                  (PeriodicOneInThreeToThreeDM.occurrencesOf
                    source atom)[2]? = some third
                simp [occurrencesEq]
              simp [usedSlots, allOccurrenceSlots,
                PeriodicOneInThreeToThreeDM.OccurrenceSlot.all,
                firstLookup, secondLookup, thirdLookup]

/- One occurrence's physical cycle-link incidences carry exactly the two
logical boundary fields, routed respectively to its own and successor slots. -/
set_option maxHeartbeats 800000 in
theorem occurrenceCycleLinkIncidentValues_perm_ofMatching
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (atom : Variable) (current target : OccurrenceSlot)
    (cell : Cell) :
    List.Perm
      ((occurrenceCycleLinkIncidences
        source atom current target).map fun incidence =>
          (problem source).incidenceValue matching incidence cell)
      ((if current = target then
          [(occurrenceBoundary
            source matching atom current cell).first]
        else []) ++
        (if nextUsedSlot source atom current = target then
          [(occurrenceBoundary
            source matching atom current cell).second]
        else [])) := by
  by_cases currentEq : current = target <;>
    by_cases nextEq :
      nextUsedSlot source atom current = target <;>
    cases kindEq :
      occurrenceConnectorKind source atom current <;>
    cases polarityEq :
      occurrencePolarity source atom current <;>
    simp_all [occurrenceCycleLinkIncidences, occurrenceTriples,
      allOrdinaryTriples, allFixedRedTriples,
      tripleReferences, ordinaryTripleReferences,
      fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement, redClauseTerminal,
      firstCycleLinkSlot, secondCycleLinkSlot,
      TypedProblem.incidenceValue, Cell.sub,
      occurrenceBoundary] <;>
    exact List.Perm.swap _ _ []

/-- Exact cover of one assembled red cycle link, rewritten solely in terms
of the logical boundaries of the occurrence modules. -/
theorem cycleLink_boundaries_hold_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (target : OccurrenceSlot)
    (targetMember : target ∈ usedSlots source atom)
    (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((usedSlots source atom).flatMap fun current =>
        (if current = target then
            [(occurrenceBoundary
              source matching atom current cell).first]
          else []) ++
          (if nextUsedSlot source atom current = target then
            [(occurrenceBoundary
              source matching atom current cell).second]
          else [])) := by
  have covered :=
    satisfies.1 (.cycleLink atom target)
      (cycleLink_mem_redElements
        source atom atomMember target targetMember) cell
  rw [TypedProblem.redIncidentValues,
    problem_redIncidences_cycleLink
      source atom atomMember target,
    List.map_flatMap] at covered
  have permutation :=
    List.Perm.flatMap_left (usedSlots source atom)
      (fun current _ =>
        occurrenceCycleLinkIncidentValues_perm_ofMatching
          source matching atom current target cell)
  exact
    (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
      permutation).mp covered

/-- All used occurrence boundaries around one variable carry the same
source-variable phase. -/
theorem occurrenceBoundary_first_eq_first
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (cell : Cell) :
    (occurrenceBoundary source matching atom slot cell).first =
      (occurrenceBoundary source matching atom .first cell).first := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | two | three
  · have slotEq : slot = .first := by
      simpa [one] using slotMember
    subst slot
    rfl
  · have firstMember :
        (.first : OccurrenceSlot) ∈ usedSlots source atom := by simp [two]
    have secondMember :
        (.second : OccurrenceSlot) ∈ usedSlots source atom := by simp [two]
    have firstRealizable :=
      occurrenceBoundary_realizableFor_of_satisfies
        source matching satisfies atom atomMember .first firstMember cell
    have secondRealizable :=
      occurrenceBoundary_realizableFor_of_satisfies
        source matching satisfies atom atomMember .second secondMember cell
    have firstRelation :=
      (variableConnectorBoundary_realizableFor_iff
        (occurrenceConnectorKind source atom .first)
        (occurrencePolarity source atom .first)
        (occurrenceBoundary source matching atom .first cell)).mp
          firstRealizable
    have secondRelation :=
      (variableConnectorBoundary_realizableFor_iff
        (occurrenceConnectorKind source atom .second)
        (occurrencePolarity source atom .second)
        (occurrenceBoundary source matching atom .second cell)).mp
          secondRealizable
    have link :=
      cycleLink_boundaries_hold_of_satisfies
        source matching satisfies atom atomMember .first firstMember cell
    have phases :
        (occurrenceBoundary
            source matching atom .second cell).first =
          (occurrenceBoundary
            source matching atom .first cell).first := by
      simp [two, nextUsedSlot,
        PeriodicOneInThree.ExactlyOne] at link
      cases firstValue :
          (occurrenceBoundary
            source matching atom .first cell).first <;>
        cases firstSecond :
          (occurrenceBoundary
            source matching atom .first cell).second <;>
        cases secondValue :
          (occurrenceBoundary
            source matching atom .second cell).first <;>
        cases secondSecond :
          (occurrenceBoundary
            source matching atom .second cell).second <;>
        simp_all
    simp [two] at slotMember
    rcases slotMember with rfl | rfl
    · rfl
    · exact phases
  · have firstMember :
        (.first : OccurrenceSlot) ∈ usedSlots source atom := by simp [three]
    have secondMember :
        (.second : OccurrenceSlot) ∈ usedSlots source atom := by simp [three]
    have thirdMember :
        (.third : OccurrenceSlot) ∈ usedSlots source atom := by simp [three]
    have firstRealizable :=
      occurrenceBoundary_realizableFor_of_satisfies
        source matching satisfies atom atomMember .first firstMember cell
    have secondRealizable :=
      occurrenceBoundary_realizableFor_of_satisfies
        source matching satisfies atom atomMember .second secondMember cell
    have thirdRealizable :=
      occurrenceBoundary_realizableFor_of_satisfies
        source matching satisfies atom atomMember .third thirdMember cell
    have firstRelation :=
      (variableConnectorBoundary_realizableFor_iff
        (occurrenceConnectorKind source atom .first)
        (occurrencePolarity source atom .first)
        (occurrenceBoundary source matching atom .first cell)).mp
          firstRealizable
    have secondRelation :=
      (variableConnectorBoundary_realizableFor_iff
        (occurrenceConnectorKind source atom .second)
        (occurrencePolarity source atom .second)
        (occurrenceBoundary source matching atom .second cell)).mp
          secondRealizable
    have thirdRelation :=
      (variableConnectorBoundary_realizableFor_iff
        (occurrenceConnectorKind source atom .third)
        (occurrencePolarity source atom .third)
        (occurrenceBoundary source matching atom .third cell)).mp
          thirdRealizable
    have firstLink :=
      cycleLink_boundaries_hold_of_satisfies
        source matching satisfies atom atomMember .first firstMember cell
    have secondLink :=
      cycleLink_boundaries_hold_of_satisfies
        source matching satisfies atom atomMember .second secondMember cell
    have secondPhase :
        (occurrenceBoundary
            source matching atom .second cell).first =
          (occurrenceBoundary
            source matching atom .first cell).first := by
      simp [three, nextUsedSlot,
        PeriodicOneInThree.ExactlyOne] at secondLink
      cases firstValue :
          (occurrenceBoundary
            source matching atom .first cell).first <;>
        cases firstSecond :
          (occurrenceBoundary
            source matching atom .first cell).second <;>
        cases secondValue :
          (occurrenceBoundary
            source matching atom .second cell).first <;>
        cases secondSecond :
          (occurrenceBoundary
            source matching atom .second cell).second <;>
        simp_all
    have thirdPhase :
        (occurrenceBoundary
            source matching atom .third cell).first =
          (occurrenceBoundary
            source matching atom .first cell).first := by
      simp [three, nextUsedSlot,
        PeriodicOneInThree.ExactlyOne] at firstLink
      cases firstValue :
          (occurrenceBoundary
            source matching atom .first cell).first <;>
        cases firstSecond :
          (occurrenceBoundary
            source matching atom .first cell).second <;>
        cases thirdValue :
          (occurrenceBoundary
            source matching atom .third cell).first <;>
        cases thirdSecond :
          (occurrenceBoundary
            source matching atom .third cell).second <;>
        simp_all
    simp [three] at slotMember
    rcases slotMember with rfl | rfl | rfl
    · rfl
    · exact secondPhase
    · exact thirdPhase

/-- Boolean source assignment recovered from the first occurrence boundary
of each protovariable.  Values of variables absent from the source are
irrelevant. -/
def assignmentOfMatching {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment) :
    Variable → Cell → Bool :=
  fun atom cell =>
    (occurrenceBoundary source matching atom .first cell).first

/-- At every used occurrence, the connector terminal selected by an
arbitrary perfect matching is precisely the truth value of that signed
literal under the recovered source assignment. -/
theorem occurrenceBoundary_connector_eq_literalSignal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (cell : Cell) :
    (occurrenceBoundary source matching atom slot cell).connector =
      variableConnectorLiteralSignal
        (assignmentOfMatching source matching atom cell)
        (occurrencePolarity source atom slot) := by
  have realizable :=
    occurrenceBoundary_realizableFor_of_satisfies
      source matching satisfies atom atomMember slot slotMember cell
  have relation :=
    (variableConnectorBoundary_realizableFor_iff
      (occurrenceConnectorKind source atom slot)
      (occurrencePolarity source atom slot)
      (occurrenceBoundary source matching atom slot cell)).mp realizable
  rw [relation.2, assignmentOfMatching,
    occurrenceBoundary_first_eq_first
      source matching satisfies atom atomMember slot slotMember cell]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
