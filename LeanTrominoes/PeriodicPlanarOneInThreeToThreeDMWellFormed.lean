import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMSemantics
import LeanTrominoes.PeriodicOneInThreeToThreeDMWellFormed

/-!
# Well-formedness of the typed planar periodic 3DM assembly

This file proves the list-bookkeeping invariant required before the typed
presentation can be encoded: every colored reference of every listed triple
names a declared colored element.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/-- The cyclic successor of a used occurrence slot is itself used. -/
theorem nextUsedSlot_mem {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom) :
    nextUsedSlot source atom slot ∈ usedSlots source atom := by
  cases slot <;>
    cases firstLookup : occurrenceAt source atom .first <;>
    cases secondLookup : occurrenceAt source atom .second <;>
    cases thirdLookup : occurrenceAt source atom .third <;>
    simp_all [nextUsedSlot, usedSlots, allOccurrenceSlots,
      PeriodicOneInThreeToThreeDM.OccurrenceSlot.all]

/-- Either polarity ordering sends each physical continuation to a declared
cycle link. -/
theorem firstCycleLinkSlot_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (slotMember : slot ∈ usedSlots source atom) :
    firstCycleLinkSlot source atom slot ∈ usedSlots source atom := by
  by_cases polarity : occurrencePolarity source atom slot
  · simp [firstCycleLinkSlot, polarity, slotMember]
  · simp [firstCycleLinkSlot, polarity,
      nextUsedSlot_mem source atom slot slotMember]

theorem secondCycleLinkSlot_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (slotMember : slot ∈ usedSlots source atom) :
    secondCycleLinkSlot source atom slot ∈ usedSlots source atom := by
  by_cases polarity : occurrencePolarity source atom slot
  · simp [secondCycleLinkSlot, polarity,
      nextUsedSlot_mem source atom slot slotMember]
  · simp [secondCycleLinkSlot, polarity, slotMember]

/-- A used slot contains a tagged source occurrence. -/
theorem exists_occurrenceAt_of_mem_usedSlots {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (slotMember : slot ∈ usedSlots source atom) :
    ∃ tagged, occurrenceAt source atom slot = some tagged := by
  simp only [usedSlots, List.mem_filter] at slotMember
  exact Option.isSome_iff_exists.mp slotMember.2

/-- A cycle link belonging to a listed variable and used slot is declared. -/
theorem cycleLink_mem_redElements {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom) :
    RedElement.cycleLink atom slot ∈ redElements source := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨atom, atomMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨slot, slotMember, ?_⟩
  simp [occurrenceRedElements]

/-- Every colored clause-core element at a valid clause index is declared. -/
theorem clauseRedElement_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (element : X3CClauseElement) :
    clauseRedElement clauseIndex element ∈ redElements source := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨clauseIndex, List.mem_range.mpr indexLt, ?_⟩
  cases element with
  | internal element =>
      simp [clauseRedElement]
  | terminal terminal =>
      rcases terminal with ⟨group, slot⟩
      cases group <;> cases slot <;>
        simp [clauseRedElement, allTerminalGroups]

theorem clauseGreenElement_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (element : X3CClauseElement) :
    clauseGreenElement clauseIndex element ∈ greenElements source := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨clauseIndex, List.mem_range.mpr indexLt, ?_⟩
  cases element with
  | internal element =>
      simp [clauseGreenElement]
  | terminal terminal =>
      rcases terminal with ⟨group, slot⟩
      cases group <;> cases slot <;>
        simp [clauseGreenElement, allTerminalGroups]

theorem clauseBlueElement_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (element : X3CClauseElement) :
    clauseBlueElement clauseIndex element ∈ blueElements source := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨clauseIndex, List.mem_range.mpr indexLt, ?_⟩
  cases element with
  | internal element =>
      simp [clauseBlueElement]
  | terminal terminal =>
      rcases terminal with ⟨group, slot⟩
      cases group <;> cases slot <;>
        simp [clauseBlueElement, allTerminalGroups]

/-- Clause-terminal references of a used occurrence point to a valid
declared clause prototype. -/
theorem occurrence_clause_elements_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (slotMember : slot ∈ usedSlots source atom) :
    redClauseTerminal source atom slot ∈ redElements source ∧
      greenClauseTerminal source atom slot ∈ greenElements source ∧
      blueClauseTerminal source atom slot ∈ blueElements source := by
  rcases exists_occurrenceAt_of_mem_usedSlots
      source atom slot slotMember with ⟨tagged, lookup⟩
  have taggedMember :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source atom slot tagged lookup).1
  have indexLt :=
    PeriodicOneInThreeToThreeDM.clauseIndex_lt_of_tagged_mem
      source tagged taggedMember
  have groupMember :
      terminalGroupOfLiteralIndex tagged.2.2 ∈ allTerminalGroups := by
    rcases tagged.2.2 with _ | index
    · simp [terminalGroupOfLiteralIndex, allTerminalGroups]
    · rcases index with _ | index
      · simp [terminalGroupOfLiteralIndex, allTerminalGroups]
      · simp [terminalGroupOfLiteralIndex, allTerminalGroups]
  constructor
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨tagged.2.1, List.mem_range.mpr indexLt, ?_⟩
    simpa [redClauseTerminal, occurrenceClauseIndex,
      occurrenceLiteralIndex, lookup] using groupMember
  constructor
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨tagged.2.1, List.mem_range.mpr indexLt, ?_⟩
    simpa [greenClauseTerminal, occurrenceClauseIndex,
      occurrenceLiteralIndex, lookup] using groupMember
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨tagged.2.1, List.mem_range.mpr indexLt, ?_⟩
    simpa [blueClauseTerminal, occurrenceClauseIndex,
      occurrenceLiteralIndex, lookup] using groupMember

/-- Ordinary internal elements selected by the connector variant are
declared in their corresponding color list. -/
theorem ordinaryGreenInternal_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    GreenElement.ordinaryInternal atom slot
        (match variant with
        | .fixedGreen => .auxiliaryShared
        | .fixedBlue => .cycleShared) ∈
      greenElements source := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨atom, atomMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨slot, slotMember, ?_⟩
  cases variant <;>
    simp_all [occurrenceGreenElements]

theorem ordinaryBlueInternal_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    BlueElement.ordinaryInternal atom slot
        (match variant with
        | .fixedGreen => .cycleShared
        | .fixedBlue => .auxiliaryShared) ∈
      blueElements source := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨atom, atomMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨slot, slotMember, ?_⟩
  cases variant <;>
    simp_all [occurrenceBlueElements]

/-- All internal elements of a listed fixed-red detour are declared. -/
theorem fixedRedInternalRed_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalRed) :
    RedElement.fixedRedInternal atom slot element ∈
      redElements source := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨atom, atomMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨slot, slotMember, ?_⟩
  cases element <;>
    simp_all [occurrenceRedElements]

theorem fixedRedInternalGreen_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalGreen) :
    GreenElement.fixedRedInternal atom slot element ∈
      greenElements source := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨atom, atomMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨slot, slotMember, ?_⟩
  cases element <;>
    simp_all [occurrenceGreenElements]

theorem fixedRedInternalBlue_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalBlue) :
    BlueElement.fixedRedInternal atom slot element ∈
      blueElements source := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨atom, atomMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨slot, slotMember, ?_⟩
  cases element <;>
    simp_all [occurrenceBlueElements]

/-- Every colored reference of a listed ordinary occurrence triple is
declared. -/
theorem ordinaryTripleReferences_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue)
    (triple : VariableOccurrenceTriple) :
    (ordinaryTripleReferences
        source atom slot variant triple).red.atom ∈ redElements source ∧
      (ordinaryTripleReferences
        source atom slot variant triple).green.atom ∈
          greenElements source ∧
      (ordinaryTripleReferences
        source atom slot variant triple).blue.atom ∈
          blueElements source := by
  have firstRed :=
    cycleLink_mem_redElements source atom atomMember
      (firstCycleLinkSlot source atom slot)
      (firstCycleLinkSlot_mem source atom slot slotMember)
  have secondRed :=
    cycleLink_mem_redElements source atom atomMember
      (secondCycleLinkSlot source atom slot)
      (secondCycleLinkSlot_mem source atom slot slotMember)
  have terminals :=
    occurrence_clause_elements_mem source atom slot slotMember
  have greenInternal :=
    ordinaryGreenInternal_mem source atom atomMember
      slot slotMember variant kindEq
  have blueInternal :=
    ordinaryBlueInternal_mem source atom atomMember
      slot slotMember variant kindEq
  cases variant <;> cases triple <;>
    simp_all [ordinaryTripleReferences,
      VariableOccurrenceTriple.references,
      ordinaryRedElement, ordinaryGreenElement, ordinaryBlueElement]

/-- Every colored reference of a listed fixed-red occurrence triple is
declared. -/
theorem fixedRedTripleReferences_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (triple : FixedRedConnectorTriple) :
    (fixedRedTripleReferences
        source atom slot triple).red.atom ∈ redElements source ∧
      (fixedRedTripleReferences
        source atom slot triple).green.atom ∈ greenElements source ∧
      (fixedRedTripleReferences
        source atom slot triple).blue.atom ∈ blueElements source := by
  have firstRed :=
    cycleLink_mem_redElements source atom atomMember
      (firstCycleLinkSlot source atom slot)
      (firstCycleLinkSlot_mem source atom slot slotMember)
  have secondRed :=
    cycleLink_mem_redElements source atom atomMember
      (secondCycleLinkSlot source atom slot)
      (secondCycleLinkSlot_mem source atom slot slotMember)
  have terminals :=
    occurrence_clause_elements_mem source atom slot slotMember
  have redInternal (element : FixedRedInternalRed) :=
    fixedRedInternalRed_mem source atom atomMember
      slot slotMember kindEq element
  have greenInternal (element : FixedRedInternalGreen) :=
    fixedRedInternalGreen_mem source atom atomMember
      slot slotMember kindEq element
  have blueInternal (element : FixedRedInternalBlue) :=
    fixedRedInternalBlue_mem source atom atomMember
      slot slotMember kindEq element
  cases triple <;>
    simp_all [fixedRedTripleReferences,
      FixedRedConnectorTriple.references,
      fixedRedRedElement, fixedRedGreenElement, fixedRedBlueElement]

/-- Every colored reference of a listed clause-core triple is declared. -/
theorem clauseTripleReferences_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet) :
    (clauseTripleReferences
        (Variable := Variable) clauseIndex set).red.atom ∈
        redElements source ∧
      (clauseTripleReferences
        (Variable := Variable) clauseIndex set).green.atom ∈
        greenElements source ∧
      (clauseTripleReferences
        (Variable := Variable) clauseIndex set).blue.atom ∈
        blueElements source := by
  exact
    ⟨clauseRedElement_mem source clauseIndex indexLt
        set.coloredReferences.red,
      clauseGreenElement_mem source clauseIndex indexLt
        set.coloredReferences.green,
      clauseBlueElement_mem source clauseIndex indexLt
        set.coloredReferences.blue⟩

/-- The complete typed planar periodic 3DM assembly is well formed. -/
theorem problem_isWellFormed {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (problem source).IsWellFormed := by
  intro triple tripleMember
  change triple ∈ triples source at tripleMember
  simp only [triples, List.mem_append] at tripleMember
  rcases tripleMember with variableMember | clauseMember
  · simp only [variableTriples, List.mem_flatMap] at variableMember
    rcases variableMember with
      ⟨atom, atomMember, slot, slotMember, moduleMember⟩
    cases kindEq : occurrenceConnectorKind source atom slot with
    | fixedRed =>
        simp only [occurrenceTriples, kindEq, List.mem_map] at moduleMember
        rcases moduleMember with
          ⟨localTriple, localMember, rfl⟩
        exact fixedRedTripleReferences_mem
          source atom atomMember slot slotMember kindEq localTriple
    | fixedGreen =>
        simp only [occurrenceTriples, kindEq, List.mem_map] at moduleMember
        rcases moduleMember with
          ⟨localTriple, localMember, rfl⟩
        exact ordinaryTripleReferences_mem
          source atom atomMember slot slotMember
          .fixedGreen kindEq localTriple
    | fixedBlue =>
        simp only [occurrenceTriples, kindEq, List.mem_map] at moduleMember
        rcases moduleMember with
          ⟨localTriple, localMember, rfl⟩
        exact ordinaryTripleReferences_mem
          source atom atomMember slot slotMember
          .fixedBlue kindEq localTriple
  · simp only [clauseTriples, List.mem_flatMap,
      List.mem_map] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, indexMember, set, setMember, rfl⟩
    exact clauseTripleReferences_mem
      source clauseIndex (List.mem_range.mp indexMember) set

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
