import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTypedSoundness

/-!
# Duplicate-free planar typed 3DM presentations

Natural-number encoding uses list positions as names.  This file proves
that every prototype triple and every colored element in the planar
assembly occurs at a unique position.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Flattening duplicate-free blocks indexed by two duplicate-free keys
preserves duplicate-freedom when equality of block members recovers both
keys. -/
private theorem nestedBlocks_nodup
    {Outer Inner Value : Type*}
    (outers : List Outer) (inners : Outer → List Inner)
    (blocks : Outer → Inner → List Value)
    (outersNodup : outers.Nodup)
    (innersNodup : ∀ outer ∈ outers, (inners outer).Nodup)
    (blocksNodup :
      ∀ outer ∈ outers, ∀ inner ∈ inners outer,
        (blocks outer inner).Nodup)
    (keysOfEqual :
      ∀ {firstOuter secondOuter firstInner secondInner first second},
        first ∈ blocks firstOuter firstInner →
        second ∈ blocks secondOuter secondInner →
        first = second →
        firstOuter = secondOuter ∧ firstInner = secondInner) :
    (outers.flatMap fun outer =>
      (inners outer).flatMap fun inner =>
        blocks outer inner).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro outer outerMember
    rw [List.nodup_flatMap]
    constructor
    · exact blocksNodup outer outerMember
    · exact (innersNodup outer outerMember).imp
        fun {firstInner secondInner} different =>
          List.disjoint_left.mpr
            fun value firstMember secondMember =>
              different
                (keysOfEqual firstMember secondMember rfl).2
  · exact outersNodup.imp
      fun {firstOuter secondOuter} different =>
        List.disjoint_left.mpr
          fun value firstMember secondMember => by
            rcases List.mem_flatMap.mp firstMember with
              ⟨firstInner, firstInnerMember, firstBlockMember⟩
            rcases List.mem_flatMap.mp secondMember with
              ⟨secondInner, secondInnerMember, secondBlockMember⟩
            exact different
              (keysOfEqual firstBlockMember secondBlockMember rfl).1

/-- Flattening duplicate-free blocks indexed by one duplicate-free key
preserves duplicate-freedom when equality of members recovers that key. -/
private theorem indexedBlocks_nodup
    {Index Value : Type*}
    (indices : List Index) (blocks : Index → List Value)
    (indicesNodup : indices.Nodup)
    (blocksNodup :
      ∀ index ∈ indices, (blocks index).Nodup)
    (indexOfEqual :
      ∀ {firstIndex secondIndex first second},
        first ∈ blocks firstIndex →
        second ∈ blocks secondIndex →
        first = second →
        firstIndex = secondIndex) :
    (indices.flatMap blocks).Nodup := by
  rw [List.nodup_flatMap]
  exact ⟨blocksNodup,
    indicesNodup.imp fun {firstIndex secondIndex} different =>
      List.disjoint_left.mpr
        fun value firstMember secondMember =>
          different (indexOfEqual firstMember secondMember rfl)⟩

/-- Variable/slot key retained by a variable-module triple. -/
private def tripleOccurrenceKey {Variable : Type*} :
    Triple Variable → Option (Variable × OccurrenceSlot)
  | .ordinary atom slot _ _ => some (atom, slot)
  | .fixedRed atom slot _ => some (atom, slot)
  | .clause _ _ => none

/-- Variable/slot key retained by a variable-side red element. -/
private def redOccurrenceKey {Variable : Type*} :
    RedElement Variable → Option (Variable × OccurrenceSlot)
  | .cycleLink atom slot => some (atom, slot)
  | .fixedRedInternal atom slot _ => some (atom, slot)
  | .clauseInternal _ | .clauseTerminal _ _ => none

/-- Variable/slot key retained by a variable-side green element. -/
private def greenOccurrenceKey {Variable : Type*} :
    GreenElement Variable → Option (Variable × OccurrenceSlot)
  | .ordinaryInternal atom slot _ => some (atom, slot)
  | .fixedRedInternal atom slot _ => some (atom, slot)
  | .clauseInternal _ | .clauseTerminal _ _ => none

/-- Variable/slot key retained by a variable-side blue element. -/
private def blueOccurrenceKey {Variable : Type*} :
    BlueElement Variable → Option (Variable × OccurrenceSlot)
  | .ordinaryInternal atom slot _ => some (atom, slot)
  | .fixedRedInternal atom slot _ => some (atom, slot)
  | .clauseInternal _ | .clauseTerminal _ _ => none

private theorem tripleOccurrenceKey_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) (triple : Triple Variable)
    (member : triple ∈ occurrenceTriples source atom slot) :
    tripleOccurrenceKey triple = some (atom, slot) := by
  have keyMember :
      tripleOccurrenceKey triple ∈
        (occurrenceTriples source atom slot).map
          tripleOccurrenceKey :=
    List.mem_map_of_mem member
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp_all [occurrenceTriples, allOrdinaryTriples,
      allFixedRedTriples, tripleOccurrenceKey]

private theorem redOccurrenceKey_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) (element : RedElement Variable)
    (member : element ∈ occurrenceRedElements source atom slot) :
    redOccurrenceKey element = some (atom, slot) := by
  have keyMember :
      redOccurrenceKey element ∈
        (occurrenceRedElements source atom slot).map
          redOccurrenceKey :=
    List.mem_map_of_mem member
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp_all [occurrenceRedElements, redOccurrenceKey]

private theorem greenOccurrenceKey_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) (element : GreenElement Variable)
    (member : element ∈ occurrenceGreenElements source atom slot) :
    greenOccurrenceKey element = some (atom, slot) := by
  have keyMember :
      greenOccurrenceKey element ∈
        (occurrenceGreenElements source atom slot).map
          greenOccurrenceKey :=
    List.mem_map_of_mem member
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp_all [occurrenceGreenElements, greenOccurrenceKey]

private theorem blueOccurrenceKey_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) (element : BlueElement Variable)
    (member : element ∈ occurrenceBlueElements source atom slot) :
    blueOccurrenceKey element = some (atom, slot) := by
  have keyMember :
      blueOccurrenceKey element ∈
        (occurrenceBlueElements source atom slot).map
          blueOccurrenceKey :=
    List.mem_map_of_mem member
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp_all [occurrenceBlueElements, blueOccurrenceKey]

private theorem redOccurrenceKey_eq_none_of_mem_clauseBlock
    {Variable : Type*} (clauseIndex : Nat)
    (element : RedElement Variable)
    (member :
      element ∈
        [RedElement.clauseInternal clauseIndex] ++
          allTerminalGroups.map
            (RedElement.clauseTerminal clauseIndex)) :
    redOccurrenceKey element = none := by
  have keyMember :
      redOccurrenceKey element ∈
        ([RedElement.clauseInternal clauseIndex] ++
          allTerminalGroups.map
            (RedElement.clauseTerminal clauseIndex)).map
              redOccurrenceKey :=
    List.mem_map_of_mem member
  simpa [allTerminalGroups, redOccurrenceKey] using keyMember

private theorem greenOccurrenceKey_eq_none_of_mem_clauseBlock
    {Variable : Type*} (clauseIndex : Nat)
    (element : GreenElement Variable)
    (member :
      element ∈
        [GreenElement.clauseInternal clauseIndex] ++
          allTerminalGroups.map
            (GreenElement.clauseTerminal clauseIndex)) :
    greenOccurrenceKey element = none := by
  have keyMember :
      greenOccurrenceKey element ∈
        ([GreenElement.clauseInternal clauseIndex] ++
          allTerminalGroups.map
            (GreenElement.clauseTerminal clauseIndex)).map
              greenOccurrenceKey :=
    List.mem_map_of_mem member
  simpa [allTerminalGroups, greenOccurrenceKey] using keyMember

private theorem blueOccurrenceKey_eq_none_of_mem_clauseBlock
    {Variable : Type*} (clauseIndex : Nat)
    (element : BlueElement Variable)
    (member :
      element ∈
        [BlueElement.clauseInternal clauseIndex] ++
          allTerminalGroups.map
            (BlueElement.clauseTerminal clauseIndex)) :
    blueOccurrenceKey element = none := by
  have keyMember :
      blueOccurrenceKey element ∈
        ([BlueElement.clauseInternal clauseIndex] ++
          allTerminalGroups.map
            (BlueElement.clauseTerminal clauseIndex)).map
              blueOccurrenceKey :=
    List.mem_map_of_mem member
  simpa [allTerminalGroups, blueOccurrenceKey] using keyMember

/-- All variable-module prototype triples are distinct. -/
theorem variableTriples_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (variableTriples source).Nodup := by
  apply nestedBlocks_nodup
    (occurringVariables source) (usedSlots source)
      (occurrenceTriples source)
    (PeriodicOneInThreeToThreeDM.occurringVariables_nodup source)
    (fun atom _ => usedSlots_nodup source atom)
    (fun atom _ slot _ => occurrenceTriples_nodup source atom slot)
  intro firstAtom secondAtom firstSlot secondSlot first second
    firstMember secondMember equal
  have firstKey :
      tripleOccurrenceKey first = some (firstAtom, firstSlot) :=
    tripleOccurrenceKey_of_mem
      source firstAtom firstSlot first firstMember
  have secondKey :
      tripleOccurrenceKey second = some (secondAtom, secondSlot) :=
    tripleOccurrenceKey_of_mem
      source secondAtom secondSlot second secondMember
  have keysEqual :
      (firstAtom, firstSlot) = (secondAtom, secondSlot) := by
    apply Option.some.inj
    rw [← firstKey, ← secondKey, equal]
  exact Prod.mk.inj keysEqual

/-- All clause-core prototype triples are distinct. -/
theorem clauseTriples_nodup
    {Variable : Type*} (source : PeriodicCNF Variable) :
    (clauseTriples (Variable := Variable) source).Nodup := by
  apply indexedBlocks_nodup
    (List.range source.clauses.length)
    (fun clauseIndex =>
      allClauseSets.map
        (Triple.clause (Variable := Variable) clauseIndex))
    List.nodup_range
    (fun clauseIndex _ => clauseSetTriples_nodup clauseIndex)
  intro firstIndex secondIndex first second
    firstMember secondMember equal
  rcases List.mem_map.mp firstMember with
    ⟨firstSet, firstSetMember, rfl⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondSet, secondSetMember, rfl⟩
  exact Triple.clause.inj equal |>.1

/-- The complete planar typed triple list is duplicate-free. -/
theorem triples_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (triples source).Nodup := by
  rw [triples, List.nodup_append]
  refine ⟨variableTriples_nodup source,
    clauseTriples_nodup source, ?_⟩
  intro variableTriple variableMember clauseTriple clauseMember equal
  rcases List.mem_flatMap.mp clauseMember with
    ⟨clauseIndex, indexMember, localMember⟩
  rcases List.mem_map.mp localMember with
    ⟨set, setMember, rfl⟩
  rcases List.mem_flatMap.mp variableMember with
    ⟨atom, atomMember, slotMember⟩
  rcases List.mem_flatMap.mp slotMember with
    ⟨slot, slotUsed, localMember⟩
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp_all [occurrenceTriples, allOrdinaryTriples,
      allFixedRedTriples]

/-- Each local red element block is duplicate-free and its members retain
the variable and occurrence-slot keys. -/
private theorem variableRedElements_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurringVariables source).flatMap fun atom =>
      (usedSlots source atom).flatMap fun slot =>
        occurrenceRedElements source atom slot).Nodup := by
  apply nestedBlocks_nodup
    (occurringVariables source) (usedSlots source)
      (occurrenceRedElements source)
    (PeriodicOneInThreeToThreeDM.occurringVariables_nodup source)
    (fun atom _ => usedSlots_nodup source atom)
  · intro atom atomMember slot slotMember
    cases kindEq : occurrenceConnectorKind source atom slot <;>
      simp [occurrenceRedElements, kindEq]
  · intro firstAtom secondAtom firstSlot secondSlot first second
      firstMember secondMember equal
    have firstKey :
        redOccurrenceKey first = some (firstAtom, firstSlot) :=
      redOccurrenceKey_of_mem
        source firstAtom firstSlot first firstMember
    have secondKey :
        redOccurrenceKey second = some (secondAtom, secondSlot) :=
      redOccurrenceKey_of_mem
        source secondAtom secondSlot second secondMember
    have keysEqual :
        (firstAtom, firstSlot) = (secondAtom, secondSlot) := by
      apply Option.some.inj
      rw [← firstKey, ← secondKey, equal]
    exact Prod.mk.inj keysEqual

/-- Each local green element block is duplicate-free and its members retain
the variable and occurrence-slot keys. -/
private theorem variableGreenElements_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurringVariables source).flatMap fun atom =>
      (usedSlots source atom).flatMap fun slot =>
        occurrenceGreenElements source atom slot).Nodup := by
  apply nestedBlocks_nodup
    (occurringVariables source) (usedSlots source)
      (occurrenceGreenElements source)
    (PeriodicOneInThreeToThreeDM.occurringVariables_nodup source)
    (fun atom _ => usedSlots_nodup source atom)
  · intro atom atomMember slot slotMember
    cases kindEq : occurrenceConnectorKind source atom slot <;>
      simp [occurrenceGreenElements, kindEq]
  · intro firstAtom secondAtom firstSlot secondSlot first second
      firstMember secondMember equal
    have firstKey :
        greenOccurrenceKey first = some (firstAtom, firstSlot) :=
      greenOccurrenceKey_of_mem
        source firstAtom firstSlot first firstMember
    have secondKey :
        greenOccurrenceKey second = some (secondAtom, secondSlot) :=
      greenOccurrenceKey_of_mem
        source secondAtom secondSlot second secondMember
    have keysEqual :
        (firstAtom, firstSlot) = (secondAtom, secondSlot) := by
      apply Option.some.inj
      rw [← firstKey, ← secondKey, equal]
    exact Prod.mk.inj keysEqual

/-- Each local blue element block is duplicate-free and its members retain
the variable and occurrence-slot keys. -/
private theorem variableBlueElements_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurringVariables source).flatMap fun atom =>
      (usedSlots source atom).flatMap fun slot =>
        occurrenceBlueElements source atom slot).Nodup := by
  apply nestedBlocks_nodup
    (occurringVariables source) (usedSlots source)
      (occurrenceBlueElements source)
    (PeriodicOneInThreeToThreeDM.occurringVariables_nodup source)
    (fun atom _ => usedSlots_nodup source atom)
  · intro atom atomMember slot slotMember
    cases kindEq : occurrenceConnectorKind source atom slot <;>
      simp [occurrenceBlueElements, kindEq]
  · intro firstAtom secondAtom firstSlot secondSlot first second
      firstMember secondMember equal
    have firstKey :
        blueOccurrenceKey first = some (firstAtom, firstSlot) :=
      blueOccurrenceKey_of_mem
        source firstAtom firstSlot first firstMember
    have secondKey :
        blueOccurrenceKey second = some (secondAtom, secondSlot) :=
      blueOccurrenceKey_of_mem
        source secondAtom secondSlot second secondMember
    have keysEqual :
        (firstAtom, firstSlot) = (secondAtom, secondSlot) := by
      apply Option.some.inj
      rw [← firstKey, ← secondKey, equal]
    exact Prod.mk.inj keysEqual

/-- Clause red-element blocks are duplicate-free. -/
private theorem clauseRedElements_nodup
    {Variable : Type*} (source : PeriodicCNF Variable) :
    ((List.range source.clauses.length).flatMap fun clauseIndex =>
      [.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (RedElement.clauseTerminal
            (Variable := Variable) clauseIndex)).Nodup := by
  apply indexedBlocks_nodup
    (List.range source.clauses.length)
    (fun clauseIndex =>
      [RedElement.clauseInternal
          (Variable := Variable) clauseIndex] ++
        allTerminalGroups.map
          (RedElement.clauseTerminal
            (Variable := Variable) clauseIndex))
    List.nodup_range
  · intro clauseIndex indexMember
    simp [allTerminalGroups]
  · intro firstIndex secondIndex first second
      firstMember secondMember equal
    simp only [List.mem_append, List.mem_singleton,
      List.mem_map] at firstMember secondMember
    rcases firstMember with rfl | ⟨group, groupMember, rfl⟩ <;>
      rcases secondMember with rfl | ⟨other, otherMember, rfl⟩ <;>
      cases equal <;> rfl

/-- Clause green-element blocks are duplicate-free. -/
private theorem clauseGreenElements_nodup
    {Variable : Type*} (source : PeriodicCNF Variable) :
    ((List.range source.clauses.length).flatMap fun clauseIndex =>
      [.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (GreenElement.clauseTerminal
            (Variable := Variable) clauseIndex)).Nodup := by
  apply indexedBlocks_nodup
    (List.range source.clauses.length)
    (fun clauseIndex =>
      [GreenElement.clauseInternal
          (Variable := Variable) clauseIndex] ++
        allTerminalGroups.map
          (GreenElement.clauseTerminal
            (Variable := Variable) clauseIndex))
    List.nodup_range
  · intro clauseIndex indexMember
    simp [allTerminalGroups]
  · intro firstIndex secondIndex first second
      firstMember secondMember equal
    simp only [List.mem_append, List.mem_singleton,
      List.mem_map] at firstMember secondMember
    rcases firstMember with rfl | ⟨group, groupMember, rfl⟩ <;>
      rcases secondMember with rfl | ⟨other, otherMember, rfl⟩ <;>
      cases equal <;> rfl

/-- Clause blue-element blocks are duplicate-free. -/
private theorem clauseBlueElements_nodup
    {Variable : Type*} (source : PeriodicCNF Variable) :
    ((List.range source.clauses.length).flatMap fun clauseIndex =>
      [.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (BlueElement.clauseTerminal
            (Variable := Variable) clauseIndex)).Nodup := by
  apply indexedBlocks_nodup
    (List.range source.clauses.length)
    (fun clauseIndex =>
      [BlueElement.clauseInternal
          (Variable := Variable) clauseIndex] ++
        allTerminalGroups.map
          (BlueElement.clauseTerminal
            (Variable := Variable) clauseIndex))
    List.nodup_range
  · intro clauseIndex indexMember
    simp [allTerminalGroups]
  · intro firstIndex secondIndex first second
      firstMember secondMember equal
    simp only [List.mem_append, List.mem_singleton,
      List.mem_map] at firstMember secondMember
    rcases firstMember with rfl | ⟨group, groupMember, rfl⟩ <;>
      rcases secondMember with rfl | ⟨other, otherMember, rfl⟩ <;>
      cases equal <;> rfl

/-- The complete red-element list is duplicate-free. -/
theorem redElements_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (redElements source).Nodup := by
  rw [redElements, List.nodup_append]
  refine ⟨variableRedElements_nodup source,
    clauseRedElements_nodup source, ?_⟩
  intro variableElement variableMember clauseElement clauseMember equal
  simp only [List.mem_flatMap] at variableMember clauseMember
  rcases variableMember with
    ⟨atom, atomMember, slot, slotMember, localMember⟩
  rcases clauseMember with
    ⟨clauseIndex, indexMember, localMemberClause⟩
  have variableKey :
      redOccurrenceKey variableElement = some (atom, slot) :=
    redOccurrenceKey_of_mem
      source atom slot variableElement localMember
  have clauseKey : redOccurrenceKey clauseElement = none :=
    redOccurrenceKey_eq_none_of_mem_clauseBlock
      clauseIndex clauseElement localMemberClause
  have keyEq := congrArg redOccurrenceKey equal
  rw [variableKey, clauseKey] at keyEq
  contradiction

/-- The complete green-element list is duplicate-free. -/
theorem greenElements_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (greenElements source).Nodup := by
  rw [greenElements, List.nodup_append]
  refine ⟨variableGreenElements_nodup source,
    clauseGreenElements_nodup source, ?_⟩
  intro variableElement variableMember clauseElement clauseMember equal
  simp only [List.mem_flatMap] at variableMember clauseMember
  rcases variableMember with
    ⟨atom, atomMember, slot, slotMember, localMember⟩
  rcases clauseMember with
    ⟨clauseIndex, indexMember, localMemberClause⟩
  have variableKey :
      greenOccurrenceKey variableElement = some (atom, slot) :=
    greenOccurrenceKey_of_mem
      source atom slot variableElement localMember
  have clauseKey : greenOccurrenceKey clauseElement = none :=
    greenOccurrenceKey_eq_none_of_mem_clauseBlock
      clauseIndex clauseElement localMemberClause
  have keyEq := congrArg greenOccurrenceKey equal
  rw [variableKey, clauseKey] at keyEq
  contradiction

/-- The complete blue-element list is duplicate-free. -/
theorem blueElements_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (blueElements source).Nodup := by
  rw [blueElements, List.nodup_append]
  refine ⟨variableBlueElements_nodup source,
    clauseBlueElements_nodup source, ?_⟩
  intro variableElement variableMember clauseElement clauseMember equal
  simp only [List.mem_flatMap] at variableMember clauseMember
  rcases variableMember with
    ⟨atom, atomMember, slot, slotMember, localMember⟩
  rcases clauseMember with
    ⟨clauseIndex, indexMember, localMemberClause⟩
  have variableKey :
      blueOccurrenceKey variableElement = some (atom, slot) :=
    blueOccurrenceKey_of_mem
      source atom slot variableElement localMember
  have clauseKey : blueOccurrenceKey clauseElement = none :=
    blueOccurrenceKey_eq_none_of_mem_clauseBlock
      clauseIndex clauseElement localMemberClause
  have keyEq := congrArg blueOccurrenceKey equal
  rw [variableKey, clauseKey] at keyEq
  contradiction

/-- All four finite lists of the planar typed problem are duplicate-free. -/
theorem problem_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (problem source).redElements.Nodup ∧
      (problem source).greenElements.Nodup ∧
      (problem source).blueElements.Nodup ∧
      (problem source).triples.Nodup :=
  ⟨redElements_nodup source, greenElements_nodup source,
    blueElements_nodup source, triples_nodup source⟩

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
