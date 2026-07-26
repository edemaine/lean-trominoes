import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVertexGeometry

/-!
# Typed elements in the finite variable-site drawing

The periodic 3DM presentation gives its red, green, and blue elements
globally typed names.  The exhaustively checked variable-site drawing instead
uses one common local element type.  This file identifies every listed
variable-side typed element with its active local name and proves that their
positions agree.

Clause elements deliberately receive harmless fallback names in the total
conversion functions below.  Every theorem in this file assumes membership
in an occurrence block, so those fallback cases are unreachable.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- The slot identification used by the finite drawing is injective. -/
theorem occurrenceVariableSiteSlot_injective :
    Function.Injective occurrenceVariableSiteSlot := by
  intro firstSlot secondSlot equal
  have inverseEqual :=
    congrArg variableSiteOccurrenceSlot equal
  simpa using inverseEqual

@[simp]
theorem occurrenceVariableSiteSlot_inj
    (firstSlot secondSlot : OccurrenceSlot) :
    occurrenceVariableSiteSlot firstSlot =
        occurrenceVariableSiteSlot secondSlot ↔
      firstSlot = secondSlot :=
  occurrenceVariableSiteSlot_injective.eq_iff

/-- The two ordinary private names remain distinct after conversion to local
element names. -/
theorem ordinaryInternalLocalElement_injective :
    Function.Injective ordinaryInternalLocalElement := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [ordinaryInternalLocalElement]

@[simp]
theorem ordinaryInternalLocalElement_inj
    (first second : OrdinaryInternal) :
    ordinaryInternalLocalElement first =
        ordinaryInternalLocalElement second ↔
      first = second :=
  ordinaryInternalLocalElement_injective.eq_iff

/-- Each fixed-red color's private names remain distinct after conversion. -/
theorem fixedRedInternalRedLocalElement_injective :
    Function.Injective fixedRedInternalRedLocalElement := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [fixedRedInternalRedLocalElement]

theorem fixedRedInternalGreenLocalElement_injective :
    Function.Injective fixedRedInternalGreenLocalElement := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [fixedRedInternalGreenLocalElement]

theorem fixedRedInternalBlueLocalElement_injective :
    Function.Injective fixedRedInternalBlueLocalElement := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [fixedRedInternalBlueLocalElement]

@[simp]
theorem fixedRedInternalRedLocalElement_inj
    (first second : FixedRedInternalRed) :
    fixedRedInternalRedLocalElement first =
        fixedRedInternalRedLocalElement second ↔
      first = second :=
  fixedRedInternalRedLocalElement_injective.eq_iff

@[simp]
theorem fixedRedInternalGreenLocalElement_inj
    (first second : FixedRedInternalGreen) :
    fixedRedInternalGreenLocalElement first =
        fixedRedInternalGreenLocalElement second ↔
      first = second :=
  fixedRedInternalGreenLocalElement_injective.eq_iff

@[simp]
theorem fixedRedInternalBlueLocalElement_inj
    (first second : FixedRedInternalBlue) :
    fixedRedInternalBlueLocalElement first =
        fixedRedInternalBlueLocalElement second ↔
      first = second :=
  fixedRedInternalBlueLocalElement_injective.eq_iff

/-- Private fixed-red elements of different colors have different local
names. -/
@[simp]
theorem fixedRedInternalRedLocalElement_ne_green
    (red : FixedRedInternalRed)
    (green : FixedRedInternalGreen) :
    fixedRedInternalRedLocalElement red ≠
      fixedRedInternalGreenLocalElement green := by
  cases red <;> cases green <;>
    simp [fixedRedInternalRedLocalElement,
      fixedRedInternalGreenLocalElement]

@[simp]
theorem fixedRedInternalRedLocalElement_ne_blue
    (red : FixedRedInternalRed)
    (blue : FixedRedInternalBlue) :
    fixedRedInternalRedLocalElement red ≠
      fixedRedInternalBlueLocalElement blue := by
  cases red <;> cases blue <;>
    simp [fixedRedInternalRedLocalElement,
      fixedRedInternalBlueLocalElement]

@[simp]
theorem fixedRedInternalGreenLocalElement_ne_red
    (green : FixedRedInternalGreen)
    (red : FixedRedInternalRed) :
    fixedRedInternalGreenLocalElement green ≠
      fixedRedInternalRedLocalElement red :=
  Ne.symm (fixedRedInternalRedLocalElement_ne_green red green)

@[simp]
theorem fixedRedInternalGreenLocalElement_ne_blue
    (green : FixedRedInternalGreen)
    (blue : FixedRedInternalBlue) :
    fixedRedInternalGreenLocalElement green ≠
      fixedRedInternalBlueLocalElement blue := by
  cases green <;> cases blue <;>
    simp [fixedRedInternalGreenLocalElement,
      fixedRedInternalBlueLocalElement]

@[simp]
theorem fixedRedInternalBlueLocalElement_ne_red
    (blue : FixedRedInternalBlue)
    (red : FixedRedInternalRed) :
    fixedRedInternalBlueLocalElement blue ≠
      fixedRedInternalRedLocalElement red :=
  Ne.symm (fixedRedInternalRedLocalElement_ne_blue red blue)

@[simp]
theorem fixedRedInternalBlueLocalElement_ne_green
    (blue : FixedRedInternalBlue)
    (green : FixedRedInternalGreen) :
    fixedRedInternalBlueLocalElement blue ≠
      fixedRedInternalGreenLocalElement green :=
  Ne.symm (fixedRedInternalGreenLocalElement_ne_blue green blue)

/-- Forget the periodic name of a red variable-side element. -/
def variableSiteRedElementOfTyped
    {Variable : Type*} : RedElement Variable → VariableSiteElement
  | .cycleLink _ slot =>
      .cycleLink (occurrenceVariableSiteSlot slot)
  | .fixedRedInternal _ slot element =>
      .fixedRed (occurrenceVariableSiteSlot slot)
        (fixedRedInternalRedLocalElement element)
  | .clauseInternal _ | .clauseTerminal _ _ =>
      .cycleLink .first

/-- Forget the periodic name of a green variable-side element. -/
def variableSiteGreenElementOfTyped
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    GreenElement Variable → VariableSiteElement
  | .ordinaryInternal atom slot element =>
      .ordinary (occurrenceVariableSiteSlot slot)
        (ordinaryVariantAt source atom slot)
        (ordinaryInternalLocalElement element)
  | .fixedRedInternal _ slot element =>
      .fixedRed (occurrenceVariableSiteSlot slot)
        (fixedRedInternalGreenLocalElement element)
  | .clauseInternal _ | .clauseTerminal _ _ =>
      .cycleLink .first

/-- Forget the periodic name of a blue variable-side element. -/
def variableSiteBlueElementOfTyped
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    BlueElement Variable → VariableSiteElement
  | .ordinaryInternal atom slot element =>
      .ordinary (occurrenceVariableSiteSlot slot)
        (ordinaryVariantAt source atom slot)
        (ordinaryInternalLocalElement element)
  | .fixedRedInternal _ slot element =>
      .fixedRed (occurrenceVariableSiteSlot slot)
        (fixedRedInternalBlueLocalElement element)
  | .clauseInternal _ | .clauseTerminal _ _ =>
      .cycleLink .first

/-- Every red element listed in an active occurrence block is active in the
finite variable-site drawing. -/
theorem variableSiteRedElementOfTyped_matches
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : RedElement Variable)
    (elementMember : element ∈ occurrenceRedElements source atom slot) :
    (variableSiteRedElementOfTyped element).MatchesKind
      (sourceVariableSiteCount source atom)
      (sourceVariableSiteKind source atom) := by
  have active :=
    occurrenceVariableSiteSlot_index_lt
      source atom atomMember slot slotMember
  have active' :
      slot.index < sourceVariableSiteCount source atom := by
    simpa using active
  have kindAt :=
    sourceVariableSiteKind_active
      source atom atomMember slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceRedElements, kindEq] at elementMember
  all_goals
    rcases elementMember with rfl | rfl | rfl
  all_goals
    simp [variableSiteRedElementOfTyped,
      VariableSiteElement.MatchesKind, active', kindAt, kindEq,
      fixedRedInternalRedLocalElement]

/-- Every green element listed in an active occurrence block is active in
the finite variable-site drawing. -/
theorem variableSiteGreenElementOfTyped_matches
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : GreenElement Variable)
    (elementMember : element ∈ occurrenceGreenElements source atom slot) :
    (variableSiteGreenElementOfTyped source element).MatchesKind
      (sourceVariableSiteCount source atom)
      (sourceVariableSiteKind source atom) := by
  have active :=
    occurrenceVariableSiteSlot_index_lt
      source atom atomMember slot slotMember
  have active' :
      slot.index < sourceVariableSiteCount source atom := by
    simpa using active
  have kindAt :=
    sourceVariableSiteKind_active
      source atom atomMember slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceGreenElements, kindEq] at elementMember
  all_goals
    rcases elementMember with rfl | rfl | rfl
  all_goals
    simp [variableSiteGreenElementOfTyped,
      VariableSiteElement.MatchesKind, active', kindAt, kindEq,
      ordinaryVariantAt, ordinaryInternalLocalElement,
      fixedRedInternalGreenLocalElement]

/-- Every blue element listed in an active occurrence block is active in the
finite variable-site drawing. -/
theorem variableSiteBlueElementOfTyped_matches
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : BlueElement Variable)
    (elementMember : element ∈ occurrenceBlueElements source atom slot) :
    (variableSiteBlueElementOfTyped source element).MatchesKind
      (sourceVariableSiteCount source atom)
      (sourceVariableSiteKind source atom) := by
  have active :=
    occurrenceVariableSiteSlot_index_lt
      source atom atomMember slot slotMember
  have active' :
      slot.index < sourceVariableSiteCount source atom := by
    simpa using active
  have kindAt :=
    sourceVariableSiteKind_active
      source atom atomMember slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceBlueElements, kindEq] at elementMember
  all_goals
    rcases elementMember with rfl | rfl | rfl
  all_goals
    simp [variableSiteBlueElementOfTyped,
      VariableSiteElement.MatchesKind, active', kindAt, kindEq,
      ordinaryVariantAt, ordinaryInternalLocalElement,
      fixedRedInternalBlueLocalElement]

/-- Active local name of one listed red occurrence element. -/
def activeVariableSiteRedElement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : RedElement Variable)
    (elementMember : element ∈ occurrenceRedElements source atom slot) :
    ActiveVariableSiteElement
      (sourceVariableSiteCount source atom)
      (sourceVariableSiteKind source atom) :=
  ⟨variableSiteRedElementOfTyped element,
    variableSiteRedElementOfTyped_matches source atom atomMember slot
      slotMember element elementMember⟩

/-- Active local name of one listed green occurrence element. -/
def activeVariableSiteGreenElement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : GreenElement Variable)
    (elementMember : element ∈ occurrenceGreenElements source atom slot) :
    ActiveVariableSiteElement
      (sourceVariableSiteCount source atom)
      (sourceVariableSiteKind source atom) :=
  ⟨variableSiteGreenElementOfTyped source element,
    variableSiteGreenElementOfTyped_matches source atom atomMember slot
      slotMember element elementMember⟩

/-- Active local name of one listed blue occurrence element. -/
def activeVariableSiteBlueElement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : BlueElement Variable)
    (elementMember : element ∈ occurrenceBlueElements source atom slot) :
    ActiveVariableSiteElement
      (sourceVariableSiteCount source atom)
      (sourceVariableSiteKind source atom) :=
  ⟨variableSiteBlueElementOfTyped source element,
    variableSiteBlueElementOfTyped_matches source atom atomMember slot
      slotMember element elementMember⟩

/-- Membership of a typed variable-side red element identifies its active
occurrence block. -/
theorem redVariableElement_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (element : RedElement Variable)
    (member : element ∈ redElements source)
    (atom : Variable)
    (owner :
      redElementMacrocellOwner element =
        AssemblyMacrocellOwner.atom atom) :
    atom ∈ occurringVariables source ∧
      ∃ slot ∈ usedSlots source atom,
        element ∈ occurrenceRedElements source atom slot := by
  rw [redElements, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · simp only [List.mem_flatMap] at variableMember
    rcases variableMember with
      ⟨blockAtom, atomMember, slot, slotMember, blockMember⟩
    cases kindEq : occurrenceConnectorKind source blockAtom slot <;>
      simp [occurrenceRedElements, kindEq] at blockMember
    all_goals
      rcases blockMember with rfl | rfl | rfl
    all_goals
      have atomEq := AssemblyMacrocellOwner.atom.inj owner
      subst atom
      exact ⟨atomMember, slot, slotMember,
        by simp [occurrenceRedElements, kindEq]⟩
  · simp only [List.mem_flatMap] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, indexMember, blockMember⟩
    simp [allTerminalGroups] at blockMember
    rcases blockMember with rfl | rfl | rfl | rfl
    all_goals cases owner

/-- Membership of a typed variable-side green element identifies its active
occurrence block. -/
theorem greenVariableElement_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (element : GreenElement Variable)
    (member : element ∈ greenElements source)
    (atom : Variable)
    (owner :
      greenElementMacrocellOwner element =
        AssemblyMacrocellOwner.atom atom) :
    atom ∈ occurringVariables source ∧
      ∃ slot ∈ usedSlots source atom,
        element ∈ occurrenceGreenElements source atom slot := by
  rw [greenElements, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · simp only [List.mem_flatMap] at variableMember
    rcases variableMember with
      ⟨blockAtom, atomMember, slot, slotMember, blockMember⟩
    cases kindEq : occurrenceConnectorKind source blockAtom slot <;>
      simp [occurrenceGreenElements, kindEq] at blockMember
    all_goals
      rcases blockMember with rfl | rfl | rfl
    all_goals
      have atomEq := AssemblyMacrocellOwner.atom.inj owner
      subst atom
      exact ⟨atomMember, slot, slotMember,
        by simp [occurrenceGreenElements, kindEq]⟩
  · simp only [List.mem_flatMap] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, indexMember, blockMember⟩
    simp [allTerminalGroups] at blockMember
    rcases blockMember with rfl | rfl | rfl | rfl
    all_goals cases owner

/-- Membership of a typed variable-side blue element identifies its active
occurrence block. -/
theorem blueVariableElement_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (element : BlueElement Variable)
    (member : element ∈ blueElements source)
    (atom : Variable)
    (owner :
      blueElementMacrocellOwner element =
        AssemblyMacrocellOwner.atom atom) :
    atom ∈ occurringVariables source ∧
      ∃ slot ∈ usedSlots source atom,
        element ∈ occurrenceBlueElements source atom slot := by
  rw [blueElements, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · simp only [List.mem_flatMap] at variableMember
    rcases variableMember with
      ⟨blockAtom, atomMember, slot, slotMember, blockMember⟩
    cases kindEq : occurrenceConnectorKind source blockAtom slot <;>
      simp [occurrenceBlueElements, kindEq] at blockMember
    all_goals
      rcases blockMember with rfl | rfl | rfl
    all_goals
      have atomEq := AssemblyMacrocellOwner.atom.inj owner
      subst atom
      exact ⟨atomMember, slot, slotMember,
        by simp [occurrenceBlueElements, kindEq]⟩
  · simp only [List.mem_flatMap] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, indexMember, blockMember⟩
    simp [allTerminalGroups] at blockMember
    rcases blockMember with rfl | rfl | rfl | rfl
    all_goals cases owner

/-- Exact active block of a listed red cycle-link element. -/
theorem redCycleLink_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (member : RedElement.cycleLink atom slot ∈ redElements source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      RedElement.cycleLink atom slot ∈
        occurrenceRedElements source atom slot := by
  rcases redVariableElement_location source
      (.cycleLink atom slot) member atom rfl with
    ⟨atomMember, blockSlot, blockSlotMember, blockMember⟩
  cases kindEq :
      occurrenceConnectorKind source atom blockSlot <;>
    simp [occurrenceRedElements, kindEq] at blockMember
  all_goals
    rcases blockMember with rfl | rfl | rfl
  all_goals
    simp_all [occurrenceRedElements]

/-- Exact active block of a listed fixed-red red-private element. -/
theorem redFixedRedInternal_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (element : FixedRedInternalRed)
    (member :
      RedElement.fixedRedInternal atom slot element ∈
        redElements source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      RedElement.fixedRedInternal atom slot element ∈
        occurrenceRedElements source atom slot := by
  rcases redVariableElement_location source
      (.fixedRedInternal atom slot element) member atom rfl with
    ⟨atomMember, blockSlot, blockSlotMember, blockMember⟩
  cases kindEq :
      occurrenceConnectorKind source atom blockSlot <;>
    simp [occurrenceRedElements, kindEq] at blockMember
  all_goals
    rcases blockMember with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp_all [occurrenceRedElements]

/-- Exact active block of a listed ordinary green-private element. -/
theorem greenOrdinaryInternal_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (element : OrdinaryInternal)
    (member :
      GreenElement.ordinaryInternal atom slot element ∈
        greenElements source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      GreenElement.ordinaryInternal atom slot element ∈
        occurrenceGreenElements source atom slot := by
  rcases greenVariableElement_location source
      (.ordinaryInternal atom slot element) member atom rfl with
    ⟨atomMember, blockSlot, blockSlotMember, blockMember⟩
  cases kindEq :
      occurrenceConnectorKind source atom blockSlot <;>
    simp [occurrenceGreenElements, kindEq] at blockMember
  all_goals
    rcases blockMember with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp_all [occurrenceGreenElements]

/-- Exact active block of a listed fixed-red green-private element. -/
theorem greenFixedRedInternal_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (element : FixedRedInternalGreen)
    (member :
      GreenElement.fixedRedInternal atom slot element ∈
        greenElements source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      GreenElement.fixedRedInternal atom slot element ∈
        occurrenceGreenElements source atom slot := by
  rcases greenVariableElement_location source
      (.fixedRedInternal atom slot element) member atom rfl with
    ⟨atomMember, blockSlot, blockSlotMember, blockMember⟩
  cases kindEq :
      occurrenceConnectorKind source atom blockSlot <;>
    simp [occurrenceGreenElements, kindEq] at blockMember
  all_goals
    rcases blockMember with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp_all [occurrenceGreenElements]

/-- Exact active block of a listed ordinary blue-private element. -/
theorem blueOrdinaryInternal_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (element : OrdinaryInternal)
    (member :
      BlueElement.ordinaryInternal atom slot element ∈
        blueElements source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      BlueElement.ordinaryInternal atom slot element ∈
        occurrenceBlueElements source atom slot := by
  rcases blueVariableElement_location source
      (.ordinaryInternal atom slot element) member atom rfl with
    ⟨atomMember, blockSlot, blockSlotMember, blockMember⟩
  cases kindEq :
      occurrenceConnectorKind source atom blockSlot <;>
    simp [occurrenceBlueElements, kindEq] at blockMember
  all_goals
    rcases blockMember with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp_all [occurrenceBlueElements]

/-- Exact active block of a listed fixed-red blue-private element. -/
theorem blueFixedRedInternal_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (element : FixedRedInternalBlue)
    (member :
      BlueElement.fixedRedInternal atom slot element ∈
        blueElements source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      BlueElement.fixedRedInternal atom slot element ∈
        occurrenceBlueElements source atom slot := by
  rcases blueVariableElement_location source
      (.fixedRedInternal atom slot element) member atom rfl with
    ⟨atomMember, blockSlot, blockSlotMember, blockMember⟩
  cases kindEq :
      occurrenceConnectorKind source atom blockSlot <;>
    simp [occurrenceBlueElements, kindEq] at blockMember
  all_goals
    rcases blockMember with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp_all [occurrenceBlueElements]

/-- The green and blue private elements selected in active occurrence
blocks never denote the same finite variable-site element. -/
theorem variableSiteGreenElement_ne_blueElement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (greenSlot : OccurrenceSlot)
    (green : GreenElement Variable)
    (greenMember :
      green ∈ occurrenceGreenElements source atom greenSlot)
    (blueSlot : OccurrenceSlot)
    (blue : BlueElement Variable)
    (blueMember :
      blue ∈ occurrenceBlueElements source atom blueSlot) :
    variableSiteGreenElementOfTyped source green ≠
      variableSiteBlueElementOfTyped source blue := by
  intro equal
  cases greenKind :
      occurrenceConnectorKind source atom greenSlot <;>
    simp [occurrenceGreenElements, greenKind] at greenMember
  all_goals
    rcases greenMember with rfl | rfl | rfl
  all_goals
    cases blueKind :
        occurrenceConnectorKind source atom blueSlot <;>
      simp [occurrenceBlueElements, blueKind] at blueMember
  all_goals
    rcases blueMember with rfl | rfl | rfl
  all_goals
    simp_all [
      variableSiteGreenElementOfTyped,
      variableSiteBlueElementOfTyped, ordinaryVariantAt]

/-- Symmetric form of the green/blue local-name separation theorem. -/
theorem variableSiteBlueElement_ne_greenElement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (blueSlot : OccurrenceSlot)
    (blue : BlueElement Variable)
    (blueMember :
      blue ∈ occurrenceBlueElements source atom blueSlot)
    (greenSlot : OccurrenceSlot)
    (green : GreenElement Variable)
    (greenMember :
      green ∈ occurrenceGreenElements source atom greenSlot) :
    variableSiteBlueElementOfTyped source blue ≠
      variableSiteGreenElementOfTyped source green :=
  Ne.symm
    (variableSiteGreenElement_ne_blueElement
      source atom greenSlot green greenMember blueSlot blue blueMember)

/-- The red typed offset is exactly the translated position certified by
the complete finite variable-site drawing. -/
theorem redElementMacrocellOffset_eq_variableSite
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : RedElement Variable)
    (elementMember : element ∈ occurrenceRedElements source atom slot) :
    redElementMacrocellOffset source element =
      Cell.add standardThreeStrandLayout.variableOffset
        ((sourceVariableSiteDrawing source atom).elementPosition
          (activeVariableSiteRedElement source atom atomMember slot
            slotMember element elementMember)) := by
  have polarityAt :=
    sourceVariableSitePolarity_active
      source atom atomMember slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceRedElements, kindEq] at elementMember
  all_goals
    rcases elementMember with rfl | rfl | rfl
  all_goals
    simp [redElementMacrocellOffset,
      sourceVariableSiteDrawing, variableSiteDrawing,
      variableSiteElementPosition, activeVariableSiteRedElement,
      variableSiteRedElementOfTyped, fixedRedInternalSitePosition,
      fixedRedInternalRedLocalElement, polarityAt]

/-- The green typed offset is exactly the translated position certified by
the complete finite variable-site drawing. -/
theorem greenElementMacrocellOffset_eq_variableSite
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : GreenElement Variable)
    (elementMember : element ∈ occurrenceGreenElements source atom slot) :
    greenElementMacrocellOffset source element =
      Cell.add standardThreeStrandLayout.variableOffset
        ((sourceVariableSiteDrawing source atom).elementPosition
          (activeVariableSiteGreenElement source atom atomMember slot
            slotMember element elementMember)) := by
  have polarityAt :=
    sourceVariableSitePolarity_active
      source atom atomMember slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceGreenElements, kindEq] at elementMember
  all_goals
    rcases elementMember with rfl | rfl | rfl
  all_goals
    simp [greenElementMacrocellOffset,
      sourceVariableSiteDrawing, variableSiteDrawing,
      variableSiteElementPosition, activeVariableSiteGreenElement,
      variableSiteGreenElementOfTyped, ordinaryInternalSitePosition,
      fixedRedInternalSitePosition, ordinaryVariantAt,
      ordinaryInternalLocalElement, fixedRedInternalGreenLocalElement]
  all_goals simp_all

/-- The blue typed offset is exactly the translated position certified by
the complete finite variable-site drawing. -/
theorem blueElementMacrocellOffset_eq_variableSite
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (element : BlueElement Variable)
    (elementMember : element ∈ occurrenceBlueElements source atom slot) :
    blueElementMacrocellOffset source element =
      Cell.add standardThreeStrandLayout.variableOffset
        ((sourceVariableSiteDrawing source atom).elementPosition
          (activeVariableSiteBlueElement source atom atomMember slot
            slotMember element elementMember)) := by
  have polarityAt :=
    sourceVariableSitePolarity_active
      source atom atomMember slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceBlueElements, kindEq] at elementMember
  all_goals
    rcases elementMember with rfl | rfl | rfl
  all_goals
    simp [blueElementMacrocellOffset,
      sourceVariableSiteDrawing, variableSiteDrawing,
      variableSiteElementPosition, activeVariableSiteBlueElement,
      variableSiteBlueElementOfTyped, ordinaryInternalSitePosition,
      fixedRedInternalSitePosition, ordinaryVariantAt,
      ordinaryInternalLocalElement, fixedRedInternalBlueLocalElement]
  all_goals simp_all

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
