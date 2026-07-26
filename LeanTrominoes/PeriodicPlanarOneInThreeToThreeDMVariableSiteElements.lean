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
