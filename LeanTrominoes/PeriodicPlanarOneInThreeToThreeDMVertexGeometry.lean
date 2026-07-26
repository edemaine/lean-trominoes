import LeanTrominoes.PeriodicMacrocellGeometry
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalDrawing
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMThreeStrandConstruction

/-!
# Macrocell geometry of the assembled planar 3DM vertices

The variable-site templates occupy relative coordinates
`[-4, 84] × [-8, 16]`, and the clause core occupies
`[0, 28] × [0, 24]`.  This file chooses a concrete `128 × 128`
refinement cell, translates both templates strictly into its interior, and
certifies the resulting finite coordinate bounds.

Every assembled typed vertex is then expressed uniformly as a source
incidence-graph vertex position refined by `128`, plus one certified local
offset.  This is the interface needed to transfer source fundamental-square
bounds and source-vertex separation to the assembled drawing.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- A fixed refinement large enough for every complete variable site and
clause core.  Both gadgets are centered around `(64, 64)`, matching the
ribbon-macrocell center inside the same refined block.  The legacy lane
offsets remain distinct interior points for the prototype routing. -/
def standardThreeStrandLayout : ThreeStrandLayout where
  factor := 128
  factorPositive := by decide
  variableOffset := (20, 64)
  clauseOffset := (50, 52)
  laneOffset
    | .red => (96, 96)
    | .green => (100, 100)
    | .blue => (104, 104)

/-- The source incidence-graph vertex whose refinement cell owns an
assembled 3DM vertex. -/
inductive AssemblyMacrocellOwner (Variable : Type*)
  | atom (value : Variable)
  | clause (clauseIndex : Nat)
  deriving DecidableEq, Repr

/-- Physical position of a source macrocell owner. -/
def assemblyMacrocellOwnerPosition
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    AssemblyMacrocellOwner Variable → Cell
  | .atom value => placement.position value
  | .clause clauseIndex =>
      positionedClausePositionAt source clauseIndex

/-- Owner of a typed triple vertex. -/
def tripleMacrocellOwner {Variable : Type*} :
    Triple Variable → AssemblyMacrocellOwner Variable
  | .ordinary atom _ _ _ => .atom atom
  | .fixedRed atom _ _ => .atom atom
  | .clause clauseIndex _ => .clause clauseIndex

/-- Owner of a typed red element vertex. -/
def redElementMacrocellOwner {Variable : Type*} :
    RedElement Variable → AssemblyMacrocellOwner Variable
  | .cycleLink atom _ => .atom atom
  | .fixedRedInternal atom _ _ => .atom atom
  | .clauseInternal clauseIndex => .clause clauseIndex
  | .clauseTerminal clauseIndex _ => .clause clauseIndex

/-- Owner of a typed green element vertex. -/
def greenElementMacrocellOwner {Variable : Type*} :
    GreenElement Variable → AssemblyMacrocellOwner Variable
  | .ordinaryInternal atom _ _ => .atom atom
  | .fixedRedInternal atom _ _ => .atom atom
  | .clauseInternal clauseIndex => .clause clauseIndex
  | .clauseTerminal clauseIndex _ => .clause clauseIndex

/-- Owner of a typed blue element vertex. -/
def blueElementMacrocellOwner {Variable : Type*} :
    BlueElement Variable → AssemblyMacrocellOwner Variable
  | .ordinaryInternal atom _ _ => .atom atom
  | .fixedRedInternal atom _ _ => .atom atom
  | .clauseInternal clauseIndex => .clause clauseIndex
  | .clauseTerminal clauseIndex _ => .clause clauseIndex

/-- Local refined-cell offset of a typed triple. -/
def tripleMacrocellOffset
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    Triple Variable → Cell
  | triple@(.ordinary _ slot _ _) =>
      Cell.add standardThreeStrandLayout.variableOffset
        (placeVariableModulePoint
          (occurrenceVariableSiteSlot slot)
          (orientedTripleLocalPosition source triple))
  | triple@(.fixedRed _ slot _) =>
      Cell.add standardThreeStrandLayout.variableOffset
        (placeVariableModulePoint
          (occurrenceVariableSiteSlot slot)
          (orientedTripleLocalPosition source triple))
  | triple@(.clause _ _) =>
      Cell.add standardThreeStrandLayout.clauseOffset
        (orientedTripleLocalPosition source triple)

/-- Local refined-cell offset of a typed red element. -/
def redElementMacrocellOffset
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    RedElement Variable → Cell
  | .cycleLink _ slot =>
      Cell.add standardThreeStrandLayout.variableOffset
        (variableCycleLinkPosition
          (occurrenceVariableSiteSlot slot))
  | .fixedRedInternal atom slot element =>
      Cell.add standardThreeStrandLayout.variableOffset
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalRedLocalElement element))
  | element@(.clauseInternal _) =>
      Cell.add standardThreeStrandLayout.clauseOffset
        (redClauseElementLocalPosition element)
  | element@(.clauseTerminal _ _) =>
      Cell.add standardThreeStrandLayout.clauseOffset
        (redClauseElementLocalPosition element)

/-- Local refined-cell offset of a typed green element. -/
def greenElementMacrocellOffset
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    GreenElement Variable → Cell
  | .ordinaryInternal atom slot element =>
      Cell.add standardThreeStrandLayout.variableOffset
        (ordinaryInternalSitePosition source atom slot element)
  | .fixedRedInternal atom slot element =>
      Cell.add standardThreeStrandLayout.variableOffset
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalGreenLocalElement element))
  | element@(.clauseInternal _) =>
      Cell.add standardThreeStrandLayout.clauseOffset
        (greenClauseElementLocalPosition element)
  | element@(.clauseTerminal _ _) =>
      Cell.add standardThreeStrandLayout.clauseOffset
        (greenClauseElementLocalPosition element)

/-- Local refined-cell offset of a typed blue element. -/
def blueElementMacrocellOffset
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    BlueElement Variable → Cell
  | .ordinaryInternal atom slot element =>
      Cell.add standardThreeStrandLayout.variableOffset
        (ordinaryInternalSitePosition source atom slot element)
  | .fixedRedInternal atom slot element =>
      Cell.add standardThreeStrandLayout.variableOffset
        (fixedRedInternalSitePosition source atom slot
          (fixedRedInternalBlueLocalElement element))
  | element@(.clauseInternal _) =>
      Cell.add standardThreeStrandLayout.clauseOffset
        (blueClauseElementLocalPosition element)
  | element@(.clauseTerminal _ _) =>
      Cell.add standardThreeStrandLayout.clauseOffset
        (blueClauseElementLocalPosition element)

/-- Every typed triple lies strictly inside its `128 × 128` refinement
cell. -/
theorem tripleMacrocellOffset_inside
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (triple : Triple Variable) :
    Cell.PositionInOpenMacrocell
      standardThreeStrandLayout.factor
      (tripleMacrocellOffset source triple) := by
  cases triple with
  | ordinary atom slot variant localTriple =>
      cases polarity : occurrencePolarity source atom slot <;>
        cases slot <;> cases variant <;> cases localTriple <;>
        norm_num [Cell.PositionInOpenMacrocell,
          tripleMacrocellOffset, standardThreeStrandLayout,
          occurrenceVariableSiteSlot, placeVariableModulePoint,
          variableModuleOrigin, orientedTripleLocalPosition,
          VariableOccurrence.orientedBoundaryDrawing,
          VariableOccurrence.boundaryDrawing,
          VariableOccurrence.boundaryTriplePosition,
          LocalIncidenceDrawing.mapPoints,
          reflectAcrossVertical, Cell.add,
          VariableSiteSlot.index, polarity]
  | fixedRed atom slot localTriple =>
      cases polarity : occurrencePolarity source atom slot <;>
        cases slot <;> cases localTriple <;>
        norm_num [Cell.PositionInOpenMacrocell,
          tripleMacrocellOffset, standardThreeStrandLayout,
          occurrenceVariableSiteSlot, placeVariableModulePoint,
          variableModuleOrigin, orientedTripleLocalPosition,
          FixedRedConnector.boundaryDrawing,
          FixedRedConnector.drawing,
          LocalIncidenceDrawing.mapPoints, rotateClockwise,
          reflectAcrossVertical,
          FixedRedConnector.normalizeFixedRedBoundary,
          reflectAcrossHorizontal, polarity,
          FixedRedConnectorTriple.position, Cell.add,
          VariableSiteSlot.index]
  | clause clauseIndex set =>
      cases set <;>
        norm_num [Cell.PositionInOpenMacrocell,
          tripleMacrocellOffset, standardThreeStrandLayout,
          orientedTripleLocalPosition,
          X3CClauseOrthogonal.setPosition, Cell.add]

/-- Every assembled red element lies strictly inside its owner cell. -/
theorem redElementMacrocellOffset_inside
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (element : RedElement Variable) :
    Cell.PositionInOpenMacrocell
      standardThreeStrandLayout.factor
      (redElementMacrocellOffset source element) := by
  cases element with
  | cycleLink atom slot =>
      cases slot <;>
        norm_num [Cell.PositionInOpenMacrocell,
          redElementMacrocellOffset, standardThreeStrandLayout,
          variableCycleLinkPosition, variableModuleOrigin,
          occurrenceVariableSiteSlot, VariableSiteSlot.index,
          Cell.add]
  | fixedRedInternal atom slot element =>
      cases polarity : occurrencePolarity source atom slot <;>
        cases slot <;> cases element <;>
        norm_num [Cell.PositionInOpenMacrocell,
          redElementMacrocellOffset, standardThreeStrandLayout,
          fixedRedInternalSitePosition,
          fixedRedInternalRedLocalElement,
          placeVariableModulePoint, variableModuleOrigin,
          occurrenceVariableSiteSlot, VariableSiteSlot.index,
          FixedRedConnector.boundaryDrawing,
          FixedRedConnector.drawing,
          LocalIncidenceDrawing.mapPoints, rotateClockwise,
          reflectAcrossVertical,
          FixedRedConnector.normalizeFixedRedBoundary,
          reflectAcrossHorizontal,
          FixedRedConnectorElement.position,
          FixedRedConnectorRed.position, Cell.add, polarity]
  | clauseInternal clauseIndex =>
      norm_num [Cell.PositionInOpenMacrocell,
        redElementMacrocellOffset, standardThreeStrandLayout,
        redClauseElementLocalPosition,
        X3CClauseOrthogonal.elementPosition, Cell.add]
  | clauseTerminal clauseIndex group =>
      cases group <;>
        norm_num [Cell.PositionInOpenMacrocell,
          redElementMacrocellOffset, standardThreeStrandLayout,
          redClauseElementLocalPosition, terminalElementForColor,
          X3CClauseTerminal.attachmentElement,
          X3CClauseOrthogonal.elementPosition, Cell.add]

/-- Every assembled green element lies strictly inside its owner cell. -/
theorem greenElementMacrocellOffset_inside
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (element : GreenElement Variable) :
    Cell.PositionInOpenMacrocell
      standardThreeStrandLayout.factor
      (greenElementMacrocellOffset source element) := by
  cases element with
  | ordinaryInternal atom slot element =>
      cases kind : occurrenceConnectorKind source atom slot <;>
        cases polarity : occurrencePolarity source atom slot <;>
        cases slot <;> cases element <;>
        norm_num [Cell.PositionInOpenMacrocell,
          greenElementMacrocellOffset, standardThreeStrandLayout,
          ordinaryInternalSitePosition, ordinaryVariantAt,
          ordinaryInternalLocalElement,
          placeVariableModulePoint, variableModuleOrigin,
          occurrenceVariableSiteSlot, VariableSiteSlot.index,
          VariableOccurrence.orientedBoundaryDrawing,
          VariableOccurrence.boundaryDrawing,
          VariableOccurrence.boundaryElementPosition,
          LocalIncidenceDrawing.mapPoints,
          reflectAcrossVertical, Cell.add, kind, polarity]
  | fixedRedInternal atom slot element =>
      cases polarity : occurrencePolarity source atom slot <;>
        cases slot <;> cases element <;>
        norm_num [Cell.PositionInOpenMacrocell,
          greenElementMacrocellOffset, standardThreeStrandLayout,
          fixedRedInternalSitePosition,
          fixedRedInternalGreenLocalElement,
          placeVariableModulePoint, variableModuleOrigin,
          occurrenceVariableSiteSlot, VariableSiteSlot.index,
          FixedRedConnector.boundaryDrawing,
          FixedRedConnector.drawing,
          LocalIncidenceDrawing.mapPoints, rotateClockwise,
          reflectAcrossVertical,
          FixedRedConnector.normalizeFixedRedBoundary,
          reflectAcrossHorizontal,
          FixedRedConnectorElement.position,
          FixedRedConnectorGreen.position, Cell.add, polarity]
  | clauseInternal clauseIndex =>
      norm_num [Cell.PositionInOpenMacrocell,
        greenElementMacrocellOffset, standardThreeStrandLayout,
        greenClauseElementLocalPosition,
        X3CClauseOrthogonal.elementPosition, Cell.add]
  | clauseTerminal clauseIndex group =>
      cases group <;>
        norm_num [Cell.PositionInOpenMacrocell,
          greenElementMacrocellOffset, standardThreeStrandLayout,
          greenClauseElementLocalPosition, terminalElementForColor,
          X3CClauseTerminal.attachmentElement,
          X3CClauseOrthogonal.elementPosition, Cell.add]

/-- Every assembled blue element lies strictly inside its owner cell. -/
theorem blueElementMacrocellOffset_inside
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (element : BlueElement Variable) :
    Cell.PositionInOpenMacrocell
      standardThreeStrandLayout.factor
      (blueElementMacrocellOffset source element) := by
  cases element with
  | ordinaryInternal atom slot element =>
      cases kind : occurrenceConnectorKind source atom slot <;>
        cases polarity : occurrencePolarity source atom slot <;>
        cases slot <;> cases element <;>
        norm_num [Cell.PositionInOpenMacrocell,
          blueElementMacrocellOffset, standardThreeStrandLayout,
          ordinaryInternalSitePosition, ordinaryVariantAt,
          ordinaryInternalLocalElement,
          placeVariableModulePoint, variableModuleOrigin,
          occurrenceVariableSiteSlot, VariableSiteSlot.index,
          VariableOccurrence.orientedBoundaryDrawing,
          VariableOccurrence.boundaryDrawing,
          VariableOccurrence.boundaryElementPosition,
          LocalIncidenceDrawing.mapPoints,
          reflectAcrossVertical, Cell.add, kind, polarity]
  | fixedRedInternal atom slot element =>
      cases polarity : occurrencePolarity source atom slot <;>
        cases slot <;> cases element <;>
        norm_num [Cell.PositionInOpenMacrocell,
          blueElementMacrocellOffset, standardThreeStrandLayout,
          fixedRedInternalSitePosition,
          fixedRedInternalBlueLocalElement,
          placeVariableModulePoint, variableModuleOrigin,
          occurrenceVariableSiteSlot, VariableSiteSlot.index,
          FixedRedConnector.boundaryDrawing,
          FixedRedConnector.drawing,
          LocalIncidenceDrawing.mapPoints, rotateClockwise,
          reflectAcrossVertical,
          FixedRedConnector.normalizeFixedRedBoundary,
          reflectAcrossHorizontal,
          FixedRedConnectorElement.position,
          FixedRedConnectorBlue.position, Cell.add, polarity]
  | clauseInternal clauseIndex =>
      norm_num [Cell.PositionInOpenMacrocell,
        blueElementMacrocellOffset, standardThreeStrandLayout,
        blueClauseElementLocalPosition,
        X3CClauseOrthogonal.elementPosition, Cell.add]
  | clauseTerminal clauseIndex group =>
      cases group <;>
        norm_num [Cell.PositionInOpenMacrocell,
          blueElementMacrocellOffset, standardThreeStrandLayout,
          blueClauseElementLocalPosition, terminalElementForColor,
          X3CClauseTerminal.attachmentElement,
          X3CClauseOrthogonal.elementPosition, Cell.add]

/-- An owner names an actual source incidence-graph vertex. -/
def AssemblyMacrocellOwner.IsDeclared
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    AssemblyMacrocellOwner Variable → Prop
  | .atom value => value ∈ occurringVariables source
  | .clause clauseIndex => clauseIndex < source.clauses.length

/-- Every listed triple belongs to a declared source macrocell. -/
theorem tripleMacrocellOwner_declared
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (triple : Triple Variable)
    (member : triple ∈ triples source) :
    (tripleMacrocellOwner triple).IsDeclared source := by
  rw [triples, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · simp only [variableTriples, List.mem_flatMap] at variableMember
    rcases variableMember with
      ⟨atom, atomMember, slot, slotMember, localMember⟩
    cases kind : occurrenceConnectorKind source atom slot <;>
      simp [occurrenceTriples, kind] at localMember
    all_goals
      rcases localMember with ⟨localTriple, localMember, rfl⟩
      exact atomMember
  · simp only [clauseTriples, List.mem_flatMap,
      List.mem_map] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, indexMember, set, setMember, rfl⟩
    exact List.mem_range.mp indexMember

/-- Every listed red element belongs to a declared source macrocell. -/
theorem redElementMacrocellOwner_declared
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (element : RedElement Variable)
    (member : element ∈ redElements source) :
    (redElementMacrocellOwner element).IsDeclared source := by
  rw [redElements, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · simp only [List.mem_flatMap] at variableMember
    rcases variableMember with
      ⟨atom, atomMember, slot, slotMember, localMember⟩
    cases kind : occurrenceConnectorKind source atom slot <;>
      simp [occurrenceRedElements, kind] at localMember
    all_goals
      rcases localMember with
        rfl | rfl | rfl
      all_goals exact atomMember
  · simp only [List.mem_flatMap] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, indexMember, localMember⟩
    have indexLt := List.mem_range.mp indexMember
    simp only [List.mem_append, List.mem_singleton,
      List.mem_map] at localMember
    rcases localMember with rfl | ⟨group, groupMember, rfl⟩
    · exact indexLt
    · exact indexLt

/-- Every listed green element belongs to a declared source macrocell. -/
theorem greenElementMacrocellOwner_declared
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (element : GreenElement Variable)
    (member : element ∈ greenElements source) :
    (greenElementMacrocellOwner element).IsDeclared source := by
  rw [greenElements, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · simp only [List.mem_flatMap] at variableMember
    rcases variableMember with
      ⟨atom, atomMember, slot, slotMember, localMember⟩
    cases kind : occurrenceConnectorKind source atom slot <;>
      simp [occurrenceGreenElements, kind] at localMember
    all_goals
      rcases localMember with
        rfl | rfl | rfl
      all_goals exact atomMember
  · simp only [List.mem_flatMap] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, indexMember, localMember⟩
    have indexLt := List.mem_range.mp indexMember
    simp only [List.mem_append, List.mem_singleton,
      List.mem_map] at localMember
    rcases localMember with rfl | ⟨group, groupMember, rfl⟩
    · exact indexLt
    · exact indexLt

/-- Every listed blue element belongs to a declared source macrocell. -/
theorem blueElementMacrocellOwner_declared
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (element : BlueElement Variable)
    (member : element ∈ blueElements source) :
    (blueElementMacrocellOwner element).IsDeclared source := by
  rw [blueElements, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · simp only [List.mem_flatMap] at variableMember
    rcases variableMember with
      ⟨atom, atomMember, slot, slotMember, localMember⟩
    cases kind : occurrenceConnectorKind source atom slot <;>
      simp [occurrenceBlueElements, kind] at localMember
    all_goals
      rcases localMember with
        rfl | rfl | rfl
      all_goals exact atomMember
  · simp only [List.mem_flatMap] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, indexMember, localMember⟩
    have indexLt := List.mem_range.mp indexMember
    simp only [List.mem_append, List.mem_singleton,
      List.mem_map] at localMember
    rcases localMember with rfl | ⟨group, groupMember, rfl⟩
    · exact indexLt
    · exact indexLt

/-- Under the standard constructed routing, a typed triple is exactly its
owner's refined source position plus its certified local offset. -/
theorem assembledTriplePosition_standard
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (triple : Triple Variable) :
    assembledTriplePosition
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        triple =
      Cell.macrocellPosition standardThreeStrandLayout.factor
        (assemblyMacrocellOwnerPosition source placement
          (tripleMacrocellOwner triple))
        (tripleMacrocellOffset source.erase triple) := by
  cases triple <;>
    simp [assembledTriplePosition,
      constructedThreeStrandRouting, constructedVariableOrigin,
      constructedClauseOrigin, tripleMacrocellOwner,
      assemblyMacrocellOwnerPosition, tripleMacrocellOffset,
      Cell.macrocellPosition, Cell.add, Cell.scale, add_assoc]

/-- The analogous macrocell expression for every red element. -/
theorem assembledRedElementPosition_standard
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (element : RedElement Variable) :
    assembledRedElementPosition
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        element =
      Cell.macrocellPosition standardThreeStrandLayout.factor
        (assemblyMacrocellOwnerPosition source placement
          (redElementMacrocellOwner element))
        (redElementMacrocellOffset source.erase element) := by
  cases element <;>
    simp [assembledRedElementPosition,
      constructedThreeStrandRouting, constructedVariableOrigin,
      constructedClauseOrigin, redElementMacrocellOwner,
      assemblyMacrocellOwnerPosition, redElementMacrocellOffset,
      Cell.macrocellPosition, Cell.add, Cell.scale, add_assoc]

/-- The analogous macrocell expression for every green element. -/
theorem assembledGreenElementPosition_standard
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (element : GreenElement Variable) :
    assembledGreenElementPosition
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        element =
      Cell.macrocellPosition standardThreeStrandLayout.factor
        (assemblyMacrocellOwnerPosition source placement
          (greenElementMacrocellOwner element))
        (greenElementMacrocellOffset source.erase element) := by
  cases element <;>
    simp [assembledGreenElementPosition,
      constructedThreeStrandRouting, constructedVariableOrigin,
      constructedClauseOrigin, greenElementMacrocellOwner,
      assemblyMacrocellOwnerPosition, greenElementMacrocellOffset,
      Cell.macrocellPosition, Cell.add, Cell.scale, add_assoc]

/-- The analogous macrocell expression for every blue element. -/
theorem assembledBlueElementPosition_standard
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (element : BlueElement Variable) :
    assembledBlueElementPosition
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        element =
      Cell.macrocellPosition standardThreeStrandLayout.factor
        (assemblyMacrocellOwnerPosition source placement
          (blueElementMacrocellOwner element))
        (blueElementMacrocellOffset source.erase element) := by
  cases element <;>
    simp [assembledBlueElementPosition,
      constructedThreeStrandRouting, constructedVariableOrigin,
      constructedClauseOrigin, blueElementMacrocellOwner,
      assemblyMacrocellOwnerPosition, blueElementMacrocellOffset,
      Cell.macrocellPosition, Cell.add, Cell.scale, add_assoc]

/-- Every clause is represented in the zero-anchor gauge. -/
def HasZeroClauseAnchors {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) : Prop :=
  ∀ clause ∈ source.clauses,
    PeriodicCNF.clauseAnchor clause.literals = (0, 0)

/-- Positioned anchor normalization establishes the zero-anchor gauge. -/
theorem normalizedPositionedSource_hasZeroClauseAnchors
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    HasZeroClauseAnchors
      (normalizedPositionedSource source placement) := by
  intro clause clauseMember
  simp only [normalizedPositionedSource,
    PositionedPeriodicCNF.anchorNormalize,
    List.mem_map] at clauseMember
  rcases clauseMember with ⟨original, originalMember, rfl⟩
  exact
    PeriodicClause.clauseAnchor_anchorNormalize
      original.literals

/-- Every declared owner position is strictly inside the source
fundamental square. -/
theorem assemblyMacrocellOwnerPosition_inside
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (owner : AssemblyMacrocellOwner Variable)
    (declared : owner.IsDeclared source.erase) :
    let base :=
      assemblyMacrocellOwnerPosition source placement owner
    0 < base.1 ∧ base.1 < placement.period ∧
      0 < base.2 ∧ base.2 < placement.period := by
  let drawing :=
    PositionedPeriodicCNF.incidenceDrawing
      source placement presentation.routes
  cases owner with
  | atom value =>
      have vertexMember :
          CNFVertex.variable value ∈
            source.erase.incidenceGraph.vertices := by
        apply List.mem_append_left
        simp only [PeriodicCNF.incidenceVariableVertices,
          List.mem_map]
        exact ⟨value, declared, rfl⟩
      have positionMember :=
        presentation.vertexPosition_mem vertexMember
      have bounds :=
        presentation.compatible.2.2.2.2.1 _
          positionMember
      rw [PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
        source placement presentation.routes vertexMember] at bounds
      simp only [PeriodicGridDrawing.PositionInFundamentalSquare]
        at bounds
      rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
        source placement presentation.routes
        presentation.periodPositive] at bounds
      simpa [assemblyMacrocellOwnerPosition,
        PositionedPeriodicCNF.incidenceVertexPositionAt] using bounds
  | clause clauseIndex =>
      have indexLt : clauseIndex < source.clauses.length := by
        change clauseIndex < source.erase.clauses.length at declared
        simpa [PositionedPeriodicCNF.erase] using declared
      have vertexMember :
          CNFVertex.clause clauseIndex ∈
            source.erase.incidenceGraph.vertices := by
        apply List.mem_append_right
        simp [PeriodicCNF.incidenceClauseVertices,
          PositionedPeriodicCNF.erase, indexLt]
      have positionMember :=
        presentation.vertexPosition_mem vertexMember
      have bounds :=
        presentation.compatible.2.2.2.2.1 _
          positionMember
      rw [PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
        source placement presentation.routes vertexMember] at bounds
      rw [PositionedPeriodicCNF.incidenceVertexPositionAt_clause
        source placement clauseIndex indexLt] at bounds
      simp only [PeriodicGridDrawing.PositionInFundamentalSquare]
        at bounds
      rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
        source placement presentation.routes
        presentation.periodPositive] at bounds
      have anchorZero :=
        anchorsZero source.clauses[clauseIndex]
          (List.getElem_mem indexLt)
      have positionEq :
          positionedClausePositionAt source clauseIndex =
            PositionedPeriodicCNF.canonicalClausePosition
              placement source.clauses[clauseIndex] := by
        simp [positionedClausePositionAt,
          List.getElem?_eq_getElem indexLt,
          PositionedPeriodicCNF.canonicalClausePosition,
          PeriodicVariablePlacement.translation,
          anchorZero, Cell.scale, Cell.sub]
      rw [← positionEq] at bounds
      simpa [assemblyMacrocellOwnerPosition] using bounds

/-- Refining a declared source owner by any certified standard local offset
keeps the result inside the assembled fundamental square. -/
theorem standardMacrocellPosition_inside
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (owner : AssemblyMacrocellOwner Variable)
    (declared : owner.IsDeclared source.erase)
    (offset : Cell)
    (offsetInside :
      Cell.PositionInOpenMacrocell
        standardThreeStrandLayout.factor offset) :
    PeriodicGridDrawing.PositionInFundamentalSquare
      (assembledDrawing
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout))
        (Cell.macrocellPosition
          standardThreeStrandLayout.factor
          (assemblyMacrocellOwnerPosition
            source placement owner)
          offset) := by
  rw [PeriodicGridDrawing.PositionInFundamentalSquare,
    assembledDrawing_gridSize]
  change
    let position :=
      Cell.macrocellPosition
        standardThreeStrandLayout.factor
        (assemblyMacrocellOwnerPosition source placement owner)
        offset
    0 < position.1 ∧
      position.1 <
        standardThreeStrandLayout.factor * placement.period ∧
      0 < position.2 ∧
      position.2 <
        standardThreeStrandLayout.factor * placement.period
  exact Cell.macrocellPosition_in_refined_square
    standardThreeStrandLayout.factorPositive
    (assemblyMacrocellOwnerPosition_inside
      presentation anchorsZero owner declared)
    offsetInside

/-- The same refined-square conclusion holds for route points lying within
one complete cell of their owner origin.  This permits local routes to touch
or pass just outside a gadget's nominal open macrocell. -/
theorem standardMacrocellHaloPosition_inside
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (owner : AssemblyMacrocellOwner Variable)
    (declared : owner.IsDeclared source.erase)
    (offset : Cell)
    (offsetInside :
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor offset) :
    PeriodicGridDrawing.PositionInFundamentalSquare
      (assembledDrawing
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout))
        (Cell.macrocellPosition
          standardThreeStrandLayout.factor
          (assemblyMacrocellOwnerPosition
            source placement owner)
          offset) := by
  rw [PeriodicGridDrawing.PositionInFundamentalSquare,
    assembledDrawing_gridSize]
  change
    let position :=
      Cell.macrocellPosition
        standardThreeStrandLayout.factor
        (assemblyMacrocellOwnerPosition source placement owner)
        offset
    0 < position.1 ∧
      position.1 <
        standardThreeStrandLayout.factor * placement.period ∧
      0 < position.2 ∧
      position.2 <
        standardThreeStrandLayout.factor * placement.period
  exact Cell.macrocellPosition_halo_in_refined_square
    standardThreeStrandLayout.factorPositive
    (assemblyMacrocellOwnerPosition_inside
      presentation anchorsZero owner declared)
    offsetInside

/-- All vertex positions in the standard assembled drawing lie inside its
fundamental square. -/
theorem standardAssembledVertexPositions_inside
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source) :
    ∀ position ∈
        assembledVertexPositions
          (constructedThreeStrandRouting
            presentation standardThreeStrandLayout),
      PeriodicGridDrawing.PositionInFundamentalSquare
        (assembledDrawing
          (constructedThreeStrandRouting
            presentation standardThreeStrandLayout))
        position := by
  intro position positionMember
  simp only [assembledVertexPositions,
    List.mem_append, List.mem_map] at positionMember
  rcases positionMember with
      ((⟨triple, tripleMember, rfl⟩ |
          ⟨redElement, redMember, rfl⟩) |
        ⟨greenElement, greenMember, rfl⟩) |
      ⟨blueElement, blueMember, rfl⟩
  · rw [assembledTriplePosition_standard presentation triple]
    exact standardMacrocellPosition_inside
      presentation anchorsZero (tripleMacrocellOwner triple)
      (tripleMacrocellOwner_declared
        source.erase triple tripleMember)
      (tripleMacrocellOffset source.erase triple)
      (tripleMacrocellOffset_inside source.erase triple)
  · rw [assembledRedElementPosition_standard
      presentation redElement]
    exact standardMacrocellPosition_inside
      presentation anchorsZero
      (redElementMacrocellOwner redElement)
      (redElementMacrocellOwner_declared
        source.erase redElement redMember)
      (redElementMacrocellOffset source.erase redElement)
      (redElementMacrocellOffset_inside source.erase redElement)
  · rw [assembledGreenElementPosition_standard
      presentation greenElement]
    exact standardMacrocellPosition_inside
      presentation anchorsZero
      (greenElementMacrocellOwner greenElement)
      (greenElementMacrocellOwner_declared
        source.erase greenElement greenMember)
      (greenElementMacrocellOffset source.erase greenElement)
      (greenElementMacrocellOffset_inside source.erase greenElement)
  · rw [assembledBlueElementPosition_standard
      presentation blueElement]
    exact standardMacrocellPosition_inside
      presentation anchorsZero
      (blueElementMacrocellOwner blueElement)
      (blueElementMacrocellOwner_declared
        source.erase blueElement blueMember)
      (blueElementMacrocellOffset source.erase blueElement)
      (blueElementMacrocellOffset_inside source.erase blueElement)

/-- The concrete zero-anchor source used by the planar reduction satisfies
the assembled fundamental-square obligation unconditionally. -/
theorem standardNormalizedAssembledVertexPositions_inside
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement) :
    ∀ position ∈
        assembledVertexPositions
          (constructedThreeStrandRouting
            (normalizedIncidencePresentation presentation)
            standardThreeStrandLayout),
      PeriodicGridDrawing.PositionInFundamentalSquare
        (assembledDrawing
          (constructedThreeStrandRouting
            (normalizedIncidencePresentation presentation)
            standardThreeStrandLayout))
        position := by
  exact standardAssembledVertexPositions_inside
    (normalizedIncidencePresentation presentation)
    (normalizedPositionedSource_hasZeroClauseAnchors
      source placement)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
