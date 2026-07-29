import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanUniqueness
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFans

/-!
# Source ports for coordinated ribbon fans

The finite coordinated-fan records and the occurrence-level corridor
construction describe the same variable and clause ports through different
indices.  This file identifies those descriptions exactly, so subsequent
route splicing can use the coordinated fans without changing either endpoint.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

namespace VariableRibbonFanData

/-- The routed finite triple selected by a source fan is the finite erasure
of the occurrence-level routed triple. -/
@[simp]
theorem sourceVariableRibbonFanData_routedTriple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (sourceVariableRibbonFanData presentation entry).routedTriple
        (occurrenceVariableSiteSlot entry.1.2) color =
      variableSiteTripleOfTyped
        (routedOccurrenceTriple
          source.erase entry.1.1 entry.1.2 color) := by
  cases kindEq :
      occurrenceConnectorKind source.erase entry.1.1 entry.1.2 <;>
    cases color <;>
    simp [routedTriple, routedOccurrenceTriple,
      variableSiteTripleOfTyped,
      sourceVariableRibbonFanData_kind, kindEq]

/-- A source fan built from one occurrence selects the right finite routed
triple for every other occurrence of the same variable. -/
@[simp]
theorem sourceVariableRibbonFanData_routedTriple_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (base candidate : ActiveOccurrenceEntry source.erase)
    (sameAtom : candidate.1.1 = base.1.1)
    (color : WireColor) :
    (sourceVariableRibbonFanData presentation base).routedTriple
        (occurrenceVariableSiteSlot candidate.1.2) color =
      variableSiteTripleOfTyped
        (routedOccurrenceTriple
          source.erase candidate.1.1 candidate.1.2 color) := by
  have fanKind :=
    sourceVariableRibbonFanData_kind_of_same_atom
      presentation base candidate sameAtom
  cases kindEq :
      occurrenceConnectorKind
        source.erase candidate.1.1 candidate.1.2 <;>
    cases color <;>
    simp [routedTriple, routedOccurrenceTriple,
      variableSiteTripleOfTyped, fanKind, kindEq]

/-- The finite source variable fan exposes exactly the occurrence-level
variable port used by the three-strand corridor. -/
theorem sourceVariableRibbonFanData_port
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    let data := sourceVariableRibbonFanData presentation entry
    let active :=
      sourceVariableRibbonFanData_slotActive presentation entry
    data.port (occurrenceVariableSiteSlot entry.1.2) active color =
      occurrenceVariableRibbonFanPort source.erase entry color := by
  dsimp only
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let active : data.SlotActive slot :=
    sourceVariableRibbonFanData_slotActive presentation entry
  change data.port slot active color =
    occurrenceVariableRibbonFanPort source.erase entry color
  have kindAt :
      sourceVariableSiteKind source.erase entry.1.1
          (occurrenceVariableSiteSlot entry.1.2) =
        occurrenceConnectorKind
          source.erase entry.1.1 entry.1.2 :=
    sourceVariableSiteKind_active source.erase
      entry.1.1 entry.atom_mem entry.1.2 entry.slot_mem
  cases kindEq :
      occurrenceConnectorKind
        source.erase entry.1.1 entry.1.2 <;>
    cases color <;>
    simp [port, occurrenceVariableRibbonFanPort,
      routedVariablePortPosition, variableSiteDrawing,
      variableSiteReference, variableSiteReferenceBase,
      variableSiteElementPosition, ordinaryVariableSiteElement,
      fixedRedVariableSiteElement, activeRoutedTriple,
      VariableOccurrence.reference,
      VariableOccurrenceTriple.references,
      FixedRedConnector.reference,
      FixedRedConnectorTriple.references,
      routedActiveVariableSiteTriple, activeVariableSiteTriple,
      routedTriple, routedOccurrenceTriple,
      variableSiteTripleOfTyped, data, slot,
      sourceVariableRibbonFanData, sourceVariableSiteDrawing,
      kindAt, kindEq]

/-- One coordinated source variable fan exposes the occurrence-level port
of every active occurrence belonging to the same variable. -/
theorem sourceVariableRibbonFanData_port_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (base candidate : ActiveOccurrenceEntry source.erase)
    (sameAtom : candidate.1.1 = base.1.1)
    (color : WireColor) :
    let data := sourceVariableRibbonFanData presentation base
    let active :=
      sourceVariableRibbonFanData_slotActive_of_same_atom
        presentation base candidate sameAtom
    data.port
        (occurrenceVariableSiteSlot candidate.1.2) active color =
      occurrenceVariableRibbonFanPort
        source.erase candidate color := by
  dsimp only
  let data := sourceVariableRibbonFanData presentation base
  let slot := occurrenceVariableSiteSlot candidate.1.2
  let active : data.SlotActive slot :=
    sourceVariableRibbonFanData_slotActive_of_same_atom
      presentation base candidate sameAtom
  change data.port slot active color =
    occurrenceVariableRibbonFanPort source.erase candidate color
  have kindAt :
      sourceVariableSiteKind source.erase candidate.1.1
          (occurrenceVariableSiteSlot candidate.1.2) =
        occurrenceConnectorKind source.erase
          candidate.1.1 candidate.1.2 :=
    sourceVariableSiteKind_active source.erase
      candidate.1.1 candidate.atom_mem
      candidate.1.2 candidate.slot_mem
  have kindAtBase :
      sourceVariableSiteKind source.erase base.1.1
          (occurrenceVariableSiteSlot candidate.1.2) =
        occurrenceConnectorKind source.erase
          candidate.1.1 candidate.1.2 := by
    calc
      sourceVariableSiteKind source.erase base.1.1
          (occurrenceVariableSiteSlot candidate.1.2) =
          sourceVariableSiteKind source.erase candidate.1.1
            (occurrenceVariableSiteSlot candidate.1.2) := by
        rw [sameAtom]
      _ = occurrenceConnectorKind source.erase
            candidate.1.1 candidate.1.2 :=
        kindAt
  have polarityAtBase :
      sourceVariableSitePolarity source.erase base.1.1
          (occurrenceVariableSiteSlot candidate.1.2) =
        sourceVariableSitePolarity source.erase candidate.1.1
          (occurrenceVariableSiteSlot candidate.1.2) := by
    rw [sameAtom]
  cases kindEq :
      occurrenceConnectorKind source.erase
        candidate.1.1 candidate.1.2 <;>
    cases color <;>
    simp [port, occurrenceVariableRibbonFanPort,
      routedVariablePortPosition, variableSiteDrawing,
      variableSiteReference, variableSiteReferenceBase,
      variableSiteElementPosition, ordinaryVariableSiteElement,
      fixedRedVariableSiteElement, activeRoutedTriple,
      VariableOccurrence.reference,
      VariableOccurrenceTriple.references,
      FixedRedConnector.reference,
      FixedRedConnectorTriple.references,
      routedActiveVariableSiteTriple, activeVariableSiteTriple,
      routedTriple, routedOccurrenceTriple,
      variableSiteTripleOfTyped, data, slot,
      sourceVariableRibbonFanData, sourceVariableSiteDrawing,
      kindAtBase, polarityAtBase, kindEq]

/-- The physical lane selected by a shared source variable fan agrees with
the occurrence-level corridor lane. -/
theorem sourceVariableRibbonFanData_ribbonLaneForColor_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (base candidate : ActiveOccurrenceEntry source.erase)
    (sameAtom : candidate.1.1 = base.1.1)
    (color : WireColor) :
    ((sourceVariableRibbonFanData presentation base).kind
        (occurrenceVariableSiteSlot candidate.1.2)).ribbonLaneForColor
          color =
      routedRibbonLane source.erase candidate color := by
  unfold routedRibbonLane occurrenceRibbonLaneForColor
  rw [sourceVariableRibbonFanData_kind_of_same_atom
    presentation base candidate sameAtom]

end VariableRibbonFanData

namespace ClauseRibbonFanData

/-- The semantic clause-fan port selected by an occurrence is exactly its
occurrence-level clause port. -/
theorem occurrenceClauseRibbonFanPort_eq_semanticPort
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    occurrenceClauseRibbonFanPort source entry color =
      semanticPort
        (occurrenceClauseTerminalGroup source entry) color := by
  cases color <;>
    rfl

/-- Selecting the occurrence's physical ribbon lane in its clause terminal
recovers the exact occurrence-level clause port. -/
theorem lanePort_routedRibbonLane
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    lanePort
        (occurrenceClauseTerminalGroup source entry)
        (routedRibbonLane source entry color) =
      occurrenceClauseRibbonFanPort source entry color := by
  unfold routedRibbonLane
  rw [occurrenceRibbonLaneForColor_eq_clause]
  unfold occurrenceClauseTerminalGroup
  rw [lanePort_ribbonLaneForColor]
  exact
    (occurrenceClauseRibbonFanPort_eq_semanticPort
      source entry color).symm

end ClauseRibbonFanData

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
