import LeanTrominoes.GadgetLPhaseTable

/-!
# Global geometric phase lift for the Figure 11 L gadgets

For every undirected drawing edge, choose a pair of supported local entries
with exactly matching geometric ports, as guaranteed by the finite phase
table.  The cell splice law then combines the four independently chosen edge
phases into one supported entry at each cell.  This constructs a coherent
port refinement of every valid orientation and proves the full Figure 11
orientation behavior theorem.
-/

namespace LeanTrominoes
namespace Gadget

/-- Independently realizable choices for the four sides of one cell can be
spliced into one supported entry realizing all four choices. -/
theorem exists_lSupportedEntry_matching_sides
    (cellType : OrthogonalCellType) (inward : Side → Bool)
    (choices : Side → LSupportedEntry)
    (choiceType : ∀ side, (choices side).1.1 = cellType)
    (choiceRealizes : ∀ side, LEntryRealizes (choices side).1 inward) :
    ∃ combined : LSupportedEntry,
      combined.1.1 = cellType ∧
        LEntryRealizes combined.1 inward ∧
          ∀ side, combined.1.2.get side =
            (choices side).1.2.get side := by
  have splice (side : Side) (selected current : LSupportedEntry)
      (selectedType : selected.1.1 = cellType)
      (currentType : current.1.1 = cellType)
      (selectedRealizes : LEntryRealizes selected.1 inward)
      (currentRealizes : LEntryRealizes current.1 inward) :
      ∃ combined : LSupportedEntry,
        combined.1.1 = cellType ∧
          LEntryRealizes combined.1 inward ∧
            combined.1.2.get side = selected.1.2.get side ∧
              ∀ other, other ≠ side →
                combined.1.2.get other = current.1.2.get other := by
    exact lCellPhaseSplice
      { cellType := cellType
        inward := inward
        first := side
        second := side
        left := selected
        right := current }
      selectedType currentType selectedRealizes currentRealizes
  obtain ⟨east, eastType, eastRealizes, eastPort, eastOther⟩ :=
    splice .east (choices .east) (choices .north)
      (choiceType .east) (choiceType .north)
      (choiceRealizes .east) (choiceRealizes .north)
  obtain ⟨south, southType, southRealizes, southPort, southOther⟩ :=
    splice .south (choices .south) east
      (choiceType .south) eastType
      (choiceRealizes .south) eastRealizes
  obtain ⟨west, westType, westRealizes, westPort, westOther⟩ :=
    splice .west (choices .west) south
      (choiceType .west) southType
      (choiceRealizes .west) southRealizes
  refine ⟨west, westType, westRealizes, ?_⟩
  intro side
  cases side with
  | north =>
      rw [westOther .north (by decide),
        southOther .north (by decide),
        eastOther .north (by decide)]
  | east =>
      rw [westOther .east (by decide),
        southOther .east (by decide),
        eastPort]
  | south =>
      rw [westOther .south (by decide), southPort]
  | west =>
      exact westPort

/-- Every valid orientation of a well-formed drawing admits a coherent
geometric L-port refinement. -/
theorem hasLPortRefinement_of_isOrientation
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (orientation : drawing.Orientation)
    (valid : drawing.IsOrientation orientation) :
    HasLPortRefinement drawing orientation := by
  classical
  have localWitness (location : Cell) :
      ∃ entry : LSupportedEntry,
        entry.1.1 = drawing.getAt location ∧
          LEntryRealizes entry.1 (orientation location) := by
    have complete : LTableOrientationComplete
        (supportedCellPortTable .L) :=
      lLocalOrientationTableCorrect.2.1
    obtain ⟨entry, entryType, entryRealizes⟩ :=
      complete (drawing.getAt location) (orientation location)
        (valid.1 location)
    refine ⟨entry, entryType, ?_⟩
    intro side active
    rw [entryType] at active ⊢
    exact entryRealizes side active
  choose base baseType baseRealizes using localWitness
  have edgeWitness (location : Cell) (side : Side) :
      ∃ left right : LSupportedEntry,
        left.1.1 = drawing.getAt location ∧
          right.1.1 = drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location side) ∧
          LEntryRealizes left.1 (orientation location) ∧
          LEntryRealizes right.1
            (orientation
              (PeriodicOrthogonalDrawing.latticeNeighbor location side)) ∧
          left.1.2.get side = right.1.2.get side.opposite := by
    by_cases active :
        ((drawing.getAt location).portColor side).isSome
    · exact lEdgePhaseMatchable
        { leftType := drawing.getAt location
          rightType := drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location side)
          leftInward := orientation location
          rightInward := orientation
            (PeriodicOrthogonalDrawing.latticeNeighbor location side)
          side := side }
        (valid.1 location)
        (valid.1
          (PeriodicOrthogonalDrawing.latticeNeighbor location side))
        (drawing.portColor_latticeNeighbor_eq wellFormed location side)
        active (valid.2 location side active)
    · let neighbor :=
        PeriodicOrthogonalDrawing.latticeNeighbor location side
      refine ⟨base location, base neighbor,
        baseType location, baseType neighbor,
        baseRealizes location, baseRealizes neighbor, ?_⟩
      have colorNone :
          (drawing.getAt location).portColor side = none := by
        cases colorEq : (drawing.getAt location).portColor side with
        | none => rfl
        | some color =>
            simp [colorEq] at active
      have neighborColorNone :
          (drawing.getAt neighbor).portColor side.opposite = none := by
        have colors :=
          drawing.portColor_latticeNeighbor_eq wellFormed location side
        rw [colorNone] at colors
        exact colors.symm
      have leftColorNone :
          (base location).1.1.portColor side = none := by
        rw [baseType location]
        exact colorNone
      have rightColorNone :
          (base neighbor).1.1.portColor side.opposite = none := by
        rw [baseType neighbor]
        exact neighborColorNone
      rw [lLocalOrientationTableCorrect.2.2
          (base location) side leftColorNone,
        lLocalOrientationTableCorrect.2.2
          (base neighbor) side.opposite rightColorNone]
  choose edgeLeft edgeRight edgeLeftType edgeRightType
    edgeLeftRealizes edgeRightRealizes edgePorts using edgeWitness
  let choices : Cell → Side → LSupportedEntry := fun location side =>
    match side with
    | .north =>
        edgeRight
          (PeriodicOrthogonalDrawing.latticeNeighbor location .north) .south
    | .east => edgeLeft location .east
    | .south => edgeLeft location .south
    | .west =>
        edgeRight
          (PeriodicOrthogonalDrawing.latticeNeighbor location .west) .east
  have choicesType (location : Cell) (side : Side) :
      (choices location side).1.1 = drawing.getAt location := by
    cases side with
    | north =>
        simpa [choices, PeriodicOrthogonalDrawing.latticeNeighbor] using
          edgeRightType
            (PeriodicOrthogonalDrawing.latticeNeighbor location .north)
            .south
    | east =>
        exact edgeLeftType location .east
    | south =>
        exact edgeLeftType location .south
    | west =>
        simpa [choices, PeriodicOrthogonalDrawing.latticeNeighbor] using
          edgeRightType
            (PeriodicOrthogonalDrawing.latticeNeighbor location .west)
            .east
  have choicesRealize (location : Cell) (side : Side) :
      LEntryRealizes (choices location side).1 (orientation location) := by
    cases side with
    | north =>
        simpa [choices, PeriodicOrthogonalDrawing.latticeNeighbor] using
          edgeRightRealizes
            (PeriodicOrthogonalDrawing.latticeNeighbor location .north)
            .south
    | east =>
        exact edgeLeftRealizes location .east
    | south =>
        exact edgeLeftRealizes location .south
    | west =>
        simpa [choices, PeriodicOrthogonalDrawing.latticeNeighbor] using
          edgeRightRealizes
            (PeriodicOrthogonalDrawing.latticeNeighbor location .west)
            .east
  have choicesAgree (location : Cell) (side : Side) :
      (choices location side).1.2.get side =
        (choices
          (PeriodicOrthogonalDrawing.latticeNeighbor location side)
          side.opposite).1.2.get side.opposite := by
    cases side with
    | north =>
        simpa [choices, Side.opposite,
          PeriodicOrthogonalDrawing.latticeNeighbor] using
          (edgePorts
            (PeriodicOrthogonalDrawing.latticeNeighbor location .north)
            .south).symm
    | east =>
        simpa [choices, Side.opposite,
          PeriodicOrthogonalDrawing.latticeNeighbor] using
          edgePorts location .east
    | south =>
        simpa [choices, Side.opposite,
          PeriodicOrthogonalDrawing.latticeNeighbor] using
          edgePorts location .south
    | west =>
        simpa [choices, Side.opposite,
          PeriodicOrthogonalDrawing.latticeNeighbor] using
          (edgePorts
            (PeriodicOrthogonalDrawing.latticeNeighbor location .west)
            .east).symm
  have combinedWitness (location : Cell) :
      ∃ combined : LSupportedEntry,
        combined.1.1 = drawing.getAt location ∧
          LEntryRealizes combined.1 (orientation location) ∧
            ∀ side, combined.1.2.get side =
              (choices location side).1.2.get side :=
    exists_lSupportedEntry_matching_sides
      (drawing.getAt location) (orientation location)
      (choices location) (choicesType location) (choicesRealize location)
  choose combined combinedType combinedRealizes combinedPorts using
    combinedWitness
  refine ⟨fun location => (combined location).1.2, ?_, ?_, ?_⟩
  · intro location
    have member := (combined location).property
    have pairEquality :
        (drawing.getAt location, (combined location).1.2) =
          (combined location).1 := by
      apply Prod.ext
      · exact (combinedType location).symm
      · rfl
    rw [pairEquality]
    exact member
  · intro location side active
    have entryActive :
        ((combined location).1.1.portColor side).isSome := by
      rw [combinedType location]
      exact active
    have realized :=
      combinedRealizes location side entryActive
    rw [combinedType location] at realized
    exact realized
  · intro location side
    rw [combinedPorts location side,
      combinedPorts
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)
        side.opposite]
    exact choicesAgree location side

/-- Completeness half of Figure 11 gadget behavior. -/
theorem lHasCompatibleGadgetTiling_of_isOrientation
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (orientation : drawing.Orientation)
    (valid : drawing.IsOrientation orientation) :
    HasCompatibleGadgetTiling .L drawing :=
  hasCompatibleGadgetTiling_of_hasLPortRefinement drawing orientation
    (hasLPortRefinement_of_isOrientation drawing wellFormed
      orientation valid)

/-- Full finite-state correctness of the Figure 11 L-tromino gadget
library. -/
theorem lOrientationBehaviorCorrect : OrientationBehaviorCorrect .L := by
  unfold OrientationBehaviorCorrect
  intro drawing
  intro _separated
  constructor
  · rintro ⟨wellFormed, orientation, valid⟩
    exact ⟨wellFormed,
      lHasCompatibleGadgetTiling_of_isOrientation drawing wellFormed
        orientation valid⟩
  · rintro ⟨wellFormed, compatible⟩
    exact lHasOrientation_of_hasCompatibleGadgetTiling
      drawing wellFormed compatible

end Gadget
end LeanTrominoes
