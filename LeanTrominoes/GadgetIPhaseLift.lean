import LeanTrominoes.GadgetIPhaseTable

/-!
# Global geometric phase lift for the Figure 12 I gadgets

Choose any preferred exact local state realizing the requested orientation
at each drawing cell.  The verified preferred-phase law says that neighboring
choices automatically have equal geometric ports.  This constructs a
coherent I-port refinement and proves the full Figure 12 orientation behavior
theorem on vertex-separated normalized drawings.
-/

namespace LeanTrominoes
namespace Gadget

/-- Every valid orientation admits a coherent geometric I-port refinement. -/
theorem hasIPortRefinement_of_isOrientation
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (orientation : drawing.Orientation)
    (valid : drawing.IsOrientation orientation) :
    HasIPortRefinement drawing orientation := by
  classical
  have localWitness (location : Cell) :
      ∃ entry : IPreferredEntry,
        entry.1.1 = drawing.getAt location ∧
          IEntryRealizes entry.1 (orientation location) := by
    have complete : IPreferredOrientationComplete :=
      iPreferredPhaseTableCorrect.1
    obtain ⟨entry, entryType, entryRealizes⟩ :=
      complete (drawing.getAt location) (orientation location)
        (valid.1 location)
    refine ⟨entry, entryType, ?_⟩
    intro side active
    rw [entryType] at active ⊢
    exact entryRealizes side active
  choose selected selectedType selectedRealizes using localWitness
  refine ⟨fun location => (selected location).1.2, ?_, ?_, ?_⟩
  · intro location
    have member :
        (selected location).1 ∈ iSeparatedCellPortTable :=
      (Finset.mem_filter.mp (selected location).property).1
    have pairEquality :
        (drawing.getAt location, (selected location).1.2) =
          (selected location).1 := by
      apply Prod.ext
      · exact (selectedType location).symm
      · rfl
    rw [pairEquality]
    exact member
  · intro location side active
    have entryActive :
        ((selected location).1.1.portColor side).isSome := by
      rw [selectedType location]
      exact active
    have realized := selectedRealizes location side entryActive
    rw [selectedType location] at realized
    exact realized
  · intro location side
    let neighbor :=
      PeriodicOrthogonalDrawing.latticeNeighbor location side
    by_cases active :
        ((drawing.getAt location).portColor side).isSome
    · cases colorMatch :
          (drawing.getAt location).portColor side with
      | none => simp [colorMatch] at active
      | some color =>
          have neighborColor :=
            drawing.portColor_latticeNeighbor_eq wellFormed location side
          rw [colorMatch] at neighborColor
          have leftColor :
              (selected location).1.1.portColor side = some color := by
            rw [selectedType location]
            exact colorMatch
          have rightColor :
              (selected neighbor).1.1.portColor side.opposite =
                some color := by
            rw [selectedType neighbor]
            exact neighborColor.symm
          have leftActive :
              ((selected location).1.1.portColor side).isSome := by
            rw [leftColor]
            simp
          have rightActive :
              ((selected neighbor).1.1.portColor side.opposite).isSome := by
            rw [rightColor]
            simp
          exact iPreferredPhaseTableCorrect.2
            (selected location) (selected neighbor) side color
            leftColor rightColor (by
              rw [selectedRealizes location side leftActive,
                selectedRealizes neighbor side.opposite rightActive]
              exact valid.2 location side active)
    · have colorNone :
          (drawing.getAt location).portColor side = none := by
        cases colorMatch :
            (drawing.getAt location).portColor side with
        | none => rfl
        | some color => simp [colorMatch] at active
      have neighborColorNone :
          (drawing.getAt neighbor).portColor side.opposite = none := by
        have colors :=
          drawing.portColor_latticeNeighbor_eq wellFormed location side
        rw [colorNone] at colors
        exact colors.symm
      have leftColorNone :
          (selected location).1.1.portColor side = none := by
        rw [selectedType location]
        exact colorNone
      have rightColorNone :
          (selected neighbor).1.1.portColor side.opposite = none := by
        rw [selectedType neighbor]
        exact neighborColorNone
      have leftMember :
          (selected location).1 ∈ iSeparatedCellPortTable :=
        (Finset.mem_filter.mp (selected location).property).1
      have rightMember :
          (selected neighbor).1 ∈ iSeparatedCellPortTable :=
        (Finset.mem_filter.mp (selected neighbor).property).1
      rw [iLocalOrientationTableCorrect.2.2.1
          ⟨(selected location).1, leftMember⟩ side leftColorNone,
        iLocalOrientationTableCorrect.2.2.1
          ⟨(selected neighbor).1, rightMember⟩ side.opposite
            rightColorNone]

/-- Completeness half of Figure 12 gadget behavior. -/
theorem iHasCompatibleGadgetTiling_of_isOrientation
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (orientation : drawing.Orientation)
    (valid : drawing.IsOrientation orientation) :
    HasCompatibleGadgetTiling .I drawing :=
  hasCompatibleGadgetTiling_of_hasIPortRefinement drawing orientation
    (hasIPortRefinement_of_isOrientation drawing wellFormed
      orientation valid)

/-- Full finite-state correctness of the Figure 12 I-tromino gadget library
on normalized vertex-separated drawings. -/
theorem iOrientationBehaviorCorrect : OrientationBehaviorCorrect .I := by
  unfold OrientationBehaviorCorrect
  intro drawing separated
  constructor
  · rintro ⟨wellFormed, orientation, valid⟩
    exact ⟨wellFormed,
      iHasCompatibleGadgetTiling_of_isOrientation drawing wellFormed
        orientation valid⟩
  · rintro ⟨wellFormed, compatible⟩
    exact iHasOrientation_of_hasCompatibleGadgetTiling
      drawing wellFormed separated compatible

end Gadget
end LeanTrominoes
