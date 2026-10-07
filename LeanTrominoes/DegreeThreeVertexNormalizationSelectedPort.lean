/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DegreeThreeVertexNormalizationFans

/-! # Uncolored port selection for the general degree-three drawing lemma -/
namespace LeanTrominoes.DegreeThreeVertexNormalization

def rotationsToWest : CanonicalVertexPort → PortRotationCount
  | .west => .zero
  | .north => .two
  | .east => .one

theorem oldPortAfterRotations_west_rotationsToWest (port : CanonicalVertexPort) :
    oldPortAfterRotations (rotationsToWest port) .west = port := by
  cases port <;> rfl

theorem oldPortAfterRotations_bijective (count : PortRotationCount) :
    Function.Bijective (oldPortAfterRotations count) := by
  constructor
  · intro first second same
    cases count <;> cases first <;> cases second <;>
      simp_all [oldPortAfterRotations,oldPortAfterClockwise]
  · intro port
    cases count <;> cases port <;>
      first | exact ⟨.west,rfl⟩ | exact ⟨.north,rfl⟩ | exact ⟨.east,rfl⟩

def selectedBoundarySide (omitted selected : VertexSide) (port : CanonicalVertexPort) : VertexSide :=
  boundarySide omitted (oldPortAfterRotations
    (rotationsToWest (canonicalPortForSide omitted selected)) port)

theorem selectedBoundarySide_west (omitted selected : VertexSide) (used : selected ≠ omitted) :
    selectedBoundarySide omitted selected .west = selected := by
  rw [selectedBoundarySide,oldPortAfterRotations_west_rotationsToWest,
    boundarySide_canonicalPortForSide omitted selected used]

theorem selectedBoundarySide_injective (omitted selected : VertexSide) :
    Function.Injective (selectedBoundarySide omitted selected) := by
  intro first second same
  have equal := congrArg (canonicalPortForSide omitted) same
  simp only [selectedBoundarySide,canonicalPortForSide_boundarySide] at equal
  exact (oldPortAfterRotations_bijective _).1 equal

theorem selectedBoundarySide_complete (omitted selected : VertexSide) (side : VertexSide)
    (used : side ≠ omitted) : ∃ port, selectedBoundarySide omitted selected port = side := by
  obtain ⟨port,equal⟩ := (oldPortAfterRotations_bijective
    (rotationsToWest (canonicalPortForSide omitted selected))).2 (canonicalPortForSide omitted side)
  refine ⟨port,?_⟩
  rw [selectedBoundarySide,equal,boundarySide_canonicalPortForSide omitted side used]

theorem selectedBoundarySide_ne_omitted (omitted selected : VertexSide) (port : CanonicalVertexPort) :
    selectedBoundarySide omitted selected port ≠ omitted := by
  cases omitted <;> cases selected <;> cases port <;>
    decide +kernel

def selectedCanonicalPort (omitted selected side : VertexSide) : CanonicalVertexPort :=
  if selectedBoundarySide omitted selected .west = side then .west
  else if selectedBoundarySide omitted selected .north = side then .north
  else .east

theorem selectedBoundarySide_selectedCanonicalPort (omitted selected side : VertexSide)
    (used : side ≠ omitted) :
    selectedBoundarySide omitted selected (selectedCanonicalPort omitted selected side) = side := by
  revert used
  cases omitted <;> cases selected <;> cases side <;> decide +kernel

theorem selectedCanonicalPort_selectedBoundarySide (omitted selected : VertexSide) (port : CanonicalVertexPort) :
    selectedCanonicalPort omitted selected (selectedBoundarySide omitted selected port) = port := by
  cases omitted <;> cases selected <;> cases port <;> decide +kernel

theorem selectedCanonicalPort_chosen (omitted selected : VertexSide) (used : selected ≠ omitted) :
    selectedCanonicalPort omitted selected selected = .west := by
  unfold selectedCanonicalPort
  rw [selectedBoundarySide_west omitted selected used]
  simp

theorem selectedCanonicalPort_injective_on_used (omitted selected : VertexSide) {first second : VertexSide}
    (firstUsed : first ≠ omitted) (secondUsed : second ≠ omitted)
    (equal : selectedCanonicalPort omitted selected first = selectedCanonicalPort omitted selected second) : first = second := by
  have boundaries := congrArg (selectedBoundarySide omitted selected) equal
  simpa only [selectedBoundarySide_selectedCanonicalPort omitted selected first firstUsed,
    selectedBoundarySide_selectedCanonicalPort omitted selected second secondUsed] using boundaries

end LeanTrominoes.DegreeThreeVertexNormalization
