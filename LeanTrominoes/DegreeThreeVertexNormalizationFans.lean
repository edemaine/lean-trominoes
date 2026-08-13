/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DegreeThreeVertexNormalizationPorts

/-!
# Finite endpoint fans for degree-three normalization

The geometric drawing reports endpoint directions as `AxisDirection`s,
whereas the local Figure 2 templates are indexed by the four genuine
`VertexSide`s.  This module bridges those representations and packages the
finite choice made at a degree-three vertex: three distinct used sides leave
one unique omitted side, and the omitted-side template transports the three
incident edge colors to the canonical west/north/east ports.
-/

namespace LeanTrominoes

open Gadget

namespace VertexSide

/-- Recover a template side from a directed axis.  The east fallback is
irrelevant whenever the direction is certified genuine. -/
def ofDirection : AxisDirection → VertexSide
  | .east => .east
  | .north => .north
  | .west => .west
  | .south => .south
  | .invalid => .east

@[simp]
theorem ofDirection_direction (side : VertexSide) :
    ofDirection side.direction = side := by
  cases side <;> rfl

/-- Converting a genuine directed axis to a side and back loses no
information. -/
theorem direction_ofDirection
    (direction : AxisDirection) (genuine : direction.IsGenuine) :
    (ofDirection direction).direction = direction := by
  cases direction <;> simp_all [ofDirection, direction, AxisDirection.IsGenuine]

end VertexSide

namespace DegreeThreeVertexNormalization

/-- The first side, in a fixed finite order, not occupied by a three-edge
fan.  Under pairwise distinctness this is its unique unused direction. -/
def omittedSide (first second third : VertexSide) : VertexSide :=
  if .east ∉ [first, second, third] then .east
  else if .north ∉ [first, second, third] then .north
  else if .west ∉ [first, second, third] then .west
  else .south

/-- Three distinct cardinal sides omit exactly the selected fourth side. -/
theorem omittedSide_spec
    (first second third : VertexSide)
    (nodup : [first, second, third].Nodup) :
    let omitted := omittedSide first second third
    omitted ∉ [first, second, third] ∧
      ∀ side, side ≠ omitted → side ∈ [first, second, third] := by
  revert nodup
  cases first <;> cases second <;> cases third <;> native_decide

/-- A finite colored fan around one degree-three vertex.  The order records
the three syntactic endpoint occurrences; only distinctness of their
directions matters to the local normalization. -/
structure ColoredFan where
  firstSide : VertexSide
  secondSide : VertexSide
  thirdSide : VertexSide
  firstColor : WireColor
  secondColor : WireColor
  thirdColor : WireColor
  sidesNodup : [firstSide, secondSide, thirdSide].Nodup

namespace ColoredFan

/-- The unique cardinal side unused by this fan. -/
def omitted (fan : ColoredFan) : VertexSide :=
  omittedSide fan.firstSide fan.secondSide fan.thirdSide

/-- Total color lookup on old sides.  Its omitted-side fallback is never
observed by the three canonical template ports. -/
def colorAtSide (fan : ColoredFan) (side : VertexSide) : WireColor :=
  if side = fan.firstSide then fan.firstColor
  else if side = fan.secondSide then fan.secondColor
  else fan.thirdColor

/-- Color assignment induced on the canonical ports by the first Figure 2
template. -/
def canonicalColoring (fan : ColoredFan) :
    CanonicalVertexPort → WireColor :=
  fun port => fan.colorAtSide (boundarySide fan.omitted port)

theorem omitted_not_first (fan : ColoredFan) :
    fan.omitted ≠ fan.firstSide := by
  intro equal
  have notMember := (omittedSide_spec fan.firstSide fan.secondSide
    fan.thirdSide fan.sidesNodup).1
  change omittedSide fan.firstSide fan.secondSide fan.thirdSide ∉
    [fan.firstSide, fan.secondSide, fan.thirdSide] at notMember
  change omittedSide fan.firstSide fan.secondSide fan.thirdSide =
    fan.firstSide at equal
  apply notMember
  rw [equal]
  simp

theorem omitted_not_second (fan : ColoredFan) :
    fan.omitted ≠ fan.secondSide := by
  intro equal
  have notMember := (omittedSide_spec fan.firstSide fan.secondSide
    fan.thirdSide fan.sidesNodup).1
  change omittedSide fan.firstSide fan.secondSide fan.thirdSide ∉
    [fan.firstSide, fan.secondSide, fan.thirdSide] at notMember
  change omittedSide fan.firstSide fan.secondSide fan.thirdSide =
    fan.secondSide at equal
  apply notMember
  rw [equal]
  simp

theorem omitted_not_third (fan : ColoredFan) :
    fan.omitted ≠ fan.thirdSide := by
  intro equal
  have notMember := (omittedSide_spec fan.firstSide fan.secondSide
    fan.thirdSide fan.sidesNodup).1
  change omittedSide fan.firstSide fan.secondSide fan.thirdSide ∉
    [fan.firstSide, fan.secondSide, fan.thirdSide] at notMember
  change omittedSide fan.firstSide fan.secondSide fan.thirdSide =
    fan.thirdSide at equal
  apply notMember
  rw [equal]
  simp

/-- Each old endpoint color is recovered at the canonical port assigned to
its old side. -/
theorem canonicalColoring_first (fan : ColoredFan) :
    fan.canonicalColoring
        (canonicalPortForSide fan.omitted fan.firstSide) =
      fan.firstColor := by
  rw [canonicalColoring, boundarySide_canonicalPortForSide]
  · simp [colorAtSide]
  · exact fan.omitted_not_first.symm

theorem canonicalColoring_second (fan : ColoredFan) :
    fan.canonicalColoring
        (canonicalPortForSide fan.omitted fan.secondSide) =
      fan.secondColor := by
  rw [canonicalColoring, boundarySide_canonicalPortForSide]
  · have different : fan.secondSide ≠ fan.firstSide := by
      intro equal
      have firstNotMem := (List.nodup_cons.mp fan.sidesNodup).1
      exact firstNotMem (by simp [equal])
    simp [colorAtSide, different]
  · exact fan.omitted_not_second.symm

theorem canonicalColoring_third (fan : ColoredFan) :
    fan.canonicalColoring
        (canonicalPortForSide fan.omitted fan.thirdSide) =
      fan.thirdColor := by
  rw [canonicalColoring, boundarySide_canonicalPortForSide]
  · have thirdFirst : fan.thirdSide ≠ fan.firstSide := by
      intro equal
      have firstNotMem := (List.nodup_cons.mp fan.sidesNodup).1
      exact firstNotMem (by simp [equal])
    have thirdSecond : fan.thirdSide ≠ fan.secondSide := by
      intro equal
      have secondNodup := (List.nodup_cons.mp fan.sidesNodup).2
      have secondNotMem := (List.nodup_cons.mp secondNodup).1
      exact secondNotMem (by simp [equal])
    simp [colorAtSide, thirdFirst, thirdSecond]
  · exact fan.omitted_not_third.symm

/-- Distinct endpoint colors remain distinct after the omitted-side
permutation to canonical ports. -/
theorem canonicalColoring_nodup (fan : ColoredFan)
    (colorsNodup :
      [fan.firstColor, fan.secondColor, fan.thirdColor].Nodup) :
    [fan.canonicalColoring .west, fan.canonicalColoring .north,
      fan.canonicalColoring .east].Nodup := by
  rcases fan with
    ⟨firstSide, secondSide, thirdSide,
      firstColor, secondColor, thirdColor, sidesNodup⟩
  revert sidesNodup colorsNodup
  cases firstSide <;> cases secondSide <;> cases thirdSide <;>
    cases firstColor <;> cases secondColor <;> cases thirdColor <;>
      native_decide

/-- A monochromatic endpoint fan induces the constant canonical coloring. -/
theorem canonicalColoring_eq_of_monochromatic
    (fan : ColoredFan) (color : WireColor)
    (first : fan.firstColor = color)
    (second : fan.secondColor = color)
    (third : fan.thirdColor = color) :
    fan.canonicalColoring = fun _ => color := by
  rcases fan with
    ⟨firstSide, secondSide, thirdSide,
      firstColor, secondColor, thirdColor, sidesNodup⟩
  simp only at first second third
  subst firstColor
  subst secondColor
  subst thirdColor
  revert sidesNodup
  cases firstSide <;> cases secondSide <;> cases thirdSide <;>
    cases color <;> native_decide

end ColoredFan
end DegreeThreeVertexNormalization
end LeanTrominoes
