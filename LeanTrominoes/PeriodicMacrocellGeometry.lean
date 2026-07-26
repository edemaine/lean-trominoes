import LeanTrominoes.PeriodicGridDrawing
import Mathlib.Tactic

/-!
# Arithmetic for periodic macrocell refinement

Geometric reductions refine every old drawing cell into a fixed square
macrocell.  A new vertex has the form

`factor • oldPosition + localOffset`.

This file records the two elementary facts used by all such assemblies:
open-macrocell offsets keep vertices inside the refined fundamental square,
and two refined positions can coincide only when both their old positions
and local offsets coincide.
-/

namespace LeanTrominoes

namespace Cell

/-- A local coordinate lies strictly inside one square macrocell. -/
def PositionInOpenMacrocell (factor : Nat) (position : Cell) : Prop :=
  0 < position.1 ∧ position.1 < factor ∧
    0 < position.2 ∧ position.2 < factor

/-- Place a local point in the macrocell refining a base lattice point. -/
def macrocellPosition
    (factor : Nat) (base offset : Cell) : Cell :=
  add (scale factor base) offset

/-- Open macrocells over distinct lattice points are disjoint.  Equality
also recovers the local coordinates within a common macrocell. -/
theorem macrocellPosition_eq_iff
    {factor : Nat} (factorPositive : 0 < factor)
    {firstBase secondBase firstLocal secondLocal : Cell}
    (firstInside : PositionInOpenMacrocell factor firstLocal)
    (secondInside : PositionInOpenMacrocell factor secondLocal) :
    macrocellPosition factor firstBase firstLocal =
        macrocellPosition factor secondBase secondLocal ↔
      firstBase = secondBase ∧ firstLocal = secondLocal := by
  rcases firstBase with ⟨firstBaseX, firstBaseY⟩
  rcases secondBase with ⟨secondBaseX, secondBaseY⟩
  rcases firstLocal with ⟨firstLocalX, firstLocalY⟩
  rcases secondLocal with ⟨secondLocalX, secondLocalY⟩
  simp only [PositionInOpenMacrocell] at firstInside secondInside
  simp only [macrocellPosition, add, scale, Prod.mk.injEq]
  constructor
  · rintro ⟨horizontal, vertical⟩
    have baseX : firstBaseX = secondBaseX := by
      by_contra different
      have ordered :
          firstBaseX < secondBaseX ∨
            secondBaseX < firstBaseX := lt_or_gt_of_ne different
      rcases ordered with forward | backward
      · have factorIntPositive : (0 : Int) < factor := by
          exact_mod_cast factorPositive
        nlinarith [firstInside.1, firstInside.2.1,
          secondInside.1, secondInside.2.1]
      · have factorIntPositive : (0 : Int) < factor := by
          exact_mod_cast factorPositive
        nlinarith [firstInside.1, firstInside.2.1,
          secondInside.1, secondInside.2.1]
    have baseY : firstBaseY = secondBaseY := by
      by_contra different
      have ordered :
          firstBaseY < secondBaseY ∨
            secondBaseY < firstBaseY := lt_or_gt_of_ne different
      rcases ordered with forward | backward
      · have factorIntPositive : (0 : Int) < factor := by
          exact_mod_cast factorPositive
        nlinarith [firstInside.2.2.1, firstInside.2.2.2,
          secondInside.2.2.1, secondInside.2.2.2]
      · have factorIntPositive : (0 : Int) < factor := by
          exact_mod_cast factorPositive
        nlinarith [firstInside.2.2.1, firstInside.2.2.2,
          secondInside.2.2.1, secondInside.2.2.2]
    subst secondBaseX
    subst secondBaseY
    simp only [true_and]
    constructor <;> omega
  · rintro ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact ⟨rfl, rfl⟩

/-- A point strictly inside an old fundamental square, refined by an
open-macrocell offset, remains strictly inside the enlarged square. -/
theorem macrocellPosition_in_refined_square
    {factor period : Nat} (factorPositive : 0 < factor)
    {base offset : Cell}
    (baseInside :
      0 < base.1 ∧ base.1 < period ∧
        0 < base.2 ∧ base.2 < period)
    (offsetInside : PositionInOpenMacrocell factor offset) :
    let position := macrocellPosition factor base offset
    0 < position.1 ∧ position.1 < factor * period ∧
      0 < position.2 ∧ position.2 < factor * period := by
  rcases base with ⟨baseX, baseY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [PositionInOpenMacrocell] at offsetInside
  simp only [macrocellPosition, add, scale]
  have factorIntPositive : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  constructor
  · nlinarith [baseInside.1, offsetInside.1]
  constructor
  · nlinarith [baseInside.2.1, offsetInside.2.1]
  constructor
  · nlinarith [baseInside.2.2.1, offsetInside.2.2.1]
  · nlinarith [baseInside.2.2.2, offsetInside.2.2.2]

end Cell

end LeanTrominoes
