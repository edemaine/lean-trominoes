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

/-- A local coordinate lies in the half-open square of one macrocell.  This
variant includes the macrocell origin used by inherited vertices. -/
def PositionInHalfOpenMacrocell (factor : Nat) (position : Cell) : Prop :=
  0 ≤ position.1 ∧ position.1 < factor ∧
    0 ≤ position.2 ∧ position.2 < factor

instance (factor : Nat) (position : Cell) :
    Decidable (PositionInHalfOpenMacrocell factor position) := by
  unfold PositionInHalfOpenMacrocell
  infer_instance

/-- A local coordinate lies less than one full refined cell from its
macrocell origin in either direction.  Route bends may lie on or just outside
the nominal local cell even when all graph vertices lie strictly inside it. -/
def PositionInMacrocellHalo (factor : Nat) (position : Cell) : Prop :=
  -(factor : Int) < position.1 ∧ position.1 < factor ∧
    -(factor : Int) < position.2 ∧ position.2 < factor

instance (factor : Nat) (position : Cell) :
    Decidable (PositionInMacrocellHalo factor position) := by
  unfold PositionInMacrocellHalo
  infer_instance

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

/-- Half-open macrocells over distinct lattice points are disjoint, including
when one or both local points are the macrocell origin. -/
theorem macrocellPosition_eq_iff_halfOpen
    {factor : Nat} (factorPositive : 0 < factor)
    {firstBase secondBase firstLocal secondLocal : Cell}
    (firstInside : PositionInHalfOpenMacrocell factor firstLocal)
    (secondInside : PositionInHalfOpenMacrocell factor secondLocal) :
    macrocellPosition factor firstBase firstLocal =
        macrocellPosition factor secondBase secondLocal ↔
      firstBase = secondBase ∧ firstLocal = secondLocal := by
  rcases firstBase with ⟨firstBaseX, firstBaseY⟩
  rcases secondBase with ⟨secondBaseX, secondBaseY⟩
  rcases firstLocal with ⟨firstLocalX, firstLocalY⟩
  rcases secondLocal with ⟨secondLocalX, secondLocalY⟩
  simp only [PositionInHalfOpenMacrocell] at firstInside secondInside
  simp only [macrocellPosition, add, scale, Prod.mk.injEq]
  constructor
  · rintro ⟨horizontal, vertical⟩
    have factorIntPositive : (0 : Int) < factor := by
      exact_mod_cast factorPositive
    have baseX : firstBaseX = secondBaseX := by
      by_contra different
      rcases lt_or_gt_of_ne different with forward | backward
      · nlinarith [firstInside.1, firstInside.2.1,
          secondInside.1, secondInside.2.1]
      · nlinarith [firstInside.1, firstInside.2.1,
          secondInside.1, secondInside.2.1]
    have baseY : firstBaseY = secondBaseY := by
      by_contra different
      rcases lt_or_gt_of_ne different with forward | backward
      · nlinarith [firstInside.2.2.1, firstInside.2.2.2,
          secondInside.2.2.1, secondInside.2.2.2]
      · nlinarith [firstInside.2.2.1, firstInside.2.2.2,
          secondInside.2.2.1, secondInside.2.2.2]
    subst secondBaseX
    subst secondBaseY
    simp only [true_and]
    constructor <;> omega
  · rintro ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    exact ⟨rfl, rfl⟩

/-- Equality after a refined-period translation separates into equality of
the local offsets and the corresponding base-period translation. -/
theorem macrocellPosition_eq_periodTranslate_iff_halfOpen
    {factor period : Nat} (factorPositive : 0 < factor)
    {firstBase secondBase firstLocal secondLocal relativeTranslate : Cell}
    (firstInside : PositionInHalfOpenMacrocell factor firstLocal)
    (secondInside : PositionInHalfOpenMacrocell factor secondLocal) :
    macrocellPosition factor firstBase firstLocal =
        Cell.add
          (Cell.scale (factor * period) relativeTranslate)
          (macrocellPosition factor secondBase secondLocal) ↔
      firstBase =
          Cell.add (Cell.scale period relativeTranslate) secondBase ∧
        firstLocal = secondLocal := by
  have translatedPosition :
      Cell.add
          (Cell.scale (factor * period) relativeTranslate)
          (macrocellPosition factor secondBase secondLocal) =
        macrocellPosition factor
          (Cell.add (Cell.scale period relativeTranslate) secondBase)
          secondLocal := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    rcases secondBase with ⟨secondBaseX, secondBaseY⟩
    rcases secondLocal with ⟨secondLocalX, secondLocalY⟩
    simp [macrocellPosition, Cell.add, Cell.scale]
    constructor <;> ring
  rw [translatedPosition]
  exact macrocellPosition_eq_iff_halfOpen
    factorPositive firstInside secondInside

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

/-- A point strictly inside an old fundamental square remains strictly
inside after refinement by any half-open local offset, including zero. -/
theorem macrocellPosition_halfOpen_in_refined_square
    {factor period : Nat} (factorPositive : 0 < factor)
    {base offset : Cell}
    (baseInside :
      0 < base.1 ∧ base.1 < period ∧
        0 < base.2 ∧ base.2 < period)
    (offsetInside : PositionInHalfOpenMacrocell factor offset) :
    let position := macrocellPosition factor base offset
    0 < position.1 ∧ position.1 < factor * period ∧
      0 < position.2 ∧ position.2 < factor * period := by
  rcases base with ⟨baseX, baseY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [PositionInHalfOpenMacrocell] at offsetInside
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

/-- A halo offset over an old point strictly inside the fundamental square
still lies strictly inside the refined square.  The integral base coordinate
provides one complete cell of slack on every side. -/
theorem macrocellPosition_halo_in_refined_square
    {factor period : Nat} (factorPositive : 0 < factor)
    {base offset : Cell}
    (baseInside :
      0 < base.1 ∧ base.1 < period ∧
        0 < base.2 ∧ base.2 < period)
    (offsetInside : PositionInMacrocellHalo factor offset) :
    let position := macrocellPosition factor base offset
    0 < position.1 ∧ position.1 < factor * period ∧
      0 < position.2 ∧ position.2 < factor * period := by
  rcases base with ⟨baseX, baseY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [PositionInMacrocellHalo] at offsetInside
  simp only [macrocellPosition, add, scale]
  have factorIntPositive : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  have baseXAtLeastOne : 1 ≤ baseX := by omega
  have baseYAtLeastOne : 1 ≤ baseY := by omega
  have baseXBelowLast : baseX + 1 ≤ period := by omega
  have baseYBelowLast : baseY + 1 ≤ period := by omega
  constructor
  · nlinarith [offsetInside.1]
  constructor
  · nlinarith [offsetInside.2.1]
  constructor
  · nlinarith [offsetInside.2.2.1]
  · nlinarith [offsetInside.2.2.2]

end Cell

end LeanTrominoes
