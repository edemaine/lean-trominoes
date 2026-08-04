import LeanTrominoes.PeriodicMacrocellGeometry

/-!
# Periodic orbits of refined macrocell positions

Logical clause anchors can select a representative several whole periods
away from the natural local gadget point.  This file records refined
positions modulo that harmless choice of representative.
-/

namespace LeanTrominoes
namespace Cell

/-- A position is a whole refined-period translate of a local point over one
base lattice position. -/
def InMacrocellOrbit
    (factor period : Nat) (base offset position : Cell) : Prop :=
  ∃ shift,
    position =
      Cell.add
        (Cell.scale (factor * period) shift)
        (macrocellPosition factor base offset)

/-- Successive macrocell refinements compose by scaling the first local
offset and then adding the second. -/
theorem InMacrocellOrbit.compose
    {firstFactor secondFactor period : Nat}
    {base firstOffset middle secondOffset position : Cell}
    (firstOrbit :
      InMacrocellOrbit firstFactor period
        base firstOffset middle)
    (secondOrbit :
      InMacrocellOrbit secondFactor (firstFactor * period)
        middle secondOffset position) :
    InMacrocellOrbit (secondFactor * firstFactor) period base
      (Cell.add (Cell.scale secondFactor firstOffset) secondOffset)
      position := by
  rcases firstOrbit with ⟨firstShift, firstEqual⟩
  rcases secondOrbit with ⟨secondShift, secondEqual⟩
  refine ⟨Cell.add secondShift firstShift, ?_⟩
  rw [secondEqual, firstEqual]
  rcases firstShift with ⟨firstShiftX, firstShiftY⟩
  rcases secondShift with ⟨secondShiftX, secondShiftY⟩
  rcases base with ⟨baseX, baseY⟩
  rcases firstOffset with ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffset with ⟨secondOffsetX, secondOffsetY⟩
  simp only [macrocellPosition, Cell.add, Cell.scale, Prod.mk.injEq]
  constructor <;> norm_num [Nat.cast_mul] <;> ring

/-- Equality of two refined orbits, up to another whole refined period,
recovers equal local codes and equality of the bases up to a base period. -/
theorem inMacrocellOrbit_eq_periodTranslate
    {factor period : Nat} (factorPositive : 0 < factor)
    {firstBase secondBase firstLocal secondLocal
      firstPosition secondPosition relativeTranslate : Cell}
    (firstInside : PositionInHalfOpenMacrocell factor firstLocal)
    (secondInside : PositionInHalfOpenMacrocell factor secondLocal)
    (firstOrbit :
      InMacrocellOrbit factor period
        firstBase firstLocal firstPosition)
    (secondOrbit :
      InMacrocellOrbit factor period
        secondBase secondLocal secondPosition)
    (positionsEqual :
      firstPosition =
        Cell.add
          (Cell.scale (factor * period) relativeTranslate)
          secondPosition) :
    ∃ baseTranslate,
      firstBase =
          Cell.add (Cell.scale period baseTranslate) secondBase ∧
        firstLocal = secondLocal := by
  rcases firstOrbit with ⟨firstShift, firstPositionEq⟩
  rcases secondOrbit with ⟨secondShift, secondPositionEq⟩
  let baseTranslate :=
    Cell.sub (Cell.add relativeTranslate secondShift) firstShift
  have macrocellEqual :
      macrocellPosition factor firstBase firstLocal =
        Cell.add
          (Cell.scale (factor * period) baseTranslate)
          (macrocellPosition factor secondBase secondLocal) := by
    rw [firstPositionEq, secondPositionEq] at positionsEqual
    rcases firstShift with ⟨firstShiftX, firstShiftY⟩
    rcases secondShift with ⟨secondShiftX, secondShiftY⟩
    rcases relativeTranslate with ⟨relativeX, relativeY⟩
    rcases firstBase with ⟨firstBaseX, firstBaseY⟩
    rcases secondBase with ⟨secondBaseX, secondBaseY⟩
    rcases firstLocal with ⟨firstLocalX, firstLocalY⟩
    rcases secondLocal with ⟨secondLocalX, secondLocalY⟩
    simp only [baseTranslate, macrocellPosition,
      Cell.add, Cell.sub, Cell.scale, Prod.mk.injEq]
      at positionsEqual ⊢
    constructor
    · nlinarith [positionsEqual.1]
    · nlinarith [positionsEqual.2]
  refine ⟨baseTranslate, ?_⟩
  exact
    (macrocellPosition_eq_periodTranslate_iff_halfOpen
      factorPositive firstInside secondInside).mp macrocellEqual

/-- The coordinate-wise residue of a macrocell-orbit representative is its
natural macrocell point whenever the base is strictly inside its fundamental
square and the local code is half-open. -/
theorem inMacrocellOrbit_residue_eq_macrocellPosition
    {factor period : Nat} (factorPositive : 0 < factor)
    {base offset position : Cell}
    (baseInside :
      0 < base.1 ∧ base.1 < period ∧
        0 < base.2 ∧ base.2 < period)
    (localInside : PositionInHalfOpenMacrocell factor offset)
    (orbit : InMacrocellOrbit factor period base offset position) :
    (position.1 % (factor * period),
        position.2 % (factor * period)) =
      macrocellPosition factor base offset := by
  rcases orbit with ⟨shift, rfl⟩
  have refinedInside :=
    macrocellPosition_halfOpen_in_refined_square
      factorPositive baseInside localInside
  have naturalNonnegativeX :
      0 ≤ (macrocellPosition factor base offset).1 := by
    exact le_of_lt refinedInside.1
  have naturalNonnegativeY :
      0 ≤ (macrocellPosition factor base offset).2 := by
    exact le_of_lt refinedInside.2.2.1
  rcases shift with ⟨shiftX, shiftY⟩
  apply Prod.ext
  · simp only [Cell.add, Cell.scale]
    simp [Int.add_emod,
      Int.emod_eq_of_lt naturalNonnegativeX refinedInside.2.1]
  · simp only [Cell.add, Cell.scale]
    simp [Int.add_emod,
      Int.emod_eq_of_lt naturalNonnegativeY refinedInside.2.2.2]

end Cell
end LeanTrominoes
