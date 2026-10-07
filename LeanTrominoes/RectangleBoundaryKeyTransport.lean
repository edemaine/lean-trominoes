/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RectangleBoundaryMatchingTransport

/-! # Boundary matching transport for combinatorial port keys

Keeping keys through the transport lets a finite router assemble ports
directly from edge occurrences and incidences.
-/
namespace LeanTrominoes.RectangleBoundaryMatchingTransport

theorem keys_preserve_before {Key : Type*} {valid : Key → Prop}
    {oldPort : Key → RealPort} {newPort : Key → GridPort}
    (sameSides : ∀ key, valid key → (newPort key).side = (oldPort key).side)
    (coordinateOrder : ∀ first, valid first → ∀ second, valid second →
      (oldPort first).side = (oldPort second).side → (oldPort first).coordinate < (oldPort second).coordinate →
      (newPort first).coordinate < (newPort second).coordinate)
    {first second : Key} (firstValid : valid first) (secondValid : valid second)
    (ordered : (oldPort first).Before (oldPort second)) : (newPort first).Before (newPort second) := by
  simp only [RealRectangleBoundary.Port.Before,RealRectangleBoundary.Port.clockwiseCode,
    Prod.Lex.toLex_lt_toLex] at ordered
  unfold OrthogonalBoundaryRouting.Port.Before
  rw [sameSides first firstValid,sameSides second secondValid]
  rcases ordered with sideOrder | ⟨same,coordinateBefore⟩
  · exact Or.inl sideOrder
  · have sides : (oldPort first).side = (oldPort second).side := Fin.ext same
    refine Or.inr ⟨sides,?_⟩
    rw [← sides] at coordinateBefore
    by_cases forward : (oldPort first).side.val < 2
    · simp only [if_pos forward] at coordinateBefore ⊢
      exact coordinateOrder first firstValid second secondValid sides coordinateBefore
    · simp only [if_neg forward] at coordinateBefore ⊢
      exact coordinateOrder second secondValid first firstValid sides.symm (by linarith)

theorem new_ports_ne_of_old_ports_ne {Key : Type*} {valid : Key → Prop}
    {oldPort : Key → RealPort} {newPort : Key → GridPort}
    (orderPreserved : ∀ first, valid first → ∀ second, valid second →
      (oldPort first).Before (oldPort second) → (newPort first).Before (newPort second))
    {first second : Key} (firstValid : valid first) (secondValid : valid second)
    (different : oldPort first ≠ oldPort second) : newPort first ≠ newPort second := by
  intro equal
  have differentCodes : (oldPort first).clockwiseCode ≠ (oldPort second).clockwiseCode :=
    fun codeEqual => different (RealRectangleBoundary.Port.clockwiseCode_injective codeEqual)
  rcases lt_or_gt_of_ne differentCodes with ordered | ordered
  · exact OrthogonalBoundaryRouting.Port.before_ne
      (orderPreserved first firstValid second secondValid ordered) equal
  · exact OrthogonalBoundaryRouting.Port.before_ne
      (orderPreserved second secondValid first firstValid ordered) equal.symm

theorem keys_preserve_noninterlacing {Key : Type*} {valid : Key → Prop}
    {oldPort : Key → RealPort} {newPort : Key → GridPort}
    (orderPreserved : ∀ first, valid first → ∀ second, valid second →
      (oldPort first).Before (oldPort second) → (newPort first).Before (newPort second))
    {a b c d : Key} (aValid : valid a) (bValid : valid b) (cValid : valid c) (dValid : valid d)
    (noninterlacing : RealRectangleBoundary.Noninterlacing (oldPort a) (oldPort b) (oldPort c) (oldPort d)) :
    OrthogonalBoundaryRouting.Noninterlacing (newPort a,newPort b) (newPort c,newPort d) := by
  rcases noninterlacing with separated | separated | nested | nested
  · exact Or.inl (orderPreserved b bValid c cValid separated)
  · exact Or.inr (Or.inl (orderPreserved d dValid a aValid separated))
  · exact Or.inr (Or.inr (Or.inl ⟨orderPreserved a aValid c cValid nested.1,
      orderPreserved d dValid b bValid nested.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨orderPreserved c cValid a aValid nested.1,
      orderPreserved b bValid d dValid nested.2⟩))

theorem keyed_straight_chords_disjoint {Key : Type*} {valid : Key → Prop}
    {oldPort : Key → RealPort} {newPort : Key → GridPort}
    (orderPreserved : ∀ first, valid first → ∀ second, valid second →
      (oldPort first).Before (oldPort second) → (newPort first).Before (newPort second))
    {a b c d : Key} (aValid : valid a) (bValid : valid b) (cValid : valid c) (dValid : valid d)
    {origin : ℝ × ℝ} {oldWidth oldHeight : ℝ} {first second : GridSegment}
    (widthPositive : 0 < oldWidth) (heightPositive : 0 < oldHeight)
    (aInside : (oldPort a).Inside oldWidth oldHeight) (bInside : (oldPort b).Inside oldWidth oldHeight)
    (cInside : (oldPort c).Inside oldWidth oldHeight) (dInside : (oldPort d).Inside oldWidth oldHeight)
    (firstOrder : (oldPort a).Before (oldPort b)) (secondOrder : (oldPort c).Before (oldPort d))
    (different : oldPort a ≠ oldPort c ∧ oldPort a ≠ oldPort d ∧ oldPort b ≠ oldPort c ∧ oldPort b ≠ oldPort d)
    (firstSides : (oldPort a).side ≠ (oldPort b).side) (secondSides : (oldPort c).side ≠ (oldPort d).side)
    (firstStart : first.RealContains ((oldPort a).shiftedPoint origin oldWidth oldHeight))
    (firstEnd : first.RealContains ((oldPort b).shiftedPoint origin oldWidth oldHeight))
    (secondStart : second.RealContains ((oldPort c).shiftedPoint origin oldWidth oldHeight))
    (secondEnd : second.RealContains ((oldPort d).shiftedPoint origin oldWidth oldHeight))
    (disjoint : ∀ point, first.RealInteriorContains point → second.RealInteriorContains point → False)
    {chords : Finset OrthogonalBoundaryRouting.Chord} {width height : Int}
    (firstMember : (newPort a,newPort b) ∈ chords) (secondMember : (newPort c,newPort d) ∈ chords)
    (room : 2*(chords.card : Int) < width ∧ 2*(chords.card : Int) < height)
    (newAInside : (newPort a).Inside width height chords.card) (newBInside : (newPort b).Inside width height chords.card)
    (newCInside : (newPort c).Inside width height chords.card) (newDInside : (newPort d).Inside width height chords.card)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (OrthogonalBoundaryRouting.matchingRoute chords width height (newPort a,newPort b)) point)
    (secondContains : GridPolyline.RealContains (OrthogonalBoundaryRouting.matchingRoute chords width height (newPort c,newPort d)) point) : False := by
  have noninterlacing := RealRectangleBoundary.shifted_noninterlacing_of_disjoint_interiors
    widthPositive heightPositive aInside bInside cInside dInside firstOrder secondOrder different
    firstSides secondSides firstStart firstEnd secondStart secondEnd disjoint
  have mapped := keys_preserve_noninterlacing orderPreserved aValid bValid cValid dValid noninterlacing
  have differentChords : (newPort a,newPort b) ≠ (newPort c,newPort d) := by
    intro equal
    exact new_ports_ne_of_old_ports_ne orderPreserved aValid cValid different.1 (congrArg Prod.fst equal)
  exact OrthogonalBoundaryRouting.matchingRoutes_disjoint firstMember secondMember differentChords room
    newAInside newBInside newCInside newDInside (orderPreserved a aValid b bValid firstOrder)
    (orderPreserved c cValid d dValid secondOrder) mapped firstContains secondContains

end LeanTrominoes.RectangleBoundaryMatchingTransport
