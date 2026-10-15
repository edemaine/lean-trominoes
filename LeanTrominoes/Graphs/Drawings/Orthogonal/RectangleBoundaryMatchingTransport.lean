/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.RealRectangleBoundaryShiftedNoninterlacing
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryMatchingCorrect

/-! # Moving boundary ports in order preserves a noninterlacing matching -/
namespace LeanTrominoes.RectangleBoundaryMatchingTransport

abbrev RealPort := RealRectangleBoundary.Port
abbrev GridPort := OrthogonalBoundaryRouting.Port

theorem preserves_before {ports : Set RealPort} {mapPort : RealPort → GridPort}
    (sameSides : ∀ port ∈ ports, (mapPort port).side = port.side)
    (coordinateOrder : ∀ first ∈ ports, ∀ second ∈ ports, first.side = second.side →
      first.coordinate < second.coordinate → (mapPort first).coordinate < (mapPort second).coordinate)
    {first second : RealPort} (firstMember : first ∈ ports) (secondMember : second ∈ ports)
    (ordered : first.Before second) : (mapPort first).Before (mapPort second) := by
  simp only [RealRectangleBoundary.Port.Before,RealRectangleBoundary.Port.clockwiseCode,
    Prod.Lex.toLex_lt_toLex] at ordered
  unfold OrthogonalBoundaryRouting.Port.Before
  rw [sameSides first firstMember,sameSides second secondMember]
  rcases ordered with sideOrder | ⟨same,coordinateBefore⟩
  · exact Or.inl sideOrder
  · have sides : first.side = second.side := Fin.ext same
    refine Or.inr ⟨sides,?_⟩
    rw [← sides] at coordinateBefore
    by_cases forward : first.side.val < 2
    · simp only [if_pos forward] at coordinateBefore ⊢
      exact coordinateOrder first firstMember second secondMember sides coordinateBefore
    · simp only [if_neg forward] at coordinateBefore ⊢
      exact coordinateOrder second secondMember first firstMember sides.symm (by linarith)

theorem injective_on {ports : Set RealPort} {mapPort : RealPort → GridPort}
    (orderPreserved : ∀ first ∈ ports, ∀ second ∈ ports,
      first.Before second → (mapPort first).Before (mapPort second)) : Set.InjOn mapPort ports := by
  intro first firstMember second secondMember equal
  by_contra different
  have differentCodes : first.clockwiseCode ≠ second.clockwiseCode :=
    fun codeEqual => different (RealRectangleBoundary.Port.clockwiseCode_injective codeEqual)
  rcases lt_or_gt_of_ne differentCodes with ordered | ordered
  · exact OrthogonalBoundaryRouting.Port.before_ne
      (orderPreserved first firstMember second secondMember ordered) equal
  · exact OrthogonalBoundaryRouting.Port.before_ne
      (orderPreserved second secondMember first firstMember ordered) equal.symm

theorem preserves_noninterlacing {ports : Set RealPort} {mapPort : RealPort → GridPort}
    (orderPreserved : ∀ first ∈ ports, ∀ second ∈ ports,
      first.Before second → (mapPort first).Before (mapPort second))
    {a b c d : RealPort} (aMember : a ∈ ports) (bMember : b ∈ ports)
    (cMember : c ∈ ports) (dMember : d ∈ ports)
    (noninterlacing : RealRectangleBoundary.Noninterlacing a b c d) :
    OrthogonalBoundaryRouting.Noninterlacing (mapPort a,mapPort b) (mapPort c,mapPort d) := by
  rcases noninterlacing with separated | separated | nested | nested
  · exact Or.inl (orderPreserved b bMember c cMember separated)
  · exact Or.inr (Or.inl (orderPreserved d dMember a aMember separated))
  · exact Or.inr (Or.inr (Or.inl ⟨orderPreserved a aMember c cMember nested.1,
      orderPreserved d dMember b bMember nested.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨orderPreserved c cMember a aMember nested.1,
      orderPreserved b bMember d dMember nested.2⟩))

theorem routed_straight_chords_disjoint {ports : Set RealPort} {mapPort : RealPort → GridPort}
    (orderPreserved : ∀ first ∈ ports, ∀ second ∈ ports,
      first.Before second → (mapPort first).Before (mapPort second))
    {a b c d : RealPort} (aMember : a ∈ ports) (bMember : b ∈ ports)
    (cMember : c ∈ ports) (dMember : d ∈ ports)
    {origin : ℝ × ℝ} {oldWidth oldHeight : ℝ} {first second : GridSegment}
    (widthPositive : 0 < oldWidth) (heightPositive : 0 < oldHeight)
    (aInside : a.Inside oldWidth oldHeight) (bInside : b.Inside oldWidth oldHeight)
    (cInside : c.Inside oldWidth oldHeight) (dInside : d.Inside oldWidth oldHeight)
    (firstOrder : a.Before b) (secondOrder : c.Before d)
    (different : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d)
    (firstSides : a.side ≠ b.side) (secondSides : c.side ≠ d.side)
    (firstStart : first.RealContains (a.shiftedPoint origin oldWidth oldHeight))
    (firstEnd : first.RealContains (b.shiftedPoint origin oldWidth oldHeight))
    (secondStart : second.RealContains (c.shiftedPoint origin oldWidth oldHeight))
    (secondEnd : second.RealContains (d.shiftedPoint origin oldWidth oldHeight))
    (disjoint : ∀ point, first.RealInteriorContains point → second.RealInteriorContains point → False)
    {chords : Finset OrthogonalBoundaryRouting.Chord} {width height : Int}
    (firstMember : (mapPort a,mapPort b) ∈ chords) (secondMember : (mapPort c,mapPort d) ∈ chords)
    (room : 2*(chords.card : Int) < width ∧ 2*(chords.card : Int) < height)
    (newAInside : (mapPort a).Inside width height chords.card)
    (newBInside : (mapPort b).Inside width height chords.card)
    (newCInside : (mapPort c).Inside width height chords.card)
    (newDInside : (mapPort d).Inside width height chords.card)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (OrthogonalBoundaryRouting.matchingRoute chords width height (mapPort a,mapPort b)) point)
    (secondContains : GridPolyline.RealContains (OrthogonalBoundaryRouting.matchingRoute chords width height (mapPort c,mapPort d)) point) : False := by
  have noninterlacing := RealRectangleBoundary.shifted_noninterlacing_of_disjoint_interiors
    widthPositive heightPositive aInside bInside cInside dInside firstOrder secondOrder different
    firstSides secondSides firstStart firstEnd secondStart secondEnd disjoint
  have mappedNoninterlacing := preserves_noninterlacing orderPreserved aMember bMember cMember dMember noninterlacing
  have differentChords : (mapPort a,mapPort b) ≠ (mapPort c,mapPort d) := by
    intro equal
    exact different.1 (injective_on orderPreserved aMember cMember (congrArg Prod.fst equal))
  exact OrthogonalBoundaryRouting.matchingRoutes_disjoint firstMember secondMember differentChords room
    newAInside newBInside newCInside newDInside (orderPreserved a aMember b bMember firstOrder)
    (orderPreserved c cMember d dMember secondOrder) mappedNoninterlacing firstContains secondContains

end LeanTrominoes.RectangleBoundaryMatchingTransport
