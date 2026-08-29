/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
import LeanTrominoes.OrthogonalPolylineLinearSeparation
import LeanTrominoes.OrthogonalPolylineLoopErasureRightLocalization

/-! # Duplicate-free routes from strictly monotone direction words -/

namespace LeanTrominoes

namespace Gadget

/-- Along a rebuilt direction stream whose steps are nonpositive in one
linear functional, no route point exceeds the initial point. -/
theorem rebuildRoute_linear_le_start
    (normal start : Cell) (directions : List AxisDirection)
    (nonpositive :
      ∀ direction ∈ directions,
        Cell.linearValue normal direction.step ≤ 0) :
    ∀ point ∈ rebuildRoute start directions,
      Cell.linearValue normal point ≤
        Cell.linearValue normal start := by
  induction directions generalizing start with
  | nil =>
      simp [rebuildRoute]
  | cons direction directions induction =>
      intro point pointMember
      rw [rebuildRoute] at pointMember
      rcases List.mem_cons.mp pointMember with rfl | pointMember
      · exact le_rfl
      · have tailBound :=
          induction
            (Cell.add start direction.step)
            (fun tailDirection tailMember =>
              nonpositive tailDirection
                (List.mem_cons_of_mem direction tailMember))
            point pointMember
        exact tailBound.trans (by
          calc
            Cell.linearValue normal
                  (Cell.add start direction.step) =
                Cell.linearValue normal start +
                  Cell.linearValue normal direction.step := by
              simp [Cell.linearValue, Cell.add]
              ring
            _ ≤ Cell.linearValue normal start :=
              add_le_of_nonpos_right
                (nonpositive direction (by simp)))

/-- If every direction strictly decreases one linear functional, rebuilding
the direction stream cannot revisit a lattice point. -/
theorem rebuildRoute_nodup_of_linear_negative
    (normal start : Cell) (directions : List AxisDirection)
    (negative :
      ∀ direction ∈ directions,
        Cell.linearValue normal direction.step < 0) :
    (rebuildRoute start directions).Nodup := by
  induction directions generalizing start with
  | nil => simp [rebuildRoute]
  | cons direction directions induction =>
      rw [rebuildRoute, List.nodup_cons]
      constructor
      · intro startMember
        have tailBound :=
          rebuildRoute_linear_le_start
            normal (Cell.add start direction.step) directions
            (fun tailDirection tailMember =>
              (negative tailDirection
                (List.mem_cons_of_mem direction tailMember)).le)
            start startMember
        have linearAdd :
            Cell.linearValue normal
                (Cell.add start direction.step) =
              Cell.linearValue normal start +
                Cell.linearValue normal direction.step := by
          simp [Cell.linearValue, Cell.add]
          ring
        rw [linearAdd] at tailBound
        have firstNegative := negative direction (by simp)
        omega
      · exact induction
          (Cell.add start direction.step)
          (fun tailDirection tailMember =>
            negative tailDirection
              (List.mem_cons_of_mem direction tailMember))

/-- If every direction is tangent to a linear functional, that functional
is constant at every point of the rebuilt route. -/
theorem rebuildRoute_linear_eq_start
    (normal start : Cell) (directions : List AxisDirection)
    (zero :
      ∀ direction ∈ directions,
        Cell.linearValue normal direction.step = 0) :
    ∀ point ∈ rebuildRoute start directions,
      Cell.linearValue normal point =
        Cell.linearValue normal start := by
  induction directions generalizing start with
  | nil => simp [rebuildRoute]
  | cons direction directions induction =>
      intro point pointMember
      rw [rebuildRoute] at pointMember
      rcases List.mem_cons.mp pointMember with rfl | pointMember
      · rfl
      · calc
          Cell.linearValue normal point =
              Cell.linearValue normal
                (Cell.add start direction.step) :=
            induction
              (Cell.add start direction.step)
              (fun tailDirection tailMember =>
                zero tailDirection
                  (List.mem_cons_of_mem direction tailMember))
              point pointMember
          _ = Cell.linearValue normal start := by
            have directionZero := zero direction (by simp)
            simp [Cell.linearValue, Cell.add] at directionZero ⊢
            ring_nf at directionZero ⊢
            omega

/-- If every direction is weakly decreasing and the first is strictly
decreasing, every point after the head is strictly below the head. -/
theorem rebuildRoute_tail_linear_lt_start
    (normal start : Cell) (directions : List AxisDirection)
    (nonpositive :
      ∀ direction ∈ directions,
        Cell.linearValue normal direction.step ≤ 0)
    (firstNegative :
      ∀ direction,
        directions.head? = some direction →
          Cell.linearValue normal direction.step < 0) :
    ∀ point ∈ (rebuildRoute start directions).tail,
      Cell.linearValue normal point <
        Cell.linearValue normal start := by
  cases directions with
  | nil => simp [rebuildRoute]
  | cons direction directions =>
      intro point pointMember
      have tailBound :=
        rebuildRoute_linear_le_start
          normal (Cell.add start direction.step) directions
          (fun tailDirection tailMember =>
            nonpositive tailDirection
              (List.mem_cons_of_mem direction tailMember))
          point (by simpa [rebuildRoute] using pointMember)
      have directionNegative :=
        firstNegative direction (by simp)
      have linearAdd :
          Cell.linearValue normal
              (Cell.add start direction.step) =
            Cell.linearValue normal start +
              Cell.linearValue normal direction.step := by
        simp [Cell.linearValue, Cell.add]
        ring
      rw [linearAdd] at tailBound
      omega

end Gadget

namespace AxisDirection

open PeriodicOrthocrossing

/-- Ordered unit subdivision is the route rebuilt from its original head
and its complete unit-direction word. -/
theorem unitSubdividePolyline_eq_rebuildRoute
    (start : Cell) (rest : List Cell)
    (orthogonal : OrthogonalPolyline (start :: rest)) :
    unitSubdividePolyline (start :: rest) =
      Gadget.rebuildRoute start
        (Gadget.unitSubdivisionDirections (start :: rest)) := by
  have subdividedHead :
      (unitSubdividePolyline (start :: rest)).head? = some start := by
    rw [unitSubdividePolyline_head? (by simp)]
    rfl
  generalize subdivisionEq :
    unitSubdividePolyline (start :: rest) = subdivided
  cases subdivided with
  | nil => simp [subdivisionEq] at subdividedHead
  | cons first tail =>
      have firstEq : first = start := by
        simpa [subdivisionEq] using subdividedHead
      subst first
      have unitSteps :
          (start :: tail).IsChain IsUnitAxisStep := by
        rw [← subdivisionEq]
        exact unitSubdividePolyline_unitSteps orthogonal
      have directionEq :
          Gadget.routeStepDirections (start :: tail) =
            Gadget.unitSubdivisionDirections (start :: rest) := by
        rw [←
          Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
            (start :: tail) unitSteps,
          ← subdivisionEq]
        exact
          Gadget.unitSubdivisionDirections_unitSubdividePolyline
            (start :: rest) orthogonal
      rw [← Gadget.rebuildRoute_routeStepDirections start tail unitSteps,
        directionEq]

/-- A nonempty orthogonal polyline has duplicate-free ordered unit
subdivision whenever one linear functional strictly decreases along every
direction in its unit-direction word. -/
theorem unitSubdividePolyline_nodup_of_direction_linear_negative
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal : OrthogonalPolyline points)
    (normal : Cell)
    (negative :
      ∀ direction ∈ Gadget.unitSubdivisionDirections points,
        Cell.linearValue normal direction.step < 0) :
    (unitSubdividePolyline points).Nodup := by
  obtain ⟨start, rest, pointsEq⟩ := List.exists_cons_of_ne_nil nonempty
  subst points
  have subdividedHead :
      (unitSubdividePolyline (start :: rest)).head? = some start := by
    rw [unitSubdividePolyline_head? (by simp)]
    rfl
  generalize subdivisionEq :
    unitSubdividePolyline (start :: rest) = subdivided
  cases subdivided with
  | nil => simp [subdivisionEq] at subdividedHead
  | cons first tail =>
      have firstEq : first = start := by
        simpa [subdivisionEq] using subdividedHead
      subst first
      have unitSteps :
          (start :: tail).IsChain IsUnitAxisStep := by
        rw [← subdivisionEq]
        exact unitSubdividePolyline_unitSteps orthogonal
      have directionEq :
          Gadget.routeStepDirections (start :: tail) =
            Gadget.unitSubdivisionDirections (start :: rest) := by
        rw [←
          Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
            (start :: tail) unitSteps,
          ← subdivisionEq]
        exact
          Gadget.unitSubdivisionDirections_unitSubdividePolyline
            (start :: rest) orthogonal
      rw [←
        Gadget.rebuildRoute_routeStepDirections start tail unitSteps,
        directionEq]
      exact Gadget.rebuildRoute_nodup_of_linear_negative
        normal start _ negative

/-- If an orthogonal route's ordered unit subdivision is duplicate-free,
normalization preserves its complete unit-direction word. -/
theorem unitSubdivisionDirections_normalizeOrthogonalPolyline_of_nodup
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal : OrthogonalPolyline points)
    (nodup : (unitSubdividePolyline points).Nodup) :
    Gadget.unitSubdivisionDirections
        (normalizeOrthogonalPolyline points) =
      Gadget.unitSubdivisionDirections points := by
  rw [normalizeOrthogonalPolyline_eq_listLoopErase
      nonempty orthogonal,
    Computability.listLoopErase_eq_self_of_nodup nodup]
  exact Gadget.unitSubdivisionDirections_unitSubdividePolyline
    points orthogonal

/-- Duplicate-freeness of the subdivided endpoint join implies that its two
subdivided pieces meet only at the advertised boundary. -/
theorem unitSubdividePolyline_only_common_of_join_nodup
    {first second : List Cell}
    {boundary : Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary)
    (joinedNodup :
      (unitSubdividePolyline
        (joinAtEndpoint first second)).Nodup) :
    ∀ point,
      point ∈ unitSubdividePolyline first →
      point ∈ unitSubdividePolyline second →
      point = boundary := by
  have subdivisionEq :
      unitSubdividePolyline (joinAtEndpoint first second) =
        joinAtEndpoint
          (unitSubdividePolyline first)
          (unitSubdividePolyline second) :=
    unitSubdividePolyline_joinAtEndpoint
      firstNonempty firstLast secondHead
  have secondSubdividedHead :
      (unitSubdividePolyline second).head? = some boundary := by
    rw [unitSubdividePolyline_head? secondNonempty, secondHead]
  have disjointTail :
      List.Disjoint
        (unitSubdividePolyline first)
        (unitSubdividePolyline second).tail := by
    rw [subdivisionEq] at joinedNodup
    unfold joinAtEndpoint at joinedNodup
    rw [List.disjoint_left]
    intro point firstMember secondMember
    exact (List.nodup_append.mp joinedNodup).2.2
      point firstMember point secondMember rfl
  intro point firstMember secondMember
  cases secondEq : unitSubdividePolyline second with
  | nil => simp [secondEq] at secondSubdividedHead
  | cons head tail =>
      have headEq : head = boundary := by
        simpa [secondEq] using secondSubdividedHead
      rw [secondEq] at secondMember
      rcases List.mem_cons.mp secondMember with pointHead | pointTail
      · exact pointHead.trans headEq
      · exact (disjointTail firstMember (by
          simpa [secondEq] using pointTail)).elim

end AxisDirection
end LeanTrominoes
