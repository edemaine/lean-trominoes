import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentLookup
import LeanTrominoes.PeriodicThreeDMVertexNormalizationDrawing

/-!
# Geometric meaning of normalized 3DM assignments

The rasterizer stores vertex centers followed by the internal points of every
normalized route.  This module exposes that underlying geometric point list
and proves that assignment locations are exactly its image on the final
torus.  It also characterizes equality after rasterization as equality of two
points up to a period translation.

These facts form the bridge from the normalized drawing's separation
certificates to `FinalAssignmentsCollisionFree`.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- The internal listed points of a route, excluding its first and last
points. -/
def routeInteriorPoints (route : List Cell) : List Cell :=
  route.tail.dropLast

/-- Forgetting the cell types emitted by the route rasterizer leaves exactly
the rasterized internal route points. -/
theorem routeInteriorAssignmentLocations
    (period : Nat) (color : WireColor) :
    ∀ route,
      (routeInteriorAssignments period color route).map Prod.fst =
        (routeInteriorPoints route).map (rasterLocation period)
  | [] => by simp [routeInteriorAssignments, routeInteriorPoints]
  | [_] => by simp [routeInteriorAssignments, routeInteriorPoints]
  | [_, _] => by simp [routeInteriorAssignments, routeInteriorPoints]
  | before :: current :: after :: rest => by
      simp only [routeInteriorAssignments, List.map_cons,
        routeInteriorPoints, List.tail_cons, List.dropLast_cons_cons]
      rw [routeInteriorAssignmentLocations period color
        (current :: after :: rest)]
      rfl

/-- Geometric points represented by the complete normalized assignment list,
in the same vertex-then-route order. -/
def PlanarPresentation.finalGeometricAssignmentPoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : List Cell :=
  presentation.finalNormalizedVertexPositions ++
    problem.contractedEdges.flatMap fun edge =>
      routeInteriorPoints (presentation.finalNormalizationRoute edge)

/-- Assignment locations are exactly the final geometric assignment points
reduced to the raster torus. -/
theorem PlanarPresentation.finalAssignmentLocations_eq_map
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalAssignmentLocations =
      presentation.finalGeometricAssignmentPoints.map
        (rasterLocation presentation.finalNormalizationPeriod) := by
  unfold PlanarPresentation.finalAssignmentLocations
    PlanarPresentation.finalCellAssignments
    PlanarPresentation.finalVertexAssignments
    PlanarPresentation.finalRouteAssignments
    PlanarPresentation.finalGeometricAssignmentPoints
  rw [presentation.finalNormalizedVertexPositions_eq_map]
  simp only [List.map_append, List.map_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro edge edgeMember
  exact routeInteriorAssignmentLocations _ _ _

/-- Two geometric points have the same raster location exactly when one is a
period translate of the other. -/
theorem rasterLocation_eq_iff_exists_periodTranslation
    (period : Nat) (first second : Cell) :
    rasterLocation period first = rasterLocation period second ↔
      ∃ translate : Cell,
        first = Cell.add second
          (Cell.scale (period : Int) translate) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  constructor
  · intro equal
    simp only [rasterLocation, Prod.mk.injEq] at equal
    have horizontalMod :
        firstX ≡ secondX [ZMOD (period : Int)] := equal.1
    have negVerticalMod :
        -firstY ≡ -secondY [ZMOD (period : Int)] := equal.2
    have verticalMod :
        firstY ≡ secondY [ZMOD (period : Int)] :=
      Int.neg_modEq_neg.mp negVerticalMod
    rcases Int.modEq_iff_add_fac.mp horizontalMod with
      ⟨horizontalTranslate, horizontalEqual⟩
    rcases Int.modEq_iff_add_fac.mp verticalMod with
      ⟨verticalTranslate, verticalEqual⟩
    refine ⟨(-horizontalTranslate, -verticalTranslate), ?_⟩
    simp only [Cell.add, Cell.scale, Prod.mk.injEq]
    constructor <;> nlinarith
  · rintro ⟨translate, equal⟩
    rw [equal]
    exact rasterLocation_add_period period (secondX, secondY) translate

/-- A finite geometric point list has neither literal duplicates nor distinct
points that become equal after translating by whole periods. -/
def PointsSeparatedModuloPeriod
    (period : Nat) (points : List Cell) : Prop :=
  points.Nodup ∧
    ∀ first ∈ points, ∀ second ∈ points,
      first ≠ second →
        ∀ translate : Cell,
          first ≠ Cell.add second
            (Cell.scale (period : Int) translate)

/-- Periodic geometric separation makes rasterization injective on a finite
point list. -/
theorem rasterLocations_nodup_of_pointsSeparatedModuloPeriod
    {period : Nat} {points : List Cell}
    (separated : PointsSeparatedModuloPeriod period points) :
    (points.map (rasterLocation period)).Nodup := by
  apply List.Nodup.map_on
  · intro first firstMember second secondMember equal
    by_contra different
    rcases
        (rasterLocation_eq_iff_exists_periodTranslation
          period first second).mp equal with
      ⟨translate, translatedEqual⟩
    exact separated.2 first firstMember second secondMember
      different translate translatedEqual
  · exact separated.1

/-- The remaining collision-freedom goal can be discharged entirely in the
geometric model, before any cell types are considered. -/
theorem PlanarPresentation.finalAssignmentsCollisionFree_of_pointsSeparated
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated : PointsSeparatedModuloPeriod
      presentation.finalNormalizationPeriod
      presentation.finalGeometricAssignmentPoints) :
    presentation.FinalAssignmentsCollisionFree := by
  unfold PlanarPresentation.FinalAssignmentsCollisionFree
  rw [presentation.finalAssignmentLocations_eq_map]
  exact rasterLocations_nodup_of_pointsSeparatedModuloPeriod separated

end PeriodicThreeDM
end LeanTrominoes
