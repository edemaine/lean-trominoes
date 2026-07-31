import LeanTrominoes.RetainedRayRasterization
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Translation of retained-ray rasters and route contacts

Clause-level source escapes are certified once at the origin and then
translated to an arbitrary shared clause gate.  This file supplies the
structural translation lemmas for the two retained raster families,
endpoint joins, ordinary continuous route avoidance, and head-only contact.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

/-- Associativity of coordinatewise cell addition. -/
private theorem cell_add_assoc
    (first second third : Cell) :
    Cell.add first (Cell.add second third) =
      Cell.add (Cell.add first second) third := by
  apply Prod.ext <;>
    simp [Cell.add] <;>
    ring

/-- Translation distributes through an endpoint join. -/
theorem translatePolyline_joinAtEndpoint
    (offset : Cell) (first second : List Cell) :
    translatePolyline offset (joinAtEndpoint first second) =
      joinAtEndpoint
        (translatePolyline offset first)
        (translatePolyline offset second) := by
  simp [translatePolyline, joinAtEndpoint]

namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT

/-- A translated diagonal staircase is the same staircase based at the
translated start. -/
theorem diagonalStaircase_translatePolyline
    (horizontal vertical : Int)
    (length : Nat) (start offset : Cell) :
    translatePolyline offset
        (diagonalStaircase horizontal vertical length start) =
      diagonalStaircase horizontal vertical length
        (Cell.add offset start) := by
  induction length generalizing start with
  | zero =>
      simp [translatePolyline, diagonalStaircase]
  | succ length induction =>
      rw [diagonalStaircase, diagonalStaircase]
      simp only [translatePolyline, List.map_cons]
      have tailTranslated :=
        induction (Cell.add start (horizontal, vertical))
      unfold translatePolyline at tailTranslated
      rw [tailTranslated]
      simp only [cell_add_assoc]

/-- Translation commutes with all eight compass-ray rasters. -/
theorem compassRay_translatePolyline
    (port : Port) (length : Nat) (start offset : Cell) :
    translatePolyline offset (compassRay port length start) =
      compassRay port length (Cell.add offset start) := by
  cases length with
  | zero =>
      simp [translatePolyline, compassRay]
  | succ length =>
      cases port with
      | northwest =>
          exact diagonalStaircase_translatePolyline
            (-1) (-1) (length + 1) start offset
      | north =>
          simp [translatePolyline, compassRay, cell_add_assoc]
      | northeast =>
          exact diagonalStaircase_translatePolyline
            1 (-1) (length + 1) start offset
      | east =>
          simp [translatePolyline, compassRay, cell_add_assoc]
      | southeast =>
          exact diagonalStaircase_translatePolyline
            1 1 (length + 1) start offset
      | south =>
          simp [translatePolyline, compassRay, cell_add_assoc]
      | southwest =>
          exact diagonalStaircase_translatePolyline
            (-1) 1 (length + 1) start offset
      | west =>
          simp [translatePolyline, compassRay, cell_add_assoc]

/-- Translation commutes with one routed-clause primitive block. -/
theorem routedClauseRayBlock_translatePolyline
    (arm : DuplicatorArm) (start offset : Cell) :
    translatePolyline offset (routedClauseRayBlock arm start) =
      routedClauseRayBlock arm (Cell.add offset start) := by
  unfold translatePolyline routedClauseRayBlock
  rw [List.map_map]
  congr 1
  funext point
  exact cell_add_assoc offset start point

/-- Translation commutes with a repeated routed-clause staircase. -/
theorem routedClauseRay_translatePolyline
    (arm : DuplicatorArm) (length : Nat) (start offset : Cell) :
    translatePolyline offset (routedClauseRay arm length start) =
      routedClauseRay arm length (Cell.add offset start) := by
  induction length generalizing start with
  | zero =>
      simp [translatePolyline, routedClauseRay]
  | succ length induction =>
      simp only [routedClauseRay,
        translatePolyline_joinAtEndpoint,
        routedClauseRayBlock_translatePolyline,
        induction]
      rw [cell_add_assoc]

/-- Translation commutes with either retained-ray raster family. -/
theorem RetainedRay.rasterize_translatePolyline
    (ray : RetainedRay) (start offset : Cell) :
    translatePolyline offset (ray.rasterize start) =
      ray.rasterize (Cell.add offset start) := by
  cases ray with
  | compass port length =>
      exact compassRay_translatePolyline port length start offset
  | routedClause arm length =>
      exact routedClauseRay_translatePolyline arm length start offset

end PeriodicEightOccurrenceSplit

namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Common translation preserves ordinary continuous route avoidance. -/
theorem RoutesAvoidEachOther.translate
    {first second : List Cell}
    (avoids : RoutesAvoidEachOther first second)
    (offset : Cell) :
    RoutesAvoidEachOther
      (translatePolyline offset first)
      (translatePolyline offset second) := by
  simpa [translatePolyline] using
    routesAvoidEachOther_translate avoids offset

/-- Common translation preserves the fact that every listed contact is the
head of both routes. -/
theorem RoutesMeetOnlyAtHeads.translate
    {first second : List Cell}
    (contacts : RoutesMeetOnlyAtHeads first second)
    (offset : Cell) :
    RoutesMeetOnlyAtHeads
      (translatePolyline offset first)
      (translatePolyline offset second) := by
  intro firstPoint firstMember secondPoint secondMember equal
  rcases List.mem_map.mp firstMember with
    ⟨originalFirst, originalFirstMember, rfl⟩
  rcases List.mem_map.mp secondMember with
    ⟨originalSecond, originalSecondMember, rfl⟩
  have originalEqual :
      originalFirst = originalSecond :=
    cell_add_left_injective offset equal
  have heads :=
    contacts originalFirst originalFirstMember
      originalSecond originalSecondMember originalEqual
  constructor
  · simpa [translatePolyline, heads.1]
  · simpa [translatePolyline, heads.2]

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
