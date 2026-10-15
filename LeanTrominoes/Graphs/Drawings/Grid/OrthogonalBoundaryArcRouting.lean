/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple
import LeanTrominoes.Graphs.Drawings.Orthogonal.Orthogonal.PeriodicOrthocrossingOrthogonal
import LeanTrominoes.Common.Geometry.GridSegmentRealAxisBox

/-! # Inward rectangular arcs between boundary ports

The sides run clockwise from the lower left: left, top, right, bottom.
Ports stay away from corners. An arc follows an inner rectangle, with
normal segments connecting its endpoints to their boundary ports.
-/
namespace LeanTrominoes.OrthogonalBoundaryRouting
open PeriodicOrthocrossing

structure Port where
  side : Fin 4
  coordinate : Int
  deriving DecidableEq

def Port.point (width height : Int) (port : Port) : Cell :=
  match port.side.val with
  | 0 => (0,port.coordinate)
  | 1 => (port.coordinate,height)
  | 2 => (width,port.coordinate)
  | _ => (port.coordinate,0)

def Port.innerPoint (width height depth : Int) (port : Port) : Cell :=
  match port.side.val with
  | 0 => (depth,port.coordinate)
  | 1 => (port.coordinate,height-depth)
  | 2 => (width-depth,port.coordinate)
  | _ => (port.coordinate,depth)

def Port.Before (first second : Port) : Prop :=
  first.side.val < second.side.val ∨
    (first.side = second.side ∧
      if first.side.val < 2 then first.coordinate < second.coordinate
      else second.coordinate < first.coordinate)

def Port.Inside (width height margin : Int) (port : Port) : Prop :=
  margin < port.coordinate ∧ port.coordinate <
    (if port.side.val = 0 ∨ port.side.val = 2 then height else width)-margin

def corner (width height depth : Int) (side : Nat) : Cell :=
  match side with
  | 0 => (depth,height-depth)
  | 1 => (width-depth,height-depth)
  | 2 => (width-depth,depth)
  | _ => (depth,depth)

def innerArc (width height depth : Int) (first second : Port) : List Cell :=
  let start := first.innerPoint width height depth
  let finish := second.innerPoint width height depth
  match first.side.val,second.side.val with
  | 0,1 => [start,corner width height depth 0,finish]
  | 0,2 => [start,corner width height depth 0,corner width height depth 1,finish]
  | 0,3 => [start,corner width height depth 0,corner width height depth 1,corner width height depth 2,finish]
  | 1,2 => [start,corner width height depth 1,finish]
  | 1,3 => [start,corner width height depth 1,corner width height depth 2,finish]
  | 2,3 => [start,corner width height depth 2,finish]
  | _,_ => [start,finish]

def route (width height depth : Int) (first second : Port) : List Cell :=
  [first.point width height] ++ innerArc width height depth first second ++
    [second.point width height]

theorem route_head (width height depth : Int) (first second : Port) :
    (route width height depth first second).head? = some (first.point width height) := by
  simp [route]

theorem route_last (width height depth : Int) (first second : Port) :
    (route width height depth first second).getLast? = some (second.point width height) := by
  unfold route
  rw [List.getLast?_append_cons]
  rfl

set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

theorem route_orthogonal {width height depth margin : Int} {first second : Port}
    (positive : 0 < depth) (depthBound : depth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    (ordered : first.Before second) : OrthogonalPolyline (route width height depth first second) := by
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  fin_cases firstSide <;> fin_cases secondSide <;>
    simp [Port.Before,Port.Inside] at ordered firstInside secondInside <;>
    simp [route,innerArc,corner,Port.point,Port.innerPoint,OrthogonalPolyline,
      gridPolylineSegments,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,GridSegment.IsVertical] <;>
    omega

theorem route_isRealOpenSimple {width height depth margin : Int} {first second : Port}
    (positive : 0 < depth) (depthBound : depth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (secondInside : second.Inside width height margin)
    (ordered : first.Before second) : GridPolyline.IsRealOpenSimple (route width height depth first second) := by
  apply GridPolyline.isRealOpenSimple_of_box_certificate
  obtain ⟨firstSide,firstCoordinate⟩ := first
  obtain ⟨secondSide,secondCoordinate⟩ := second
  fin_cases firstSide <;> fin_cases secondSide <;>
    simp [Port.Before,Port.Inside] at ordered firstInside secondInside <;>
    simp [route,innerArc,corner,Port.point,Port.innerPoint,GridPolyline.SimpleBoxCertificate,
      gridPolylineSegments,GridSegment.BoxIntersectionIsPoint] <;>
    omega

end LeanTrominoes.OrthogonalBoundaryRouting
