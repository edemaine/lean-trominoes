/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GraphAbstractBridge

/-! # Shared explicit drawing geometry and exact flat input fields -/
namespace LeanTrominoes.GraphDrawingAbstractBridge
namespace Data
open GraphAbstractBridge.Data
abbrev IndexedSegment := ℕ × ℕ × Segment
abbrev IndexedPoint := ℕ × ℕ × ℕ × Cell

def indexedSegments (d : Drawing) : List IndexedSegment :=
  d.edgeRoutes.zipIdx.flatMap fun route => (segments route.1).zipIdx.map fun s => (route.2,s.2,s.1)
def indexedPoints (d : Drawing) : List IndexedPoint :=
  d.edgeRoutes.zipIdx.flatMap fun route => route.1.zipIdx.map fun p => (route.2,p.2,route.1.length,p.1)
def drawingTranslation (d : Drawing) (z : Cell) : Cell := ((d.gridSize : ℤ)*z.1,(d.gridSize : ℤ)*z.2)
def translateSegment (s : Segment) (z : Cell) : Segment :=
  ((z.1+s.1.1,z.2+s.1.2),(z.1+s.2.1,z.2+s.2.2))
def between (a b x : ℤ) : Prop := (a≤x ∧ x≤b) ∨ (b≤x ∧ x≤a)
def strictlyBetween (a b x : ℤ) : Prop := (a<x ∧ x<b) ∨ (b<x ∧ x<a)
def gridContains (s : Segment) (p : Cell) : Prop :=
  (Horizontal s ∧ p.2=s.1.2 ∧ between s.1.1 s.2.1 p.1) ∨
  (Vertical s ∧ p.1=s.1.1 ∧ between s.1.2 s.2.2 p.2)
def gridInterior (s : Segment) (p : Cell) : Prop :=
  (Horizontal s ∧ p.2=s.1.2 ∧ strictlyBetween s.1.1 s.2.1 p.1) ∨
  (Vertical s ∧ p.1=s.1.1 ∧ strictlyBetween s.1.2 s.2.2 p.2)
def intervalsOverlap (a b c e : ℤ) : Prop := min a b<max c e ∧ min c e<max a b
def segmentInteriorsMeet (a b : Segment) : Prop :=
  (Horizontal a ∧ Horizontal b ∧ a.1.2=b.1.2 ∧ intervalsOverlap a.1.1 a.2.1 b.1.1 b.2.1) ∨
  (Vertical a ∧ Vertical b ∧ a.1.1=b.1.1 ∧ intervalsOverlap a.1.2 a.2.2 b.1.2 b.2.2) ∨
  (Horizontal a ∧ Vertical b ∧ strictlyBetween a.1.1 a.2.1 b.1.1 ∧ strictlyBetween b.1.2 b.2.2 a.1.2) ∨
  (Vertical a ∧ Horizontal b ∧ strictlyBetween b.1.1 b.2.1 a.1.1 ∧ strictlyBetween a.1.2 a.2.2 b.1.2)
def segmentKey (s : IndexedSegment) (z : Cell) := (s.1,s.2.1,z)
def pointKey (p : IndexedPoint) (z : Cell) := (p.1,p.2.1,z)
def pointEndpoint (p : IndexedPoint) : Prop := p.2.1=0 ∨ p.2.1+1=p.2.2.1

def DrawingContinuous (d : Drawing) : Prop :=
  (∀ a∈indexedSegments d, ∀ b∈indexedSegments d, ∀ z w p,
    segmentKey a z≠segmentKey b w → gridInterior (translateSegment a.2.2 (drawingTranslation d z)) p →
    ¬gridContains (translateSegment b.2.2 (drawingTranslation d w)) p) ∧
  (∀ v∈d.vertexPositions, ∀ a∈indexedSegments d, ∀ z w,
    ¬gridInterior (translateSegment a.2.2 (drawingTranslation d w))
      (v.1+(drawingTranslation d z).1,v.2+(drawingTranslation d z).2)) ∧
  ∀ a∈indexedSegments d, ∀ b∈indexedSegments d, ∀ z w,
    segmentKey a z≠segmentKey b w →
    ¬segmentInteriorsMeet (translateSegment a.2.2 (drawingTranslation d z)) (translateSegment b.2.2 (drawingTranslation d w))

def DrawingEndpointContacts (d : Drawing) : Prop :=
  ∀ a∈indexedPoints d, ∀ b∈indexedPoints d, ∀ z w, pointKey a z≠pointKey b w →
    (a.2.2.2.1+(drawingTranslation d z).1,a.2.2.2.2+(drawingTranslation d z).2)=
      (b.2.2.2.1+(drawingTranslation d w).1,b.2.2.2.2+(drawingTranslation d w).2) → pointEndpoint a ∧ pointEndpoint b

def DrawingGeometry (d : Drawing) : Prop := Orthogonal d ∧ DrawingContinuous d ∧ DrawingEndpointContacts d

def DrawingHalo (d : Drawing) : Prop :=
  ∀ a∈indexedSegments d, ∀ p∈[a.2.2.1,a.2.2.2],
    -(d.gridSize : ℤ)<p.1 ∧ p.1<2*(d.gridSize : ℤ) ∧ -(d.gridSize : ℤ)<p.2 ∧ p.2<2*(d.gridSize : ℤ)

def drawingRadius (d : Drawing) : ℕ :=
  ((d.vertexPositions++(indexedSegments d).flatMap (fun s => [s.2.2.1,s.2.2.2])).map
    (fun p => p.1.natAbs+p.2.natAbs)).sum

def drawingPointFields (p : Cell) : List ℕ := [Encodable.encode p.1,Encodable.encode p.2]
def drawingSegmentFields (s : IndexedSegment) : List ℕ :=
  [s.1,s.2.1,Encodable.encode s.2.2.1.1,Encodable.encode s.2.2.1.2,
    Encodable.encode s.2.2.2.1,Encodable.encode s.2.2.2.2]
def drawingFields (d : Drawing) : List ℕ :=
  [d.gridSize,drawingRadius d,(indexedSegments d).length,d.vertexPositions.length]++
    (indexedSegments d).flatMap drawingSegmentFields++d.vertexPositions.flatMap drawingPointFields++
    d.edgeRoutes.length::d.edgeRoutes.flatMap (fun route => route.length::route.flatMap drawingPointFields)
end Data
open Data GraphAbstractBridge.Data
abbrev drawing := GraphAbstractBridge.Correspondence.drawing
private def segment (s : Data.IndexedSegment) : IndexedGridSegment := ⟨s.1,s.2.1,⟨s.2.2.1,s.2.2.2⟩⟩
private def point (p : Data.IndexedPoint) : IndexedRoutePoint := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩

theorem indexedSegments_eq (d : Drawing) : (drawing d).indexedSegments=(Data.indexedSegments d).map segment := by
  simp [PeriodicGridDrawing.indexedSegments,Data.indexedSegments,GraphAbstractBridge.Correspondence.drawing_routes,
    GraphAbstractBridge.Correspondence.segments,List.zipIdx_map,List.map_flatMap,List.map_map,Function.comp_def,segment]
  rfl

theorem indexedPoints_eq (d : Drawing) : (drawing d).indexedRoutePoints=(Data.indexedPoints d).map point := by
  simp [PeriodicGridDrawing.indexedRoutePoints,Data.indexedPoints,List.map_flatMap,List.map_map,Function.comp_def,point]
  rfl

theorem continuous_iff (d : Drawing) : Data.DrawingContinuous d ↔ (drawing d).IsContinuouslyPlanar := by
  simp only [Data.DrawingContinuous,PeriodicGridDrawing.IsContinuouslyPlanar,PeriodicGridDrawing.IsPlanar,
    PeriodicGridDrawing.RoutesAvoidInteriors,PeriodicGridDrawing.VerticesAvoidRouteInteriors,
    PeriodicGridDrawing.RoutesHaveDisjointInteriors,indexedSegments_eq,List.forall_mem_map,
    GraphAbstractBridge.Correspondence.drawing_positions]
  constructor
  · rintro ⟨a,b,c⟩
    exact ⟨⟨a,b⟩,c⟩
  · rintro ⟨⟨a,b⟩,c⟩
    exact ⟨a,b,c⟩

theorem contacts_iff (d : Drawing) : Data.DrawingEndpointContacts d ↔ (drawing d).RoutePointsMeetOnlyAtEndpoints := by
  simp only [Data.DrawingEndpointContacts,PeriodicGridDrawing.RoutePointsMeetOnlyAtEndpoints,
    indexedPoints_eq,List.forall_mem_map,point,PeriodicGridDrawing.RoutePointOccurrenceKey,
    Data.pointKey,Data.pointEndpoint,IndexedRoutePoint.IsEndpoint,Data.drawingTranslation,
    Cell.add,PeriodicGridDrawing.periodTranslation,Cell.scale,GraphAbstractBridge.Correspondence.drawing_period]

theorem geometry_iff (d : Drawing) : Data.DrawingGeometry d ↔
    (drawing d).IsOrthogonal ∧ (drawing d).IsContinuouslyPlanar ∧ (drawing d).RoutePointsMeetOnlyAtEndpoints :=
  and_congr (GraphAbstractBridge.Correspondence.orthogonal d).symm (and_congr (continuous_iff d) (contacts_iff d))

theorem halo_iff (d : Drawing) : Data.DrawingHalo d ↔ (drawing d).SegmentEndpointsInExpandedSquare := by
  simp only [Data.DrawingHalo,PeriodicGridDrawing.SegmentEndpointsInExpandedSquare,
    indexedSegments_eq,List.forall_mem_map,segment,PeriodicGridDrawing.PositionInExpandedSquare,
    GraphAbstractBridge.Correspondence.drawing_period,List.forall_mem_cons,List.forall_mem_nil,and_true,and_assoc]
  simp

theorem drawingFields_eq (d : Drawing) : Data.drawingFields d=PeriodicGridDrawing.Arithmetic.fields (drawing d) := by
  simp only [Data.drawingFields,PeriodicGridDrawing.Arithmetic.fields,indexedSegments_eq,List.length_map,
    GraphAbstractBridge.Correspondence.drawing_period,GraphAbstractBridge.Correspondence.drawing_positions,
    GraphAbstractBridge.Correspondence.drawing_routes,PeriodicGridDrawing.FiniteBounds.radius,
    PeriodicGridDrawing.FiniteBounds.points,Data.drawingRadius,PeriodicGridDrawing.Arithmetic.segmentFields,
    Data.drawingSegmentFields,PeriodicGridDrawing.Arithmetic.pointFields,Data.drawingPointFields,
    PeriodicGridDrawing.Arithmetic.trailer,PeriodicGridDrawing.Arithmetic.routeFields,List.flatMap_map,
    List.map_map,Function.comp_def,segment]
  simp only [Data.drawingSegmentFields,Data.drawingPointFields,PeriodicGridDrawing.Arithmetic.pointFields,PeriodicGridDrawing.Arithmetic.routeFields,List.append_assoc]
  rfl

theorem drawing_equiv_computable : Computable drawing := PeriodicGridDrawing.equivData_symm_primrec.to_comp
 theorem drawing_equiv_symm_computable : Computable drawing.symm := PeriodicGridDrawing.equivData_primrec.to_comp


def relabel {A B : Type} (e : A≃B) (g : PeriodicGraph A) : PeriodicGraph B where
  vertices := g.vertices.map e
  edges := g.edges.map fun edge => ⟨e edge.source,e edge.target,edge.offset⟩

theorem idxOf_relabel {A B : Type} [DecidableEq A] [DecidableEq B] (e : A≃B) (xs : List A) (v : A) :
    (xs.map e).idxOf (e v)=xs.idxOf v := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    by_cases same : a=v
    · subst a; simp
    · have different : e a≠e v := fun h => same (e.injective h)
      simp [List.idxOf_cons,same,different,ih]

theorem vertexPosition_relabel {A B : Type} [DecidableEq A] [DecidableEq B]
    (e : A≃B) (g : PeriodicGraph A) (d : PeriodicGridDrawing) (v : A) :
    d.vertexPosition (relabel e g) (e v)=d.vertexPosition g v := by
  simp only [PeriodicGridDrawing.vertexPosition,relabel,idxOf_relabel]

private theorem mem_map_relabel {A B : Type} (e : A≃B) (xs : List A) (v : A) : e v∈xs.map e ↔ v∈xs := by
  constructor
  · intro member
    obtain ⟨a,ha,equal⟩ := List.mem_map.mp member
    have same := e.injective equal
    simpa only [same] using ha
  · exact fun member => List.mem_map.mpr ⟨v,member,rfl⟩

theorem wellFormed_relabel {A B : Type} [DecidableEq A] [DecidableEq B]
    (e : A≃B) (g : PeriodicGraph A) : (relabel e g).IsWellFormed ↔ g.IsWellFormed := by
  simp only [PeriodicGraph.IsWellFormed,relabel,List.forall_mem_map,mem_map_relabel]
  constructor
  · rintro ⟨nodup,edges⟩; exact ⟨List.Nodup.of_map e nodup,edges⟩
  · rintro ⟨nodup,edges⟩; exact ⟨nodup.map e.injective,edges⟩

theorem compatible_relabel {A B : Type} [DecidableEq A] [DecidableEq B]
    (e : A≃B) (g : PeriodicGraph A) (d : PeriodicGridDrawing) :
    d.IsCompatible (relabel e g) ↔ d.IsCompatible g := by
  simp only [PeriodicGridDrawing.IsCompatible,wellFormed_relabel]
  simp only [PeriodicGridDrawing.RoutesMatch,relabel,List.length_map,List.zipIdx_map,List.forall_mem_map,Prod.map,id_eq,PeriodicGridDrawing.vertexPosition,idxOf_relabel]

end LeanTrominoes.GraphDrawingAbstractBridge
