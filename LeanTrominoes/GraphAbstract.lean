/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract
import LeanTrominoes.GraphAbstractBridge
import LeanTrominoes.GraphPlanarAbstractBridge
import LeanTrominoes.GraphOrientationAbstractBridge
import LeanTrominoes.GraphAlgorithmsAbstractBridge
import LeanTrominoes.GraphDrawingAbstractBridge
import LeanTrominoes.GraphThreeDMAbstractBridge
import LeanTrominoes.GraphTwoSATAbstractBridge
import LeanTrominoes.GraphConstraintsAbstractBridge

/-!
# Periodic graphs, constraints, and algorithms: a formal abstract

This file introduces the graph, drawing, and constraint notions needed for
Sections 2–4 of the paper and proves their main geometric, complexity, and
algorithmic results. Section comments separate the mathematical stories.
To review what is proved, read the definitions and theorem statements here;
Lean checks the proofs through `GraphAbstractBridge` and the development.

Finite input records are described by their fields below. Lists retain edge
and literal occurrences: parallel edges are distinct and loops have two ends.
The canonical complexity definitions are shared with `TilingAbstract`:
`LeanWang.CoREComplete` means that no-instances can be recognized by a possibly
nonterminating algorithm and every such problem reduces by a total computable
answer-preserving map. `ComplexityAbstract.PSPACEComplete` and `NPComplete` mean
membership and hardness under polynomial-time many-one reductions. PSPACE
uses always-halting finite-alphabet Turing machines with polynomial space;
NP uses polynomial-length binary witnesses checked by polynomial-time
finite-alphabet machines. Each bounded-complexity theorem names its encoding.
The algorithm theorems below use the bounded-word RAM defined in
`ComplexityAbstract`: Horn satisfiability has a linear instruction bound,
local 2SAT has a polynomial bound in each fixed dimension, and quotient
matching has a conservative quartic bound. These bounds include input
processing, allocation, and halt and hold for every larger allowed word width.
-/

namespace LeanTrominoes.GraphAbstract

/-! ## Periodic graphs in arbitrary dimension -/

/-- A lattice vector has d integer coordinates. A protoedge records its source,
target, and translation offset: its copy at z joins (source,z) to
(target,z+offset). Graphs retain lists of vertices and edge occurrences,
including isolated vertices, parallel edges, and both ends of loops. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Edge (V : Type) (d : ℕ) := V × V × Lattice d
abbrev Graph (V : Type) (d : ℕ) := List V × List (Edge V d)
def Edge.source {V : Type} {d : ℕ} (e : Edge V d) : V := e.1
def Edge.target {V : Type} {d : ℕ} (e : Edge V d) : V := e.2.1
def Edge.offset {V : Type} {d : ℕ} (e : Edge V d) : Lattice d := e.2.2
def Graph.vertices {V : Type} {d : ℕ} (g : Graph V d) : List V := g.1
def Graph.edges {V : Type} {d : ℕ} (g : Graph V d) : List (Edge V d) := g.2

def Adjacent {V : Type} {d : ℕ} (es : List (Edge V d))
    (u v : V × Lattice d) : Prop :=
  ∃ e ∈ es,
    (e.source = u.1 ∧ e.target = v.1 ∧ v.2 = u.2+e.offset) ∨
    (e.source = v.1 ∧ e.target = u.1 ∧ u.2 = v.2+e.offset)

/-- Well-formed graphs list distinct vertices and only listed edge endpoints.
Degree counts edge ends, twice for a loop. -/
def WellFormed {V : Type} {d : ℕ} (g : Graph V d) : Prop :=
  g.vertices.Nodup ∧ ∀ e ∈ g.edges, e.source ∈ g.vertices ∧ e.target ∈ g.vertices
def DegreeAtMost {V : Type} [DecidableEq V] {d : ℕ} (k : ℕ) (g : Graph V d) : Prop :=
  ∀ v, (g.edges.flatMap fun e => [e.source,e.target]).count v ≤ k

/-- Locality in the paper means L₁ offset length at most one, in every
dimension. Coordinate locality bounds each coordinate separately and also
allows diagonal offsets; it is a weaker hypothesis. -/
def Local {V : Type} {d : ℕ} (es : List (Edge V d)) : Prop :=
  ∀ e ∈ es, ∑ i, (e.offset i).natAbs ≤ 1
def CoordinateLocal {V : Type} {d : ℕ} (es : List (Edge V d)) : Prop :=
  ∀ e ∈ es, ∀ i, (e.offset i).natAbs ≤ 1

/-- Connectivity and proper two-colorings concern the entire infinite lift.
The vertex type supplies the protovertices, including isolated vertices. -/
def Connected {V : Type} {d : ℕ} (es : List (Edge V d)) : Prop :=
  ∀ u v, Relation.ReflTransGen (Adjacent es) u v
def ProperColoring {V : Type} {d : ℕ} (es : List (Edge V d))
    (color : V × Lattice d → Bool) : Prop :=
  ∀ u v, Adjacent es u v → color u ≠ color v

/-- Paper-local graphs also satisfy coordinate locality. -/
theorem local_implies_coordinate_local {V : Type} {d : ℕ} (es : List (Edge V d))
    (h : Local es) : CoordinateLocal es :=
  GraphAbstractBridge.Data.local_implies_coordinate_local es h

/-! ## Polygonal drawings of two-dimensional periodic graphs -/

/-- Drawing coordinates are integer pairs. For a graph in dimension two,
its offset vector has horizontal coordinate `offset 0` and vertical coordinate
`offset 1`. Only drawing notions specialize the graph dimension to two. -/
abbrev Cell := ℤ × ℤ

/-- Polygonal routes are lists of integer points interpreted as closed real
segments. A simple route has nonzero pieces; consecutive pieces meet only at
their common endpoint. The first and last pieces may close a loop. -/
abbrev Segment := Cell × Cell
def segments (route : List Cell) : List Segment := route.zip route.tail
def realPoint (c : Cell) : ℝ × ℝ := (c.1,c.2)
def SegmentContains (s : Segment) (p : ℝ × ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p.1 = s.1.1+t*(s.2.1-s.1.1) ∧
    p.2 = s.1.2+t*(s.2.2-s.1.2)
def SegmentInterior (s : Segment) (p : ℝ × ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p.1 = s.1.1+t*(s.2.1-s.1.1) ∧
    p.2 = s.1.2+t*(s.2.2-s.1.2)
def RouteContains (route : List Cell) (p : ℝ × ℝ) : Prop :=
  ∃ s ∈ segments route, SegmentContains s p
def RouteEndpoint (route : List Cell) (p : ℝ × ℝ) : Prop :=
  (∃ c, route.head? = some c ∧ p = realPoint c) ∨
    ∃ c, route.getLast? = some c ∧ p = realPoint c
def SimpleRoute (route : List Cell) : Prop :=
  2 ≤ route.length ∧ (∀ s ∈ segments route, s.1 ≠ s.2) ∧
    ∀ a ∈ (segments route).zipIdx, ∀ b ∈ (segments route).zipIdx,
      a.2 < b.2 → ∀ p : ℝ × ℝ, SegmentContains a.1 p → SegmentContains b.1 p →
        (a.2+1 = b.2 ∧ p = realPoint a.1.2) ∨
          (a.2 = 0 ∧ b.2+1 = (segments route).length ∧
            p = realPoint a.1.1 ∧ p = realPoint b.1.2)

def Horizontal (s : Segment) : Prop := s.1.2 = s.2.2 ∧ s.1.1 ≠ s.2.1
def Vertical (s : Segment) : Prop := s.1.1 = s.2.1 ∧ s.1.2 ≠ s.2.2

/-- A drawing stores M-1, vertex positions in vertex-list order, and routes
in edge-list order. Thus its square period M is positive by construction. -/
abbrev Drawing := ℕ × List Cell × List (List Cell)
def Drawing.gridSize (d : Drawing) : ℕ := d.1+1
def Drawing.vertexPositions (d : Drawing) : List Cell := d.2.1
def Drawing.edgeRoutes (d : Drawing) : List (List Cell) := d.2.2
def Drawing.edgeRoute (d : Drawing) (i : ℕ) : List Cell := d.edgeRoutes.getD i []
def Drawing.vertexPosition {V : Type} [DecidableEq V] (d : Drawing) (g : Graph V 2) (v : V) : Cell :=
  d.vertexPositions.getD (g.vertices.idxOf v) (0,0)
def scale (k : ℤ) (c : Cell) : Cell := (k*c.1,k*c.2)
def translatedRoute (d : Drawing) (i : ℕ) (z : Cell) : List Cell :=
  (d.edgeRoute i).map (fun c => ((d.gridSize : ℤ)*z.1+c.1, (d.gridSize : ℤ)*z.2+c.2))

/-- Compatibility matches the two finite lists, puts distinct vertex positions
strictly inside the fundamental square, and attaches each route to its source
and its offset-translated target. -/
def Compatible {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing) : Prop :=
  WellFormed g ∧ d.vertexPositions.length = g.vertices.length ∧
    d.edgeRoutes.length = g.edges.length ∧ d.vertexPositions.Nodup ∧
    (∀ p ∈ d.vertexPositions, 0 < p.1 ∧ p.1 < d.gridSize ∧ 0 < p.2 ∧ p.2 < d.gridSize) ∧
    ∀ e ∈ g.edges.zipIdx,
      (d.edgeRoute e.2).head? = some (d.vertexPosition g e.1.source) ∧
      (d.edgeRoute e.2).getLast? = some
        ((d.vertexPosition g e.1.target).1+(d.gridSize : ℤ)*(e.1.offset 0),
         (d.vertexPosition g e.1.target).2+(d.gridSize : ℤ)*(e.1.offset 1))

def VerticesAvoidRoutes (d : Drawing) : Prop :=
  ∀ v ∈ d.vertexPositions, ∀ (vertexCell edgeCell : Cell) i, i < d.edgeRoutes.length →
    RouteContains (translatedRoute d i edgeCell)
      (realPoint (v.1+(d.gridSize : ℤ)*vertexCell.1, v.2+(d.gridSize : ℤ)*vertexCell.2)) →
    RouteEndpoint (translatedRoute d i edgeCell)
      (realPoint (v.1+(d.gridSize : ℤ)*vertexCell.1, v.2+(d.gridSize : ℤ)*vertexCell.2))
def RoutesMeetAtEndpoints (d : Drawing) : Prop :=
  ∀ i j a b, i < d.edgeRoutes.length → j < d.edgeRoutes.length → (i,a) ≠ (j,b) →
    ∀ p : ℝ × ℝ, RouteContains (translatedRoute d i a) p →
      RouteContains (translatedRoute d j b) p →
        RouteEndpoint (translatedRoute d i a) p ∧ RouteEndpoint (translatedRoute d j b) p

def IsDrawing {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing) : Prop :=
  Compatible g d ∧ (∀ route ∈ d.edgeRoutes, SimpleRoute route) ∧ VerticesAvoidRoutes d
def PlanarDrawing {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing) : Prop :=
  IsDrawing g d ∧ RoutesMeetAtEndpoints d
def Planar {V : Type} [DecidableEq V] (g : Graph V 2) : Prop := ∃ d : Drawing, PlanarDrawing g d

/-- Orthogonal routes have nondegenerate horizontal or vertical pieces.
Orthocrossing drawings allow further contacts only at perpendicular segment
interiors. Local drawings stay in the two closed cells of each edge's ends. -/
def Orthogonal (d : Drawing) : Prop :=
  ∀ route ∈ d.edgeRoutes, ∀ s ∈ segments route, Horizontal s ∨ Vertical s

/-- The following finite lists retain segment and listed-point indices, so
geometrically coincident occurrences stay distinct. The certificate excludes
integer endpoint/interior contacts, real collinear interior overlap, and
unrelated bend contacts throughout the periodic lift. Orthogonality is
required. `DrawingHalo` bounds segment endpoints to the open one-cell halo. -/
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

def ProperCrossing (a b : Segment) (p : ℝ × ℝ) : Prop :=
  SegmentInterior a p ∧ SegmentInterior b p ∧
    ((Horizontal a ∧ Vertical b) ∨ (Vertical a ∧ Horizontal b))
def Orthocrossing (d : Drawing) : Prop :=
  ∀ i j a b, i < d.edgeRoutes.length → j < d.edgeRoutes.length → (i,a) ≠ (j,b) →
    ∀ p : ℝ × ℝ, RouteContains (translatedRoute d i a) p →
      RouteContains (translatedRoute d j b) p →
        (RouteEndpoint (translatedRoute d i a) p ∧ RouteEndpoint (translatedRoute d j b) p) ∨
        ∃ s ∈ segments (translatedRoute d i a), ∃ t ∈ segments (translatedRoute d j b),
          ProperCrossing s t p

def PointInCell (d : Drawing) (z : Cell) (p : ℝ × ℝ) : Prop :=
  (d.gridSize : ℝ)*z.1 ≤ p.1 ∧ p.1 ≤ (d.gridSize : ℝ)*(z.1+1) ∧
    (d.gridSize : ℝ)*z.2 ≤ p.2 ∧ p.2 ≤ (d.gridSize : ℝ)*(z.2+1)
def LocalDrawing {V : Type} (d : Drawing) (g : Graph V 2) : Prop :=
  ∀ e ∈ g.edges.zipIdx, ∀ p : ℝ × ℝ, RouteContains (d.edgeRoute e.2) p →
    PointInCell d (0,0) p ∨ PointInCell d (e.1.offset 0,e.1.offset 1) p

/-- A port identifies an indexed edge end: false is the source, true the target.
Degree-three vertices select one incident port. Directions are unit vectors;
(0,0) is the fallback for malformed or non-axis-aligned route ends. -/
abbrev Port (V : Type) := V × ℕ × Bool
def Port.vertex {V : Type} (p : Port V) : V := p.1
def Port.edgeIndex {V : Type} (p : Port V) : ℕ := p.2.1
def Port.isTarget {V : Type} (p : Port V) : Bool := p.2.2
def ports {V : Type} (g : Graph V 2) : List (Port V) :=
  g.edges.zipIdx.flatMap (fun e => [(e.1.source,e.2,false), (e.1.target,e.2,true)])
def portsAt {V : Type} [DecidableEq V] (g : Graph V 2) (v : V) : List (Port V) :=
  (ports g).filter (fun p => p.vertex = v)
def SelectedIncidences {V : Type} [DecidableEq V] (g : Graph V 2) (chosen : V → Port V) : Prop :=
  ∀ v ∈ g.vertices, (portsAt g v).length = 3 → chosen v ∈ portsAt g v

def direction (a b : Cell) : Cell :=
  if a.2 = b.2 then
    if a.1 < b.1 then (1,0) else if b.1 < a.1 then (-1,0) else (0,0)
  else if a.1 = b.1 then
    if a.2 < b.2 then (0,1) else if b.2 < a.2 then (0,-1) else (0,0)
  else (0,0)
def firstDirection : List Cell → Cell
  | a :: b :: _ => direction a b
  | _ => (0,0)
def portDirection {V : Type} (d : Drawing) (p : Port V) : Cell :=
  firstDirection (if p.isTarget then (d.edgeRoute p.edgeIndex).reverse else d.edgeRoute p.edgeIndex)
def IsNormalized {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing)
    (chosen : V → Port V) : Prop :=
  (∀ p ∈ ports g, (portsAt g p.vertex).length = 3 →
    portDirection d p ∈ [(-1,0),(0,1),(1,0)]) ∧
  ∀ v ∈ g.vertices, (portsAt g v).length = 3 → portDirection d (chosen v) = (-1,0)

/-- Theorem 2.1: every well-formed local periodic graph has a simple local
orthocrossing drawing on a linear-size grid, including loops and isolated
vertices. With degree at most four the drawing can also be orthogonal. -/
theorem orthocrossing_drawing {V : Type} [DecidableEq V] (g : Graph V 2)
    (valid : WellFormed g) (locality : Local g.edges) :
    ∃ d : Drawing, IsDrawing g d ∧ LocalDrawing d g ∧ Orthocrossing d ∧
      d.gridSize ≤ 16*(g.vertices.length+g.edges.length+1) :=
  GraphAbstractBridge.Data.orthocrossing_drawing g valid locality

theorem orthogonal_orthocrossing_drawing {V : Type} [DecidableEq V] (g : Graph V 2)
    (valid : WellFormed g) (locality : Local g.edges) (degree : DegreeAtMost 4 g) :
    ∃ d : Drawing, IsDrawing g d ∧ LocalDrawing d g ∧ Orthocrossing d ∧
      Orthogonal d ∧ d.gridSize ≤ 16*(g.vertices.length+g.edges.length+1) :=
  GraphAbstractBridge.Data.orthogonal_orthocrossing_drawing g valid locality degree

/-- Theorem 2.2: a planar local polygonal drawing of degree at most four has
a planar local orthogonal refinement of period at most 84480 M³. Original
vertices are scaled by exactly (16M+32)(160M+1600), with M the old period. -/
theorem orthogonal_refinement {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing)
    (planar : PlanarDrawing g d) (degree : DegreeAtMost 4 g)
    (locality : Local g.edges) (routes : LocalDrawing d g) :
    ∃ out : Drawing, PlanarDrawing g out ∧ LocalDrawing out g ∧ Orthogonal out ∧
      out.gridSize ≤ 84480*d.gridSize^3 ∧
      out.vertexPositions = d.vertexPositions.map
        (fun p => ((((16*d.gridSize+32)*(160*d.gridSize+1600) : ℕ) : ℤ)*p.1,
          (((16*d.gridSize+32)*(160*d.gridSize+1600) : ℕ) : ℤ)*p.2)) :=
  GraphAbstractBridge.Data.orthogonal_refinement g d planar degree locality routes

/-- Lemma 2.3: select one incidence at each degree-three vertex. Scaling the
drawing by 32 preserves planarity and orthogonality and makes the selected
incidence point west; the other two point north and east. Locality is preserved.
A `Port` identifies an edge end, distinguishing both ends of a loop. -/
theorem normalize_incidence_directions {V : Type} [DecidableEq V] (g : Graph V 2) (d : Drawing)
    (planar : PlanarDrawing g d) (orthogonal : Orthogonal d)
    (chosen : V → Port V) (selection : SelectedIncidences g chosen) :
    ∃ out : Drawing, PlanarDrawing g out ∧ Orthogonal out ∧
      IsNormalized g out chosen ∧ out.gridSize = 32*d.gridSize ∧
      out.vertexPositions = d.vertexPositions.map (scale 32) ∧
      (LocalDrawing d g → LocalDrawing out g) :=
  GraphAbstractBridge.Data.normalize_incidence_directions g d planar orthogonal chosen selection

/-! ## Boolean constraints and their complexity -/

/-- A literal has an `atom : ℕ`, an integer-pair `offset`, and a Boolean
`value`. A formula has a finite list `clauses` of lists of literals. Clauses
are imposed at every translate. Duplicate literals count as occurrences;
empty clauses are false. Formulas are two-dimensional unless restricted below. -/
abbrev Literal := ℕ × Cell × Bool
abbrev Formula := List (List Literal)
def Literal.atom (l : Literal) : ℕ := l.1
def Literal.offset (l : Literal) : Cell := l.2.1
def Literal.value (l : Literal) : Bool := l.2.2
def Formula.clauses (f : Formula) : List (List Literal) := f

def Satisfies (f : Formula) (a : ℕ → Cell → Bool) : Prop :=
  ∀ (z : Cell) c, c ∈ f.clauses → ∃ l ∈ c,
    a l.atom (z.1+l.offset.1, z.2+l.offset.2) = l.value
def Satisfiable (f : Formula) : Prop := ∃ a, Satisfies f a
def LocalFormula (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, ∀ r ∈ c,
    (l.offset.1-r.offset.1).natAbs + (l.offset.2-r.offset.2).natAbs ≤ 1
def WidthAtMost (k : ℕ) (f : Formula) : Prop := ∀ c ∈ f.clauses, c.length ≤ k
def OccurrencesAtMost (k : ℕ) (f : Formula) : Prop :=
  ∀ v, (f.clauses.flatMap fun c => c.map Literal.atom).count v ≤ k

/-- A zero-dimensional formula has no offsets, so translated cells are
independent copies of one finite SAT instance. -/
def ZeroDimensional (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.offset = (0,0)

/-- A one-dimensional formula has zero vertical offset in every literal. -/
def OneDimensional (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.offset.2 = 0

/-- A line-local clause uses offsets at horizontal distance at most one. -/
def LineLocal (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, ∀ r ∈ c, (l.offset.1-r.offset.1).natAbs ≤ 1

/-- Line satisfiability assigns a Boolean to every variable at every integer.
The flat binary encoding lists clause lengths and literal fields, including
signed coordinates; invalid locality and width restrictions are rejected. -/
def LineSAT (f : Formula) : Prop :=
  (∃ a : ℕ → ℤ → Bool, ∀ (z : ℤ) c, c ∈ f.clauses →
    ∃ l ∈ c, a l.atom (z+l.offset.1) = l.value) ∧ OneDimensional f ∧ LineLocal f

/-- Binary fields list the clause count, then each clause length and its
literal fields: atom, signed horizontal and vertical offsets, and value. -/
def literalFields (l : Literal) : List ℕ :=
  [l.atom,Encodable.encode l.offset.1,Encodable.encode l.offset.2,if l.value then 1 else 0]
def clauseFields (c : List Literal) : List ℕ := c.length :: c.flatMap literalFields
def formulaEncoding (f : Formula) : List ComplexityAbstract.Symbol :=
  ComplexityAbstract.binaryFields (f.clauses.length :: f.clauses.flatMap clauseFields)

/-- Theorems 3.2–3.4: local line SAT remains PSPACE-complete with width at
most three and with at most three occurrences of each variable. -/
theorem line_sat : ComplexityAbstract.PSPACEComplete formulaEncoding LineSAT :=
  GraphConstraintsAbstractBridge.line_sat
theorem line_three_sat : ComplexityAbstract.PSPACEComplete formulaEncoding
    (fun f => LineSAT f ∧ WidthAtMost 3 f) :=
  GraphConstraintsAbstractBridge.line_three_sat
theorem line_three_sat_three : ComplexityAbstract.PSPACEComplete formulaEncoding
    (fun f => LineSAT f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  GraphConstraintsAbstractBridge.line_three_sat_three

/-- The plane classifications also hold for local width-three formulas and
for their occurrence-three restriction. Natural numbers are the atom names. -/
theorem plane_three_sat : LeanWang.CoREComplete
    (fun f => Satisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f) :=
  GraphConstraintsAbstractBridge.plane_three_sat
theorem plane_three_sat_three : LeanWang.CoREComplete
    (fun f => Satisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  GraphConstraintsAbstractBridge.plane_three_sat_three

/-- Exact-one satisfaction counts true literal occurrences, so two copies
of the same literal are not silently identified. -/
def ExactlyOneSatisfiable (f : Formula) : Prop :=
  ∃ a : ℕ → Cell → Bool, ∀ (z : Cell) c, c ∈ f.clauses →
    (c.map fun l => a l.atom (z.1+l.offset.1, z.2+l.offset.2) == l.value).count true = 1

theorem plane_exact_one : LeanWang.CoREComplete
    (fun f => ExactlyOneSatisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  GraphConstraintsAbstractBridge.plane_exact_one

/-- The line exact-one problems are PSPACE-complete as well, with width at
most three, and also with at most three occurrences of each variable. -/
theorem line_exact_one : ComplexityAbstract.PSPACEComplete formulaEncoding
    (fun f => ExactlyOneSatisfiable f ∧ OneDimensional f ∧ LocalFormula f ∧ WidthAtMost 3 f) :=
  GraphConstraintsAbstractBridge.line_exact_one
theorem line_exact_one_three : ComplexityAbstract.PSPACEComplete formulaEncoding
    (fun f => ExactlyOneSatisfiable f ∧ OneDimensional f ∧ LocalFormula f ∧
      WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  GraphConstraintsAbstractBridge.line_exact_one_three

/-- A d-dimensional formula is a list of clauses of ((variable,offset),value)
literals, with offset in ℤᵈ. A satisfying assignment need not be periodic. -/
abbrev FormulaIn (d : ℕ) := List (List ((ℕ × Lattice d) × Bool))
def SatisfiableIn {d : ℕ} (f : FormulaIn d) : Prop :=
  ∃ a : ℕ → Lattice d → Bool, ∀ z c, c ∈ f → ∃ l ∈ c, a l.1.1 (z+l.1.2) = l.2
def LocalIn {d : ℕ} (f : FormulaIn d) : Prop :=
  ∀ c ∈ f, ∀ l ∈ c, ∀ r ∈ c, ∑ i, (l.1.2 i-r.1.2 i).natAbs ≤ 1

/-- Theorem 3.2: unrestricted and local periodic CNF SAT are co-r.e.-complete
in every dimension at least two. -/
theorem higher_dimensional_sat (d : ℕ) (dimension : 2 ≤ d) :
    LeanWang.CoREComplete (@SatisfiableIn d) ∧
      LeanWang.CoREComplete (fun f : FormulaIn d => SatisfiableIn f ∧ LocalIn f) :=
  GraphAbstractBridge.Data.higher_dimensional_sat d dimension

/-- Cook–Levin: satisfiability of zero-dimensional formulas of width at most
three is NP-hard under the same binary formula encoding. This supplies the
finite SAT source for the NP-hardness reductions. -/
theorem cook_levin : ComplexityAbstract.NPHard formulaEncoding
    (fun f => Satisfiable f ∧ ZeroDimensional f ∧ WidthAtMost 3 f) :=
  GraphConstraintsAbstractBridge.cook_levin

/-! ## Planar SAT, three-dimensional matching, and orientation -/

/-- The incidence graph has one vertex for each occurring variable and each
clause. Left sum tags denote variables, right tags denote clause indices.
A clause is anchored at its first literal's offset; every literal occurrence
supplies an edge to its variable at the difference from that anchor. -/
abbrev IncidenceVertex := Sum ℕ ℕ
def clauseAnchor (clause : List Literal) : Cell :=
  (clause.head?.map Literal.offset).getD (0,0)
def formulaAtoms (f : Formula) : List ℕ := (f.flatMap fun c => c.map Literal.atom).dedup
def incidenceGraph (f : Formula) : Graph IncidenceVertex 2 :=
  ((formulaAtoms f).map Sum.inl ++ (List.range f.length).map Sum.inr,
    f.zipIdx.flatMap fun tagged => tagged.1.map fun literal =>
      (Sum.inr tagged.2,Sum.inl literal.atom,
        ![literal.offset.1-(clauseAnchor tagged.1).1,
          literal.offset.2-(clauseAnchor tagged.1).2]))

/-- A supplied incidence drawing lists its vertices and routes in graph order
and attaches every route to the indicated translated endpoints. Vertex
residues modulo the period must be distinct. Exact-one presentations also
place the vertex representatives strictly inside the fundamental square. -/
abbrev PlanarInput := Formula × Drawing
def formulaRoutesMatch (f : Formula) (d : Drawing) : Prop :=
  ∀ e ∈ (incidenceGraph f).edges.zipIdx,
    (d.edgeRoute e.2).head? = some (d.vertexPosition (incidenceGraph f) e.1.source) ∧
    (d.edgeRoute e.2).getLast? = some
      ((d.vertexPosition (incidenceGraph f) e.1.target).1+(d.gridSize : ℤ)*(e.1.offset 0),
       (d.vertexPosition (incidenceGraph f) e.1.target).2+(d.gridSize : ℤ)*(e.1.offset 1))
def planarOrbitCompatible (f : Formula) (d : Drawing) : Prop :=
  d.vertexPositions.length=(incidenceGraph f).vertices.length ∧
    d.edgeRoutes.length=(incidenceGraph f).edges.length ∧
    (d.vertexPositions.map (fun p => (p.1%(d.gridSize : ℤ),p.2%(d.gridSize : ℤ)))).Nodup ∧
    formulaRoutesMatch f d
def planarFiniteCompatible (f : Formula) (d : Drawing) : Prop :=
  d.vertexPositions.length=(incidenceGraph f).vertices.length ∧
    d.edgeRoutes.length=(incidenceGraph f).edges.length ∧ d.vertexPositions.Nodup ∧
    (∀ p ∈ d.vertexPositions, 0 < p.1 ∧ p.1 < d.gridSize ∧ 0 < p.2 ∧ p.2 < d.gridSize) ∧
    formulaRoutesMatch f d
def planarGridBound (coefficient : ℕ) (i : PlanarInput) : Prop :=
  i.2.gridSize ≤ coefficient*(i.1.length+i.1.flatten.length+1)

/-- The binary encoding stores a length-delimited drawing followed by the
formula fields. It includes all coordinates, route points, and occurrences. -/
def planarEncoding (i : PlanarInput) : List ComplexityAbstract.Symbol :=
  ComplexityAbstract.binaryFields ((drawingFields i.2).length::
    (drawingFields i.2 ++ (i.1.length::i.1.flatMap clauseFields)))

/-- Planar SAT requires orthogonal, separated routes. Distinct lifted route
points may meet only at outer route endpoints; segment interiors and vertices
are separated as specified by `DrawingGeometry`. The grid bounds are linear
in clause-plus-literal count, with the displayed constants. -/
def PlanarSAT (i : PlanarInput) : Prop :=
  Satisfiable i.1 ∧ planarGridBound 8847360 i ∧ LocalFormula i.1 ∧
    WidthAtMost 3 i.1 ∧ planarOrbitCompatible i.1 i.2 ∧ DrawingGeometry i.2
def PlanarExactOne (i : PlanarInput) : Prop :=
  ExactlyOneSatisfiable i.1 ∧ planarGridBound 637009920 i ∧ LocalFormula i.1 ∧
    WidthAtMost 3 i.1 ∧ planarFiniteCompatible i.1 i.2 ∧ DrawingGeometry i.2
def PlanarLineSAT (i : PlanarInput) : Prop := PlanarSAT i ∧ OneDimensional i.1
def PlanarLineExactOne (i : PlanarInput) : Prop := PlanarExactOne i ∧ OneDimensional i.1

/-- Theorems 3.5–3.6: the four supplied-drawing plane problems are
co-r.e.-complete, including the three-occurrence restrictions. -/
theorem planar_plane_sat : LeanWang.CoREComplete PlanarSAT :=
  GraphPlanarAbstractBridge.planar_plane_sat
theorem planar_plane_three_occurrences : LeanWang.CoREComplete
    (fun i => PlanarSAT i ∧ OccurrencesAtMost 3 i.1) :=
  GraphPlanarAbstractBridge.planar_plane_three_occurrences
theorem planar_plane_exact_one : LeanWang.CoREComplete PlanarExactOne :=
  GraphPlanarAbstractBridge.planar_plane_exact_one
theorem planar_plane_exact_one_three : LeanWang.CoREComplete
    (fun i => PlanarExactOne i ∧ OccurrencesAtMost 3 i.1) :=
  GraphPlanarAbstractBridge.planar_plane_exact_one_three

/-- The supplied-drawing line problems are PSPACE-complete, with the same
locality, width, geometry, and linear grid bounds. -/
theorem planar_line_sat : ComplexityAbstract.PSPACEComplete planarEncoding PlanarLineSAT :=
  GraphPlanarAbstractBridge.planar_line_sat
theorem planar_line_three_occurrences : ComplexityAbstract.PSPACEComplete planarEncoding
    (fun i => PlanarLineSAT i ∧ OccurrencesAtMost 3 i.1) :=
  GraphPlanarAbstractBridge.planar_line_three_occurrences
theorem planar_line_exact_one : ComplexityAbstract.PSPACEComplete planarEncoding PlanarLineExactOne :=
  GraphPlanarAbstractBridge.planar_line_exact_one
theorem planar_line_exact_one_three : ComplexityAbstract.PSPACEComplete planarEncoding
    (fun i => PlanarLineExactOne i ∧ OccurrencesAtMost 3 i.1) :=
  GraphPlanarAbstractBridge.planar_line_exact_one_three

/-! Periodic 3DM has three color classes (indexed by `Fin 3`) on the
lattice ℤ². A triple lists one (element index,offset) reference per color.
The three counts and triple occurrences are explicit finite data. -/
namespace ThreeDM
abbrev Reference := ℕ × Cell
abbrev Triple := Reference × Reference × Reference
abbrev Problem := ℕ × ℕ × ℕ × List Triple

def reference (t : Triple) (color : Fin 3) : Reference :=
  if color=0 then t.1 else if color=1 then t.2.1 else t.2.2

def elementCount (p : Problem) (color : Fin 3) : ℕ :=
  if color=0 then p.1 else if color=1 then p.2.1 else p.2.2.1

def triples (p : Problem) : List Triple := p.2.2.2

def incidences (p : Problem) (color : Fin 3) (atom : ℕ) : List (ℕ × Cell) :=
  (List.range (triples p).length).filterMap fun j =>
    let r := reference ((triples p).getD j ((0,(0,0)),(0,(0,0)),(0,(0,0)))) color
    if r.1=atom then some (j,r.2) else none

def Matches (p : Problem) : Prop :=
  ∃ selected : ℕ → Cell → Bool, ∀ color atom, atom<elementCount p color → ∀ z : Cell,
    ((incidences p color atom).map fun i => selected i.1 (z.1-i.2.1,z.2-i.2.2)).count true=1

def WellFormed (p : Problem) : Prop :=
  ∀ t∈triples p, ∀ color, (reference t color).1<elementCount p color

def DegreeTwoOrThree (p : Problem) : Prop :=
  ∀ color atom, atom<elementCount p color → (incidences p color atom).length∈([2,3] : List ℕ)

def Local (p : Problem) : Prop :=
  ∀ t∈triples p, ∀ color, (reference t color).2.1.natAbs+(reference t color).2.2.natAbs≤1

def OneDimensional (p : Problem) : Prop :=
  ∀ t∈triples p, ∀ color, (reference t color).2.2=0

def Line (p : Problem) : Prop := Matches p ∧ WellFormed p ∧ DegreeTwoOrThree p ∧ OneDimensional p ∧ Local p

def referenceFields (r : Reference) : List ℕ := [r.1,Encodable.encode r.2.1,Encodable.encode r.2.2]
def tripleFields (t : Triple) : List ℕ := referenceFields t.1++referenceFields t.2.1++referenceFields t.2.2

def fields (p : Problem) : List ℕ := p.1::p.2.1::p.2.2.1::(triples p).length::(triples p).flatMap tripleFields

def encoding (p : Problem) : List ComplexityAbstract.Symbol := ComplexityAbstract.binaryFields (fields p)


abbrev Vertex := ℕ ⊕ (Fin 3 × ℕ)
def incidenceVertices (p : Problem) : List Vertex :=
  (List.range (triples p).length).map Sum.inl++(List.finRange 3).flatMap fun c =>
    (List.range (elementCount p c)).map fun atom => Sum.inr (c,atom)
def incidenceGraph (p : Problem) : Graph Vertex 2 :=
  (incidenceVertices p,(triples p).zipIdx.flatMap fun t => (List.finRange 3).map fun c =>
    (Sum.inl t.2,Sum.inr (c,(reference t.1 c).1),fun i : Fin 2 => if i=0 then (reference t.1 c).2.1 else (reference t.1 c).2.2))
abbrev Input := Problem × Drawing

def DrawingCompatible (p : Problem) (d : Drawing) : Prop :=
  LeanTrominoes.GraphAbstract.Compatible (incidenceGraph p) d

def Plane (input : Input) : Prop := Matches input.1 ∧ Local input.1 ∧ WellFormed input.1 ∧ DegreeTwoOrThree input.1 ∧
  DrawingCompatible input.1 input.2 ∧ DrawingGeometry input.2 ∧ DrawingHalo input.2

def PlanarLine (input : Input) : Prop := Line input.1 ∧ DrawingCompatible input.1 input.2 ∧
  DrawingGeometry input.2 ∧ DrawingHalo input.2

def planarFields (input : Input) : List ℕ := (drawingFields input.2).length::
  (drawingFields input.2++fields input.1)
def planarEncoding (input : Input) : List ComplexityAbstract.Symbol := ComplexityAbstract.binaryFields (planarFields input)

end ThreeDM

abbrev PeriodicThreeDM := ThreeDM.Problem
abbrev PeriodicThreeDMInput := ThreeDM.Input
def Matches (p : PeriodicThreeDM) : Prop := ThreeDM.Matches p
def ThreeDMPlane (input : PeriodicThreeDMInput) : Prop := ThreeDM.Plane input
def ThreeDMLine (p : PeriodicThreeDM) : Prop := ThreeDM.Line p

/-- Theorem 3.7: local colored degree-two-or-three 3DM is co-r.e.-complete
with a supplied orthogonal drawing in the plane, and PSPACE-complete on the
line, with or without that drawing. The supplied drawing must satisfy the
full continuous separation, endpoint-contact, and open-halo conditions above.
The binary encoding stores counts and reference fields; supplied drawings
use the complete cached segment, vertex, and route fields from `drawingFields`. -/
theorem three_dm_plane : LeanWang.CoREComplete ThreeDMPlane :=
  GraphThreeDMAbstractBridge.three_dm_plane

theorem three_dm_line : ComplexityAbstract.PSPACEComplete ThreeDM.encoding ThreeDMLine :=
  GraphThreeDMAbstractBridge.three_dm_line

theorem three_dm_planar_line : ComplexityAbstract.PSPACEComplete ThreeDM.planarEncoding ThreeDM.PlanarLine :=
  GraphThreeDMAbstractBridge.three_dm_planar_line

/-- A colored graph lists vertex kinds and edge records
`((source,target,offset),color)`, with colors numbered 0, 1, 2.
`true` marks a trichromatic vertex. The other vertices are monochromatic.
At translate z an edge joins (source,z) to (target,z+offset). -/
abbrev OrientationInput := List Bool × List ((ℕ × ℕ × Cell) × Fin 3)
abbrev OrientationLiteral := ℕ × Cell × Bool

/-- The two ends of an edge read the same direction bit with opposite signs.
The target reads it at the source translate, hence the negated offset.
Loops contribute both ends. The final component records the edge color. -/
def orientationEnds (i : OrientationInput) (v : ℕ) :
    List (ℕ × OrientationLiteral × Fin 3) :=
  (i.2.zipIdx.flatMap fun (e,k) =>
    [(e.1.1,(k,(0,0),false),e.2),
     (e.1.2.1,(k,(-e.1.2.2.1,-e.1.2.2.2),true),e.2)]).filter
    (fun incidence => incidence.1 = v)
def orientationIncoming (i : OrientationInput) (v : ℕ) : List OrientationLiteral :=
  (orientationEnds i v).map (fun incidence => incidence.2.1)
def orientationColors (i : OrientationInput) (v : ℕ) : List (Fin 3) :=
  (orientationEnds i v).map (fun incidence => incidence.2.2)

/-- Every edge endpoint is in range and every vertex has three ends.
Trichromatic vertices have one end of each color; monochromatic vertices
have three ends of a single color. -/
def OrientationWellFormed (i : OrientationInput) : Prop :=
  (∀ e ∈ i.2, e.1.1 < i.1.length ∧ e.1.2.1 < i.1.length) ∧
    ∀ v < i.1.length, (orientationColors i v).length = 3 ∧
      if i.1.getD v false then ∀ color : Fin 3, (orientationColors i v).count color = 1
      else ∃ color : Fin 3, ∀ c ∈ orientationColors i v, c = color

/-- A valid orientation has indegree one at monochromatic vertices and
indegree zero or three at trichromatic vertices. Directions are chosen
independently at every translate. -/
def IsOrientation (i : OrientationInput) (a : ℕ → Cell → Bool) : Prop :=
  ∀ (z : Cell) v, v < i.1.length → if i.1.getD v false then
    (∀ l ∈ orientationIncoming i v, ∀ r ∈ orientationIncoming i v,
      (a l.1 (z.1+l.2.1.1,z.2+l.2.1.2) = l.2.2) ↔
        (a r.1 (z.1+r.2.1.1,z.2+r.2.1.2) = r.2.2))
  else ((orientationIncoming i v).map fun l =>
    a l.1 (z.1+l.2.1.1,z.2+l.2.1.2) == l.2.2).count true = 1
def Orientable (i : OrientationInput) : Prop := ∃ a, IsOrientation i a
def OrientationProblem (i : OrientationInput) : Prop := Orientable i ∧ OrientationWellFormed i
def OrientationLocal (i : OrientationInput) : Prop :=
  OrientationProblem i ∧ ∀ e ∈ i.2, e.1.2.2.1.natAbs+e.1.2.2.2.natAbs ≤ 1
def OrientationLine (i : OrientationInput) : Prop :=
  OrientationLocal i ∧ ∀ e ∈ i.2, e.1.2.2.2 = 0
def OrientationFinite (i : OrientationInput) : Prop :=
  (∃ a : ℕ → Bool, IsOrientation i (fun e _ => a e)) ∧
    OrientationWellFormed i ∧ ∀ e ∈ i.2, e.1.2.2 = (0,0)

/-- The binary encoding lists the vertex and edge counts, vertex-kind bits,
and five fields per edge: endpoints, encoded signed coordinates, and color. -/
def orientationEncoding (i : OrientationInput) : List ComplexityAbstract.Symbol :=
  ComplexityAbstract.binaryFields (i.1.length :: i.2.length ::
    (i.1.map Bool.toNat ++ i.2.flatMap fun e =>
      [e.1.1,e.1.2.1,Encodable.encode e.1.2.2.1,Encodable.encode e.1.2.2.2,e.2.val]))

/-- Theorem 3.8: local colored orientation is co-r.e.-complete in the plane,
PSPACE-complete on the line, and NP-complete for finite inputs.
Finite inputs require every offset to be zero. -/
theorem orientation_plane : LeanWang.CoREComplete OrientationLocal :=
  GraphOrientationAbstractBridge.orientation_plane
theorem orientation_line : ComplexityAbstract.PSPACEComplete orientationEncoding OrientationLine :=
  GraphOrientationAbstractBridge.orientation_line
theorem orientation_finite : ComplexityAbstract.NPComplete orientationEncoding OrientationFinite :=
  GraphOrientationAbstractBridge.orientation_finite

/-! ## Period-one models and polynomial algorithms -/

/-- A Horn rule consists of premises and an optional conclusion; `none`
means false. A periodic rule labels its variables by translation offsets.
Dual Horn complements the assignment's truth values. -/
abbrev HornRule (V : Type) := List V × Option V

def HornSatisfies {V : Type} (rules : List (HornRule V)) (model : V → Prop) : Prop :=
  ∀ rule∈rules, (∀ atom∈rule.1, model atom) →
    match rule.2 with | none => False | some atom => model atom

def HornSatisfiable {V : Type} (rules : List (HornRule V)) : Prop := ∃ model, HornSatisfies rules model

def DualHornSatisfiable {V : Type} (rules : List (HornRule V)) : Prop :=
  ∃ model : V → Prop, HornSatisfies rules (fun atom => ¬model atom)

def PeriodicHornSatisfies {V G : Type} [Add G] (rules : List (HornRule (V×G))) (model : V → G → Prop) : Prop :=
  ∀ rule∈rules, ∀ z, (∀ premise∈rule.1, model premise.1 (z+premise.2)) →
    match rule.2 with | none => False | some head => model head.1 (z+head.2)

def PeriodicHornSatisfiable {V G : Type} [Add G] (rules : List (HornRule (V×G))) : Prop := ∃ model, PeriodicHornSatisfies rules model

def PeriodicDualHornSatisfies {V G : Type} [Add G] (rules : List (HornRule (V×G))) (model : V → G → Prop) : Prop :=
  PeriodicHornSatisfies rules (fun v z => ¬model v z)

def PeriodicDualHornSatisfiable {V G : Type} [Add G] (rules : List (HornRule (V×G))) : Prop := ∃ model, PeriodicDualHornSatisfies rules model

abbrev HornInput := Σ n : Nat, List (HornRule (Fin n))

def hornOccurrences (input : HornInput) : List (Fin input.1 × Nat) :=
  (List.finRange input.2.length).flatMap fun rule => (input.2.get rule).1.map fun v => (v,rule.val)

def hornAtomCode {n : Nat} : Option (Fin n) → Nat | none => 0 | some v => v.val+1

def hornEncoding (input : HornInput) : List Int :=
  ([input.1,input.2.length,(hornOccurrences input).length]++
    (List.finRange input.2.length).map (fun rule => hornAtomCode (input.2.get rule).2)++
    (hornOccurrences input).map (fun (occurrence : Fin input.1 × Nat) => occurrence.1.val+1)++
    (hornOccurrences input).map Prod.snd).map Int.ofNat

def hornSize (input : HornInput) : Nat := input.1+input.2.length+(hornOccurrences input).length+1

/-- Theorem 4.2: every satisfiable periodic Horn or dual Horn instance
has a model constant on all translates of each variable. Offsets may belong
to any additive group; no locality assumption is needed. -/
theorem horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule (V×G)))
    (h : PeriodicHornSatisfiable rules) :
    ∃ model : V → Prop, PeriodicHornSatisfies rules (fun v _ => model v) :=
  GraphAlgorithmsAbstractBridge.horn_period_one rules h

theorem dual_horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule (V×G)))
    (h : PeriodicDualHornSatisfiable rules) :
    ∃ model : V → Prop, PeriodicDualHornSatisfies rules (fun v _ => model v) :=
  GraphAlgorithmsAbstractBridge.dual_horn_period_one rules h

/-- A fixed bounded-word RAM decides Horn satisfiability in linear time.
The encoding lists variable, rule, and premise-occurrence counts, rule heads,
and occurrence variable/rule arrays. Zero encodes false; variable i has code
 i+1. Repeated premises remain distinct. The bound includes reading this
input, allocation, propagation, and halt, for every sufficiently large width. -/
theorem horn_linear : ComplexityAbstract.RAM.DecidesWithin hornEncoding (fun input => HornSatisfiable input.2)
    (fun input => 120*(hornSize input+1)) (fun input => 27*Nat.log2 (hornSize input+2)+2) :=
  GraphAlgorithmsAbstractBridge.horn_linear

theorem dual_horn_linear : ComplexityAbstract.RAM.DecidesWithin hornEncoding (fun input => DualHornSatisfiable input.2)
    (fun input => 120*(hornSize input+1)) (fun input => 27*Nat.log2 (hornSize input+2)+2) :=
  GraphAlgorithmsAbstractBridge.dual_horn_linear

/-! A periodic binary clause has two signed variables and their lattice offsets.
`true` is a positive sign. Repeating a literal gives a unit clause; `none` is
an empty clause. Every lattice translate of every listed clause is required. -/
namespace TwoSAT
abbrev Literal (n d : ℕ) := (Fin n × Bool) × Lattice d
abbrev Clause (n d : ℕ) := Option (Literal n d × Literal n d)
abbrev Formula (n d : ℕ) := List (Clause n d)

def Truth {n d : ℕ} (model : Fin n → Lattice d → Prop)
    (literal : Fin n × Bool) (z : Lattice d) : Prop :=
  if literal.2 then model literal.1 z else ¬ model literal.1 z

def Holds {n d : ℕ} (model : Fin n → Lattice d → Prop)
    (z : Lattice d) : Clause n d → Prop
  | none => False
  | some (a,b) => Truth model a.1 (z+a.2) ∨ Truth model b.1 (z+b.2)

def Satisfiable {n d : ℕ} (formula : Formula n d) : Prop :=
  ∃ model, ∀ clause ∈ formula, ∀ z, Holds model z clause

/-- Locality bounds relative offsets coordinatewise by one. The two literals
may have an arbitrarily large common offset. -/
def Local {n d : ℕ} (formula : Formula n d) : Prop :=
  ∀ a b, some (a,b) ∈ formula → ∀ i, (b.2 i-a.2 i).natAbs ≤ 1

abbrev Input (d : ℕ) := {input : (Σ n : ℕ, Formula n d) // Local input.2}

/-- Each clause record stores a presence flag, two variable indices, two sign
bits, and both original offset vectors. Empty clauses use zero records.
The input starts with the variable and clause counts and ends with a zero
record for padding. Its structural size is variables plus clauses plus one. -/
def clauseWords {n d : ℕ} : Clause n d → List ℤ
  | none => List.replicate (5+2*d) 0
  | some (a,b) => [(1:ℤ),(a.1.1.val:ℤ),(if a.1.2 then 1 else 0),
      (b.1.1.val:ℤ),(if b.1.2 then 1 else 0)] ++
      (List.finRange d).map a.2 ++ (List.finRange d).map b.2

def encode {d : ℕ} (input : Input d) : List ℤ :=
  [(input.val.1:ℤ),(input.val.2.length:ℤ)] ++
    (input.val.2++[none]).flatMap clauseWords

def size {d : ℕ} (input : Input d) : ℕ := input.val.1+input.val.2.length+1
end TwoSAT

/-- Theorem 4.1: at each fixed dimension, periodic local 2SAT is decidable in
polynomial time on a bounded-word RAM. One program works at every sufficiently
large logarithmic word size accommodating the original signed input words. -/
theorem two_sat_polynomial (d : ℕ) :
    ComplexityAbstract.RAM.PolynomialTime TwoSAT.encode TwoSAT.size
      (fun input : TwoSAT.Input d => TwoSAT.Satisfiable input.val.2) :=
  GraphTwoSATAbstractBridge.polynomialTime d

/-! ## Periodic matchings -/

/-- A bipartite protoedge records its left and right endpoint and offset.
It joins (left,z) to (right,z+offset). A perfect matching is a bijection of
the lifted color classes supported by these adjacencies. Period one means
commuting with every lattice translation; quotient matching ignores offsets. -/
abbrev BipartiteEdge (L R : Type) (d : Nat) := L × R × Lattice d

def BipartiteAdjacent {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d))
    (u : L × Lattice d) (v : R × Lattice d) : Prop :=
  ∃ e∈es, e.1=u.1 ∧ e.2.1=v.1 ∧ v.2=u.2+e.2.2

def PerfectMatching {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d), ∀ u, BipartiteAdjacent es u (f u)
def PeriodOneMatching {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d),
    (∀ u, BipartiteAdjacent es u (f u)) ∧ ∀ l z t, f (l,z+t)=((f (l,z)).1,(f (l,z)).2+t)
def QuotientMatching {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : L ≃ R, ∀ l, ∃ e∈es, e.1=l ∧ e.2.1=f l

abbrev MatchingInput (d : Nat) := Σ n : Nat, Σ m : Nat, List (BipartiteEdge (Fin n) (Fin m) d)
def matchingEncoding {d : Nat} (input : MatchingInput d) : List Int :=
  ([input.1,input.2.1,input.2.2.length]++input.2.2.map (fun edge => edge.1.val)++
    input.2.2.map (fun edge => edge.2.1.val)).map Int.ofNat
def matchingSize {d : Nat} (input : MatchingInput d) := input.1+input.2.1+input.2.2.length+1


/-- Theorem 4.6: in every dimension, perfect matching is equivalent to finite
quotient matching and admits a period-one witness. Offsets need not be local. -/
theorem matching_period_one {L R : Type} [Fintype L] [Fintype R] {d : ℕ}
    (es : List (BipartiteEdge L R d)) :
    (PerfectMatching es ↔ QuotientMatching es) ∧ (PerfectMatching es → PeriodOneMatching es) :=
  GraphAlgorithmsAbstractBridge.matching_period_one es

/-- A fixed bounded-word RAM decides periodic bipartite perfect matching
within this conservative quartic instruction bound. Its encoding contains
n, m, E and the two endpoint arrays; offsets can be discarded by the quotient
equivalence above. The bound includes input parsing, allocation, alternating
path searches and rewrites, and halt, and works at every larger word width. -/
theorem matching_algorithm {d : ℕ} : ComplexityAbstract.RAM.DecidesWithin (matchingEncoding (d:=d))
    (fun input => PerfectMatching input.2.2) (fun input => 1000*(matchingSize input+1)^4)
    (fun input => 8*Nat.log2 (matchingSize input+2)+2) :=
  GraphAlgorithmsAbstractBridge.matching_algorithm

/-- A general matching is a partially defined partner function: partners are
mutual, distinct, and adjacent. Period one means that this function commutes
with every lattice translation. A perfect matching may have any period. -/
def IsPartialMatching {V : Type} {d : ℕ} (es : List (Edge V d))
    (mate : V × Lattice d → Option (V × Lattice d)) : Prop :=
  (∀ u v, mate u = some v → mate v = some u ∧ Adjacent es u v) ∧
    ∀ u, mate u ≠ some u

def IsPeriodOne {V : Type} {d : ℕ}
    (mate : V × Lattice d → Option (V × Lattice d)) : Prop :=
  ∀ u t, mate (u.1,u.2+t) = (mate u).map (fun v => (v.1,v.2+t))

def HasPerfectMatching {V : Type} {d : ℕ} (es : List (Edge V d)) : Prop :=
  ∃ mate : V × Lattice d → V × Lattice d,
    Function.Involutive mate ∧ (∀ u, mate u ≠ u) ∧ ∀ u, Adjacent es u (mate u)

/-- An augmenting path is a simple list with two free ends and an odd number
of edges. Consecutive edges alternate between unused and matched edges,
starting and ending with unused edges. -/
def IsAugmentingPath {V : Type} {d : ℕ} (es : List (Edge V d))
    (mate : V × Lattice d → Option (V × Lattice d)) (root : V × Lattice d)
    (path : List (V × Lattice d)) : Prop :=
  path.Nodup ∧ path.head? = some root ∧ mate root = none ∧
    (∀ last, path.getLast? = some last → mate last = none) ∧
    (∃ k, path.length = 2*k+2) ∧
    ∀ i (hi : i+1 < path.length), Adjacent es path[i] path[i+1] ∧
      (if i % 2 = 0 then mate path[i] ≠ some path[i+1]
       else mate path[i] = some path[i+1])

/-- Lemma 4.4: every proper two-coloring of a connected periodic graph is
invariant under twice every translation, in every dimension. -/
theorem bipartition_doubled {V : Type} {d : ℕ}
    (es : List (Edge V d)) (connected : Connected es)
    (color : V × Lattice d → Bool) (proper : ProperColoring es color)
    (v : V) (z t : Lattice d) : color (v, z+(t+t)) = color (v,z) :=
  GraphAbstractBridge.Data.bipartition_doubled es connected color proper v z t

/-- Lemma 4.3: every free vertex of a period-one partial matching starts a
simple augmenting path of coordinate diameter at most 2dE when the graph has
a perfect matching. The weaker coordinate locality suffices, hence so does
the paper's L₁ locality. No bipartiteness assumption is required. -/
theorem bounded_augmenting_path {V : Type} [DecidableEq V] [Fintype V] {d : ℕ}
    (es : List (Edge V d)) (locality : CoordinateLocal es)
    (perfect : HasPerfectMatching es)
    (mate : V × Lattice d → Option (V × Lattice d))
    (matching : IsPartialMatching es mate) (periodic : IsPeriodOne mate)
    (root : V × Lattice d) (free : mate root = none) :
    ∃ path : List (V × Lattice d), IsAugmentingPath es mate root path ∧
      ∀ x ∈ path, ∀ y ∈ path, ∀ i, (x.2 i-y.2 i).natAbs ≤ 2*d*es.length :=
  GraphAbstractBridge.Data.bounded_augmenting_path es locality perfect mate matching periodic root free

/-- A bipartite partial matching gives mutual partial inverse partner
functions. Supported partners are adjacent; period one requires both
functions to commute with lattice translations. -/
def PeriodOneBipartitePartial {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d))
    (left : L × Lattice d → Option (R × Lattice d))
    (right : R × Lattice d → Option (L × Lattice d)) : Prop :=
  (∀ u v, left u=some v ↔ right v=some u) ∧
  (∀ u v, left u=some v → BipartiteAdjacent es u v) ∧
  (∀ l z t, left (l,z+t)=(left (l,z)).map (fun v => (v.1,v.2+t))) ∧
  ∀ r z t, right (r,z+t)=(right (r,z)).map (fun u => (u.1,u.2+t))

def PerfectBipartitePartial {L R : Type} {d : Nat}
    (left : L × Lattice d → Option (R × Lattice d))
    (right : R × Lattice d → Option (L × Lattice d)) : Prop :=
  (∀ u, left u≠none) ∧ ∀ v, right v≠none

def IsShortBipartiteAugmentingPath {L R : Type} [Fintype L] [Fintype R] {d : Nat}
    (es : List (BipartiteEdge L R d))
    (left : L × Lattice d → Option (R × Lattice d))
    (right : R × Lattice d → Option (L × Lattice d))
    (pairs : List ((L × Lattice d) × (R × Lattice d))) : Prop :=
  pairs≠[] ∧
  (∀ pair∈pairs, BipartiteAdjacent es pair.1 pair.2 ∧ left pair.1≠some pair.2) ∧
  (∀ pair, pairs.head?=some pair → left pair.1=none) ∧
  (∀ pair, pairs.getLast?=some pair → right pair.2=none) ∧
  (∀ i (hi : i+1<pairs.length), right pairs[i].2=some pairs[i+1].1) ∧
  (pairs.flatMap (fun pair => [Sum.inl pair.1.1,Sum.inr pair.2.1])).Nodup ∧
  2*pairs.length-1<Fintype.card L+Fintype.card R


/-- Lemma 4.5: a period-one partial matching is perfect or has a short
augmenting path. Each listed pair is an unused edge; successive pairs are
joined by matched edges. Its ends are free, projected protovertices are
pairwise distinct, and its number of edges is less than |L|+|R|. -/
theorem short_augmenting_path {L R : Type} [DecidableEq L] [DecidableEq R]
    [Fintype L] [Fintype R] {d : ℕ} (es : List (BipartiteEdge L R d))
    (perfect : PerfectMatching es)
    (left : L × Lattice d → Option (R × Lattice d))
    (right : R × Lattice d → Option (L × Lattice d))
    (matching : PeriodOneBipartitePartial es left right) :
    PerfectBipartitePartial left right ∨ ∃ pairs, IsShortBipartiteAugmentingPath es left right pairs :=
  GraphAlgorithmsAbstractBridge.short_augmenting_path es perfect left right matching

end LeanTrominoes.GraphAbstract
