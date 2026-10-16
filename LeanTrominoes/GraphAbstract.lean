/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract
import LeanTrominoes.GraphAbstractBridge

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
The algorithm theorems below bound instrumented operation counters. Connecting
these bounds to the shared `ComplexityAbstract.RAM` execution model requires
program simulations; these statements do not yet provide those simulations.
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
abbrev Literal := PeriodicLiteral ℕ
abbrev Formula := PeriodicCNF ℕ

def Satisfies (f : Formula) (a : ℕ → Cell → Bool) : Prop :=
  ∀ (z : Cell) c, c ∈ f.clauses → ∃ l ∈ c,
    a l.atom (z.1+l.offset.1, z.2+l.offset.2) = l.value
def Satisfiable (f : Formula) : Prop := ∃ a, Satisfies f a
def LocalFormula (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, ∀ r ∈ c,
    (l.offset.1-r.offset.1).natAbs + (l.offset.2-r.offset.2).natAbs ≤ 1
def WidthAtMost (k : ℕ) (f : Formula) : Prop := ∀ c ∈ f.clauses, c.length ≤ k
def OccurrencesAtMost (k : ℕ) (f : Formula) : Prop :=
  ∀ v, (f.clauses.flatMap fun c => c.map PeriodicLiteral.atom).count v ≤ k

/-- A zero-dimensional formula has no offsets, so translated cells are
independent copies of one finite SAT instance. -/
def ZeroDimensional (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.offset = (0,0)

/-- A one-dimensional formula has zero vertical offset in every literal. -/
def OneDimensional (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.offset.2 = 0

/-- Line satisfiability assigns a Boolean to every variable at every integer.
The flat binary encoding lists clause lengths and literal fields, including
signed coordinates; invalid locality and width restrictions are rejected. -/
def LineSAT (f : Formula) : Prop :=
  (∃ a : ℕ → ℤ → Bool, ∀ (z : ℤ) c, c ∈ f.clauses →
    ∃ l ∈ c, a l.atom (z+l.offset.1) = l.value) ∧ OneDimensional f ∧ f.IsLocalOnLine
abbrev formulaEncoding := PeriodicCNFFlatEncoding.finEncoding

/-- Theorems 3.2–3.4: local line SAT remains PSPACE-complete with width at
most three and with at most three occurrences of each variable. -/
theorem line_sat : ComplexityAbstract.PSPACEComplete formulaEncoding.encode LineSAT :=
  GraphAbstractBridge.Data.line_sat
theorem line_three_sat : ComplexityAbstract.PSPACEComplete formulaEncoding.encode
    (fun f => LineSAT f ∧ WidthAtMost 3 f) :=
  GraphAbstractBridge.Data.line_three_sat
theorem line_three_sat_three : ComplexityAbstract.PSPACEComplete formulaEncoding.encode
    (fun f => LineSAT f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  GraphAbstractBridge.Data.line_three_sat_three

/-- The plane classifications also hold for local width-three formulas and
for their occurrence-three restriction. Natural numbers are the atom names. -/
theorem plane_three_sat : LeanWang.CoREComplete
    (fun f => Satisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f) :=
  GraphAbstractBridge.Data.plane_three_sat
theorem plane_three_sat_three : LeanWang.CoREComplete
    (fun f => Satisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  GraphAbstractBridge.Data.plane_three_sat_three

/-- Exact-one satisfaction counts true literal occurrences, so two copies
of the same literal are not silently identified. -/
def ExactlyOneSatisfiable (f : Formula) : Prop :=
  ∃ a : ℕ → Cell → Bool, ∀ (z : Cell) c, c ∈ f.clauses →
    (c.map fun l => a l.atom (z.1+l.offset.1, z.2+l.offset.2) == l.value).count true = 1

theorem plane_exact_one : LeanWang.CoREComplete
    (fun f => ExactlyOneSatisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  GraphAbstractBridge.Data.plane_exact_one

/-- The line exact-one problems are PSPACE-complete as well, with width at
most three, and also with at most three occurrences of each variable. -/
theorem line_exact_one : ComplexityAbstract.PSPACEComplete formulaEncoding.encode
    (fun f => ExactlyOneSatisfiable f ∧ OneDimensional f ∧ LocalFormula f ∧ WidthAtMost 3 f) :=
  GraphAbstractBridge.Data.line_exact_one
theorem line_exact_one_three : ComplexityAbstract.PSPACEComplete formulaEncoding.encode
    (fun f => ExactlyOneSatisfiable f ∧ OneDimensional f ∧ LocalFormula f ∧
      WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  GraphAbstractBridge.Data.line_exact_one_three

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
theorem cook_levin : ComplexityAbstract.NPHard formulaEncoding.encode
    (fun f => Satisfiable f ∧ ZeroDimensional f ∧ WidthAtMost 3 f) :=
  GraphAbstractBridge.Data.cook_levin

/-! ## Planar SAT, three-dimensional matching, and orientation -/

/-- A planar SAT input is a formula and a supplied polygonal drawing of its
variable/clause incidence graph. Its compatibility check matches every edge
end and separates vertex orbits; continuous planarity excludes all contacts
except common endpoints. The ordinary and exact-one line problems also
require locality, width three, zero vertical offsets, and the proved linear
grid bound (8847360 and 637009920 times clause-plus-literal count plus one).
The binary encoding includes every drawing coordinate and route point. -/
abbrev PlanarInput := PeriodicPlanarSAT.Input ℕ
abbrev planarEncoding := PeriodicPlanarSAT.FlatEncoding.finEncoding
def PlanarSAT (i : PlanarInput) : Prop :=
  Satisfiable i.1 ∧ PeriodicPlanarSAT.GridBound 8847360 i ∧ LocalFormula i.1 ∧
    (WidthAtMost 3 i.1 ∧ PeriodicGridDrawing.OrbitCertificate.Compatible i.1.incidenceGraph i.2) ∧
    i.2.IsContinuouslyPlanar
def PlanarExactOne (i : PlanarInput) : Prop :=
  ExactlyOneSatisfiable i.1 ∧ PeriodicPlanarSAT.GridBound 637009920 i ∧ LocalFormula i.1 ∧
    (WidthAtMost 3 i.1 ∧ PeriodicGridDrawing.FiniteCertificate.Compatible i.1.incidenceGraph i.2) ∧
    i.2.IsContinuouslyPlanar
def PlanarLineSAT (i : PlanarInput) : Prop :=
  PlanarSAT i ∧ OneDimensional i.1
def PlanarLineExactOne (i : PlanarInput) : Prop :=
  PlanarExactOne i ∧ OneDimensional i.1

/-- Theorems 3.5–3.6, plane case: all four local supplied-drawing problems
are co-r.e.-complete, even with the stated linear grid bound. -/
theorem planar_plane_sat : LeanWang.CoREComplete PlanarSAT :=
  GraphAbstractBridge.Data.planar_plane_sat
theorem planar_plane_three_occurrences : LeanWang.CoREComplete
    (fun i => PlanarSAT i ∧ OccurrencesAtMost 3 i.1) :=
  GraphAbstractBridge.Data.planar_plane_three_occurrences
theorem planar_plane_exact_one : LeanWang.CoREComplete PlanarExactOne :=
  GraphAbstractBridge.Data.planar_plane_exact_one
theorem planar_plane_exact_one_three : LeanWang.CoREComplete
    (fun i => PlanarExactOne i ∧ OccurrencesAtMost 3 i.1) :=
  GraphAbstractBridge.Data.planar_plane_exact_one_three

/-- Theorems 3.5–3.6, line case: all four supplied-drawing problems are
PSPACE-complete, including the at-most-three-occurrence variants. -/
theorem planar_line_sat : ComplexityAbstract.PSPACEComplete planarEncoding.encode PlanarLineSAT :=
  GraphAbstractBridge.Data.planar_line_sat
theorem planar_line_three_occurrences : ComplexityAbstract.PSPACEComplete planarEncoding.encode
    (fun i => PlanarLineSAT i ∧ OccurrencesAtMost 3 i.1) :=
  GraphAbstractBridge.Data.planar_line_three_occurrences
theorem planar_line_exact_one : ComplexityAbstract.PSPACEComplete planarEncoding.encode PlanarLineExactOne :=
  GraphAbstractBridge.Data.planar_line_exact_one
theorem planar_line_exact_one_three : ComplexityAbstract.PSPACEComplete planarEncoding.encode
    (fun i => PlanarLineExactOne i ∧ OccurrencesAtMost 3 i.1) :=
  GraphAbstractBridge.Data.planar_line_exact_one_three

/-- A periodic three-dimensional matching instance lists three color-class sizes
and prototype triples. The lattice is ℤ²; triples have three color classes.
Each triple has one (atom,offset) reference per color. A selection chooses
triples at lattice translates; exactly one selected triple must cover each
translated element. Every reference is in range, and every element has degree
two or three. Plane inputs also carry a checked orthogonal planar drawing. -/
abbrev PeriodicThreeDMInput := PeriodicThreeDM.NormalizationCompiler.Input
def Matches (p : PeriodicThreeDM) : Prop :=
  ∃ selected : ℕ → Cell → Bool, ∀ color atom, atom < p.elementCount color → ∀ (z : Cell),
    ((p.incidences color atom).map fun i =>
      selected i.tripleIndex (z.1-i.offset.1, z.2-i.offset.2)).count true = 1
def ThreeDMPlane (i : PeriodicThreeDMInput) : Prop :=
  Matches i.problem ∧ i.problem.IsLocal ∧ i.problem.IsWellFormed ∧
    i.problem.DegreeTwoOrThree ∧
    PeriodicThreeDM.FiniteDrawingCertificate.verifies i.problem i.drawing = true
def ThreeDMLine (p : PeriodicThreeDM) : Prop :=
  Matches p ∧ p.IsWellFormed ∧ p.DegreeTwoOrThree ∧ p.IsOneDimensional ∧ p.IsLocal

/-- Theorem 3.7: local planar colored degree-two-or-three 3DM is co-r.e.-complete
in the plane, and PSPACE-complete on the line with or without a supplied drawing. -/
theorem three_dm_plane : LeanWang.CoREComplete ThreeDMPlane :=
  GraphAbstractBridge.Data.three_dm_plane
theorem three_dm_line : ComplexityAbstract.PSPACEComplete PeriodicThreeDM.FlatEncoding.finEncoding.encode
    ThreeDMLine :=
  GraphAbstractBridge.Data.three_dm_line
theorem three_dm_planar_line : ComplexityAbstract.PSPACEComplete PeriodicThreeDM.FlatEncoding.Planar.finEncoding.encode
    (fun i => ThreeDMLine i.problem ∧
      PeriodicThreeDM.FiniteDrawingCertificate.verifies i.problem i.drawing = true) :=
  GraphAbstractBridge.Data.three_dm_planar_line

/-- A colored graph has a list of vertex kinds and colored edges. Every vertex
has three edge ends, all one color at a monochromatic vertex and one of each
color at a trichromatic vertex. A valid orientation has indegree one at the
former and indegree zero or three at the latter. Edge directions are chosen
independently at every translate; loops contribute both ends. -/
abbrev OrientationInput := TrichromaticGraphOrientation.Input
def IsOrientation (i : OrientationInput) (a : ℕ → Cell → Bool) : Prop :=
  ∀ (z : Cell) v, v < i.1.length → if i.1.getD v false then
    (∀ l ∈ TrichromaticGraphOrientation.incoming i v,
      ∀ r ∈ TrichromaticGraphOrientation.incoming i v,
      (a l.atom (z.1+l.offset.1,z.2+l.offset.2) = l.value) ↔
        (a r.atom (z.1+r.offset.1,z.2+r.offset.2) = r.value))
  else ((TrichromaticGraphOrientation.incoming i v).map fun l =>
    a l.atom (z.1+l.offset.1,z.2+l.offset.2) == l.value).count true = 1
def Orientable (i : OrientationInput) : Prop := ∃ a, IsOrientation i a
def OrientationProblem (i : OrientationInput) : Prop :=
  Orientable i ∧ TrichromaticGraphOrientation.IsWellFormed i
def OrientationLocal (i : OrientationInput) : Prop :=
  OrientationProblem i ∧ ∀ e ∈ i.2, e.1.offset.1.natAbs+e.1.offset.2.natAbs ≤ 1
def OrientationLine (i : OrientationInput) : Prop :=
  OrientationLocal i ∧ ∀ e ∈ i.2, e.1.offset.2 = 0
def OrientationFinite (i : OrientationInput) : Prop :=
  (∃ a : ℕ → Bool, IsOrientation i (fun e _ => a e)) ∧
    TrichromaticGraphOrientation.IsWellFormed i ∧ ∀ e ∈ i.2, e.1.offset = (0,0)

/-- Theorem 3.8: local colored orientation is co-r.e.-complete in the plane,
PSPACE-complete for local line inputs, and NP-complete for finite inputs.
The line and finite classifications use lossless binary graph encodings;
finite inputs require every offset to be zero. -/
theorem orientation_plane : LeanWang.CoREComplete OrientationLocal :=
  GraphAbstractBridge.Data.orientation_plane
theorem orientation_line : ComplexityAbstract.PSPACEComplete TrichromaticGraphOrientation.FlatEncoding.finEncoding.encode
    OrientationLine :=
  GraphAbstractBridge.Data.orientation_line
theorem orientation_finite : ComplexityAbstract.NPComplete TrichromaticGraphOrientation.FlatEncoding.finEncoding.encode
    OrientationFinite :=
  GraphAbstractBridge.Data.orientation_finite

/-! ## Period-one models and polynomial algorithms -/

/-- A periodic Horn rule has a list of (variable,offset) premises and an
optional conclusion: `none` means false. At every translate, truth of every
premise forces its conclusion. Dual Horn reverses all Boolean values.
Offsets may belong to any additive group, with no locality assumption. -/
abbrev HornRule := Horn.PeriodicRule
abbrev HornSatisfiable := @Horn.PeriodicSatisfiable

/-- Theorem 4.2: a satisfiable periodic Horn instance has a model constant
on all translates of each variable; the same holds for dual Horn. -/
theorem horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule V G))
    (h : HornSatisfiable rules) :
    ∃ a : V → Prop, Horn.PeriodicSatisfies rules (fun v _ => a v) :=
  GraphAbstractBridge.Data.horn_period_one rules h
theorem dual_horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule V G))
    (h : Horn.PeriodicDualSatisfiable rules) :
    ∃ a : V → Prop, Horn.PeriodicDualSatisfies rules (fun v _ => a v) :=
  GraphAbstractBridge.Data.dual_horn_period_one rules h

/-- The indexed Horn worklist algorithm decides Horn and dual Horn SAT in at
most 72(n+m+L+2) indexed operations. Variables are explicitly indexed by `Fin n`,
m is the rule count, and L counts all premise occurrences, including repeats. -/
theorem horn_linear {n : ℕ} {G : Type} [AddGroup G]
    (rules : Array (HornRule (Fin n) G)) :
    (Horn.PeriodicIndexed.check rules = true ↔ HornSatisfiable rules.toList) ∧
    (Horn.PeriodicIndexed.check rules = true ↔ Horn.PeriodicDualSatisfiable rules.toList) ∧
    Horn.PeriodicIndexed.totalCost rules ≤ 72*Horn.PeriodicIndexed.inputSize rules :=
  GraphAbstractBridge.Data.horn_linear rules

/-- Theorem 4.1: periodic 2SAT has an executable polynomial-cost decision in
every fixed dimension. Clauses have at most two literals (a repeated literal
encodes a unit); `none` encodes an empty clause. Locality bounds differences
of offsets coordinatewise by one, allowing arbitrarily large common offsets.
The bound includes clause normalization and finite-cover construction. -/
theorem two_sat_polynomial {n d : ℕ} (f : PeriodicTwoSAT.Formula (Fin n) d)
    (locality : PeriodicTwoSAT.LocalDifferences f) :
    ((PeriodicTwoSAT.solveLocal f).1 = true ↔ PeriodicTwoSAT.Satisfiable f) ∧
      (PeriodicTwoSAT.solveLocal f).2 ≤
        PeriodicTwoSAT.localCoefficient d*(PeriodicTwoSAT.inputSize f)^(PeriodicTwoSAT.degree d) :=
  GraphAbstractBridge.Data.two_sat_polynomial f locality

/-! ## Periodic matchings -/

/-- A bipartite protoedge has `left`, `right`, and an offset in ℤᵈ. It joins
(left,z) to (right,z+offset). A perfect matching is an adjacency-preserving
bijection of the two lifted color classes. A period-one matching commutes
with every lattice translation; a quotient matching ignores offsets. -/
abbrev BipartiteEdge := PeriodicBipartite.Edge
def PerfectMatching {L R : Type} {d : ℕ} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d), ∀ u, ∃ e ∈ es,
    e.left = u.1 ∧ e.right = (f u).1 ∧ (f u).2 = u.2+e.offset
def PeriodOneMatching {L R : Type} {d : ℕ} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d),
    (∀ u, ∃ e ∈ es, e.left = u.1 ∧ e.right = (f u).1 ∧ (f u).2 = u.2+e.offset) ∧
    ∀ l z t, f (l,z+t) = ((f (l,z)).1, (f (l,z)).2+t)
def QuotientMatching {L R : Type} {d : ℕ} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : L ≃ R, ∀ l, ∃ e ∈ es, e.left = l ∧ e.right = f l

/-- Theorem 4.6: in every dimension, perfect matching is equivalent to finite
quotient matching and admits a period-one witness. Offsets need not be local. -/
theorem matching_period_one {L R : Type} [Fintype L] [Fintype R] {d : ℕ}
    (es : List (BipartiteEdge L R d)) :
    (PerfectMatching es ↔ QuotientMatching es) ∧
      (PerfectMatching es → PeriodOneMatching es) :=
  GraphAbstractBridge.Data.matching_period_one es

/-- Theorem 4.7: the algorithm returns `none` exactly when there is no perfect
matching; otherwise its table chooses one protoedge at each left vertex and
gives a period-one perfect matching. With E edges and V vertex slots its
instrumented cost bound is 1000(E+1)(⌊√V⌋+1), and at most 4000E⌊√V⌋ when E>0. -/
theorem matching_algorithm {n m d : ℕ} (es : List (BipartiteEdge (Fin n) (Fin m) d)) :
    ((PeriodicBipartite.matchingSolver es).table.isSome = true ↔ PerfectMatching es) ∧
    PeriodicBipartite.MatchingResultSpec es (PeriodicBipartite.matchingSolver es).table ∧
    (PeriodicBipartite.matchingSolver es).cost ≤ 1000*(es.length+1)*(Nat.sqrt (n+m)+1) :=
  GraphAbstractBridge.Data.matching_algorithm es

theorem matching_nonempty_cost {n m d : ℕ} (es : List (BipartiteEdge (Fin n) (Fin m) d))
    (nonempty : 0 < es.length) :
    (PeriodicBipartite.matchingSolver es).cost ≤ 4000*es.length*Nat.sqrt (n+m) :=
  GraphAbstractBridge.Data.matching_nonempty_cost es nonempty

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

/-- Lemma 4.5: a period-one partial matching of a bipartite periodic graph
with a perfect matching is either perfect already or has an augmenting path
with distinct projected protovertices and fewer than |L|+|R| edges. These
properties are the `protoSimple` and `length` fields of `ShortAugmentingPath`. -/
theorem short_augmenting_path {L R : Type} [DecidableEq L] [DecidableEq R]
    [Fintype L] [Fintype R] {d : ℕ} (es : List (BipartiteEdge L R d))
    (perfect : PerfectMatching es) (matching : PeriodicBipartite.PeriodOnePartial es) :
    PeriodicBipartite.PerfectPartial matching ∨ Nonempty (PeriodicBipartite.ShortAugmentingPath matching) :=
  GraphAbstractBridge.Data.short_augmenting_path es perfect matching

end LeanTrominoes.GraphAbstract
