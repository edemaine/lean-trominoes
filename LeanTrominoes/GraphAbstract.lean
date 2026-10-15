/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
answer-preserving map. `Complexity.PSPACEComplete` and `NPComplete` mean
membership and hardness under polynomial-time many-one reductions. PSPACE
uses always-halting finite-alphabet Turing machines with polynomial space;
NP uses polynomial-length binary witnesses checked by polynomial-time
finite-alphabet machines. Each bounded-complexity theorem names its encoding.
RAM bounds below count the stated indexed operations, with scalar arithmetic
and array access of unit cost; they are not bit-Turing running-time bounds.
-/

namespace LeanTrominoes.GraphAbstract

/-! ## Periodic graphs and polygonal drawings -/

/-- A cell is an integer pair. A graph has finite lists `vertices` and `edges`;
each edge has `source`, `target`, and an integer-pair `offset`. Its translate
at z joins (source,z) to (target,z+offset), as an undirected edge. -/
abbrev Cell := ℤ × ℤ
abbrev Graph (V : Type) := PeriodicGraph V
abbrev Edge (V : Type) := PeriodicEdge V

def Adjacent {V : Type} (g : Graph V) (u v : V × Cell) : Prop :=
  ∃ e ∈ g.edges,
    (u = (e.source, (v.2.1-e.offset.1, v.2.2-e.offset.2)) ∧ v.1 = e.target) ∨
    (v = (e.source, (u.2.1-e.offset.1, u.2.2-e.offset.2)) ∧ u.1 = e.target)

/-- A well-formed graph lists distinct vertices and names only listed endpoints.
Locality means Manhattan offset at most one; degree counts edge ends, twice
for a loop. -/
def WellFormed {V : Type} (g : Graph V) : Prop :=
  g.vertices.Nodup ∧ ∀ e ∈ g.edges, e.source ∈ g.vertices ∧ e.target ∈ g.vertices
def Local {V : Type} (g : Graph V) : Prop :=
  ∀ e ∈ g.edges, e.offset.1.natAbs + e.offset.2.natAbs ≤ 1
def DegreeAtMost {V : Type} [DecidableEq V] (k : ℕ) (g : Graph V) : Prop :=
  ∀ v, (g.edges.flatMap fun e => [e.source, e.target]).count v ≤ k

/-- A drawing records a positive square period `gridSize = gridSizePred+1`,
integer `vertexPositions` in vertex-list order, and polygonal `edgeRoutes`
in edge-list order. Consecutive points give closed straight segments in ℝ².
`RealContains` and `RealIsEndpoint` mean membership in such a polygonal route
and equality to its first or last point. -/
abbrev Drawing := PeriodicGridDrawing
abbrev RouteContains := GridPolyline.RealContains
abbrev RouteEndpoint := GridPolyline.RealIsEndpoint
abbrev SimpleRoute := GridPolyline.IsRealSimple

/-- A drawing matches its graph when endpoints, list lengths, distinct vertex
positions, and positions in the fundamental square agree. It is a genuine
drawing when routes are simple (simple closed loops are allowed) and no
translated vertex lies in a route interior. It is planar when distinct
translated edge routes meet only at their endpoints. -/
def IsDrawing {V : Type} [DecidableEq V] (g : Graph V) (d : Drawing) : Prop :=
  d.IsCompatible g ∧ d.RealRoutesAreSimple ∧ d.RealVerticesAvoidRoutes
def PlanarDrawing {V : Type} [DecidableEq V] (g : Graph V) (d : Drawing) : Prop :=
  IsDrawing g d ∧ d.RealRoutesMeetOnlyAtEndpoints
def Planar {V : Type} [DecidableEq V] (g : Graph V) : Prop :=
  ∃ d : Drawing, PlanarDrawing g d

/-- Orthogonal routes use horizontal and vertical segments. An orthocrossing
drawing permits additional contacts only as perpendicular interior crossings.
A local drawing keeps each edge in the two period cells of its endpoints. -/
abbrev Orthogonal := PeriodicGridDrawing.IsOrthogonal
abbrev Orthocrossing := PeriodicGridDrawing.IsRealOrthocrossing
abbrev LocalDrawing := @PeriodicGridDrawing.IsRealLocal

/-- Theorem 2.1: every well-formed local periodic graph has a simple local
orthocrossing drawing on a linear-size grid, including loops and isolated
vertices. With degree at most four the drawing can also be orthogonal. -/
theorem orthocrossing_drawing {V : Type} [DecidableEq V] (g : Graph V)
    (valid : WellFormed g) (locality : Local g) :
    ∃ d : Drawing, IsDrawing g d ∧ LocalDrawing d g ∧ Orthocrossing d ∧
      d.gridSize ≤ 16*(g.vertices.length+g.edges.length+1) := by
  obtain ⟨d, h, hl, hc, hb, _⟩ := GraphAbstractBridge.local_orthocrossing_drawing valid locality
  exact ⟨d, h, hl, hc, hb⟩

theorem orthogonal_orthocrossing_drawing {V : Type} [DecidableEq V] (g : Graph V)
    (valid : WellFormed g) (locality : Local g) (degree : DegreeAtMost 4 g) :
    ∃ d : Drawing, IsDrawing g d ∧ LocalDrawing d g ∧ Orthocrossing d ∧
      Orthogonal d ∧ d.gridSize ≤ 16*(g.vertices.length+g.edges.length+1) := by
  obtain ⟨d, h, hl, hc, ho, hb, _⟩ :=
    GraphAbstractBridge.local_orthogonal_orthocrossing_drawing valid locality degree
  exact ⟨d, h, hl, hc, ho, hb⟩

/-- Theorem 2.2: a planar local polygonal drawing of degree at most four has
a planar local orthogonal refinement of period at most 84480 M³. Original
vertices are scaled by exactly (16M+32)(160M+1600), with M the old period. -/
theorem orthogonal_refinement {V : Type} [DecidableEq V] (g : Graph V) (d : Drawing)
    (planar : PlanarDrawing g d) (degree : DegreeAtMost 4 g)
    (locality : Local g) (routes : LocalDrawing d g) :
    ∃ out : Drawing, PlanarDrawing g out ∧ LocalDrawing out g ∧ Orthogonal out ∧
      out.gridSize ≤ 84480*d.gridSize^3 ∧
      out.vertexPositions = d.vertexPositions.map
        (fun p => ((((16*d.gridSize+32)*(160*d.gridSize+1600) : ℕ) : ℤ)*p.1,
          (((16*d.gridSize+32)*(160*d.gridSize+1600) : ℕ) : ℤ)*p.2)) := by
  exact GraphAbstractBridge.polygonal_cubic_refinement planar degree locality routes

/-- Lemma 2.3: select one incidence at each degree-three vertex. Scaling the
drawing by 32 preserves planarity and orthogonality and makes the selected
incidence point west; the other two point north and east. Locality is preserved.
A `GraphPort` identifies an edge end, distinguishing both ends of a loop. -/
theorem normalize_incidence_directions {V : Type} [DecidableEq V] (g : Graph V) (d : Drawing)
    (planar : PlanarDrawing g d) (orthogonal : Orthogonal d)
    (chosen : V → PeriodicOrthocrossing.GraphPort V) (selection : GeneralVertexNormalization.SelectedIncidences g chosen) :
    ∃ out : Drawing, PlanarDrawing g out ∧ Orthogonal out ∧
      GeneralVertexNormalization.IsNormalized g out chosen ∧ out.gridSize = 32*d.gridSize ∧
      out.vertexPositions = d.vertexPositions.map (LeanTrominoes.Cell.scale 32) ∧
      (LocalDrawing d g → LocalDrawing out g) :=
  GraphAbstractBridge.lemma23 planar orthogonal chosen selection

/-! ## Boolean constraints and their complexity -/

/-- A literal has an `atom : ℕ`, an integer-pair `offset`, and a Boolean
`value`. A formula has a finite list `clauses` of lists of literals. Clauses
are imposed at every translate. Duplicate literals count as occurrences;
empty clauses are false. A line formula uses zero vertical offsets. -/
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
def OnLine (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.offset.2 = 0

/-- Line satisfiability assigns a Boolean to every variable at every integer.
The flat binary encoding lists clause lengths and literal fields, including
signed coordinates; invalid locality and width restrictions are rejected. -/
def LineSAT (f : Formula) : Prop :=
  OnLine f ∧ f.IsLocalOnLine ∧ ∃ a : ℕ → ℤ → Bool,
    ∀ (z : ℤ) c, c ∈ f.clauses → ∃ l ∈ c, a l.atom (z+l.offset.1) = l.value
abbrev formulaEncoding := PeriodicCNFFlatEncoding.finEncoding

/-- Theorems 3.2–3.4: local line SAT remains PSPACE-complete with width at
most three and with at most three occurrences of each variable. -/
theorem line_sat : Complexity.PSPACEComplete formulaEncoding LineSAT :=
  GraphAbstractBridge.localPeriodicCNF1DSAT_PSPACEComplete
theorem line_three_sat : Complexity.PSPACEComplete formulaEncoding
    (fun f => WidthAtMost 3 f ∧ LineSAT f) :=
  GraphAbstractBridge.localPeriodicThreeCNF1DSAT_PSPACEComplete
theorem line_three_sat_three : Complexity.PSPACEComplete formulaEncoding
    (fun f => OccurrencesAtMost 3 f ∧ WidthAtMost 3 f ∧ LineSAT f) :=
  GraphAbstractBridge.localPeriodicThreeSATThree1DSAT_PSPACEComplete

/-- The plane classifications also hold for local width-three formulas and
for their occurrence-three restriction. Natural numbers are the atom names. -/
theorem plane_three_sat : LeanWang.CoREComplete
    (fun f => LocalFormula f ∧ WidthAtMost 3 f ∧ Satisfiable f) :=
  GraphAbstractBridge.plane_three_sat
theorem plane_three_sat_three : LeanWang.CoREComplete
    (fun f => LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f ∧ Satisfiable f) :=
  GraphAbstractBridge.plane_three_sat_three

/-- Exact-one satisfaction counts true literal occurrences, so two copies
of the same literal are not silently identified. -/
def ExactlyOneSatisfiable (f : Formula) : Prop :=
  ∃ a : ℕ → Cell → Bool, ∀ (z : Cell) c, c ∈ f.clauses →
    (c.map fun l => a l.atom (z.1+l.offset.1, z.2+l.offset.2) == l.value).count true = 1

theorem plane_exact_one : LeanWang.CoREComplete
    (fun f => LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f ∧
      ExactlyOneSatisfiable f) := GraphAbstractBridge.plane_exact_one

/-- The line exact-one problems are PSPACE-complete as well, with width at
most three, and also with at most three occurrences of each variable. -/
theorem line_exact_one : Complexity.PSPACEComplete formulaEncoding
    (fun f => WidthAtMost 3 f ∧ OnLine f ∧ LocalFormula f ∧ ExactlyOneSatisfiable f) :=
  GraphAbstractBridge.localOneDimensionalThreeSAT_PSPACEComplete
theorem line_exact_one_three : Complexity.PSPACEComplete formulaEncoding
    (fun f => OccurrencesAtMost 3 f ∧ WidthAtMost 3 f ∧
      OnLine f ∧ LocalFormula f ∧ ExactlyOneSatisfiable f) :=
  GraphAbstractBridge.localOneDimensionalThreeSATThree_PSPACEComplete

/-- A d-dimensional formula is a list of clauses of ((variable,offset),value)
literals, with offset in ℤᵈ. A satisfying assignment need not be periodic. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev FormulaIn (d : ℕ) := List (List ((ℕ × Lattice d) × Bool))
def SatisfiableIn {d : ℕ} (f : FormulaIn d) : Prop :=
  ∃ a : ℕ → Lattice d → Bool, ∀ z c, c ∈ f → ∃ l ∈ c, a l.1.1 (z+l.1.2) = l.2
def LocalIn {d : ℕ} (f : FormulaIn d) : Prop :=
  ∀ c ∈ f, ∀ l ∈ c, ∀ r ∈ c, ∑ i, (l.1.2 i-r.1.2 i).natAbs ≤ 1

/-- Theorem 3.2: unrestricted and local periodic CNF SAT are co-r.e.-complete
in every dimension at least two. -/
theorem higher_dimensional_sat (d : ℕ) (dimension : 2 ≤ d) :
    LeanWang.CoREComplete (@SatisfiableIn d) ∧
      LeanWang.CoREComplete (fun f : FormulaIn d => LocalIn f ∧ SatisfiableIn f) :=
  ⟨GraphAbstractBridge.satisfiable_coREComplete dimension,
    GraphAbstractBridge.higher_local_sat d dimension⟩

/-- Cook–Levin: finite width-three CNF SAT is NP-hard under its native binary
formula encoding. Here finite literals have only an atom and a Boolean value. -/
def FiniteThreeSAT (f : List (List (ℕ × Bool))) : Prop :=
  (∀ c ∈ f, c.length ≤ 3) ∧ ∃ a : ℕ → Bool, ∀ c ∈ f, ∃ l ∈ c, a l.1 = l.2
theorem cook_levin : Complexity.NPHard FiniteCNFCompiler.finEncoding FiniteThreeSAT :=
  GraphAbstractBridge.threeSatisfiable_npHard

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
  PeriodicPlanarSAT.GridBound 8847360 i ∧ LocalFormula i.1 ∧
    (WidthAtMost 3 i.1 ∧ PeriodicGridDrawing.OrbitCertificate.Compatible i.1.incidenceGraph i.2) ∧
    i.2.IsContinuouslyPlanar ∧ Satisfiable i.1
def PlanarExactOne (i : PlanarInput) : Prop :=
  PeriodicPlanarSAT.GridBound 637009920 i ∧ LocalFormula i.1 ∧
    (WidthAtMost 3 i.1 ∧ PeriodicGridDrawing.FiniteCertificate.Compatible i.1.incidenceGraph i.2) ∧
    i.2.IsContinuouslyPlanar ∧ ExactlyOneSatisfiable i.1
def PlanarLineSAT (i : PlanarInput) : Prop :=
  OnLine i.1 ∧ PlanarSAT i
def PlanarLineExactOne (i : PlanarInput) : Prop :=
  OnLine i.1 ∧ PlanarExactOne i

/-- Theorems 3.5–3.6, plane case: all four local supplied-drawing problems
are co-r.e.-complete, even with the stated linear grid bound. -/
theorem planar_plane_sat : LeanWang.CoREComplete PlanarSAT := GraphAbstractBridge.planar_plane_sat
theorem planar_plane_three_occurrences : LeanWang.CoREComplete
    (fun i => OccurrencesAtMost 3 i.1 ∧ PlanarSAT i) := GraphAbstractBridge.planar_plane_three_sat
theorem planar_plane_exact_one : LeanWang.CoREComplete PlanarExactOne :=
  GraphAbstractBridge.planar_plane_exact_one
theorem planar_plane_exact_one_three : LeanWang.CoREComplete
    (fun i => OccurrencesAtMost 3 i.1 ∧ PlanarExactOne i) := GraphAbstractBridge.planar_plane_exact_one_three

/-- Theorems 3.5–3.6, line case: all four supplied-drawing problems are
PSPACE-complete, including the at-most-three-occurrence variants. -/
theorem planar_line_sat : Complexity.PSPACEComplete planarEncoding PlanarLineSAT :=
  GraphAbstractBridge.ordinary_PSPACEComplete
theorem planar_line_three_occurrences : Complexity.PSPACEComplete planarEncoding
    (fun i => OccurrencesAtMost 3 i.1 ∧ PlanarLineSAT i) := GraphAbstractBridge.planar_line_three_sat
theorem planar_line_exact_one : Complexity.PSPACEComplete planarEncoding PlanarLineExactOne :=
  GraphAbstractBridge.exactOne_PSPACEComplete
theorem planar_line_exact_one_three : Complexity.PSPACEComplete planarEncoding
    (fun i => OccurrencesAtMost 3 i.1 ∧ PlanarLineExactOne i) := GraphAbstractBridge.planar_line_exact_one_three

/-- A periodic 3DM instance lists three color-class sizes and prototype triples.
Each triple has one (atom,offset) reference per color. A selection chooses
triples at lattice translates; exactly one selected triple must cover each
translated element. Every reference is in range, and every element has degree
two or three. Plane inputs also carry a checked orthogonal planar drawing. -/
abbrev ThreeDM := PeriodicThreeDM
abbrev ThreeDMInput := PeriodicThreeDM.NormalizationCompiler.Input
def Matches (p : ThreeDM) : Prop :=
  ∃ selected : ℕ → Cell → Bool, ∀ color atom, atom < p.elementCount color → ∀ (z : Cell),
    ((p.incidences color atom).map fun i =>
      selected i.tripleIndex (z.1-i.offset.1, z.2-i.offset.2)).count true = 1
def ThreeDMPlane (i : ThreeDMInput) : Prop :=
  i.problem.IsLocal ∧ i.problem.IsWellFormed ∧ i.problem.DegreeTwoOrThree ∧
    PeriodicThreeDM.FiniteDrawingCertificate.verifies i.problem i.drawing = true ∧ Matches i.problem
def ThreeDMLine (p : ThreeDM) : Prop :=
  p.IsWellFormed ∧ p.DegreeTwoOrThree ∧ p.IsOneDimensional ∧ p.IsLocal ∧ Matches p

/-- Theorem 3.7: local planar colored degree-two-or-three 3DM is co-r.e.-complete
in the plane, and PSPACE-complete on the line with or without a supplied drawing. -/
theorem three_dm_plane : LeanWang.CoREComplete ThreeDMPlane :=
  GraphAbstractBridge.localPlaneProblem_coREComplete
theorem three_dm_line : Complexity.PSPACEComplete PeriodicThreeDM.FlatEncoding.finEncoding
    ThreeDMLine := GraphAbstractBridge.localLineProblem_PSPACEComplete
theorem three_dm_planar_line : Complexity.PSPACEComplete PeriodicThreeDM.FlatEncoding.Planar.finEncoding
    (fun i => ThreeDMLine i.problem ∧
      PeriodicThreeDM.FiniteDrawingCertificate.verifies i.problem i.drawing = true) :=
  GraphAbstractBridge.localPlanarLineProblem_PSPACEComplete

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
  TrichromaticGraphOrientation.IsWellFormed i ∧ Orientable i
def OrientationLocal (i : OrientationInput) : Prop :=
  (∀ e ∈ i.2, e.1.offset.1.natAbs+e.1.offset.2.natAbs ≤ 1) ∧ OrientationProblem i
def OrientationLine (i : OrientationInput) : Prop :=
  OrientationLocal i ∧ ∀ e ∈ i.2, e.1.offset.2 = 0
def OrientationFinite (i : OrientationInput) : Prop :=
  TrichromaticGraphOrientation.IsWellFormed i ∧ (∀ e ∈ i.2, e.1.offset = (0,0)) ∧
    ∃ a : ℕ → Bool, IsOrientation i (fun e _ => a e)

/-- Theorem 3.8: local colored orientation is co-r.e.-complete in the plane,
PSPACE-complete for local line inputs, and NP-complete for finite inputs.
The line and finite classifications use lossless binary graph encodings;
finite inputs require every offset to be zero. -/
theorem orientation_plane : LeanWang.CoREComplete OrientationLocal :=
  GraphAbstractBridge.orientation_plane
theorem orientation_line : Complexity.PSPACEComplete
    TrichromaticGraphOrientation.FlatEncoding.finEncoding
    OrientationLine := GraphAbstractBridge.orientation_line
theorem orientation_finite : Complexity.NPComplete
    TrichromaticGraphOrientation.FlatEncoding.finEncoding
    OrientationFinite := GraphAbstractBridge.finiteProblem_npComplete

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
  GraphAbstractBridge.exists_period_one rules h
theorem dual_horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule V G))
    (h : Horn.PeriodicDualSatisfiable rules) :
    ∃ a : V → Prop, Horn.PeriodicDualSatisfies rules (fun v _ => a v) :=
  GraphAbstractBridge.dual_exists_period_one rules h

/-- The indexed Horn worklist algorithm decides Horn and dual Horn SAT in at
most 72(n+m+L+2) RAM operations. Variables are explicitly indexed by `Fin n`,
m is the rule count, and L counts all premise occurrences, including repeats. -/
theorem horn_linear {n : ℕ} {G : Type} [AddGroup G]
    (rules : Array (HornRule (Fin n) G)) :
    (Horn.PeriodicIndexed.check rules = true ↔ HornSatisfiable rules.toList) ∧
    (Horn.PeriodicIndexed.check rules = true ↔ Horn.PeriodicDualSatisfiable rules.toList) ∧
    Horn.PeriodicIndexed.totalCost rules ≤ 72*Horn.PeriodicIndexed.inputSize rules :=
  GraphAbstractBridge.certified rules

/-- Theorem 4.1: periodic 2SAT has an executable polynomial RAM decision in
every fixed dimension. Clauses have at most two literals (a repeated literal
encodes a unit); `none` encodes an empty clause. Locality bounds differences
of offsets coordinatewise by one, allowing arbitrarily large common offsets.
The bound includes clause normalization and finite-cover construction. -/
theorem two_sat_polynomial {n d : ℕ} (f : PeriodicTwoSAT.Formula (Fin n) d)
    (locality : PeriodicTwoSAT.LocalDifferences f) :
    ((PeriodicTwoSAT.solveLocal f).1 = true ↔ PeriodicTwoSAT.Satisfiable f) ∧
      (PeriodicTwoSAT.solveLocal f).2 ≤
        PeriodicTwoSAT.localCoefficient d*(PeriodicTwoSAT.inputSize f)^(PeriodicTwoSAT.degree d) :=
  GraphAbstractBridge.local_certified f locality

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
  ⟨GraphAbstractBridge.perfect_iff_quotient es, GraphAbstractBridge.exists_period_one es⟩

/-- Theorem 4.7: the algorithm returns `none` exactly when there is no perfect
matching; otherwise its table chooses one protoedge at each left vertex and
gives a period-one perfect matching. With E edges and V vertex slots its
uniform RAM budget is 1000(E+1)(⌊√V⌋+1), and at most 4000E⌊√V⌋ when E>0. -/
theorem matching_algorithm {n m d : ℕ} (es : List (BipartiteEdge (Fin n) (Fin m) d)) :
    ((PeriodicBipartite.matchingSolver es).table.isSome = true ↔ PerfectMatching es) ∧
    PeriodicBipartite.MatchingResultSpec es (PeriodicBipartite.matchingSolver es).table ∧
    (PeriodicBipartite.matchingSolver es).cost ≤ 1000*(es.length+1)*(Nat.sqrt (n+m)+1) :=
  GraphAbstractBridge.matchingSolver_certified es

theorem matching_nonempty_cost {n m d : ℕ} (es : List (BipartiteEdge (Fin n) (Fin m) d))
    (nonempty : 0 < es.length) :
    (PeriodicBipartite.matchingSolver es).cost ≤ 4000*es.length*Nat.sqrt (n+m) :=
  GraphAbstractBridge.matchingSolver_edge_sqrt_bound es nonempty

/-- Lemma 4.4: every proper two-coloring of a connected periodic graph is
invariant under twice every translation, in every dimension. An `Arc` has
source, target, and offset; adjacency forgets its direction. -/
theorem bipartition_doubled {V : Type} {d : ℕ}
    (es : List (PeriodicLatticeGraph.Arc V d)) (connected : PeriodicLatticeGraph.Connected es)
    (color : V × Lattice d → Bool) (proper : PeriodicLatticeGraph.ProperColoring es color)
    (v : V) (z t : Lattice d) : color (v, z+(t+t)) = color (v,z) :=
  GraphAbstractBridge.bipartition_two_periodic es connected color proper v z t

/-- Lemma 4.3: if a local periodic graph has any perfect matching, every free
vertex of a period-one partial matching starts a simple augmenting path of
coordinate diameter at most 2dE. No bipartiteness assumption is required.
A partial matching pairs some adjacent vertices mutually; period one means
that the partner function commutes with translations. An augmenting path is
simple, has free ends, and alternates unused and matched edges. -/
theorem bounded_augmenting_path {V : Type} [DecidableEq V] [Fintype V] {d : ℕ}
    (es : List (PeriodicLatticeGraph.Arc V d)) (locality : PeriodicLatticeGraph.Local es)
    (perfect : PeriodicLatticeGraph.HasPerfectMatching es)
    (matching : PeriodicLatticeGraph.PeriodOneMatching es)
    (root : V × Lattice d) (free : matching.mate root = none) :
    ∃ path : TwoMatching.AugmentingPath matching.toPartialMatching
      (PeriodicLatticeGraph.UndirectedAdj es) root,
      ∀ x ∈ path.vertices, ∀ y ∈ path.vertices, ∀ i, (x.2 i-y.2 i).natAbs ≤ 2*d*es.length :=
  GraphAbstractBridge.bounded_augmenting_path es locality perfect matching root free

/-- Lemma 4.5: a period-one partial matching of a bipartite periodic graph
with a perfect matching is either perfect already or has an augmenting path
with distinct projected protovertices and fewer than |L|+|R| edges. These
properties are the `protoSimple` and `length` fields of `ShortAugmentingPath`. -/
theorem short_augmenting_path {L R : Type} [DecidableEq L] [DecidableEq R]
    [Fintype L] [Fintype R] {d : ℕ} (es : List (BipartiteEdge L R d))
    (perfect : PerfectMatching es) (matching : PeriodicBipartite.PeriodOnePartial es) :
    PeriodicBipartite.PerfectPartial matching ∨ Nonempty (PeriodicBipartite.ShortAugmentingPath matching) :=
  GraphAbstractBridge.perfect_or_short_augmenting es perfect matching

end LeanTrominoes.GraphAbstract
