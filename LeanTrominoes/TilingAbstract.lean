/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingAbstractBridge

/-!
# Tiling and completion: a formal abstract

This file introduces finite shapes, exact tilings, prescribed tiles, and
periodic inputs, and proves the main results of Section 5: tromino complexity,
tilings by two or three polyominoes or polycubes, completion and aperiodicity,
and doubled-period domino tilings. Section comments separate the result families.
To review what is proved, read the definitions and theorem statements here;
Lean checks their proofs through `TilingAbstractBridge` and the development.
This file does not depend on `GraphAbstract`.

The canonical complexity notions are reused, rather than redefined:
`LeanWang.CoREComplete` means that an algorithm recognizes no-instances and
every problem with such an algorithm reduces by a total computable map
preserving both answers. `Complexity.PSPACEComplete` means membership and
hardness for polynomial-space, always-halting finite-alphabet Turing machines;
`NPComplete` uses polynomial-length witnesses checked by polynomial-time
finite-alphabet machines. Their many-one reductions are polynomial time.
Each bounded-complexity theorem specifies the input encoding, whose size is
essential. Lists describe finite algorithmic inputs; repeated cells are harmless.
No periodicity is imposed on a tiling unless a theorem explicitly says so.
-/

namespace LeanTrominoes.TilingAbstract

/-! ## Shapes, motions, and exact cover -/

/-- A planar cell is (x,y) in ℤ². A shape is a finite set of cells; it need
not be connected. The I and L trominoes have cells {(0,0),(1,0),(2,0)} and
{(0,0),(1,0),(0,1)}, respectively. `Tromino.I` and `Tromino.L` name them. -/
abbrev Cell := ℤ × ℤ
abbrev Shape := Finset Cell
abbrev Tromino := LeanTrominoes.Tromino
def trominoShape : Tromino → Shape
  | .I => {(0,0), (1,0), (2,0)}
  | .L => {(0,0), (1,0), (0,1)}

/-- A placement records a tile `kind`, one of the eight square symmetries
`symmetry`, and a translation `offset`. The symmetries act by
(x,y), (-y,x), (-x,-y), (y,-x), (x,-y), (y,x), (-x,y), and (-y,-x).
Its occupied cells are the image of its shape under that motion. -/
abbrev Placement := LeanTrominoes.Placement
def placedCells {I : Type} (tiles : I → Shape) (p : Placement I) : Shape :=
  (tiles p.kind).image fun c =>
    (p.offset.1+(p.symmetry.act c).1, p.offset.2+(p.symmetry.act c).2)

/-- An exact cover puts every chosen tile inside the target and covers each
target cell exactly once. The definition works equally for placements and
for geometric footprints, in any dimension. -/
def ExactCover {A B : Type} (cells : B → Finset A) (region : Set A) (chosen : Set B) : Prop :=
  (∀ p ∈ chosen, ∀ c ∈ cells p, c ∈ region) ∧
    ∀ c ∈ region, ∃! p, p ∈ chosen ∧ c ∈ cells p
def Tileable {I : Type} (tiles : I → Shape) (region : Set Cell) : Prop :=
  ∃ chosen, ExactCover (placedCells tiles) region chosen
def TranslationTileable {I : Type} (tiles : I → Shape) (region : Set Cell) : Prop :=
  ∃ chosen, ExactCover (placedCells tiles) region chosen ∧
    ∀ p ∈ chosen, p.symmetry = .identity

/-- Connected shapes are nonempty and joined through shared sides, rather
than corner contacts. `sideGraph` is the ordinary graph on the shape's cells
whose edges join cells differing by one in exactly one coordinate. -/
def Connected (s : Shape) : Prop := (Polyomino.sideGraph s).Connected
def Strip (height : ℕ) : Set Cell := {c | 0 ≤ c.2 ∧ c.2 < height}
def Pair (p q : Shape) : Bool → Shape := fun b => if b then q else p

/-! ## Periodic tromino regions -/

/-- A plane input records a finite cell list `motif` and integer vectors
`period₁`, `period₂`. They must be independent; repeating the motif by their
integer span gives the target region. Degenerate periods are no-instances. -/
abbrev PlaneInput := PeriodicRegion
def FullRank (r : PlaneInput) : Prop :=
  r.period₁.1*r.period₂.2-r.period₁.2*r.period₂.1 ≠ 0
def PlaneRegion (r : PlaneInput) : Set Cell :=
  {c | ∃ b ∈ r.motif, ∃ i j : ℤ,
    c = (b.1+i*r.period₁.1+j*r.period₂.1, b.2+i*r.period₁.2+j*r.period₂.2)}
def TrominoPlane (t : Tromino) (r : PlaneInput) : Prop :=
  FullRank r ∧ Tileable (fun _ : Unit => trominoShape t) (PlaneRegion r)

/-- A strip input records a `motif`, a positive `width` (height), and a positive
horizontal `period`. Motif cells must lie in [0,period)×[0,width); their
horizontal translates give the target. All numerical fields use the stated
unary geometric encoding, so the bounding rectangle has polynomial area. -/
abbrev StripInput := PeriodicStrip
def ValidStrip (r : StripInput) : Prop :=
  0 < r.width ∧ 0 < r.period ∧ ∀ c ∈ r.motif,
    0 ≤ c.1 ∧ c.1 < r.period ∧ 0 ≤ c.2 ∧ c.2 < r.width
def StripRegion (r : StripInput) : Set Cell :=
  {c | 0 ≤ c.2 ∧ c.2 < r.width ∧ ∃ b ∈ r.motif, ∃ i : ℤ,
    c = (b.1+i*r.period, b.2)}
def TrominoStrip (t : Tromino) (r : StripInput) : Prop :=
  ValidStrip r ∧ Tileable (fun _ : Unit => trominoShape t) (StripRegion r)
abbrev stripEncoding := PeriodicStripFlatEncoding.finEncoding

/-- Theorem 5.2: for either individual tromino, periodic-subset tiling is
co-r.e.-complete in the plane and PSPACE-complete in a strip. -/
theorem tromino_plane (t : Tromino) : LeanWang.CoREComplete (TrominoPlane t) :=
  TilingAbstractBridge.tromino_plane t
theorem tromino_strip (t : Tromino) : Complexity.PSPACEComplete stripEncoding (TrominoStrip t) :=
  TilingAbstractBridge.tromino_strip t

/-- Corollary 5.3: translations of the horizontal and vertical I trominoes
give the same plane and strip complexity. The two shapes are fixed. -/
def straightTiles (vertical : Bool) : Shape :=
  if vertical then {(0,0), (0,1), (0,2)} else trominoShape .I
theorem two_translated_trominoes :
    LeanWang.CoREComplete (fun r : PlaneInput =>
      FullRank r ∧ TranslationTileable straightTiles (PlaneRegion r)) ∧
    Complexity.PSPACEComplete stripEncoding (fun r : StripInput =>
      ValidStrip r ∧ TranslationTileable straightTiles (StripRegion r)) := by
  exact TilingAbstractBridge.translated_trominoes

/-- Corollary 5.4: finite-region tileability is NP-complete for either tromino.
The input explicitly lists cells, with unary signed coordinates. -/
abbrev finiteRegionEncoding := LeanTrominoes.Tromino.FiniteCoordinateColumns.regionEncoding
theorem finite_tromino_region (t : Tromino) : Complexity.NPComplete finiteRegionEncoding
    (fun cells : List Cell => Tileable (fun _ : Unit => trominoShape t) (cells.toFinset : Set Cell)) :=
  TilingAbstractBridge.finite_region t

/-! ## Two or three planar prototiles -/

/-- Theorem 5.5: there is one fixed connected 15-cell tile P for which input
nonempty disconnected Q gives co-r.e.-complete plane tiling and PSPACE-complete
strip tiling. Both tiles may rotate and reflect. Strip height and Q coordinates
are unary; empty or connected Q, and height zero, are no-instances. -/
theorem two_polyominoes : ∃ p : Shape, p.card = 15 ∧ Connected p ∧
    LeanWang.CoREComplete (fun q : List Cell => q.toFinset.Nonempty ∧
      ¬ Connected q.toFinset ∧ Tileable (Pair p q.toFinset) Set.univ) ∧
    Complexity.PSPACEComplete Theorem55StripEncoding.finEncoding
      (fun i : ℕ × List Cell => 0 < i.1 ∧ i.2.toFinset.Nonempty ∧
        ¬ Connected i.2.toFinset ∧ Tileable (Pair p i.2.toFinset) (Strip i.1)) :=
  TilingAbstractBridge.two_polyominoes

/-- A three-tile palette has two fixed tiles indexed by Bool and an input
tile indexed by `none`; `some b` selects fixed tile b. -/
def ThreeTiles {A : Type} (fixed : Bool → A) (input : A) : Option Bool → A
  | none => input
  | some b => fixed b

/-- Corollary 5.6: two distinct fixed connected 15-cell tiles and input
nonempty disconnected Q have the same complexities with translations alone. -/
theorem three_translated_polyominoes : ∃ fixed : Bool → Shape,
    (∀ b, (fixed b).card = 15 ∧ Connected (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Cell => q.toFinset.Nonempty ∧
      ¬ Connected q.toFinset ∧ TranslationTileable (ThreeTiles fixed q.toFinset) Set.univ) ∧
    Complexity.PSPACEComplete Theorem55StripEncoding.finEncoding
      (fun i : ℕ × List Cell => 0 < i.1 ∧ i.2.toFinset.Nonempty ∧
        ¬ Connected i.2.toFinset ∧
          TranslationTileable (ThreeTiles fixed i.2.toFinset) (Strip i.1)) :=
  TilingAbstractBridge.three_polyominoes

/-- Corollary 5.7: with two fixed shapes, one connected and of size 15, the
finite seed alone can encode a co-r.e.-complete completion problem. A seed is
a list of actual placements, and every prescribed placement must be retained;
overlapping prescriptions are rejected, even far from the origin. -/
def FiniteSeedCompletion (p q : Shape) (seed : List (Placement Bool)) : Prop :=
  ∃ chosen, ExactCover (placedCells (Pair p q)) Set.univ chosen ∧ ∀ s ∈ seed, s ∈ chosen
theorem fixed_pair_seed : ∃ p q : Shape, p.card = 15 ∧ Connected p ∧ q.Nonempty ∧
    LeanWang.CoREComplete (FiniteSeedCompletion p q) := TilingAbstractBridge.fixed_seed

/-! ## Connected polycubes in full space and fixed-height slabs -/

/-- A voxel ((x,y),z) is an integer point of ℤ³; a polycube is a finite voxel
set. Connectivity is through shared faces and includes nonemptiness.
A voxel placement records a kind, an offset, and one of all 48 cube symmetries:
signed coordinate permutations, including reflections. -/
abbrev Voxel := LeanTrominoes.Voxel
abbrev Polycube := Finset Voxel
abbrev VoxelPlacement := LeanTrominoes.VoxelPlacement
def Connected3 (p : Polycube) : Prop := (LeanTrominoes.Polycube.faceGraph p).Connected
def Tileable3 {I : Type} (tiles : I → Polycube) (region : Set Voxel) : Prop :=
  ∃ chosen, ExactCover (fun p : VoxelPlacement I => p.cells tiles) region chosen
def TranslationTileable3 {I : Type} (tiles : I → Polycube) (region : Set Voxel) : Prop :=
  ∃ chosen, ExactCover (fun p : VoxelPlacement I => p.cells tiles) region chosen ∧
    ∀ p ∈ chosen, p.symmetry = CubeSymmetry.identity
def Pair3 (p q : Polycube) : Bool → Polycube := fun b => if b then q else p
def Slab (height : ℕ) : Set Voxel := {c | 0 ≤ c.2 ∧ c.2 < height}

/-- Corollary 5.8, full space: one fixed connected 45-voxel tile P and an
input connected Q give co-r.e.-complete tiling, allowing every cube symmetry. -/
theorem two_polycubes_space : ∃ p : Polycube, p.card = 45 ∧ Connected3 p ∧
    LeanWang.CoREComplete (fun q : List Voxel => Connected3 q.toFinset ∧
      Tileable3 (Pair3 p q.toFinset) Set.univ) := TilingAbstractBridge.two_polycubes_space

/-- Corollary 5.8, slabs: for each fixed height h>1, a fixed connected tile P
of at most 45 voxels gives the same completeness. P may depend on h, but not Q. -/
theorem two_polycubes_slab (height : ℕ) (positive : 1 < height) :
    ∃ p : Polycube, p.card ≤ 45 ∧ Connected3 p ∧
    LeanWang.CoREComplete (fun q : List Voxel => Connected3 q.toFinset ∧
      Tileable3 (Pair3 p q.toFinset) (Slab height)) :=
  TilingAbstractBridge.two_polycubes_slab height positive

/-- Corollary 5.9: translations of two distinct fixed connected 45-voxel
tiles and input connected Q give co-r.e.-complete full-space tiling. For each
fixed slab height >1, two fixed connected tiles of at most 45 voxels suffice. -/
theorem three_translated_polycubes_space : ∃ fixed : Bool → Polycube,
    (∀ b, (fixed b).card = 45 ∧ Connected3 (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Voxel => Connected3 q.toFinset ∧
      TranslationTileable3 (ThreeTiles fixed q.toFinset) Set.univ) :=
  TilingAbstractBridge.three_polycubes_space
theorem three_translated_polycubes_slab (height : ℕ) (positive : 1 < height) :
    ∃ fixed : Bool → Polycube,
    (∀ b, (fixed b).card ≤ 45 ∧ Connected3 (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Voxel => Connected3 q.toFinset ∧
      TranslationTileable3 (ThreeTiles fixed q.toFinset) (Slab height)) :=
  TilingAbstractBridge.three_polycubes_slab height positive

/-! ## Completion and aperiodicity -/

/-- A geometric footprint identifies placements occupying the same cells.
A tromino footprint is the occupied cell set of a legal placement. A tiling
by footprints uses only such sets and covers the target exactly once.
Completion retains every prescribed footprint, not merely its occupied cells. -/
def Footprint (t : Tromino) (f : Shape) : Prop :=
  ∃ p : Placement Unit, placedCells (fun _ => trominoShape t) p = f
def FootprintTiling (t : Tromino) (region : Set Cell) (chosen : Set Shape) : Prop :=
  (∀ f ∈ chosen, Footprint t f) ∧ ExactCover id region chosen
def Completable (t : Tromino) (region : Set Cell) (seed : Set Shape) : Prop :=
  ∃ chosen, FootprintTiling t region chosen ∧ seed ⊆ chosen

/-- A periodic prefill has a finite placement `motif` and two vectors
`period₁`, `period₂`. Its seed consists of all integer translates of motif
footprints by those vectors. Only the prefill is required to be periodic. -/
abbrev PlanePrefill := PeriodicTrominoPrefill
def Prescribed (t : Tromino) (i : PlanePrefill) : Set Shape :=
  {f | ∃ p ∈ i.motif, ∃ a b : ℤ,
    f = (placedCells (fun _ => trominoShape t) p).image
      (fun c => (a*i.period₁.1+b*i.period₂.1+c.1, a*i.period₁.2+b*i.period₂.2+c.2))}
def PlaneCompletion (t : Tromino) (i : PlanePrefill) : Prop :=
  i.period₁.1*i.period₂.2-i.period₁.2*i.period₂.1 ≠ 0 ∧
    Completable t Set.univ (Prescribed t i)

/-- Theorem 5.10, plane case: periodic prefill completion is co-r.e.-complete
for each tromino. Invalid or overlapping prescribed tiles are no-instances. -/
theorem tromino_completion_plane (t : Tromino) : LeanWang.CoREComplete (PlaneCompletion t) :=
  TilingAbstractBridge.completion_plane t

/-- A strip prefill has a placement `motif`, positive `height`, and positive
horizontal `period`. Its prescribed tiles are all horizontal repeats; tiles
must fit the strip and are never clipped. Height, period, coordinates, and
placement fields use the explicit unary encoding. -/
abbrev StripPrefill := PeriodicStripTrominoPrefill
def StripCompletion (t : Tromino) (i : StripPrefill) : Prop :=
  0 < i.height ∧ 0 < i.period ∧
    Completable t (Strip i.height) (Prescribed t ⟨i.motif, (i.period,0), (0,0)⟩)
theorem tromino_completion_strip (t : Tromino) : Complexity.PSPACEComplete
    CompletionStripEncoding.finEncoding (StripCompletion t) := TilingAbstractBridge.completion_strip t

/-- Aperiodicity means no nonzero translation preserves the collection of
tile footprints. This excludes even a single translation period. -/
def TranslationPeriod (chosen : Set Shape) (v : Cell) : Prop :=
  ∀ f, f ∈ chosen ↔ f.image (fun c => (v.1+c.1, v.2+c.2)) ∈ chosen
def Aperiodic (chosen : Set Shape) : Prop := ∀ v, TranslationPeriod chosen v → v = (0,0)

/-- Corollary 5.11: for either tromino there is a doubly periodic prefill
with at least one completion, and every completion is aperiodic. -/
theorem aperiodic_completions (t : Tromino) : ∃ i : PlanePrefill,
    PlaneCompletion t i ∧ ∀ completed,
      FootprintTiling t Set.univ completed → Prescribed t i ⊆ completed → Aperiodic completed := by
  obtain ⟨i, rank, _, h, ha⟩ := TilingAbstractBridge.exists_aperiodic_completion t
  exact ⟨i, ⟨rank, (TilingAbstractBridge.completes_iff _ _ _).mpr h⟩,
    fun completed ht hs => ha completed ((TilingAbstractBridge.footprints_iff _ _ _).mp ht) hs⟩

/-- Theorem 5.12: finite-preplacement completion of the full plane is
NP-complete for either tromino. The encoding explicitly lists the canonical
witness bounding box in addition to unary placement coordinates. Complexity
is measured in that padded input length. Repeated identical footprints are
identified; incompatible overlapping footprints cannot be completed. -/
abbrev finiteCompletionEncoding := LeanTrominoes.Tromino.FiniteCoordinateColumns.completionEncoding
def FiniteCompletion (t : Tromino) (ps : List (Placement Unit)) : Prop :=
  Completable t Set.univ ((ps.map (placedCells (fun _ => trominoShape t))).toFinset : Set Shape)
theorem finite_tromino_completion (t : Tromino) : Complexity.NPComplete
    (finiteCompletionEncoding t) (FiniteCompletion t) := TilingAbstractBridge.finite_completion t

/-! ## Dominoes in arbitrary dimension -/

/-- A d-dimensional cell has integer coordinates indexed by `Fin d`.
A domino is a pair of face-adjacent cells. A chart has finitely many origins
and r independent period generators, with each cell origin+period(z) represented
uniquely. The represented region may be disconnected, and r may be less than d. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Chart := Domino.Chart
def DominoFootprint {d : ℕ} (f : Finset (Lattice d)) : Prop :=
  ∃ x y : Lattice d, (∃ i, y = x+Pi.single i 1 ∨ x = y+Pi.single i 1) ∧ f = {x,y}
def DominoTiling {d : ℕ} (region : Set (Lattice d)) (chosen : Set (Finset (Lattice d))) : Prop :=
  (∀ f ∈ chosen, DominoFootprint f) ∧ ExactCover id region chosen
def PeriodicTiles {d r : ℕ} (period : Lattice r →+ Lattice d)
    (chosen : Set (Finset (Lattice d))) : Prop :=
  ∀ f ∈ chosen, ∀ z, f.image (fun c => c+period z) ∈ chosen

/-- Theorem 5.13: a tileable periodic domino region has a tiling invariant
under twice each original period generator, in every dimension and rank. -/
theorem domino_doubled {V : Type} [DecidableEq V] [Fintype V] {d r : ℕ}
    (C : Chart V d r) (tileable : ∃ chosen, DominoTiling C.region chosen) :
    ∃ chosen, DominoTiling C.region chosen ∧
      PeriodicTiles (Domino.doubledPeriod C.period) chosen :=
  TilingAbstractBridge.domino_doubled C tileable

/-- Corollary 5.14: the doubled-period tiling can retain every domino in any
periodic prefill that admits a completion. -/
theorem domino_completion_doubled {V : Type} [DecidableEq V] [Fintype V] {d r : ℕ}
    (C : Chart V d r) (seed : Set (Finset (Lattice d)))
    (periodic : PeriodicTiles C.period seed)
    (completable : ∃ chosen, DominoTiling C.region chosen ∧ seed ⊆ chosen) :
    ∃ chosen, DominoTiling C.region chosen ∧ seed ⊆ chosen ∧
      PeriodicTiles (Domino.doubledPeriod C.period) chosen :=
  TilingAbstractBridge.domino_completion_doubled C seed periodic completable

/-- Corollary 5.15: representatives and a nonsingular integer period matrix
give an executable decision. A valid `BasisData n d` lists n distinct cell
orbits and its d×d period matrix; the arithmetic RAM cost is at most
C(d)(n+1)² for the explicit coefficient `polynomialCoefficient d`.
Dimension is fixed; arithmetic and indexed access each have unit cost. -/
theorem domino_decision {n d : ℕ} (B : Domino.BasisData n d) (valid : B.Valid) :
    (B.solve = true ↔ ∃ chosen, DominoTiling (B.chart valid).region chosen) ∧
      B.totalCost ≤ Domino.polynomialCoefficient d*(n+1)^2 :=
  TilingAbstractBridge.domino_decision B valid

end LeanTrominoes.TilingAbstract
