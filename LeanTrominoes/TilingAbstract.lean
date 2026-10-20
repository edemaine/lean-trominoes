/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract
import LeanTrominoes.TilingAbstractBridge
import LeanTrominoes.TilingAlgorithmsAbstractBridge

/-!
# Tiling and completion: a formal abstract

This file introduces finite shapes, exact tilings, prescribed tiles, and
periodic inputs, and proves the main results of Section 5: tromino complexity,
tilings by two or three polyominoes or polycubes, completion and aperiodicity,
and doubled-period domino tilings. Section comments separate the result families.
To review what is proved, read the definitions and theorem statements here;
Lean checks their proofs through `TilingAbstractBridge` and the development.
This file does not depend on `GraphAbstract`.

`ComplexityAbstract` states the shared NP, PSPACE, and RAM definitions;
`lean-wang` supplies co-r.e.-completeness. Read those definitions together
with this file's statements. Each bounded-complexity result specifies its
encoding. Lists describe finite inputs; repeated cells are harmless.
No periodicity is imposed on a tiling unless a theorem explicitly says so.
-/

namespace LeanTrominoes.TilingAbstract

/-! ## Shapes, motions, and exact cover -/

/-- A planar cell is (x,y) in ℤ². A shape is a finite set of cells; it need
not be connected. The I and L trominoes have cells {(0,0),(1,0),(2,0)} and
{(0,0),(1,0),(0,1)}, respectively. `Tromino.I` and `Tromino.L` name them. -/
abbrev Cell := ℤ × ℤ
abbrev Shape := Finset Cell
inductive Tromino
  | I | L
  deriving DecidableEq

def Tromino.isL : Tromino → Bool
  | .I => false
  | .L => true

def trominoShape (t : Tromino) : Shape :=
  if t.isL then {(0,0), (1,0), (0,1)} else {(0,0), (1,0), (2,0)}

/-- A placement records a tile `kind`, one of the eight square symmetries
`symmetry`, and a translation `offset`. The symmetries act by
(x,y), (-y,x), (-x,-y), (y,-x), (x,-y), (y,x), (-x,y), and (-y,-x).
Its occupied cells are the image of its shape under that motion. -/
abbrev Symmetry := Fin 8
def symmetryAct (s : Symmetry) (c : Cell) : Cell :=
  ![(c.1,c.2), (-c.2,c.1), (-c.1,-c.2), (c.2,-c.1),
    (c.1,-c.2), (c.2,c.1), (-c.1,c.2), (-c.2,-c.1)] s
abbrev Placement (I : Type) := I × Symmetry × Cell
def Placement.kind {I : Type} (p : Placement I) : I := p.1
def Placement.symmetry {I : Type} (p : Placement I) : Symmetry := p.2.1
def Placement.offset {I : Type} (p : Placement I) : Cell := p.2.2
def placedCells {I : Type} (tiles : I → Shape) (p : Placement I) : Shape :=
  (tiles p.kind).image fun c =>
    (p.offset.1+(symmetryAct p.symmetry c).1, p.offset.2+(symmetryAct p.symmetry c).2)

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
    ∀ p ∈ chosen, p.symmetry = 0

/-- Connected shapes are nonempty and joined through shared sides, rather
than corner contacts. `sideGraph` is the ordinary graph on the shape's cells
whose edges join cells differing by one in exactly one coordinate. -/
def SideAdjacent (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2+1 = b.2 ∨ b.2+1 = a.2)) ∨
    (a.2 = b.2 ∧ (a.1+1 = b.1 ∨ b.1+1 = a.1))
def sideGraph (s : Shape) : SimpleGraph {c // c ∈ s} where
  Adj a b := SideAdjacent a.val b.val
  symm := TilingAbstractBridge.Data.sideGraph_symm s
  loopless := TilingAbstractBridge.Data.sideGraph_loopless s
def Connected (s : Shape) : Prop := (sideGraph s).Connected
def Strip (height : ℕ) : Set Cell := {c | 0 ≤ c.2 ∧ c.2 < height}
def Pair (p q : Shape) : Bool → Shape := fun b => if b then q else p

/-! ## Periodic tromino regions -/

/-- A plane input records a finite cell list `motif` and integer vectors
`period₁`, `period₂`. They must be independent; repeating the motif by their
integer span gives the target region. Degenerate periods are no-instances. -/
abbrev PlaneInput := List Cell × Cell × Cell
def PlaneInput.motif (r : PlaneInput) : List Cell := r.1
def PlaneInput.period₁ (r : PlaneInput) : Cell := r.2.1
def PlaneInput.period₂ (r : PlaneInput) : Cell := r.2.2
def FullRank (r : PlaneInput) : Prop :=
  r.period₁.1*r.period₂.2-r.period₁.2*r.period₂.1 ≠ 0
def PlaneRegion (r : PlaneInput) : Set Cell :=
  {c | ∃ b ∈ r.motif, ∃ i j : ℤ,
    c = (b.1+i*r.period₁.1+j*r.period₂.1, b.2+i*r.period₁.2+j*r.period₂.2)}
def TrominoPlane (t : Tromino) (r : PlaneInput) : Prop :=
  Tileable (fun _ : Unit => trominoShape t) (PlaneRegion r) ∧ FullRank r

/-- A strip input records a `motif`, a positive `width` (height), and a positive
horizontal `period`. Motif cells must lie in [0,period)×[0,width); their
horizontal translates give the target. All numerical fields use the stated
binary field encoding below. -/
abbrev StripInput := ℕ × ℕ × List Cell
def StripInput.width (r : StripInput) : ℕ := r.1
def StripInput.period (r : StripInput) : ℕ := r.2.1
def StripInput.motif (r : StripInput) : List Cell := r.2.2
def ValidStrip (r : StripInput) : Prop :=
  0 < r.width ∧ 0 < r.period ∧ ∀ c ∈ r.motif,
    0 ≤ c.1 ∧ c.1 < r.period ∧ 0 ≤ c.2 ∧ c.2 < r.width
def StripRegion (r : StripInput) : Set Cell :=
  {c | 0 ≤ c.2 ∧ c.2 < r.width ∧ ∃ b ∈ r.motif, ∃ i : ℤ,
    c = (b.1+i*r.period, b.2)}
def TrominoStrip (t : Tromino) (r : StripInput) : Prop :=
  Tileable (fun _ : Unit => trominoShape t) (StripRegion r) ∧ ValidStrip r
def cellFields (c : Cell) : List ℕ := [Encodable.encode c.1, Encodable.encode c.2]
def stripEncoding (r : StripInput) : List ComplexityAbstract.Symbol :=
  ComplexityAbstract.binaryFields
    ([r.width, r.period, r.motif.length] ++ r.motif.flatMap cellFields)

/-- Theorem 5.2: for either individual tromino, periodic-subset tiling is
co-r.e.-complete in the plane and PSPACE-complete in a strip. -/
theorem tromino_plane (t : Tromino) : LeanWang.CoREComplete (TrominoPlane t) :=
  TilingAbstractBridge.Data.tromino_plane t.isL
theorem tromino_strip (t : Tromino) : ComplexityAbstract.PSPACEComplete stripEncoding (TrominoStrip t) :=
  TilingAbstractBridge.Data.tromino_strip t.isL

/-- Corollary 5.3: translations of the horizontal and vertical I trominoes
give the same plane and strip complexity. The two shapes are fixed. -/
def straightTiles (vertical : Bool) : Shape :=
  if vertical then {(0,0), (0,1), (0,2)} else trominoShape .I
theorem two_translated_trominoes :
    LeanWang.CoREComplete (fun r : PlaneInput =>
      TranslationTileable straightTiles (PlaneRegion r) ∧ FullRank r) ∧
    ComplexityAbstract.PSPACEComplete stripEncoding (fun r : StripInput =>
      TranslationTileable straightTiles (StripRegion r) ∧ ValidStrip r) :=
  TilingAbstractBridge.Data.two_translated_trominoes

/-- The finite-coordinate alphabet tags five unary columns: region x/y,
placement symmetry, and placement x/y. The right summand is reserved for
certificate bits. Empty columns contribute no symbols. -/
abbrev CoordinateSymbol := Sum (Fin 5 × Bool) Bool
def unaryFields (fields : List ℕ) : List Bool :=
  fields.flatMap fun n => List.replicate n true ++ [false]
def coordinateEncoding (cells : List Cell) (ps : List (Placement Unit)) : List CoordinateSymbol :=
  let columns : Fin 5 → List ℕ := ![
    cells.map (fun c => Encodable.encode c.1), cells.map (fun c => Encodable.encode c.2),
    ps.map (fun p => p.symmetry.val), ps.map (fun p => Encodable.encode p.offset.1),
    ps.map (fun p => Encodable.encode p.offset.2)]
  (List.finRange 5).flatMap fun k => (unaryFields (columns k)).map (fun b => .inl (k,b))
def finiteRegionEncoding (cells : List Cell) : List CoordinateSymbol := coordinateEncoding cells []
/-- Corollary 5.4: finite-region tileability is NP-complete for either tromino.
The input explicitly lists cells, with unary signed coordinates. -/
theorem finite_tromino_region (t : Tromino) : ComplexityAbstract.NPComplete finiteRegionEncoding
    (fun cells : List Cell => Tileable (fun _ : Unit => trominoShape t) (cells.toFinset : Set Cell)) :=
  TilingAbstractBridge.Data.finite_tromino_region t.isL

/-! ## Two or three planar prototiles -/

/-- Strip height, cell count, and signed coordinates use unary fields. -/
def polyominoStripEncoding (input : ℕ × List Cell) : List Bool :=
  unaryFields ([input.1, input.2.length] ++ input.2.flatMap cellFields)

/-- Theorem 5.5: there is one fixed connected 15-cell tile P for which input
nonempty disconnected Q gives co-r.e.-complete plane tiling and PSPACE-complete
strip tiling. Both tiles may rotate and reflect. Strip height and Q coordinates
are unary; empty or connected Q, and height zero, are no-instances. -/
theorem two_polyominoes : ∃ p : Shape, p.card = 15 ∧ Connected p ∧
    LeanWang.CoREComplete (fun q : List Cell => Tileable (Pair p q.toFinset) Set.univ ∧
      q.toFinset.Nonempty ∧ ¬ Connected q.toFinset) ∧
    ComplexityAbstract.PSPACEComplete polyominoStripEncoding
      (fun i : ℕ × List Cell => Tileable (Pair p i.2.toFinset) (Strip i.1) ∧
        0 < i.1 ∧ i.2.toFinset.Nonempty ∧ ¬ Connected i.2.toFinset) :=
  TilingAbstractBridge.Data.two_polyominoes

/-- A three-tile palette has two fixed tiles indexed by Bool and an input
tile indexed by `none`; `some b` selects fixed tile b. -/
def ThreeTiles {A : Type} (fixed : Bool → A) (input : A) : Option Bool → A
  | none => input
  | some b => fixed b

/-- Corollary 5.6: two distinct fixed connected 15-cell tiles and input
nonempty disconnected Q have the same complexities with translations alone. -/
theorem three_translated_polyominoes : ∃ fixed : Bool → Shape,
    (∀ b, (fixed b).card = 15 ∧ Connected (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Cell => TranslationTileable (ThreeTiles fixed q.toFinset) Set.univ ∧
      q.toFinset.Nonempty ∧ ¬ Connected q.toFinset) ∧
    ComplexityAbstract.PSPACEComplete polyominoStripEncoding
      (fun i : ℕ × List Cell => TranslationTileable (ThreeTiles fixed i.2.toFinset) (Strip i.1) ∧
        0 < i.1 ∧ i.2.toFinset.Nonempty ∧ ¬ Connected i.2.toFinset) :=
  TilingAbstractBridge.Data.three_translated_polyominoes

/-- Corollary 5.7: with two fixed shapes, one connected and of size 15, the
finite seed alone can encode a co-r.e.-complete completion problem. A seed is
a list of actual placements, and every prescribed placement must be retained;
overlapping prescriptions are rejected, even far from the origin. -/
def FiniteSeedCompletion (p q : Shape) (seed : List (Placement Bool)) : Prop :=
  ∃ chosen, ExactCover (placedCells (Pair p q)) Set.univ chosen ∧ ∀ s ∈ seed, s ∈ chosen
theorem fixed_pair_seed : ∃ p q : Shape, p.card = 15 ∧ Connected p ∧ q.Nonempty ∧
    LeanWang.CoREComplete (FiniteSeedCompletion p q) :=
  TilingAbstractBridge.Data.fixed_pair_seed

/-! ## Connected polycubes in full space and fixed-height slabs -/

/-- A voxel ((x,y),z) is an integer point of ℤ³; a polycube is a finite voxel
set. Connectivity is through shared faces and includes nonemptiness.
A voxel placement records a kind, an offset, and one of all 48 cube symmetries:
signed coordinate permutations, including reflections. -/
abbrev Voxel := Cell × ℤ
abbrev Polycube := Finset Voxel
abbrev CubeSymmetry := Symmetry × Bool × Fin 3
abbrev VoxelPlacement (I : Type) := I × CubeSymmetry × Voxel
def cycleCoordinates (axis : Fin 3) (c : Voxel) : Voxel :=
  ![c, ((c.2,c.1.1),c.1.2), ((c.1.2,c.2),c.1.1)] axis
def cubeAct (s : CubeSymmetry) (c : Voxel) : Voxel :=
  cycleCoordinates s.2.2 (symmetryAct s.1 c.1, if s.2.1 then -c.2 else c.2)
def voxelCells {I : Type} (tiles : I → Polycube) (p : VoxelPlacement I) : Polycube :=
  (tiles p.1).image fun c =>
    let a := cubeAct p.2.1 c
    ((p.2.2.1.1+a.1.1, p.2.2.1.2+a.1.2), p.2.2.2+a.2)
def FaceAdjacent (a b : Voxel) : Prop :=
  (a.2 = b.2 ∧ SideAdjacent a.1 b.1) ∨
    (a.1 = b.1 ∧ (a.2+1 = b.2 ∨ b.2+1 = a.2))
def faceGraph (p : Polycube) : SimpleGraph {c // c ∈ p} where
  Adj a b := FaceAdjacent a.val b.val
  symm := TilingAbstractBridge.Data.faceGraph_symm p
  loopless := TilingAbstractBridge.Data.faceGraph_loopless p
def Connected3 (p : Polycube) : Prop := (faceGraph p).Connected
def Tileable3 {I : Type} (tiles : I → Polycube) (region : Set Voxel) : Prop :=
  ∃ chosen, ExactCover (voxelCells tiles) region chosen
def TranslationTileable3 {I : Type} (tiles : I → Polycube) (region : Set Voxel) : Prop :=
  ∃ chosen, ExactCover (voxelCells tiles) region chosen ∧
    ∀ p ∈ chosen, p.2.1 = (0,false,0)
def Pair3 (p q : Polycube) : Bool → Polycube := fun b => if b then q else p
def Slab (height : ℕ) : Set Voxel := {c | 0 ≤ c.2 ∧ c.2 < height}

/-- Corollary 5.8, full space: one fixed connected 45-voxel tile P and an
input connected Q give co-r.e.-complete tiling, allowing every cube symmetry. -/
theorem two_polycubes_space : ∃ p : Polycube, p.card = 45 ∧ Connected3 p ∧
    LeanWang.CoREComplete (fun q : List Voxel => Tileable3 (Pair3 p q.toFinset) Set.univ ∧
      Connected3 q.toFinset) :=
  TilingAbstractBridge.Data.two_polycubes_space

/-- Corollary 5.8, slabs: for each fixed height h>1, a fixed connected tile P
of at most 45 voxels gives the same completeness. P may depend on h, but not Q. -/
theorem two_polycubes_slab (height : ℕ) (positive : 1 < height) :
    ∃ p : Polycube, p.card ≤ 45 ∧ Connected3 p ∧
    LeanWang.CoREComplete (fun q : List Voxel => Tileable3 (Pair3 p q.toFinset) (Slab height) ∧
      Connected3 q.toFinset) :=
  TilingAbstractBridge.Data.two_polycubes_slab height positive

/-- Corollary 5.9: translations of two distinct fixed connected 45-voxel
tiles and input connected Q give co-r.e.-complete full-space tiling. For each
fixed slab height >1, two fixed connected tiles of at most 45 voxels suffice. -/
theorem three_translated_polycubes_space : ∃ fixed : Bool → Polycube,
    (∀ b, (fixed b).card = 45 ∧ Connected3 (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Voxel => TranslationTileable3 (ThreeTiles fixed q.toFinset) Set.univ ∧
      Connected3 q.toFinset) :=
  TilingAbstractBridge.Data.three_translated_polycubes_space
theorem three_translated_polycubes_slab (height : ℕ) (positive : 1 < height) :
    ∃ fixed : Bool → Polycube,
    (∀ b, (fixed b).card ≤ 45 ∧ Connected3 (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Voxel => TranslationTileable3 (ThreeTiles fixed q.toFinset) (Slab height) ∧
      Connected3 q.toFinset) :=
  TilingAbstractBridge.Data.three_translated_polycubes_slab height positive

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
abbrev PlanePrefill := List (Placement Unit) × Cell × Cell
def PlanePrefill.motif (i : PlanePrefill) : List (Placement Unit) := i.1
def PlanePrefill.period₁ (i : PlanePrefill) : Cell := i.2.1
def PlanePrefill.period₂ (i : PlanePrefill) : Cell := i.2.2
def Prescribed (t : Tromino) (i : PlanePrefill) : Set Shape :=
  {f | ∃ p ∈ i.motif, ∃ a b : ℤ,
    f = (placedCells (fun _ => trominoShape t) p).image
      (fun c => (a*i.period₁.1+b*i.period₂.1+c.1, a*i.period₁.2+b*i.period₂.2+c.2))}
def PlaneCompletion (t : Tromino) (i : PlanePrefill) : Prop :=
  Completable t Set.univ (Prescribed t i) ∧
    i.period₁.1*i.period₂.2-i.period₁.2*i.period₂.1 ≠ 0

/-- Theorem 5.10, plane case: periodic prefill completion is co-r.e.-complete
for each tromino. Invalid or overlapping prescribed tiles are no-instances. -/
theorem tromino_completion_plane (t : Tromino) : LeanWang.CoREComplete (PlaneCompletion t) :=
  TilingAbstractBridge.Data.tromino_completion_plane t.isL

/-- A strip prefill has a placement `motif`, positive `height`, and positive
horizontal `period`. Its prescribed tiles are all horizontal repeats; tiles
must fit the strip and are never clipped. Height, period, coordinates, and
placement fields use the explicit unary encoding. -/
abbrev StripPrefill := List (Placement Unit) × ℕ × ℕ
def StripPrefill.motif (i : StripPrefill) : List (Placement Unit) := i.1
def StripPrefill.height (i : StripPrefill) : ℕ := i.2.1
def StripPrefill.period (i : StripPrefill) : ℕ := i.2.2
def StripCompletion (t : Tromino) (i : StripPrefill) : Prop :=
  Completable t (Strip i.height) (Prescribed t ⟨i.motif, (i.period,0), (0,0)⟩) ∧
    0 < i.height ∧ 0 < i.period
def completionStripEncoding (i : StripPrefill) : List Bool :=
  unaryFields ([i.height, i.period, i.motif.length] ++ i.motif.flatMap
    (fun p => [p.symmetry.val, Encodable.encode p.offset.1, Encodable.encode p.offset.2]))
theorem tromino_completion_strip (t : Tromino) : ComplexityAbstract.PSPACEComplete
    completionStripEncoding (StripCompletion t) :=
  TilingAbstractBridge.Data.tromino_completion_strip t.isL

/-- Aperiodicity means no nonzero translation preserves the collection of
tile footprints. This excludes even a single translation period. -/
def TranslationPeriod (chosen : Set Shape) (v : Cell) : Prop :=
  ∀ f, f ∈ chosen ↔ f.image (fun c => (v.1+c.1, v.2+c.2)) ∈ chosen
def Aperiodic (chosen : Set Shape) : Prop := ∀ v, TranslationPeriod chosen v → v = (0,0)

/-- Corollary 5.11: for either tromino there is a doubly periodic prefill
with at least one completion, and every completion is aperiodic. -/
theorem aperiodic_completions (t : Tromino) : ∃ i : PlanePrefill,
    PlaneCompletion t i ∧ ∀ completed,
      FootprintTiling t Set.univ completed → Prescribed t i ⊆ completed → Aperiodic completed :=
  TilingAbstractBridge.Data.aperiodic_completions t.isL

/-- Theorem 5.12: finite-preplacement completion of the full plane is
NP-complete for either tromino. The encoding explicitly lists the canonical
witness bounding box in addition to unary placement coordinates. Complexity
is measured in that padded input length. Repeated identical footprints are
identified; incompatible overlapping footprints cannot be completed. -/
def completionRadius (t : Tromino) (ps : List (Placement Unit)) : ℕ :=
  ((ps.map (placedCells (fun _ => trominoShape t))).toFinset.biUnion id).sup
    (fun c => max c.1.natAbs c.2.natAbs)
def completionBox (r : ℕ) : List Cell :=
  (List.range (2*r+1)).flatMap fun x => (List.range (2*r+1)).map fun y =>
    ((x : ℤ)-(r : ℤ), (y : ℤ)-(r : ℤ))
def finiteCompletionEncoding (t : Tromino) (ps : List (Placement Unit)) : List CoordinateSymbol :=
  coordinateEncoding (completionBox (completionRadius t ps)) ps
def FiniteCompletion (t : Tromino) (ps : List (Placement Unit)) : Prop :=
  Completable t Set.univ ((ps.map (placedCells (fun _ => trominoShape t))).toFinset : Set Shape)
theorem finite_tromino_completion (t : Tromino) : ComplexityAbstract.NPComplete
    (finiteCompletionEncoding t) (FiniteCompletion t) :=
  TilingAbstractBridge.Data.finite_tromino_completion t.isL

/-! ## Dominoes in arbitrary dimension -/

/-- A d-dimensional cell has integer coordinates indexed by `Fin d`.
A domino is a pair of face-adjacent cells. A chart has finitely many origins
and r period generators, with each cell origin+period(z) represented
uniquely. The represented region may be disconnected, and r may be less than d. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Chart (V : Type) (d r : ℕ) := (V → Lattice d) × (Lattice r →+ Lattice d)
def Chart.origin {V : Type} {d r : ℕ} (C : Chart V d r) : V → Lattice d := C.1
def Chart.period {V : Type} {d r : ℕ} (C : Chart V d r) : Lattice r →+ Lattice d := C.2
def Chart.Valid {V : Type} {d r : ℕ} (C : Chart V d r) : Prop :=
  Function.Injective (fun x : V × Lattice r => C.origin x.1+C.period x.2)
def Chart.region {V : Type} {d r : ℕ} (C : Chart V d r) : Set (Lattice d) :=
  Set.range (fun x : V × Lattice r => C.origin x.1+C.period x.2)
def DominoFootprint {d : ℕ} (f : Finset (Lattice d)) : Prop :=
  ∃ x y : Lattice d, (∃ i, y = x+Pi.single i 1 ∨ x = y+Pi.single i 1) ∧ f = {x,y}
def DominoTiling {d : ℕ} (region : Set (Lattice d)) (chosen : Set (Finset (Lattice d))) : Prop :=
  (∀ f ∈ chosen, DominoFootprint f) ∧ ExactCover id region chosen
def PeriodicTiles {d r : ℕ} (period : Lattice r →+ Lattice d)
    (chosen : Set (Finset (Lattice d))) : Prop :=
  ∀ f ∈ chosen, ∀ z, f.image (fun c => c+period z) ∈ chosen

def doubledPeriod {d r : ℕ} (period : Lattice r →+ Lattice d) : Lattice r →+ Lattice d where
  toFun z := period (z+z)
  map_zero' := TilingAbstractBridge.Data.doubledPeriod_zero period
  map_add' := TilingAbstractBridge.Data.doubledPeriod_add period

/-- Theorem 5.13: a tileable periodic domino region has a tiling invariant
under twice each original period generator, in every dimension and rank. -/
theorem domino_doubled {V : Type} [DecidableEq V] [Fintype V] {d r : ℕ}
    (C : Chart V d r) (unique : C.Valid) (tileable : ∃ chosen, DominoTiling C.region chosen) :
    ∃ chosen, DominoTiling C.region chosen ∧
      PeriodicTiles (doubledPeriod C.period) chosen :=
  TilingAbstractBridge.Data.domino_doubled C unique tileable

/-- Corollary 5.14: the doubled-period tiling can retain every domino in any
periodic prefill that admits a completion. -/
theorem domino_completion_doubled {V : Type} [DecidableEq V] [Fintype V] {d r : ℕ}
    (C : Chart V d r) (unique : C.Valid) (seed : Set (Finset (Lattice d)))
    (periodic : PeriodicTiles C.period seed)
    (completable : ∃ chosen, DominoTiling C.region chosen ∧ seed ⊆ chosen) :
    ∃ chosen, DominoTiling C.region chosen ∧ seed ⊆ chosen ∧
      PeriodicTiles (doubledPeriod C.period) chosen :=
  TilingAbstractBridge.Data.domino_completion_doubled C unique seed periodic completable

/-- A full-rank presentation lists an integer period matrix and one origin
for each cell orbit. Validity requires a nonsingular matrix and unique
representation of every cell in the region. -/
abbrev DominoBasis (n d : ℕ) := Matrix (Fin d) (Fin d) ℤ × (Fin n → Lattice d)
def DominoBasis.basis {n d : ℕ} (B : DominoBasis n d) := B.1
def DominoBasis.origin {n d : ℕ} (B : DominoBasis n d) := B.2
def DominoBasis.realize {n d : ℕ} (B : DominoBasis n d) (a : Fin n × Lattice d) : Lattice d :=
  B.origin a.1+B.basis.mulVec a.2
def DominoBasis.Valid {n d : ℕ} (B : DominoBasis n d) : Prop :=
  B.basis.det≠0 ∧ Function.Injective B.realize
def DominoBasis.region {n d : ℕ} (B : DominoBasis n d) : Set (Lattice d) := Set.range B.realize
abbrev DominoInput (d : ℕ) := Σ n : ℕ, {B : DominoBasis n d // B.Valid}

/-- Binary fields appear in row-major order: the matrix followed by the
origins. Each signed integer is its residue modulo 2^L, written in L little
endian bits. A fixed dimension-dependent padding factor chooses L; the
three header words give the representative count, entry-bit bound, and L. -/
def dominoMagnitude {n d : ℕ} (B : DominoBasis n d) : ℕ :=
  1+(∑ i, ∑ j, (B.basis i j).natAbs)+(∑ v, ∑ i, (B.origin v i).natAbs)
def dominoEntryBits {n d : ℕ} (B : DominoBasis n d) : ℕ := Nat.log2 (dominoMagnitude B+1)+2
def dominoPrecision {n d : ℕ} (padding : ℕ) (B : DominoBasis n d) : ℕ := padding*dominoEntryBits B+4
def dominoBits (length value : ℕ) : List ℤ :=
  (List.range length).map (fun i => ((value/2^i)%2 : ℕ))

def dominoIntegerBits (length : ℕ) (z : ℤ) : List ℤ := dominoBits length (z%(2^length : ℤ)).toNat
def dominoFields {n d : ℕ} (B : DominoBasis n d) : List ℤ :=
  (List.finRange d).flatMap (fun i => (List.finRange d).map (fun j => B.basis i j)) ++
    (List.finRange n).flatMap (fun v => (List.finRange d).map (fun i => B.origin v i))
def dominoEncoding {d : ℕ} (padding : ℕ) (input : DominoInput d) : List ℤ :=
  [(input.1 : ℤ),(dominoEntryBits input.2.val : ℤ),(dominoPrecision padding input.2.val : ℤ)]++
    (dominoFields input.2.val).flatMap (dominoIntegerBits (dominoPrecision padding input.2.val))
def dominoInputSize {d : ℕ} (padding : ℕ) (input : DominoInput d) : ℕ :=
  input.1+dominoEntryBits input.2.val+dominoPrecision padding input.2.val+(dominoEncoding padding input).length+1

/-- Corollary 5.15: domino tilability of valid full-rank presentations is
decidable in polynomial time on the bounded-word RAM, for each fixed
dimension. A single dimension-dependent precision padding is used for all
inputs. The bound includes binary arithmetic, allocation, graph construction,
matching, and halt, and works for every sufficiently large logarithmic word. -/
theorem domino_decision (d : ℕ) : ∃ padding,
    ComplexityAbstract.RAM.PolynomialTime (dominoEncoding (d:=d) padding) (dominoInputSize padding)
      (fun input => ∃ chosen, DominoTiling input.2.val.region chosen) :=
  TilingAlgorithmsAbstractBridge.polynomialTime d

end LeanTrominoes.TilingAbstract
