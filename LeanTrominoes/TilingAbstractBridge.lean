/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Results
import LeanTrominoes.ComplexityAbstractBridge

/-! # Proof bridge for the tiling abstract

The input records, their encodings, and their mathematical answers are
preserved. The lemmas below expand exact-cover and completion predicates;
they do not replace an input representation by a merely set-theoretically
equivalent one. This module does not import `TilingAbstract` or `GraphAbstract`.
-/

namespace LeanTrominoes.TilingAbstractBridge

namespace Native

def ExactCover {A B : Type} (cells : B → Finset A) (region : Set A) (chosen : Set B) : Prop :=
  (∀ p ∈ chosen, ∀ c ∈ cells p, c ∈ region) ∧
    ∀ c ∈ region, ∃! p, p ∈ chosen ∧ c ∈ cells p

def Tiles2 {I : Type} (tiles : I → Polyomino) (region : Set Cell) : Prop :=
  ∃ chosen, ExactCover (fun p : Placement I => p.cells tiles) region chosen

theorem tiles2_iff {I : Type} (tiles : I → Polyomino) (region : Set Cell) :
    Tiles2 tiles region ↔ Tileable tiles region := by
  constructor
  · rintro ⟨ps, inside, cover⟩
    exact ⟨ps, ⟨inside, cover⟩⟩
  · rintro ⟨ps, h⟩
    exact ⟨ps, h.tilesInside, h.uniqueCover⟩

def TranslationTiles2 {I : Type} (tiles : I → Polyomino) (region : Set Cell) : Prop :=
  ∃ chosen, ExactCover (fun p : Placement I => p.cells tiles) region chosen ∧
    ∀ p ∈ chosen, p.symmetry = .identity

theorem translation2_iff {I : Type} (tiles : I → Polyomino) (region : Set Cell) :
    TranslationTiles2 tiles region ↔ TranslationTileable tiles region := by
  constructor
  · rintro ⟨ps, ⟨inside, cover⟩, legal⟩
    exact ⟨ps, ⟨inside, cover⟩, legal⟩
  · rintro ⟨ps, h, legal⟩
    exact ⟨ps, ⟨h.tilesInside, h.uniqueCover⟩, legal⟩

def FootprintTiling (t : Tromino) (region : Set Cell) (chosen : Set (Finset Cell)) : Prop :=
  (∀ f ∈ chosen, t.IsFootprint f) ∧ ExactCover id region chosen

theorem footprints_iff (t : Tromino) (region : Set Cell) (chosen : Set (Finset Cell)) :
    FootprintTiling t region chosen ↔ t.IsFootprintTiling region chosen := by
  constructor
  · rintro ⟨legal, inside, cover⟩
    exact ⟨fun f hf => ⟨legal f hf, inside f hf⟩, cover⟩
  · intro h
    exact ⟨fun f hf => (h.tilesInside f hf).1,
      (fun f hf => (h.tilesInside f hf).2), h.uniqueCover⟩

def Completes (t : Tromino) (region : Set Cell) (seed : Set (Finset Cell)) : Prop :=
  ∃ chosen, FootprintTiling t region chosen ∧ seed ⊆ chosen

theorem completes_iff (t : Tromino) (region : Set Cell) (seed : Set (Finset Cell)) :
    Completes t region seed ↔ t.Completable region seed := by
  exact exists_congr fun chosen => and_congr_left fun _ => footprints_iff t region chosen

def Tiles3 {I : Type} (tiles : I → Polycube) (region : Set Voxel) : Prop :=
  ∃ chosen, ExactCover (fun p : VoxelPlacement I => p.cells tiles) region chosen

theorem tiles3_iff {I : Type} (tiles : I → Polycube) (region : Set Voxel) :
    Tiles3 tiles region ↔ VoxelTileable tiles region := by
  constructor
  · rintro ⟨ps, inside, cover⟩
    exact ⟨ps, ⟨inside, cover⟩⟩
  · rintro ⟨ps, h⟩
    exact ⟨ps, h.tilesInside, h.uniqueCover⟩

def TranslationTiles3 {I : Type} (tiles : I → Polycube) (region : Set Voxel) : Prop :=
  ∃ chosen, ExactCover (fun p : VoxelPlacement I => p.cells tiles) region chosen ∧
    ∀ p ∈ chosen, p.symmetry = CubeSymmetry.identity

theorem translation3_iff {I : Type} (tiles : I → Polycube) (region : Set Voxel) :
    TranslationTiles3 tiles region ↔ VoxelTranslationTileable tiles region := by
  constructor
  · rintro ⟨ps, ⟨inside, cover⟩, legal⟩
    exact ⟨ps, ⟨inside, cover⟩, legal⟩
  · rintro ⟨ps, h, legal⟩
    exact ⟨ps, ⟨h.tilesInside, h.uniqueCover⟩, legal⟩

theorem coRE_congr {A : Type} [Primcodable A] {p q : A → Prop}
    (h : ∀ a, p a ↔ q a) (hp : LeanWang.CoREComplete p) : LeanWang.CoREComplete q := by
  have eq : p = q := funext fun a => propext (h a)
  exact eq ▸ hp

theorem pspace_congr {A : Type} {e : FiniteEncoding A} {p q : A → Prop}
    (h : ∀ a, p a ↔ q a) (hp : Complexity.PSPACEComplete e p) :
    Complexity.PSPACEComplete e q := by
  have eq : p = q := funext fun a => propext (h a)
  exact eq ▸ hp

theorem np_congr {A : Type} {e : FiniteEncoding A} {p q : A → Prop}
    (h : ∀ a, p a ↔ q a) (hp : Complexity.NPComplete e p) :
    Complexity.NPComplete e q := by
  have eq : p = q := funext fun a => propext (h a)
  exact eq ▸ hp

theorem tromino_plane (t : Tromino) : LeanWang.CoREComplete
    (fun r : PeriodicRegion => r.IsFullRank ∧ Tiles2 (fun _ : Unit => t.cells) r.carrier) := by
  apply coRE_congr _ (Theorem52.proved.1 t)
  intro r
  exact and_congr_right fun _ => (tiles2_iff _ _).symm

theorem strip_carrier (r : PeriodicStrip) : r.carrier =
    {c | 0 ≤ c.2 ∧ c.2 < (r.width : Int) ∧ ∃ b ∈ r.motif, ∃ i : Int,
      c = (b.1+i*(r.period : Int), b.2)} := by
  ext c
  simp only [PeriodicStrip.carrier, Cell.add, Cell.scale, mul_zero, add_zero]

theorem tromino_strip (t : Tromino) : Complexity.PSPACEComplete PeriodicStripFlatEncoding.finEncoding
    (fun r : PeriodicStrip => r.IsWellFormed ∧ Tiles2 (fun _ : Unit => t.cells)
      {c | 0 ≤ c.2 ∧ c.2 < (r.width : Int) ∧ ∃ b ∈ r.motif, ∃ i : Int,
        c = (b.1+i*(r.period : Int), b.2)}) := by
  apply pspace_congr _ (Theorem52.proved.2 t)
  intro r
  rw [← strip_carrier]
  exact and_congr_right fun _ => (tiles2_iff _ _).symm

theorem translated_trominoes :
    LeanWang.CoREComplete (fun r : PeriodicRegion => r.IsFullRank ∧
      TranslationTiles2 (fun (b : Bool) => if b then ({(0,0),(0,1),(0,2)} : Polyomino) else Tromino.I.cells)
        r.carrier) ∧
    Complexity.PSPACEComplete PeriodicStripFlatEncoding.finEncoding (fun r : PeriodicStrip =>
      r.IsWellFormed ∧
      TranslationTiles2 (fun (b : Bool) => if b then ({(0,0),(0,1),(0,2)} : Polyomino) else Tromino.I.cells)
        {c | 0 ≤ c.2 ∧ c.2 < (r.width : Int) ∧ ∃ b ∈ r.motif, ∃ i : Int,
          c = (b.1+i*(r.period : Int), b.2)}) := by
  have tiles : TwoTranslationTrominoes.tiles =
      (fun (b : Bool) => if b then ({(0,0),(0,1),(0,2)} : Polyomino) else Tromino.I.cells) := by
    funext b
    cases b <;> decide
  constructor
  · apply coRE_congr _ TwoTranslationTrominoes.planeProved
    intro r
    simp only [TwoTranslationTrominoes.planeProblem, tiles, translation2_iff]
  · apply pspace_congr _ TwoTranslationTrominoes.stripProved
    intro r
    simp only [TwoTranslationTrominoes.stripProblem, tiles, translation2_iff, strip_carrier]

theorem completion_plane (t : Tromino) : LeanWang.CoREComplete
    (fun i : PeriodicTrominoPrefill => (i.occupiedRegion t).IsFullRank ∧
      Completes t Set.univ (i.prescribed t)) := by
  apply coRE_congr _ (PeriodicTrominoPrefill.planeProblem_coREComplete t)
  intro i
  exact and_congr_right fun _ => (completes_iff _ _ _).symm

theorem completion_strip (t : Tromino) : Complexity.PSPACEComplete CompletionStripEncoding.finEncoding
    (fun i : PeriodicStripTrominoPrefill => 0 < i.height ∧ 0 < i.period ∧
      Completes t i.region (i.periodic.prescribed t)) := by
  apply pspace_congr _ (PeriodicStripTrominoPrefill.problem_PSPACEComplete t)
  intro i
  exact and_congr_right fun _ => and_congr_right fun _ => (completes_iff _ _ _).symm

theorem finite_region (t : Tromino) : Complexity.NPComplete Tromino.FiniteCoordinateColumns.regionEncoding
    (fun cells : List Cell => Tiles2 (fun _ : Unit => t.cells) (cells.toFinset : Set Cell)) := by
  apply np_congr _ (Tromino.FiniteCoordinateColumns.region_npComplete t)
  intro cells
  exact (tiles2_iff _ _).symm

theorem finite_completion (t : Tromino) : Complexity.NPComplete
    (Tromino.FiniteCoordinateColumns.completionEncoding t)
    (fun ps : List (Placement Unit) => Completes t Set.univ
      ((Tromino.FiniteCoordinateColumns.completionFootprints t ps).toFinset : Set (Finset Cell))) := by
  apply np_congr _ (Tromino.FiniteCoordinateColumns.completion_npComplete t)
  intro ps
  exact (completes_iff _ _ _).symm

theorem two_polyominoes : ∃ p : Polyomino, p.card = 15 ∧ Polyomino.IsConnected p ∧
    LeanWang.CoREComplete (fun q : List Cell => q.toFinset.Nonempty ∧
      ¬ Polyomino.IsConnected q.toFinset ∧ Tiles2 (pairTiles p q.toFinset) Set.univ) ∧
    Complexity.PSPACEComplete Theorem55StripEncoding.finEncoding
      (fun i : Nat × List Cell => 0 < i.1 ∧ i.2.toFinset.Nonempty ∧
        ¬ Polyomino.IsConnected i.2.toFinset ∧ Tiles2 (pairTiles p i.2.toFinset) (horizontalStrip i.1)) := by
  refine ⟨PlusRefinement.bumpy, PlusRefinement.bumpy_card, PlusRefinement.bumpy_connected, ?_, ?_⟩
  · apply coRE_congr _ Theorem55.planeProved
    intro q
    exact and_congr_right fun _ => and_congr_right fun _ => (tiles2_iff _ _).symm
  · apply pspace_congr _ Theorem55.stripProved
    intro i
    exact and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => (tiles2_iff _ _).symm

def threeTiles {A : Type} (fixed : Bool → A) (input : A) : Option Bool → A
  | none => input
  | some b => fixed b

theorem three_polyominoes : ∃ fixed : Bool → Polyomino,
    (∀ b, (fixed b).card = 15 ∧ Polyomino.IsConnected (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Cell => q.toFinset.Nonempty ∧
      ¬ Polyomino.IsConnected q.toFinset ∧ TranslationTiles2 (threeTiles fixed q.toFinset) Set.univ) ∧
    Complexity.PSPACEComplete Theorem55StripEncoding.finEncoding
      (fun i : Nat × List Cell => 0 < i.1 ∧ i.2.toFinset.Nonempty ∧
        ¬ Polyomino.IsConnected i.2.toFinset ∧
          TranslationTiles2 (threeTiles fixed i.2.toFinset) (horizontalStrip i.1)) := by
  refine ⟨ThreeTranslationPolyominoes.fixed, fun b =>
    ⟨ThreeTranslationPolyominoes.fixed_card b, ThreeTranslationPolyominoes.fixed_connected b⟩,
    ThreeTranslationPolyominoes.fixed_distinct, ?_, ?_⟩
  · apply coRE_congr _ ThreeTranslationPolyominoes.planeProved
    intro q
    exact and_congr_right fun _ => and_congr_right fun _ => (translation2_iff _ _).symm
  · apply pspace_congr _ ThreeTranslationPolyominoes.stripProved
    intro i
    exact and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => (translation2_iff _ _).symm

theorem two_polycubes_space : ∃ p : Polycube, p.card = 45 ∧ Polycube.IsConnected p ∧
    LeanWang.CoREComplete (fun q : List Voxel => Polycube.IsConnected q.toFinset ∧
      Tiles3 (Polycube.pairTiles p q.toFinset) Set.univ) := by
  refine ⟨Polycube.bumpyThree, Polycube.bumpyThree_card, Polycube.bumpyThree_connected, ?_⟩
  apply coRE_congr _ TwoConnectedPolycubes.spaceProved
  intro q
  exact and_congr_right fun _ => (tiles3_iff _ _).symm

theorem two_polycubes_slab (height : Nat) (positive : 1 < height) :
    ∃ p : Polycube, p.card ≤ 45 ∧ Polycube.IsConnected p ∧
    LeanWang.CoREComplete (fun q : List Voxel => Polycube.IsConnected q.toFinset ∧
      Tiles3 (Polycube.pairTiles p q.toFinset) (voxelSlab height)) := by
  refine ⟨TwoConnectedPolycubes.slabSmall height, TwoConnectedPolycubes.slabSmall_card_le height,
    TwoConnectedPolycubes.slabSmall_connected height, ?_⟩
  apply coRE_congr _ (TwoConnectedPolycubes.slabsProved height positive)
  intro q
  exact and_congr_right fun _ => (tiles3_iff _ _).symm

theorem three_polycubes_space : ∃ fixed : Bool → Polycube,
    (∀ b, (fixed b).card = 45 ∧ Polycube.IsConnected (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Voxel => Polycube.IsConnected q.toFinset ∧
      TranslationTiles3 (threeTiles fixed q.toFinset) Set.univ) := by
  refine ⟨ThreeTranslationPolycubes.fixed {0,1,2}, fun b => ⟨?_,
    ThreeTranslationPolycubes.fixed_three_connected b⟩, ThreeTranslationPolycubes.space_fixed_distinct, ?_⟩
  · simpa using ThreeTranslationPolycubes.fixed_card ({0,1,2} : Finset Int) b
  · apply coRE_congr _ ThreeTranslationPolycubes.spaceProved
    intro q
    exact and_congr_right fun _ => (translation3_iff _ _).symm

theorem three_polycubes_slab (height : Nat) (positive : 1 < height) :
    ∃ fixed : Bool → Polycube,
    (∀ b, (fixed b).card ≤ 45 ∧ Polycube.IsConnected (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Voxel => Polycube.IsConnected q.toFinset ∧
      TranslationTiles3 (threeTiles fixed q.toFinset) (voxelSlab height)) := by
  refine ⟨ThreeTranslationPolycubes.fixed (ThreeTranslationPolycubes.slabLayers height),
    fun b => ⟨ThreeTranslationPolycubes.slab_fixed_card_le height b,
      ThreeTranslationPolycubes.slab_fixed_connected height b⟩,
    ThreeTranslationPolycubes.slab_fixed_distinct height, ?_⟩
  apply coRE_congr _ (ThreeTranslationPolycubes.slabsProved height positive)
  intro q
  exact and_congr_right fun _ => (translation3_iff _ _).symm

theorem fixed_seed : ∃ p q : Polyomino, p.card = 15 ∧ Polyomino.IsConnected p ∧ q.Nonempty ∧
    LeanWang.CoREComplete (fun seed : List (Placement Bool) =>
      ∃ chosen, ExactCover (fun p' : Placement Bool => p'.cells (pairTiles p q)) Set.univ chosen ∧
        ∀ s ∈ seed, s ∈ chosen) := by
  obtain ⟨p,q,hp,hc,hq,h⟩ := FixedPolyominoSeed.corollary57
  refine ⟨p,q,hp,hc,hq,coRE_congr ?_ h⟩
  intro seed
  have palette : PlaneTilingSearch.tiles (p.toList,q.toList) = pairTiles p q := by
    funext b
    cases b <;> simp [PlaneTilingSearch.tiles, PlaneTilingSearch.tileList, pairTiles]
  change (∃ chosen, IsTiling (PlaneTilingSearch.tiles (p.toList,q.toList)) Set.univ chosen ∧
    ∀ s ∈ seed, s ∈ chosen) ↔ _
  rw [palette]
  constructor
  · rintro ⟨ps, ht, hs⟩
    exact ⟨ps, ⟨ht.tilesInside, ht.uniqueCover⟩, hs⟩
  · rintro ⟨ps, ⟨inside, cover⟩, hs⟩
    exact ⟨ps, ⟨inside, cover⟩, hs⟩

def DominoTiling {d : Nat} (region : Set (Domino.Cell d))
    (chosen : Set (Finset (Domino.Cell d))) : Prop :=
  (∀ f ∈ chosen, Domino.IsDomino f) ∧ ExactCover id region chosen

theorem domino_tiling_iff {d : Nat} (region : Set (Domino.Cell d))
    (chosen : Set (Finset (Domino.Cell d))) :
    DominoTiling region chosen ↔ Domino.IsTiling region chosen := by
  constructor
  · rintro ⟨legal, inside, cover⟩
    exact ⟨fun f hf => ⟨legal f hf, inside f hf⟩, cover⟩
  · intro h
    exact ⟨fun f hf => (h.inside f hf).1, (fun f hf => (h.inside f hf).2), h.covers⟩

theorem domino_doubled {V : Type} [DecidableEq V] [Fintype V] {d r : Nat}
    (C : Domino.Chart V d r) (tileable : ∃ chosen, DominoTiling C.region chosen) :
    ∃ chosen, DominoTiling C.region chosen ∧
      Domino.PeriodicTiles (Domino.doubledPeriod C.period) chosen := by
  obtain ⟨chosen, h⟩ := tileable
  obtain ⟨tiles, ht, hp⟩ := Domino.theorem513 C ⟨chosen, (domino_tiling_iff _ _).mp h⟩
  exact ⟨tiles, (domino_tiling_iff _ _).mpr ht, hp⟩

theorem domino_completion_doubled {V : Type} [DecidableEq V] [Fintype V] {d r : Nat}
    (C : Domino.Chart V d r) (seed : Set (Finset (Domino.Cell d)))
    (periodic : Domino.PeriodicTiles C.period seed)
    (completable : ∃ chosen, DominoTiling C.region chosen ∧ seed ⊆ chosen) :
    ∃ chosen, DominoTiling C.region chosen ∧ seed ⊆ chosen ∧
      Domino.PeriodicTiles (Domino.doubledPeriod C.period) chosen := by
  obtain ⟨chosen, ht, hs⟩ := completable
  obtain ⟨tiles, h, s, p⟩ := Domino.corollary514 C seed periodic
    ⟨chosen, (domino_tiling_iff _ _).mp ht, hs⟩
  exact ⟨tiles, (domino_tiling_iff _ _).mpr h, s, p⟩

theorem domino_decision {n d : Nat} (B : Domino.BasisData n d) (valid : B.Valid) :
    (B.solve = true ↔ ∃ chosen, DominoTiling (B.chart valid).region chosen) ∧
      B.totalCost ≤ Domino.polynomialCoefficient d*(n+1)^2 := by
  obtain ⟨correct, cost⟩ := Domino.corollary515 B valid
  exact ⟨correct.trans (exists_congr fun chosen => (domino_tiling_iff _ _).symm), cost⟩

/-- Express the aperiodic completion result using the abstract's exact-cover predicates. -/
theorem aperiodic_completions (t : Tromino) : ∃ i : PeriodicTrominoPrefill,
    ((i.occupiedRegion t).IsFullRank ∧ Completes t Set.univ (i.prescribed t)) ∧
      ∀ completed, FootprintTiling t Set.univ completed → i.prescribed t ⊆ completed →
        ∀ v, CompletionPeriodic.HasTranslationPeriod completed v → v = (0,0) := by
  obtain ⟨i, rank, _, h, ha⟩ := PeriodicTrominoPrefill.exists_aperiodic_completion t
  exact ⟨i, ⟨rank, (completes_iff _ _ _).mpr h⟩,
    fun completed ht hs => ha completed ((footprints_iff _ _ _).mp ht) hs⟩

export TwoTranslationTrominoes (proved)
export Theorem55 (planeProved stripProved)
export FixedPolyominoSeed (corollary57)
export PeriodicTrominoPrefill (exists_aperiodic_completion)
export Tromino.FiniteCoordinateColumns (completion_npComplete)
export Domino (theorem513 corollary514 corollary515)

end Native

/-! The bridge duplicates only the public mathematical predicates needed by
its statements. All input types below are standard products and lists. -/
namespace Data

abbrev Tromino := Bool
def trominoShape (t : Bool) : Finset (ℤ × ℤ) :=
  if t then {(0,0), (1,0), (0,1)} else {(0,0), (1,0), (2,0)}

abbrev Cell := ℤ × ℤ

abbrev Shape := Finset Cell

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

def ExactCover {A B : Type} (cells : B → Finset A) (region : Set A) (chosen : Set B) : Prop :=
  (∀ p ∈ chosen, ∀ c ∈ cells p, c ∈ region) ∧
    ∀ c ∈ region, ∃! p, p ∈ chosen ∧ c ∈ cells p

def Tileable {I : Type} (tiles : I → Shape) (region : Set Cell) : Prop :=
  ∃ chosen, ExactCover (placedCells tiles) region chosen

def TranslationTileable {I : Type} (tiles : I → Shape) (region : Set Cell) : Prop :=
  ∃ chosen, ExactCover (placedCells tiles) region chosen ∧
    ∀ p ∈ chosen, p.symmetry = 0

def SideAdjacent (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2+1 = b.2 ∨ b.2+1 = a.2)) ∨
    (a.2 = b.2 ∧ (a.1+1 = b.1 ∨ b.1+1 = a.1))

def sideGraph (s : Shape) : SimpleGraph {c // c ∈ s} where
  Adj a b := SideAdjacent a.val b.val
  symm := ⟨by intros a b h; unfold SideAdjacent at *; omega⟩
  loopless := ⟨by intros a h; unfold SideAdjacent at h; omega⟩

def Connected (s : Shape) : Prop := (sideGraph s).Connected

def Strip (height : ℕ) : Set Cell := {c | 0 ≤ c.2 ∧ c.2 < height}

def Pair (p q : Shape) : Bool → Shape := fun b => if b then q else p

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

def straightTiles (vertical : Bool) : Shape :=
  if vertical then {(0,0), (0,1), (0,2)} else trominoShape false

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

def polyominoStripEncoding (input : ℕ × List Cell) : List Bool :=
  unaryFields ([input.1, input.2.length] ++ input.2.flatMap cellFields)

def ThreeTiles {A : Type} (fixed : Bool → A) (input : A) : Option Bool → A
  | none => input
  | some b => fixed b

def FiniteSeedCompletion (p q : Shape) (seed : List (Placement Bool)) : Prop :=
  ∃ chosen, ExactCover (placedCells (Pair p q)) Set.univ chosen ∧ ∀ s ∈ seed, s ∈ chosen

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
  symm := ⟨by intros a b h; simp only [FaceAdjacent, SideAdjacent, Prod.ext_iff] at *; omega⟩
  loopless := ⟨by intros a h; simp only [FaceAdjacent, SideAdjacent] at h; omega⟩

def Connected3 (p : Polycube) : Prop := (faceGraph p).Connected

def Tileable3 {I : Type} (tiles : I → Polycube) (region : Set Voxel) : Prop :=
  ∃ chosen, ExactCover (voxelCells tiles) region chosen

def TranslationTileable3 {I : Type} (tiles : I → Polycube) (region : Set Voxel) : Prop :=
  ∃ chosen, ExactCover (voxelCells tiles) region chosen ∧
    ∀ p ∈ chosen, p.2.1 = (0,false,0)

def Pair3 (p q : Polycube) : Bool → Polycube := fun b => if b then q else p

def Slab (height : ℕ) : Set Voxel := {c | 0 ≤ c.2 ∧ c.2 < height}

def Footprint (t : Tromino) (f : Shape) : Prop :=
  ∃ p : Placement Unit, placedCells (fun _ => trominoShape t) p = f

def FootprintTiling (t : Tromino) (region : Set Cell) (chosen : Set Shape) : Prop :=
  (∀ f ∈ chosen, Footprint t f) ∧ ExactCover id region chosen

def Completable (t : Tromino) (region : Set Cell) (seed : Set Shape) : Prop :=
  ∃ chosen, FootprintTiling t region chosen ∧ seed ⊆ chosen

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

def TranslationPeriod (chosen : Set Shape) (v : Cell) : Prop :=
  ∀ f, f ∈ chosen ↔ f.image (fun c => (v.1+c.1, v.2+c.2)) ∈ chosen

def Aperiodic (chosen : Set Shape) : Prop := ∀ v, TranslationPeriod chosen v → v = (0,0)

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

end Data

namespace Correspondence

open Data

/-- Public symmetry indices follow the displayed order of the eight motions. -/
def symmetry : Data.Symmetry ≃ SquareSymmetry where
  toFun s := ![.identity, .rotate90, .rotate180, .rotate270,
    .reflectX, .reflectDiagonal, .reflectY, .reflectAntidiagonal] s
  invFun s := ⟨CompletionStripEncoding.symmetryCode s, by cases s <;> decide⟩
  left_inv s := by fin_cases s <;> rfl
  right_inv s := by cases s <;> rfl

theorem symmetry_act (s : Data.Symmetry) (c : Data.Cell) :
    Data.symmetryAct s c = (symmetry s).act c := by
  rcases c with ⟨x,y⟩
  fin_cases s <;> rfl

theorem symmetry_code (s : Data.Symmetry) :
    CompletionStripEncoding.symmetryCode (symmetry s) = s.val := by
  fin_cases s <;> rfl

def placement (I : Type) : Data.Placement I ≃ LeanTrominoes.Placement I where
  toFun p := ⟨p.1, symmetry p.2.1, p.2.2⟩
  invFun p := (p.kind, symmetry.symm p.symmetry, p.offset)
  left_inv p := by rcases p with ⟨i,s,c⟩; simp
  right_inv p := by rcases p with ⟨i,s,c⟩; simp

theorem placedCells {I : Type} (tiles : I → Data.Shape) (p : Data.Placement I) :
    Data.placedCells tiles p = (placement I p).cells tiles := by
  unfold Data.placedCells LeanTrominoes.Placement.cells
  simp only [Data.Placement.kind, Data.Placement.offset, Data.Placement.symmetry,
    placement, symmetry_act]
  rfl

def tromino : Bool → LeanTrominoes.Tromino
  | false => .I
  | true => .L

theorem tromino_cells (t : Bool) : Data.trominoShape t = (tromino t).cells := by
  cases t <;> rfl

/-- Transport an exact cover along a bijection of the possible tile occurrences. -/
private theorem exactCover_forward {A B C : Type} (e : A ≃ B) (cells : B → Finset C)
    (region : Set C) (chosen : Set A)
    (cover : Data.ExactCover (fun a => cells (e a)) region chosen) :
    Data.ExactCover cells region (e.symm ⁻¹' chosen) := by
  obtain ⟨inside, unique⟩ := cover
  constructor
  · intro b hb c hc
    exact inside (e.symm b) hb c (by simpa using hc)
  · intro c hc
    obtain ⟨a, ha, single⟩ := unique c hc
    refine ⟨e a, ⟨by simpa using ha.1, ha.2⟩, ?_⟩
    intro b hb
    have equal := single (e.symm b) ⟨hb.1, by simpa using hb.2⟩
    simpa using congrArg e equal

theorem exactCover_iff {A B C : Type} (e : A ≃ B) (cells : B → Finset C)
    (region : Set C) (chosen : Set A) :
    Data.ExactCover (fun a => cells (e a)) region chosen ↔
      Data.ExactCover cells region (e.symm ⁻¹' chosen) := by
  constructor
  · exact exactCover_forward e cells region chosen
  · intro h
    have back := exactCover_forward e.symm (fun a => cells (e a)) region
      (e.symm ⁻¹' chosen) (by simpa only [Data.ExactCover, Equiv.apply_symm_apply] using h)
    simpa [Data.ExactCover] using back

theorem tiles2_iff {I : Type} (tiles : I → Data.Shape) (region : Set Data.Cell) :
    Data.Tileable tiles region ↔ Native.Tiles2 tiles region := by
  constructor
  · rintro ⟨chosen, cover⟩
    refine ⟨((placement I).symm ⁻¹' chosen), ?_⟩
    apply (exactCover_iff (placement I) (fun p => p.cells tiles) region chosen).mp
    simpa only [Data.ExactCover, Native.ExactCover, placedCells] using cover
  · rintro ⟨chosen, cover⟩
    refine ⟨(placement I ⁻¹' chosen), ?_⟩
    have back := exactCover_forward (placement I).symm (Data.placedCells tiles) region chosen
      (by simpa only [Data.ExactCover, Native.ExactCover, placedCells, Equiv.apply_symm_apply] using cover)
    exact back

end Correspondence

namespace Correspondence

open _root_.Computability

theorem identity_iff {I : Type} (p : Data.Placement I) :
    (placement I p).symmetry = SquareSymmetry.identity ↔ p.2.1 = 0 := by
  change symmetry p.2.1 = symmetry 0 ↔ p.2.1 = 0
  exact symmetry.injective.eq_iff

theorem translation2_iff {I : Type} (tiles : I → Data.Shape) (region : Set Data.Cell) :
    Data.TranslationTileable tiles region ↔ Native.TranslationTiles2 tiles region := by
  constructor
  · rintro ⟨chosen, cover, legal⟩
    refine ⟨(placement I).symm ⁻¹' chosen, ?_, ?_⟩
    · apply (exactCover_iff (placement I) (fun p => p.cells tiles) region chosen).mp
      simpa only [Data.ExactCover, Native.ExactCover, placedCells] using cover
    · intro p hp
      have := (identity_iff ((placement I).symm p)).mpr (legal _ hp)
      simpa using this
  · rintro ⟨chosen, cover, legal⟩
    refine ⟨placement I ⁻¹' chosen, ?_, ?_⟩
    · exact exactCover_forward (placement I).symm (Data.placedCells tiles) region chosen
        (by simpa only [Data.ExactCover, Native.ExactCover, placedCells,
          Equiv.apply_symm_apply] using cover)
    · intro p hp
      exact (identity_iff p).mp (legal _ hp)

theorem footprint_iff (t : Bool) (f : Data.Shape) :
    Data.Footprint t f ↔ (tromino t).IsFootprint f := by
  constructor
  · rintro ⟨p, h⟩
    refine ⟨placement Unit p, ?_⟩
    rw [← placedCells, ← tromino_cells]
    exact h
  · rintro ⟨p, h⟩
    refine ⟨(placement Unit).symm p, ?_⟩
    rw [placedCells, Equiv.apply_symm_apply, tromino_cells]
    exact h

theorem footprints_iff (t : Bool) (region : Set Data.Cell) (chosen : Set Data.Shape) :
    Data.FootprintTiling t region chosen ↔ Native.FootprintTiling (tromino t) region chosen := by
  simp only [Data.FootprintTiling, Native.FootprintTiling, footprint_iff]
  rfl

theorem completes_iff (t : Bool) (region : Set Data.Cell) (seed : Set Data.Shape) :
    Data.Completable t region seed ↔ Native.Completes (tromino t) region seed := by
  simp only [Data.Completable, Native.Completes, footprints_iff]

def plane : Data.PlaneInput ≃ PeriodicRegion := PeriodicRegion.equivData.symm

def strip : Data.StripInput ≃ PeriodicStrip := PeriodicStrip.equivData.symm

def planePrefill : Data.PlanePrefill ≃ PeriodicTrominoPrefill :=
  (Equiv.prodCongr (Equiv.listEquivOfEquiv (placement Unit)) (Equiv.refl _)).trans
    PeriodicTrominoPrefill.equivData.symm

def stripPrefill : Data.StripPrefill ≃ PeriodicStripTrominoPrefill where
  toFun i := ⟨i.1.map (placement Unit), i.2.1, i.2.2⟩
  invFun i := (i.motif.map (placement Unit).symm, i.height, i.period)
  left_inv i := by rcases i with ⟨m,h,p⟩; simp
  right_inv i := by rcases i with ⟨m,h,p⟩; simp

theorem plane_primrec : Primrec plane := Primrec.of_equiv_symm

theorem plane_symm_primrec : Primrec plane.symm := Primrec.of_equiv

theorem placement_unit_primrec : Primrec (placement Unit) := by
  have build : Primrec TrominoAssignment.placementUnitEquiv.symm := Primrec.of_equiv_symm
  exact build.comp (Primrec.pair Primrec.fst
    (Primrec.pair ((Primrec.dom_finite symmetry).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)))

theorem placement_unit_symm_primrec : Primrec (placement Unit).symm := by
  have data : Primrec TrominoAssignment.placementUnitEquiv := Primrec.of_equiv
  exact (Primrec.pair Primrec.fst
    (Primrec.pair ((Primrec.dom_finite symmetry.symm).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).comp data

theorem planePrefill_primrec : Primrec planePrefill := by
  have build : Primrec PeriodicTrominoPrefill.equivData.symm := Primrec.of_equiv_symm
  have motif := Primrec.list_map Primrec.id (placement_unit_primrec.comp Primrec.snd).to₂
  exact build.comp (Primrec.pair (motif.comp Primrec.fst) Primrec.snd)

theorem planePrefill_symm_primrec : Primrec planePrefill.symm := by
  have data : Primrec PeriodicTrominoPrefill.equivData := Primrec.of_equiv
  have motif := Primrec.list_map Primrec.id (placement_unit_symm_primrec.comp Primrec.snd).to₂
  exact (Primrec.pair (motif.comp Primrec.fst) Primrec.snd).comp data

theorem prescribed (t : Bool) (i : Data.PlanePrefill) :
    Data.Prescribed t i = (planePrefill i).prescribed (tromino t) := by
  ext f
  simp [Data.Prescribed, PeriodicTrominoPrefill.prescribed, planePrefill,
    Equiv.listEquivOfEquiv, PeriodicTrominoPrefill.equivData, Data.PlanePrefill.motif,
    Data.PlanePrefill.period₁, Data.PlanePrefill.period₂, List.mem_map,
    ← tromino_cells, ← placedCells, Cell.add, Cell.scale]
  rfl

end Correspondence

namespace Correspondence

def cubeSymmetry : Data.CubeSymmetry ≃ LeanTrominoes.CubeSymmetry :=
  (Equiv.prodCongr symmetry (Equiv.refl _)).trans VoxelTilingSearch.symmetryEquiv.symm

theorem cube_act (s : Data.CubeSymmetry) (c : Data.Voxel) :
    Data.cubeAct s c = (cubeSymmetry s).act c := by
  rcases s with ⟨s,flip,axis⟩
  unfold Data.cubeAct LeanTrominoes.CubeSymmetry.act
  simp only [cubeSymmetry, Equiv.trans_apply, Equiv.prodCongr_apply,
    VoxelTilingSearch.symmetryEquiv, Equiv.coe_fn_symm_mk]
  rw [symmetry_act]
  fin_cases axis <;> rfl

def voxelPlacement (I : Type) : Data.VoxelPlacement I ≃ LeanTrominoes.VoxelPlacement I where
  toFun p := ⟨p.1, cubeSymmetry p.2.1, p.2.2⟩
  invFun p := (p.kind, cubeSymmetry.symm p.symmetry, p.offset)
  left_inv p := by rcases p with ⟨i,s,c⟩; simp
  right_inv p := by rcases p with ⟨i,s,c⟩; simp

theorem voxelCells {I : Type} (tiles : I → Data.Polycube) (p : Data.VoxelPlacement I) :
    Data.voxelCells tiles p = (voxelPlacement I p).cells tiles := by
  unfold Data.voxelCells LeanTrominoes.VoxelPlacement.cells
  simp only [voxelPlacement, cube_act]
  rfl

theorem tiles3_iff {I : Type} (tiles : I → Data.Polycube) (region : Set Data.Voxel) :
    Data.Tileable3 tiles region ↔ Native.Tiles3 tiles region := by
  constructor
  · rintro ⟨chosen, cover⟩
    refine ⟨(voxelPlacement I).symm ⁻¹' chosen, ?_⟩
    apply (exactCover_iff (voxelPlacement I) (fun p => p.cells tiles) region chosen).mp
    simpa only [Data.ExactCover, Native.ExactCover, voxelCells] using cover
  · rintro ⟨chosen, cover⟩
    refine ⟨voxelPlacement I ⁻¹' chosen, ?_⟩
    exact exactCover_forward (voxelPlacement I).symm (Data.voxelCells tiles) region chosen
      (by simpa only [Data.ExactCover, Native.ExactCover, voxelCells,
        Equiv.apply_symm_apply] using cover)

theorem cube_identity_iff {I : Type} (p : Data.VoxelPlacement I) :
    (voxelPlacement I p).symmetry = LeanTrominoes.CubeSymmetry.identity ↔ p.2.1 = (0,false,0) := by
  change cubeSymmetry p.2.1 = cubeSymmetry (0,false,0) ↔ p.2.1 = (0,false,0)
  exact cubeSymmetry.injective.eq_iff

theorem translation3_iff {I : Type} (tiles : I → Data.Polycube) (region : Set Data.Voxel) :
    Data.TranslationTileable3 tiles region ↔ Native.TranslationTiles3 tiles region := by
  constructor
  · rintro ⟨chosen, cover, legal⟩
    refine ⟨(voxelPlacement I).symm ⁻¹' chosen, ?_, ?_⟩
    · apply (exactCover_iff (voxelPlacement I) (fun p => p.cells tiles) region chosen).mp
      simpa only [Data.ExactCover, Native.ExactCover, voxelCells] using cover
    · intro p hp
      have := (cube_identity_iff ((voxelPlacement I).symm p)).mpr (legal _ hp)
      simpa using this
  · rintro ⟨chosen, cover, legal⟩
    refine ⟨voxelPlacement I ⁻¹' chosen, ?_, ?_⟩
    · exact exactCover_forward (voxelPlacement I).symm (Data.voxelCells tiles) region chosen
        (by simpa only [Data.ExactCover, Native.ExactCover, voxelCells,
          Equiv.apply_symm_apply] using cover)
    · intro p hp
      exact (cube_identity_iff p).mp (legal _ hp)

end Correspondence

namespace Data

theorem two_polyominoes : ∃ p : Shape, p.card = 15 ∧ Connected p ∧
    LeanWang.CoREComplete (fun q : List Cell => Tileable (Pair p q.toFinset) Set.univ ∧
      q.toFinset.Nonempty ∧ ¬ Connected q.toFinset) ∧
    ComplexityAbstract.PSPACEComplete polyominoStripEncoding
      (fun i : ℕ × List Cell => Tileable (Pair p i.2.toFinset) (Strip i.1) ∧
        0 < i.1 ∧ i.2.toFinset.Nonempty ∧ ¬ Connected i.2.toFinset) := by
  obtain ⟨p, card, connected, plane, strip⟩ := Native.two_polyominoes
  refine ⟨p, card, connected, Native.coRE_congr ?_ plane, ?_⟩
  · intro q
    simp only [← Correspondence.tiles2_iff, and_assoc, and_comm]
    rfl
  · apply ComplexityAbstractBridge.pspaceComplete_congr _
      ((ComplexityAbstractBridge.pspaceComplete_iff _ _).mpr strip)
    intro i
    simp only [← Correspondence.tiles2_iff, and_assoc, and_left_comm, and_comm]
    rfl

theorem three_translated_polyominoes : ∃ fixed : Bool → Shape,
    (∀ b, (fixed b).card = 15 ∧ Connected (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Cell => TranslationTileable (ThreeTiles fixed q.toFinset) Set.univ ∧
      q.toFinset.Nonempty ∧ ¬ Connected q.toFinset) ∧
    ComplexityAbstract.PSPACEComplete polyominoStripEncoding
      (fun i : ℕ × List Cell => TranslationTileable (ThreeTiles fixed i.2.toFinset) (Strip i.1) ∧
        0 < i.1 ∧ i.2.toFinset.Nonempty ∧ ¬ Connected i.2.toFinset) := by
  obtain ⟨fixed, sizes, distinct, plane, strip⟩ := Native.three_polyominoes
  refine ⟨fixed, sizes, distinct, Native.coRE_congr ?_ plane, ?_⟩
  · intro q
    simp only [← Correspondence.translation2_iff, and_assoc, and_comm]
    rfl
  · apply ComplexityAbstractBridge.pspaceComplete_congr _
      ((ComplexityAbstractBridge.pspaceComplete_iff _ _).mpr strip)
    intro i
    simp only [← Correspondence.translation2_iff, and_assoc, and_left_comm, and_comm]
    rfl

theorem two_polycubes_space : ∃ p : Polycube, p.card = 45 ∧ Connected3 p ∧
    LeanWang.CoREComplete (fun q : List Voxel => Tileable3 (Pair3 p q.toFinset) Set.univ ∧
      Connected3 q.toFinset) := by
  obtain ⟨p, card, connected, complete⟩ := Native.two_polycubes_space
  refine ⟨p, card, connected, Native.coRE_congr ?_ complete⟩
  intro q
  simp only [← Correspondence.tiles3_iff, and_comm]
  rfl

theorem two_polycubes_slab (height : ℕ) (positive : 1 < height) :
    ∃ p : Polycube, p.card ≤ 45 ∧ Connected3 p ∧
    LeanWang.CoREComplete (fun q : List Voxel => Tileable3 (Pair3 p q.toFinset) (Slab height) ∧
      Connected3 q.toFinset) := by
  obtain ⟨p, card, connected, complete⟩ := Native.two_polycubes_slab height positive
  refine ⟨p, card, connected, Native.coRE_congr ?_ complete⟩
  intro q
  simp only [← Correspondence.tiles3_iff, and_comm]
  rfl

theorem three_translated_polycubes_space : ∃ fixed : Bool → Polycube,
    (∀ b, (fixed b).card = 45 ∧ Connected3 (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Voxel => TranslationTileable3 (ThreeTiles fixed q.toFinset) Set.univ ∧
      Connected3 q.toFinset) := by
  obtain ⟨fixed, sizes, distinct, complete⟩ := Native.three_polycubes_space
  refine ⟨fixed, sizes, distinct, Native.coRE_congr ?_ complete⟩
  intro q
  simp only [← Correspondence.translation3_iff, and_comm]
  rfl

theorem three_translated_polycubes_slab (height : ℕ) (positive : 1 < height) :
    ∃ fixed : Bool → Polycube,
    (∀ b, (fixed b).card ≤ 45 ∧ Connected3 (fixed b)) ∧ fixed false ≠ fixed true ∧
    LeanWang.CoREComplete (fun q : List Voxel => TranslationTileable3 (ThreeTiles fixed q.toFinset) (Slab height) ∧
      Connected3 q.toFinset) := by
  obtain ⟨fixed, sizes, distinct, complete⟩ := Native.three_polycubes_slab height positive
  refine ⟨fixed, sizes, distinct, Native.coRE_congr ?_ complete⟩
  intro q
  simp only [← Correspondence.translation3_iff, and_comm]
  rfl

end Data

namespace Correspondence

theorem plane_problem_iff (t : Bool) (i : Data.PlaneInput) :
    Data.TrominoPlane t i ↔ ((plane i).IsFullRank ∧
      Native.Tiles2 (fun _ : Unit => (tromino t).cells) (plane i).carrier) := by
  rw [← tromino_cells]
  change (Data.Tileable (fun _ : Unit => Data.trominoShape t) (Data.PlaneRegion i) ∧
    Data.FullRank i) ↔ (Data.FullRank i ∧
      Native.Tiles2 (fun _ : Unit => Data.trominoShape t) (Data.PlaneRegion i))
  rw [tiles2_iff]
  exact and_comm

theorem strip_problem_iff (t : Bool) (i : Data.StripInput) :
    Data.TrominoStrip t i ↔ ((strip i).IsWellFormed ∧
      Native.Tiles2 (fun _ : Unit => (tromino t).cells)
        {c | 0 ≤ c.2 ∧ c.2 < ((strip i).width : Int) ∧ ∃ b ∈ (strip i).motif, ∃ k : Int,
          c = (b.1+k*((strip i).period : Int), b.2)}) := by
  rw [← tromino_cells]
  change (Data.Tileable (fun _ : Unit => Data.trominoShape t) (Data.StripRegion i) ∧
    Data.ValidStrip i) ↔ (Data.ValidStrip i ∧
      Native.Tiles2 (fun _ : Unit => Data.trominoShape t) (Data.StripRegion i))
  rw [tiles2_iff]
  exact and_comm

theorem strip_words (i : Data.StripInput) :
    (Data.stripEncoding i).map (Equiv.refl _) = PeriodicStripFlatEncoding.finEncoding.encode (strip i) := by
  simp only [Equiv.coe_refl, List.map_id]
  change Turing.PartrecToTM2.trList _ = PeriodicCNFFlatEncoding.encodeNatFields _
  exact (PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _).symm

theorem plane_completion_iff (t : Bool) (i : Data.PlanePrefill) :
    Data.PlaneCompletion t i ↔
      ((planePrefill i).occupiedRegion (tromino t)).IsFullRank ∧
        Native.Completes (tromino t) Set.univ ((planePrefill i).prescribed (tromino t)) := by
  unfold Data.PlaneCompletion
  rw [completes_iff, prescribed]
  exact and_comm

end Correspondence

namespace Data

theorem tromino_plane (t : Tromino) : LeanWang.CoREComplete (TrominoPlane t) := by
  exact ComplexityAbstractBridge.coRE_recode Correspondence.plane
    Correspondence.plane_primrec.to_comp Correspondence.plane_symm_primrec.to_comp
    _ _ (Correspondence.plane_problem_iff t) (Native.tromino_plane (Correspondence.tromino t))

theorem tromino_strip (t : Tromino) : ComplexityAbstract.PSPACEComplete stripEncoding (TrominoStrip t) := by
  exact ComplexityAbstractBridge.pspaceComplete_recode stripEncoding _
    Correspondence.strip (Equiv.refl _) Correspondence.strip_words _ _
    (Correspondence.strip_problem_iff t)
    ((ComplexityAbstractBridge.pspaceComplete_iff _ _).mpr
      (Native.tromino_strip (Correspondence.tromino t)))

theorem tromino_completion_plane (t : Tromino) : LeanWang.CoREComplete (PlaneCompletion t) := by
  exact ComplexityAbstractBridge.coRE_recode Correspondence.planePrefill
    Correspondence.planePrefill_primrec.to_comp Correspondence.planePrefill_symm_primrec.to_comp
    _ _ (Correspondence.plane_completion_iff t)
    (Native.completion_plane (Correspondence.tromino t))

theorem aperiodic_completions (t : Tromino) : ∃ i : PlanePrefill,
    PlaneCompletion t i ∧ ∀ completed,
      FootprintTiling t Set.univ completed → Prescribed t i ⊆ completed → Aperiodic completed := by
  obtain ⟨i, completion, aperiodic⟩ := Native.aperiodic_completions (Correspondence.tromino t)
  let j := Correspondence.planePrefill.symm i
  have hj : Correspondence.planePrefill j = i := Equiv.apply_symm_apply _ _
  refine ⟨j, (Correspondence.plane_completion_iff t j).mpr ?_, ?_⟩
  · rw [hj]
    exact completion
  · intro completed ht hs
    have retained : i.prescribed (Correspondence.tromino t) ⊆ completed := by
      rw [← hj, ← Correspondence.prescribed]
      exact hs
    exact aperiodic completed ((Correspondence.footprints_iff _ _ _).mp ht) retained

end Data

namespace Correspondence

theorem strip_completion_iff (t : Bool) (i : Data.StripPrefill) :
    Data.StripCompletion t i ↔
      (0 < (stripPrefill i).height ∧ 0 < (stripPrefill i).period ∧
        Native.Completes (tromino t) (stripPrefill i).region
          ((stripPrefill i).periodic.prescribed (tromino t))) := by
  unfold Data.StripCompletion
  rw [completes_iff, prescribed]
  constructor
  · rintro ⟨completion, height, period⟩
    exact ⟨height, period, completion⟩
  · rintro ⟨height, period, completion⟩
    exact ⟨completion, height, period⟩

theorem completion_strip_words (i : Data.StripPrefill) :
    (Data.completionStripEncoding i).map (Equiv.refl _) =
      CompletionStripEncoding.finEncoding.encode (stripPrefill i) := by
  simp [Data.completionStripEncoding, Data.StripPrefill.height, Data.StripPrefill.period,
    Data.StripPrefill.motif, Data.Placement.symmetry, Data.Placement.offset,
    CompletionStripEncoding.finEncoding, CompletionStripEncoding.fields,
    CompletionStripEncoding.placementFields, stripPrefill, placement, symmetry_code,
    List.flatMap_map, Data.unaryFields, CompletionStripEncoding.unaryFields]

end Correspondence

namespace Data

theorem two_translated_trominoes :
    LeanWang.CoREComplete (fun r : PlaneInput =>
      TranslationTileable straightTiles (PlaneRegion r) ∧ FullRank r) ∧
    ComplexityAbstract.PSPACEComplete stripEncoding (fun r : StripInput =>
      TranslationTileable straightTiles (StripRegion r) ∧ ValidStrip r) := by
  obtain ⟨plane, strip⟩ := Native.translated_trominoes
  constructor
  · apply ComplexityAbstractBridge.coRE_recode Correspondence.plane
      Correspondence.plane_primrec.to_comp Correspondence.plane_symm_primrec.to_comp _ _ _ plane
    intro i
    change (TranslationTileable straightTiles (PlaneRegion i) ∧ FullRank i) ↔
      (FullRank i ∧ Native.TranslationTiles2 straightTiles (PlaneRegion i))
    rw [Correspondence.translation2_iff]
    exact and_comm
  · apply ComplexityAbstractBridge.pspaceComplete_recode stripEncoding _
      Correspondence.strip (Equiv.refl _) Correspondence.strip_words _ _ _
      ((ComplexityAbstractBridge.pspaceComplete_iff _ _).mpr strip)
    intro i
    change (TranslationTileable straightTiles (StripRegion i) ∧ ValidStrip i) ↔
      (ValidStrip i ∧ Native.TranslationTiles2 straightTiles (StripRegion i))
    rw [Correspondence.translation2_iff]
    exact and_comm

theorem tromino_completion_strip (t : Tromino) : ComplexityAbstract.PSPACEComplete
    completionStripEncoding (StripCompletion t) := by
  exact ComplexityAbstractBridge.pspaceComplete_recode completionStripEncoding _
    Correspondence.stripPrefill (Equiv.refl _) Correspondence.completion_strip_words _ _
    (Correspondence.strip_completion_iff t)
    ((ComplexityAbstractBridge.pspaceComplete_iff _ _).mpr
      (Native.completion_strip (Correspondence.tromino t)))

end Data

namespace Correspondence

open _root_.Computability

def seed : List (Data.Placement Bool) ≃ List (LeanTrominoes.Placement Bool) :=
  Equiv.listEquivOfEquiv (placement Bool)

theorem placement_bool_primrec : Primrec (placement Bool) := by
  exact PlaneTilingSearch.placement_mk_primrec.comp (Primrec.pair Primrec.fst
    (Primrec.pair ((Primrec.dom_finite symmetry).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)))

theorem placement_bool_symm_primrec : Primrec (placement Bool).symm := by
  exact (Primrec.pair Primrec.fst
    (Primrec.pair ((Primrec.dom_finite symmetry.symm).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).comp PlaneTilingSearch.placement_data_primrec

theorem seed_primrec : Primrec seed :=
  Primrec.list_map Primrec.id (placement_bool_primrec.comp Primrec.snd).to₂

theorem seed_symm_primrec : Primrec seed.symm :=
  Primrec.list_map Primrec.id (placement_bool_symm_primrec.comp Primrec.snd).to₂

theorem seedCompletion_iff (p q : Data.Shape) (ps : List (Data.Placement Bool)) :
    Data.FiniteSeedCompletion p q ps ↔
      (∃ chosen, Native.ExactCover (fun s : LeanTrominoes.Placement Bool =>
        s.cells (pairTiles p q)) Set.univ chosen ∧ ∀ s ∈ seed ps, s ∈ chosen) := by
  have palette : Data.Pair p q = pairTiles p q := by funext b; cases b <;> rfl
  constructor
  · rintro ⟨chosen, cover, prescribed⟩
    change Data.ExactCover (Data.placedCells (Data.Pair p q)) Set.univ chosen at cover
    rw [palette] at cover
    refine ⟨(placement Bool).symm ⁻¹' chosen, ?_, ?_⟩
    · apply (exactCover_iff (placement Bool) (fun s => s.cells (pairTiles p q)) Set.univ chosen).mp
      simpa only [Data.ExactCover, Native.ExactCover, placedCells] using cover
    · intro s member
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp member
      change (placement Bool).symm (placement Bool p) ∈ chosen
      simpa using prescribed p hp
  · rintro ⟨chosen, cover, prescribed⟩
    refine ⟨placement Bool ⁻¹' chosen, ?_, ?_⟩
    · rw [palette]
      exact exactCover_forward (placement Bool).symm (Data.placedCells (pairTiles p q)) Set.univ chosen
        (by simpa only [Data.ExactCover, Native.ExactCover, placedCells,
          Equiv.apply_symm_apply] using cover)
    · intro p member
      exact prescribed (placement Bool p) (List.mem_map.mpr ⟨p, member, rfl⟩)

end Correspondence

namespace Data

theorem fixed_pair_seed : ∃ p q : Shape, p.card = 15 ∧ Connected p ∧ q.Nonempty ∧
    LeanWang.CoREComplete (FiniteSeedCompletion p q) := by
  obtain ⟨p,q,card,connected,nonempty,complete⟩ := Native.fixed_seed
  refine ⟨p,q,card,connected,nonempty,?_⟩
  exact ComplexityAbstractBridge.coRE_recode Correspondence.seed
    Correspondence.seed_primrec.to_comp Correspondence.seed_symm_primrec.to_comp
    _ _ (Correspondence.seedCompletion_iff p q) complete

end Data

namespace Correspondence

private abbrev Columns := LeanTrominoes.Tromino.FiniteCoordinateColumns.Field
private abbrev Tokens := LeanTrominoes.Tromino.FiniteCoordinateColumns.Token

private def column : Fin 5 ≃ Columns where
  toFun k := ![.regionX, .regionY, .prefillSymmetry, .prefillX, .prefillY] k
  invFun k := match k with
    | .regionX => 0 | .regionY => 1 | .prefillSymmetry => 2 | .prefillX => 3 | .prefillY => 4
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by cases k <;> rfl

private def unarySymbol : Bool ≃ UnaryFieldEncoderMachine.Symbol where
  toFun b := if b then .unit else .delimiter
  invFun s := match s with | .unit => true | .delimiter => false
  left_inv b := by cases b <;> rfl
  right_inv s := by cases s <;> rfl

def coordinateSymbol : Data.CoordinateSymbol ≃ Tokens where
  toFun s := match s with
    | .inl (k,b) => .field (column k) (unarySymbol b)
    | .inr b => .bit b
  invFun s := match s with
    | .field k b => .inl (column.symm k, unarySymbol.symm b)
    | .bit b => .inr b
  left_inv s := by rcases s with ⟨k,b⟩ | b <;> simp
  right_inv s := by cases s <;> simp

private theorem unary_words (values : List ℕ) :
    (Data.unaryFields values).map unarySymbol = UnaryFieldEncoderMachine.unaryFields values := by
  simp [Data.unaryFields, UnaryFieldEncoderMachine.unaryFields,
    List.map_flatMap, List.map_replicate, unarySymbol]
  rfl

private theorem column_words (k : Fin 5) (values : List ℕ) :
    ((Data.unaryFields values).map (fun b => Sum.inl (k,b))).map coordinateSymbol =
      (UnaryFieldEncoderMachine.unaryFields values).map (LeanTrominoes.Tromino.FiniteCoordinateColumns.Token.field (column k)) := by
  rw [← unary_words]
  simp only [List.map_map]
  rfl

private theorem coordinate_values (cells : List Data.Cell) (ps : List (Data.Placement Unit))
    (k : Fin 5) :
    LeanTrominoes.Tromino.FiniteCoordinateColumns.values ⟨cells, ps.map (placement Unit)⟩ (column k) =
      ![cells.map (fun c => Encodable.encode c.1), cells.map (fun c => Encodable.encode c.2),
        ps.map (fun p => p.symmetry.val), ps.map (fun p => Encodable.encode p.offset.1),
        ps.map (fun p => Encodable.encode p.offset.2)] k := by
  fin_cases k <;> simp [LeanTrominoes.Tromino.FiniteCoordinateColumns.values, column,
    placement, symmetry_code, List.map_map, Function.comp_def, Data.Placement.symmetry,
    Data.Placement.offset]

theorem coordinate_words (cells : List Data.Cell) (ps : List (Data.Placement Unit)) :
    (Data.coordinateEncoding cells ps).map coordinateSymbol =
      LeanTrominoes.Tromino.FiniteCoordinateColumns.encodeInput ⟨cells, ps.map (placement Unit)⟩ := by
  have columns : LeanTrominoes.Tromino.FiniteCoordinateColumns.fields = (List.finRange 5).map column := rfl
  unfold Data.coordinateEncoding LeanTrominoes.Tromino.FiniteCoordinateColumns.encodeInput
  dsimp only
  rw [columns, List.flatMap_map, List.map_flatMap]
  apply congrArg (fun f : Fin 5 → List Tokens => (List.finRange 5).flatMap f)
  funext k
  rw [coordinate_values]
  exact column_words k _

def unitSeed : List (Data.Placement Unit) ≃ List (LeanTrominoes.Placement Unit) :=
  Equiv.listEquivOfEquiv (placement Unit)

theorem completion_footprints (t : Bool) (ps : List (Data.Placement Unit)) :
    LeanTrominoes.Tromino.FiniteCoordinateColumns.completionFootprints (tromino t) (unitSeed ps) =
      ps.map (Data.placedCells (fun _ => Data.trominoShape t)) := by
  unfold LeanTrominoes.Tromino.FiniteCoordinateColumns.completionFootprints
  change ((ps.map (placement Unit)).map _) = _
  rw [List.map_map]
  apply congrArg (fun f : Data.Placement Unit → Data.Shape => ps.map f)
  funext p
  change (placement Unit p).cells (fun _ => (tromino t).cells) =
    Data.placedCells (fun _ => Data.trominoShape t) p
  rw [← placedCells, ← tromino_cells]

theorem completion_radius (t : Bool) (ps : List (Data.Placement Unit)) :
    Data.completionRadius t ps = LeanTrominoes.Tromino.FiniteWitness.radius
      (LeanTrominoes.Tromino.FiniteCoordinateColumns.completionFootprints (tromino t) (unitSeed ps)).toFinset := by
  rw [completion_footprints]
  rfl

theorem finite_completion_words (t : Bool) (ps : List (Data.Placement Unit)) :
    (Data.finiteCompletionEncoding t ps).map coordinateSymbol =
      (LeanTrominoes.Tromino.FiniteCoordinateColumns.completionEncoding (tromino t)).encode (unitSeed ps) := by
  unfold Data.finiteCompletionEncoding
  rw [coordinate_words]
  change LeanTrominoes.Tromino.FiniteCoordinateColumns.encodeInput
      ⟨Data.completionBox (Data.completionRadius t ps), ps.map (placement Unit)⟩ =
    LeanTrominoes.Tromino.FiniteCoordinateColumns.encodeInput
      ⟨LeanTrominoes.Tromino.FiniteWitness.boxList
        (LeanTrominoes.Tromino.FiniteWitness.radius
          (LeanTrominoes.Tromino.FiniteCoordinateColumns.completionFootprints (tromino t) (unitSeed ps)).toFinset),
        ps.map (placement Unit)⟩
  rw [← completion_radius]
  rfl

theorem finite_completion_iff (t : Bool) (ps : List (Data.Placement Unit)) :
    Data.FiniteCompletion t ps ↔ Native.Completes (tromino t) Set.univ
      ((LeanTrominoes.Tromino.FiniteCoordinateColumns.completionFootprints (tromino t) (unitSeed ps)).toFinset :
        Set (Finset Data.Cell)) := by
  unfold Data.FiniteCompletion
  rw [completes_iff, completion_footprints]

end Correspondence

namespace Data

theorem finite_tromino_region (t : Tromino) : ComplexityAbstract.NPComplete finiteRegionEncoding
    (fun cells : List Cell => Tileable (fun _ : Unit => trominoShape t) (cells.toFinset : Set Cell)) := by
  apply ComplexityAbstractBridge.npComplete_recode finiteRegionEncoding
    LeanTrominoes.Tromino.FiniteCoordinateColumns.regionEncoding.encode
    (Equiv.refl _) Correspondence.coordinateSymbol
    (fun cells => Correspondence.coordinate_words cells []) _ _ _
    ((ComplexityAbstractBridge.npComplete_iff _ _).mpr
      (Native.finite_region (Correspondence.tromino t)))
  intro cells
  rw [← Correspondence.tromino_cells]
  exact Correspondence.tiles2_iff _ _

theorem finite_tromino_completion (t : Tromino) : ComplexityAbstract.NPComplete
    (finiteCompletionEncoding t) (FiniteCompletion t) := by
  exact ComplexityAbstractBridge.npComplete_recode (finiteCompletionEncoding t) _
    Correspondence.unitSeed Correspondence.coordinateSymbol (Correspondence.finite_completion_words t) _ _
    (Correspondence.finite_completion_iff t)
    ((ComplexityAbstractBridge.npComplete_iff _ _).mpr
      (Native.finite_completion (Correspondence.tromino t)))

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
  map_zero' := by simp
  map_add' := by intros; simp only [map_add]; abel

theorem domino_doubled {V : Type} [DecidableEq V] [Fintype V] {d r : ℕ}
    (C : Chart V d r) (unique : C.Valid) (tileable : ∃ chosen, DominoTiling C.region chosen) :
    ∃ chosen, DominoTiling C.region chosen ∧
      PeriodicTiles (doubledPeriod C.period) chosen := by
  let native : LeanTrominoes.Domino.Chart V d r := ⟨C.origin, C.period, unique⟩
  exact Native.domino_doubled native tileable

theorem domino_completion_doubled {V : Type} [DecidableEq V] [Fintype V] {d r : ℕ}
    (C : Chart V d r) (unique : C.Valid) (seed : Set (Finset (Lattice d)))
    (periodic : PeriodicTiles C.period seed)
    (completable : ∃ chosen, DominoTiling C.region chosen ∧ seed ⊆ chosen) :
    ∃ chosen, DominoTiling C.region chosen ∧ seed ⊆ chosen ∧
      PeriodicTiles (doubledPeriod C.period) chosen := by
  let native : LeanTrominoes.Domino.Chart V d r := ⟨C.origin, C.period, unique⟩
  exact Native.domino_completion_doubled native seed periodic completable

end Data

end LeanTrominoes.TilingAbstractBridge
