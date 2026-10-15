/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Results

/-! # Proof bridge for the tiling abstract

The input records, their encodings, and their mathematical answers are
preserved. The lemmas below expand exact-cover and completion predicates;
they do not replace an input representation by a merely set-theoretically
equivalent one. This module does not import `TilingAbstract` or `GraphAbstract`.
-/

namespace LeanTrominoes.TilingAbstractBridge

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

export TwoTranslationTrominoes (proved)
export Theorem55 (planeProved stripProved)
export FixedPolyominoSeed (corollary57)
export PeriodicTrominoPrefill (exists_aperiodic_completion)
export Tromino.FiniteCoordinateColumns (completion_npComplete)
export Domino (theorem513 corollary514 corollary515)

end LeanTrominoes.TilingAbstractBridge
