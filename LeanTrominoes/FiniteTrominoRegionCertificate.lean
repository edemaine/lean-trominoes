/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoWitness

/-! # Binary certificates for finite-region tromino tiling

An explicitly listed region has at most 24 candidate placements per listed
cell. One bit per candidate selects a finite exact cover. This supplies an
executable verifier and a linear certificate bound; a polynomial-time Turing
machine implementing the verifier is a separate requirement for NP membership.
-/
namespace LeanTrominoes.Tromino.FiniteRegion
open FiniteWitness

def Valid (t : Tromino) (region : Finset Cell) (tiles : Finset (Finset Cell)) : Prop :=
  FiniteWitness.Valid t region ∅ tiles ∧ ∀ tile∈tiles, tile⊆region

instance (t : Tromino) (region : Finset Cell) (tiles : Finset (Finset Cell)) :
    Decidable (Valid t region tiles) := by unfold Valid; infer_instance

theorem valid_iff_footprintTiling (t : Tromino) (region : Finset Cell) (tiles : Finset (Finset Cell)) :
    Valid t region tiles ↔ t.IsFootprintTiling (region : Set Cell) (tiles : Set (Finset Cell)) := by
  constructor
  · rintro ⟨h,inside⟩
    refine ⟨fun tile ht => ⟨((mem_candidates t region tile).mp (h.1 ht)).1,inside tile ht⟩,?_⟩
    intro cell hc
    obtain ⟨tile,ht,covers⟩ := h.2.2.2 cell hc
    exact ⟨tile,⟨ht,covers⟩,fun other ho => h.2.2.1 other ho.1 tile ht cell ho.2 covers⟩
  · intro tiling
    have candidate (tile : Finset Cell) (ht : tile∈tiles) : tile∈candidates t region := by
      obtain ⟨placement,eq⟩ := (tiling.tilesInside tile ht).1
      apply (mem_candidates t region tile).mpr
      have covers : placement.offset∈tile := eq ▸ offset_mem_placement_cells t placement
      exact ⟨⟨placement,eq⟩,placement.offset,(tiling.tilesInside tile ht).2 _ covers,covers⟩
    refine ⟨⟨candidate,by simp,?_,?_⟩,fun tile ht => (tiling.tilesInside tile ht).2⟩
    · intro first hf second hs cell hc hd
      obtain ⟨chosen,_,unique⟩ := tiling.uniqueCover cell ((tiling.tilesInside first hf).2 cell hc)
      exact (unique first ⟨hf,hc⟩).trans (unique second ⟨hs,hd⟩).symm
    · intro cell hc
      obtain ⟨tile,⟨ht,covers⟩,_⟩ := tiling.uniqueCover cell hc
      exact ⟨tile,ht,covers⟩

theorem tileable_iff_valid (t : Tromino) (region : Finset Cell) :
    t.Tileable (region : Set Cell) ↔ ∃ tiles, Valid t region tiles := by
  rw [tileable_iff_exists_footprintTiling]
  constructor
  · rintro ⟨footprints,tiling⟩
    classical
    let tiles := (candidates t region).filter fun tile => tile∈footprints
    have member (tile : Finset Cell) : tile∈tiles ↔ tile∈candidates t region ∧ tile∈footprints :=
      Finset.mem_filter
    have covers (cell : Cell) (hc : cell∈region) :
        ∃ tile∈tiles, cell∈tile := by
      obtain ⟨tile,⟨ht,covers⟩,_⟩ := tiling.uniqueCover cell hc
      exact ⟨tile,(member tile).mpr ⟨(mem_candidates t region tile).mpr
        ⟨(tiling.tilesInside tile ht).1,cell,hc,covers⟩,ht⟩,covers⟩
    refine ⟨tiles,⟨⟨fun tile ht => ((member tile).mp ht).1,by simp,?_,covers⟩,?_⟩⟩
    · intro first hf second hs cell hc hd
      have firstIn := ((member first).mp hf).2
      have secondIn := ((member second).mp hs).2
      obtain ⟨chosen,_,unique⟩ := tiling.uniqueCover cell ((tiling.tilesInside first firstIn).2 cell hc)
      exact (unique first ⟨firstIn,hc⟩).trans (unique second ⟨secondIn,hd⟩).symm
    · intro tile ht
      exact (tiling.tilesInside tile ((member tile).mp ht).2).2
  · rintro ⟨tiles,h⟩
    exact ⟨(tiles : Set (Finset Cell)),(valid_iff_footprintTiling t region tiles).mp h⟩

def symmetries : List SquareSymmetry :=
  [.identity,.rotate90,.rotate180,.rotate270,.reflectX,.reflectDiagonal,.reflectY,.reflectAntidiagonal]

@[simp] theorem mem_symmetries (symmetry : SquareSymmetry) : symmetry∈symmetries := by
  cases symmetry <;> simp [symmetries]

def baseCells : Tromino → List Cell
  | .I => [(0,0),(1,0),(2,0)]
  | .L => [(0,0),(1,0),(0,1)]

@[simp] theorem mem_baseCells (t : Tromino) (cell : Cell) : cell∈baseCells t ↔ cell∈t.cells := by
  cases t <;> simp [baseCells,Tromino.cells]

def coveringList (t : Tromino) (cell : Cell) : List (Placement Unit) :=
  symmetries.flatMap fun symmetry => (baseCells t).map fun source =>
    ⟨(),symmetry,Cell.sub cell (symmetry.act source)⟩

theorem mem_coveringList (t : Tromino) (cell : Cell) (placement : Placement Unit) :
    placement∈coveringList t cell ↔ placement∈TrominoAssignment.coveringPlacements t cell := by
  simp [coveringList,TrominoAssignment.coveringPlacements,List.mem_flatMap,List.mem_map,
    Finset.mem_image,Finset.mem_product]

@[simp] theorem coveringList_length (t : Tromino) (cell : Cell) : (coveringList t cell).length=24 := by
  cases t <;> simp [coveringList,symmetries,baseCells]

def candidateList (t : Tromino) (cells : List Cell) : List (Finset Cell) :=
  cells.flatMap fun cell => (coveringList t cell).map (Placement.cells (fun _ => t.cells))

theorem candidateList_eq (t : Tromino) (cells : List Cell) :
    (candidateList t cells).toFinset=candidates t cells.toFinset := by
  ext tile
  simp [candidateList,candidates,List.mem_flatMap,List.mem_map,Finset.mem_biUnion,
    Finset.mem_image,mem_coveringList]

@[simp] theorem candidateList_length (t : Tromino) (cells : List Cell) :
    (candidateList t cells).length=24*cells.length := by
  simp [candidateList,Nat.mul_comm]

def select (candidates : List (Finset Cell)) (bits : List Bool) : Finset (Finset Cell) :=
  ((candidates.zip bits).filterMap fun entry => if entry.2 then some entry.1 else none).toFinset

theorem select_encode (candidates : List (Finset Cell)) (tiles : Finset (Finset Cell)) :
    select candidates (candidates.map fun tile => decide (tile∈tiles))=
      candidates.toFinset.filter (fun tile => tile∈tiles) := by
  induction candidates with
  | nil => simp [select]
  | cons tile candidates ih =>
    by_cases member : tile∈tiles <;> simp_all [select,List.zip]
    all_goals
      ext other
      simp only [Finset.mem_insert,Finset.mem_filter]
      aesop

def check (t : Tromino) (cells : List Cell) (bits : List Bool) : Bool :=
  decide (Valid t cells.toFinset (select (candidateList t cells) bits))

/-- The witness is one bit for each of 24 candidate placements per input cell.
Duplicate input cells and duplicate placement representations are allowed. -/
theorem tileable_iff_bounded_certificate (t : Tromino) (cells : List Cell) :
    t.Tileable (cells.toFinset : Set Cell) ↔
      ∃ bits : List Bool, bits.length≤24*cells.length ∧ check t cells bits=true := by
  rw [tileable_iff_valid]
  constructor
  · rintro ⟨tiles,valid⟩
    refine ⟨(candidateList t cells).map fun tile => decide (tile∈tiles),by simp,?_⟩
    have selected : select (candidateList t cells)
        ((candidateList t cells).map fun tile => decide (tile∈tiles))=tiles := by
      rw [select_encode,candidateList_eq]
      ext tile
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨valid.1.1 h,h⟩⟩
    simpa [check,selected] using valid
  · rintro ⟨bits,_,h⟩
    exact ⟨select (candidateList t cells) bits,by simpa [check] using h⟩

end LeanTrominoes.Tromino.FiniteRegion
