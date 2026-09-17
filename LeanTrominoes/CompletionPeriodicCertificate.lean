/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPrefillComputability

/-! # Finite certificates for periodic plane completions

A certificate stores a relative tile at every cell of a square period.
Local agreement of tiles covering the same cell certifies an exact tiling.
-/
namespace LeanTrominoes
namespace CompletionPeriodic
open PeriodicTrominoPrefill TrominoAssignment
set_option maxHeartbeats 2000000

abbrev Certificate := Nat × List (Placement Unit)
def residue (n : Nat) (c : Cell) : Cell := (c.1 % (n:Int), c.2 % (n:Int))
def key (n : Nat) (c : Cell) : Nat := (residue n c).1.toNat*n+(residue n c).2.toNat
def entry (w : Certificate) (c : Cell) : Placement Unit :=
  w.2.getD (key w.1 c) ⟨(),.identity,(0,0)⟩
def tileList (t : Tromino) (w : Certificate) (c : Cell) : List Cell :=
  (placementCells t (entry w c)).map (Cell.add c)
def tile (t : Tromino) (w : Certificate) (c : Cell) : Finset Cell := (tileList t w c).toFinset

def SameCells (xs ys : List Cell) : Prop := (∀ c ∈ xs, c ∈ ys) ∧ (∀ c ∈ ys, c ∈ xs)
theorem sameCells_iff (xs ys : List Cell) : SameCells xs ys ↔ xs.toFinset = ys.toFinset := by
  simp only [SameCells, Finset.ext_iff, List.mem_toFinset]
  constructor
  · rintro ⟨a,b⟩ c; exact ⟨a c,b c⟩
  · intro h; exact ⟨fun c => (h c).mp,fun c => (h c).mpr⟩

def Check (t : Tromino) (input : PeriodicTrominoPrefill) (w : Certificate) : Prop :=
  0 < w.1 ∧
  (∀ c ∈ boxCellList w.1, c ∈ tileList t w c ∧
    ∀ d ∈ tileList t w c, SameCells (tileList t w d) (tileList t w c)) ∧
  (∀ index ∈ boxCellList w.1, ∀ p ∈ input.motif,
    SameCells (repeatedCells t input index p)
      (tileList t w (Cell.add (repeatOffset input index) p.offset)))

theorem residue_mem (n : Nat) (hn : 0 < n) (c : Cell) : residue n c ∈ boxCellList n := by
  rw [mem_boxCellList_iff]
  have h : (0:Int) < n := by exact_mod_cast hn
  have hx := Int.emod_nonneg c.1 (ne_of_gt h)
  have hy := Int.emod_nonneg c.2 (ne_of_gt h)
  have hxx := Int.emod_lt_of_pos c.1 h
  have hyy := Int.emod_lt_of_pos c.2 h
  dsimp [residue,LeanWang.InBox]; omega

theorem residue_add (n : Nat) (a b : Cell) :
    residue n (Cell.add (residue n a) b) = residue n (Cell.add a b) := by
  ext <;> simp [residue,Cell.add,Int.add_emod]

theorem residue_idem (n : Nat) (c : Cell) : residue n (residue n c) = residue n c := by
  ext <;> simp [residue]

theorem tile_eq_image (t : Tromino) (w : Certificate) (c : Cell) :
    tile t w c = ((entry w c).cells (fun _ => t.cells)).image (Cell.add c) := by
  ext d; simp [tile,tileList,mem_placementCells]

theorem tile_legal (t : Tromino) (w : Certificate) (c : Cell) : t.IsFootprint (tile t w c) := by
  rw [tile_eq_image]; exact Tromino.IsFootprint.translate ⟨_,rfl⟩ c

/-- Tile fields commute with any translation that preserves the residue. -/
theorem tile_translate (t : Tromino) (w : Certificate) (a v : Cell)
    (h : residue w.1 (Cell.add a v) = residue w.1 a) :
    tile t w (Cell.add a v) = (tile t w a).image (Cell.add v) := by
  have e : entry w (Cell.add a v) = entry w a := by simp only [entry,key,h]
  simp only [tile_eq_image,e,Finset.image_image]
  congr 1; funext c; ext <;> simp [Cell.add] <;> omega

private theorem shift_mem (f : Finset Cell) (c v : Cell) :
    Cell.add c v ∈ f.image (Cell.add v) ↔ c ∈ f := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨d,hd,eq⟩
    have hx := congrArg Prod.fst eq; have hy := congrArg Prod.snd eq
    have : d = c := by ext <;> dsimp [Cell.add] at * <;> omega
    simpa [this] using hd
  · exact fun h => ⟨c,h,by ext <;> simp [Cell.add,Int.add_comm]⟩

/-- Agreement on one finite period implies agreement everywhere. -/
theorem check_global (t : Tromino) (input : PeriodicTrominoPrefill) (w : Certificate)
    (h : Check t input w) : ∀ c, c ∈ tile t w c ∧ ∀ d ∈ tile t w c, tile t w d = tile t w c := by
  intro c
  let r := residue w.1 c
  let v := Cell.sub c r
  have cv : Cell.add r v = c := by ext <;> simp [v,Cell.add,Cell.sub]
  have trans (a : Cell) : residue w.1 (Cell.add a v) = residue w.1 a := by
    ext <;> simp [residue,v,r,Cell.add,Cell.sub,Int.add_emod,Int.sub_emod]
  have checked :=  h.2.1 r (residue_mem w.1 h.1 c)
  have tc := tile_translate t w r v (trans r)
  rw [cv] at tc
  constructor
  · rw [tc,← cv,shift_mem]; exact List.mem_toFinset.mpr checked.1
  · intro d hd
    rw [tc] at hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    rw [show Cell.add v e = Cell.add e v by ext <;> simp [Cell.add,Int.add_comm]]
    have agree : tile t w e = tile t w r := (sameCells_iff _ _).mp (checked.2 e (List.mem_toFinset.mp he))
    rw [tile_translate t w e v (trans e),agree,tc]

/-- Every accepted certificate tiles the whole plane. -/
theorem check_tiling (t : Tromino) (input : PeriodicTrominoPrefill) (w : Certificate)
    (h : Check t input w) : t.IsFootprintTiling Set.univ (Set.range (tile t w)) := by
  refine ⟨?_,?_⟩
  · rintro _ ⟨c,rfl⟩; exact ⟨tile_legal t w c,by simp⟩
  · intro c _
    refine ⟨tile t w c,⟨⟨c,rfl⟩,(check_global t input w h c).1⟩,?_⟩
    rintro _ ⟨⟨d,rfl⟩,hc⟩
    exact ((check_global t input w h d).2 c hc).symm
theorem check_retained (t : Tromino) (input : PeriodicTrominoPrefill) (w : Certificate)
    (h : Check t input w) : input.prescribed t ⊆ Set.range (tile t w) := by
  rintro f ⟨p,hp,i,j,rfl⟩
  let index : Cell := (i,j)
  let r := residue w.1 index
  let a := repeatOffset input index
  let b := repeatOffset input r
  let v := Cell.sub a b
  have hr : residue w.1 a = residue w.1 b := by
    ext <;> simp [a,b,r,index,repeatOffset,residue,Cell.add,Cell.scale,Int.add_emod,Int.mul_emod]
  have trans (c : Cell) : residue w.1 (Cell.add c v) = residue w.1 c := by
    have hx := congrArg Prod.fst hr; have hy := congrArg Prod.snd hr
    dsimp [residue] at hx hy
    ext <;> simp [residue,v,Cell.add,Cell.sub,Int.add_emod,Int.sub_emod,hx,hy]
  have checked :=  (sameCells_iff _ _).mp (h.2.2 r (residue_mem w.1 h.1 index) p hp)
  rw [repeatedCells_toFinset] at checked
  change ((p.cells (fun _ => t.cells)).image (Cell.add b)) = tile t w (Cell.add b p.offset) at checked
  have atA : Cell.add (Cell.add b p.offset) v = Cell.add a p.offset := by
    ext <;> dsimp [v,Cell.add,Cell.sub] <;> omega
  refine ⟨Cell.add a p.offset,?_⟩
  rw [← atA,tile_translate t w _ v (trans _),← checked,Finset.image_image]
  congr 1; funext c; ext <;> dsimp [a,b,v,index,repeatOffset,Cell.add,Cell.sub,Cell.scale] <;> ring

theorem check_completable (t : Tromino) (input : PeriodicTrominoPrefill) (w : Certificate)
    (h : Check t input w) : t.Completable Set.univ (input.prescribed t) :=
  ⟨Set.range (tile t w),check_tiling t input w h,check_retained t input w h⟩

end CompletionPeriodic
end LeanTrominoes
