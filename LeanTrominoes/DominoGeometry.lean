/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoMatchingTrace
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Dominoes in arbitrary dimension and their perfect-matching semantics -/
namespace LeanTrominoes.Domino
abbrev Cell (d : Nat) := Fin d → Int
variable {d : Nat}

def unit (i : Fin d) : Cell d := Pi.single i 1
def Adjacent (x y : Cell d) : Prop := ∃ i, y=x+unit i ∨ x=y+unit i
def color (x : Cell d) : Bool := decide ((∑ i, x i)%2=0)

theorem adjacent_symm {x y : Cell d} (h : Adjacent x y) : Adjacent y x := by
  obtain ⟨i,h⟩ := h
  exact ⟨i,h.symm⟩

theorem sum_add_unit (x : Cell d) (i : Fin d) : (∑ j, (x+unit i) j)=(∑ j,x j)+1 := by
  simp [unit,Pi.add_apply,Finset.sum_add_distrib]

theorem color_add_unit_ne (x : Cell d) (i : Fin d) : color x ≠ color (x+unit i) := by
  unfold color
  rw [sum_add_unit]
  by_cases h : (∑ j,x j)%2=0
  · have next : ((∑ j,x j)+1)%2≠0 := by omega
    simp [h,next]
  · have next : ((∑ j,x j)+1)%2=0 := by omega
    simp [h,next]

theorem adjacent_color {x y : Cell d} (h : Adjacent x y) : color x ≠ color y := by
  obtain ⟨i,h | h⟩ := h
  · subst y; exact color_add_unit_ne x i
  · subst x; exact (color_add_unit_ne y i).symm

theorem adjacent_ne {x y : Cell d} (h : Adjacent x y) : x≠y := by
  intro equal
  exact adjacent_color h (congrArg color equal)

theorem adjacent_translate {x y : Cell d} (h : Adjacent x y) (t : Cell d) : Adjacent (x+t) (y+t) := by
  obtain ⟨i,h | h⟩ := h
  · exact ⟨i,Or.inl (by rw [h]; abel)⟩
  · exact ⟨i,Or.inr (by rw [h]; abel)⟩

theorem color_double (x t : Cell d) : color (x+(t+t))=color x := by
  unfold color
  simp only [Pi.add_apply,Finset.sum_add_distrib]
  have same : ((∑ i,x i)+((∑ i,t i)+(∑ i,t i)))%2=(∑ i,x i)%2 := by omega
  rw [same]

def IsDomino (tile : Finset (Cell d)) : Prop := ∃ x y, Adjacent x y ∧ tile={x,y}

structure IsTiling (region : Set (Cell d)) (tiles : Set (Finset (Cell d))) : Prop where
  inside : ∀ tile∈tiles, IsDomino tile ∧ ∀ x∈tile, x∈region
  covers : ∀ x∈region, ∃! tile, tile∈tiles ∧ x∈tile

def Tileable (region : Set (Cell d)) : Prop := ∃ tiles, IsTiling region tiles
def HasPairing (region : Set (Cell d)) : Prop :=
  ∃ p : TwoMatching.PerfectMatching region, ∀ x, Adjacent x.val (p.mate x).val

private theorem mem_pair_iff {x a b : Cell d} : x∈({a,b} : Finset (Cell d)) ↔ x=a ∨ x=b := by simp

theorem other_unique {tile : Finset (Cell d)} (domino : IsDomino tile) {x : Cell d} (hx : x∈tile) :
    ∃! y, y∈tile ∧ y≠x := by
  obtain ⟨a,b,adj,rfl⟩ := domino
  have ne := adjacent_ne adj
  rcases mem_pair_iff.mp hx with rfl | rfl
  · refine ⟨b,⟨by simp,ne.symm⟩,?_⟩
    intro y hy
    rcases mem_pair_iff.mp hy.1 with rfl | rfl
    · exact (hy.2 rfl).elim
    · rfl
  · refine ⟨a,⟨by simp,ne⟩,?_⟩
    intro y hy
    rcases mem_pair_iff.mp hy.1 with rfl | rfl
    · rfl
    · exact (hy.2 rfl).elim

theorem adjacent_of_mem {tile : Finset (Cell d)} (domino : IsDomino tile)
    {x y : Cell d} (hx : x∈tile) (hy : y∈tile) (ne : x≠y) : Adjacent x y := by
  obtain ⟨a,b,adj,rfl⟩ := domino
  rcases mem_pair_iff.mp hx with rfl | rfl <;>
    rcases mem_pair_iff.mp hy with rfl | rfl
  · exact (ne rfl).elim
  · exact adj
  · exact adjacent_symm adj
  · exact (ne rfl).elim

def pairingTiles {region : Set (Cell d)} (p : TwoMatching.PerfectMatching region) : Set (Finset (Cell d)) :=
  {tile | ∃ x, tile={x.val,(p.mate x).val}}

theorem pairing_isTiling {region : Set (Cell d)} (p : TwoMatching.PerfectMatching region)
    (supported : ∀ x, Adjacent x.val (p.mate x).val) : IsTiling region (pairingTiles p) := by
  constructor
  · rintro tile ⟨x,rfl⟩
    refine ⟨⟨x.val,(p.mate x).val,supported x,rfl⟩,?_⟩
    intro y hy
    rcases mem_pair_iff.mp hy with rfl | rfl
    · exact x.property
    · exact (p.mate x).property
  · intro x hx
    let a : region := ⟨x,hx⟩
    refine ⟨{x,(p.mate a).val},⟨⟨a,rfl⟩,by simp⟩,?_⟩
    rintro tile ⟨⟨b,rfl⟩,member⟩
    rcases mem_pair_iff.mp member with equal | equal
    · have same : a=b := Subtype.ext equal
      rw [← same]
    · have same : a=p.mate b := Subtype.ext equal
      change {b.val,(p.mate b).val}={a.val,(p.mate a).val}
      rw [same,p.involutive]
      ext; simp [or_comm]

theorem tiling_hasPairing {region : Set (Cell d)} {tiles : Set (Finset (Cell d))}
    (tiling : IsTiling region tiles) : HasPairing region := by
  classical
  let paired := fun x y : region => ∃ tile∈tiles, x.val∈tile ∧ y.val∈tile ∧ x≠y
  have partners : ∀ x, ∃! y, paired x y := by
    intro x
    obtain ⟨tile,ht,uniqueTile⟩ := tiling.covers x.val x.property
    obtain ⟨y,hy,uniqueOther⟩ := other_unique (tiling.inside tile ht.1).1 ht.2
    let b : region := ⟨y,(tiling.inside tile ht.1).2 y hy.1⟩
    refine ⟨b,⟨tile,ht.1,ht.2,hy.1,?_⟩,?_⟩
    · intro equal
      exact hy.2 (congrArg Subtype.val equal).symm
    · rintro e ⟨other,ho,hx,he,ne⟩
      have same := uniqueTile other ⟨ho,hx⟩
      subst other
      apply Subtype.ext
      exact uniqueOther e.val ⟨he,fun equal => ne (Subtype.ext equal.symm)⟩
  choose mate supported unique using partners
  refine ⟨⟨mate,?_,?_⟩,?_⟩
  · intro x
    apply (unique (mate x) x ?_).symm
    obtain ⟨tile,ht,hx,hy,ne⟩ := supported x
    exact ⟨tile,ht,hy,hx,ne.symm⟩
  · intro x equal
    obtain ⟨tile,ht,hx,hy,ne⟩ := supported x
    exact ne equal.symm
  · intro x
    obtain ⟨tile,ht,hx,hy,ne⟩ := supported x
    exact adjacent_of_mem (tiling.inside tile ht).1 hx hy (fun equal => ne (Subtype.ext equal))

theorem tileable_iff_pairing (region : Set (Cell d)) : Tileable region ↔ HasPairing region := by
  constructor
  · rintro ⟨tiles,tiling⟩; exact tiling_hasPairing tiling
  · rintro ⟨p,hp⟩; exact ⟨pairingTiles p,pairing_isTiling p hp⟩

end LeanTrominoes.Domino
