/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteICompletionGeometry

/-! # Tiling disjoint lattice rays by straight trominoes -/
namespace LeanTrominoes.Tromino.FiniteI

/-- Any injectively parametrized family of rays can be tiled by grouping
successive positions in triples. The footprint hypothesis supplies geometry. -/
theorem tileable_rays {ι : Type*} (point : ι → Nat → Cell)
    (injective : Function.Injective (fun p : ι × Nat => point p.1 p.2))
    (legal : ∀ i k, Tromino.I.IsFootprint {point i (3*k),point i (3*k+1),point i (3*k+2)}) :
    Tromino.I.Tileable (Set.range (fun p : ι × Nat => point p.1 p.2)) := by
  let tile (i : ι) (k : Nat) : Finset Cell := {point i (3*k),point i (3*k+1),point i (3*k+2)}
  apply (Tromino.I.tileable_iff_exists_footprintTiling _).mpr
  refine ⟨Set.range (fun p : ι × Nat => tile p.1 p.2),?_,?_⟩
  · rintro f ⟨⟨i,k⟩,rfl⟩
    refine ⟨legal i k,?_⟩
    intro c hc
    simp only [tile,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl|rfl|rfl
    · exact ⟨(i,3*k),rfl⟩
    · exact ⟨(i,3*k+1),rfl⟩
    · exact ⟨(i,3*k+2),rfl⟩
  · rintro c ⟨⟨i,n⟩,rfl⟩
    have division : n=3*(n/3) ∨ n=3*(n/3)+1 ∨ n=3*(n/3)+2 := by omega
    have cover : point i n∈tile i (n/3) := by
      simp only [tile,Finset.mem_insert,Finset.mem_singleton]
      rcases division with h|h|h
      · exact Or.inl (congrArg (point i) h)
      · exact Or.inr (Or.inl (congrArg (point i) h))
      · exact Or.inr (Or.inr (congrArg (point i) h))
    refine ⟨tile i (n/3),⟨⟨(i,n/3),rfl⟩,cover⟩,?_⟩
    rintro f ⟨⟨⟨j,k⟩,rfl⟩,hc⟩
    simp only [tile,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with h|h|h
    all_goals
      have same := @injective (i,n) (j,_) h
      have ij : i=j := congrArg Prod.fst same
      have nk := congrArg Prod.snd same
      dsimp at nk
      have kk : k=n/3 := by omega
      simp only [ij,kk]

/-- Legal triples on each of the four oriented axis rays. -/
theorem right_triple (x y : Int) (k : Nat) :
    Tromino.I.IsFootprint {(x+(3*k:Nat),y),(x+(3*k+1:Nat),y),(x+(3*k+2:Nat),y)} := by
  convert horizontal_footprint (x+3*k) y using 1 <;> simp [horizontal,Nat.cast_add,Nat.cast_mul,add_assoc]

theorem left_triple (x y : Int) (k : Nat) :
    Tromino.I.IsFootprint {(x-(3*k:Nat),y),(x-(3*k+1:Nat),y),(x-(3*k+2:Nat),y)} := by
  have equal : ({(x-(3*k:Nat),y),(x-(3*k+1:Nat),y),(x-(3*k+2:Nat),y)} : Finset Cell)=
      horizontal (x-3*k-2) y := by
    ext c; rcases c with ⟨u,v⟩
    simp [horizontal,Prod.mk.injEq,Nat.cast_add,Nat.cast_mul]
    omega
  rw [equal]; exact horizontal_footprint _ _

theorem up_triple (x y : Int) (k : Nat) :
    Tromino.I.IsFootprint {(x,y+(3*k:Nat)),(x,y+(3*k+1:Nat)),(x,y+(3*k+2:Nat))} := by
  convert vertical_footprint x (y+3*k) using 1 <;> simp [vertical,Nat.cast_add,Nat.cast_mul,add_assoc]

theorem down_triple (x y : Int) (k : Nat) :
    Tromino.I.IsFootprint {(x,y-(3*k:Nat)),(x,y-(3*k+1:Nat)),(x,y-(3*k+2:Nat))} := by
  have equal : ({(x,y-(3*k:Nat)),(x,y-(3*k+1:Nat)),(x,y-(3*k+2:Nat))} : Finset Cell)=
      vertical x (y-3*k-2) := by
    ext c; rcases c with ⟨u,v⟩
    simp [vertical,Prod.mk.injEq,Nat.cast_add,Nat.cast_mul]
    omega
  rw [equal]; exact vertical_footprint _ _

end LeanTrominoes.Tromino.FiniteI
