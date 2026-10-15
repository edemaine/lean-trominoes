/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteICompletionFrontier
import LeanTrominoes.Tiling.Tromino.TrominoRayTiling

/-! # An explicit partition of the uncovered exterior into disjoint rays -/
namespace LeanTrominoes.Tromino.FiniteI

abbrev RayIndex (r : Nat) :=
  (Bool × Int) ⊕ (Bool × {x : Int // -(r:Int)≤x ∧ x≤r})

def rayPoint (r : Nat) (tiles : Finset (Finset Cell)) : RayIndex r → Nat → Cell
  | .inl (false,y), n => (leftEnd r tiles y-1-n,y)
  | .inl (true,y), n => (rightEnd r tiles y+1+n,y)
  | .inr (false,x), n => (x.val,bottomEnd r tiles x.val-1-n)
  | .inr (true,x), n => (x.val,topEnd r tiles x.val+1+n)

theorem rayPoint_injective (r : Nat) (tiles : Finset (Finset Cell)) :
    Function.Injective (fun p : RayIndex r × Nat => rayPoint r tiles p.1 p.2) := by
  rintro ⟨i,m⟩ ⟨j,n⟩ equal
  have e1 := congrArg Prod.fst equal
  have e2 := congrArg Prod.snd equal
  have bounds (z : Int) := And.intro (rightEnd_ge r tiles z)
    (And.intro (leftEnd_le r tiles z) (And.intro (topEnd_ge r tiles z) (bottomEnd_le r tiles z)))
  rcases i with ⟨si,x⟩|⟨si,x⟩ <;> rcases j with ⟨sj,y⟩|⟨sj,y⟩
  all_goals
    have bx := bounds x
    have byy := bounds y
    clear bounds
    first | have px := x.property | skip
    first | have py := y.property | skip
    cases si <;> cases sj
  all_goals simp_all [rayPoint,Prod.mk.injEq,Subtype.ext_iff] <;> omega

theorem rayPoint_legal (r : Nat) (tiles : Finset (Finset Cell)) (i : RayIndex r) (k : Nat) :
    Tromino.I.IsFootprint {rayPoint r tiles i (3*k),rayPoint r tiles i (3*k+1),rayPoint r tiles i (3*k+2)} := by
  rcases i with ⟨s,y⟩|⟨s,x⟩ <;> cases s
  · exact left_triple (leftEnd r tiles y-1) y k
  · exact right_triple (rightEnd r tiles y+1) y k
  · exact down_triple x.val (bottomEnd r tiles x.val-1) k
  · exact up_triple x.val (topEnd r tiles x.val+1) k

theorem Boundary.rayPoint_free {r : Nat} {tiles : Finset (Finset Cell)} (h : Boundary r tiles)
    (i : RayIndex r) (n : Nat) : rayPoint r tiles i n∉cellsOf tiles := by
  rcases i with ⟨s,y⟩|⟨s,x⟩ <;> cases s
  · have bound := leftEnd_le r tiles y
    exact (h.left_free y _ (by omega)).mpr (by omega)
  · have bound := rightEnd_ge r tiles y
    exact (h.right_free y _ (by omega)).mpr (by omega)
  · have bound := bottomEnd_le r tiles x.val
    exact (h.bottom_free x.val _ (by omega)).mpr (by omega)
  · have bound := topEnd_ge r tiles x.val
    exact (h.top_free x.val _ (by omega)).mpr (by omega)

theorem Boundary.free_in_range {r : Nat} {tiles : Finset (Finset Cell)} (h : Boundary r tiles)
    (c : Cell) (free : c∉cellsOf tiles) :
    c∈Set.range (fun p : RayIndex r × Nat => rayPoint r tiles p.1 p.2) := by
  rcases c with ⟨x,y⟩
  by_cases left : x < -(r:Int)
  · have gap := (h.left_free y x left).mp free
    refine ⟨(.inl (false,y),(leftEnd r tiles y-1-x).toNat),?_⟩
    simp only [rayPoint]
    apply Prod.ext <;> dsimp <;> omega
  by_cases right : (r:Int)<x
  · have gap := (h.right_free y x right).mp free
    refine ⟨(.inl (true,y),(x-(rightEnd r tiles y+1)).toNat),?_⟩
    simp only [rayPoint]
    apply Prod.ext <;> dsimp <;> omega
  have within : -(r:Int)≤x ∧ x≤r := by omega
  by_cases bottom : y < -(r:Int)
  · have gap := (h.bottom_free x y bottom).mp free
    refine ⟨(.inr (false,⟨x,within⟩),(bottomEnd r tiles x-1-y).toNat),?_⟩
    simp only [rayPoint]
    apply Prod.ext <;> dsimp <;> omega
  have top : (r:Int)<y := by
    by_contra notTop
    exact free (h.covers (x,y) (by dsimp [Box]; omega))
  have gap := (h.top_free x y top).mp free
  refine ⟨(.inr (true,⟨x,within⟩),(y-(topEnd r tiles x+1)).toNat),?_⟩
  simp only [rayPoint]
  apply Prod.ext <;> dsimp <;> omega

/-- Covering a box by straight trominoes leaves a tileable exterior. -/
theorem Boundary.exterior_tileable {r : Nat} {tiles : Finset (Finset Cell)} (h : Boundary r tiles) :
    Tromino.I.Tileable (Set.univ \ (cellsOf tiles : Set Cell)) := by
  have region : (Set.univ \ (cellsOf tiles : Set Cell))=
      Set.range (fun p : RayIndex r × Nat => rayPoint r tiles p.1 p.2) := by
    ext c
    constructor
    · intro hc; exact h.free_in_range c hc.2
    · rintro ⟨⟨i,n⟩,rfl⟩; exact ⟨Set.mem_univ _,h.rayPoint_free i n⟩
  rw [region]
  exact tileable_rays (rayPoint r tiles) (rayPoint_injective r tiles) (rayPoint_legal r tiles)

end LeanTrominoes.Tromino.FiniteI
