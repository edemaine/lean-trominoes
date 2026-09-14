import LeanTrominoes.CompletionIMicroGeometry

namespace LeanTrominoes.CompletionGuardedShape

def Member (w h : Nat) (c : Cell) : Prop :=
  0 ≤ c.1 ∧ c.1 < w ∧
    ((1 ≤ c.2 ∧ c.2 < h) ∨
     ((9 ≤ c.1 % 18 ∨ c.1 % 18 = 5) ∧ c.2 = 0) ∨
     ((c.1 % 18 < 9 ∨ c.1 % 18 = 14) ∧ c.2 = h))

instance (w h : Nat) (c : Cell) : Decidable (Member w h c) := by
  unfold Member
  infer_instance

def cells (w h : Nat) : List Cell :=
  (List.range w).flatMap fun (x : Nat) =>
    ((List.range (h+1)).filter fun (y : Nat) => decide (Member w h (x,y))).map
      fun (y : Nat) => ((x : Int),(y : Int))

theorem mem_cells (w h : Nat) (c : Cell) : c ∈ cells w h ↔ Member w h c := by
  constructor
  · intro member
    obtain ⟨x,hx,member⟩ := List.mem_flatMap.mp member
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp member
    exact of_decide_eq_true (List.mem_filter.mp hy).2
  · intro member
    have hx : 0 ≤ c.1 ∧ c.1 < w := ⟨member.1,member.2.1⟩
    have hy : 0 ≤ c.2 ∧ c.2 ≤ h := by
      rcases member.2.2 with inside | top | bottom <;> omega
    have ex : (c.1.toNat : Int) = c.1 := Int.toNat_of_nonneg hx.1
    have ey : (c.2.toNat : Int) = c.2 := Int.toNat_of_nonneg hy.1
    apply List.mem_flatMap.mpr
    refine ⟨c.1.toNat,List.mem_range.mpr (by omega),List.mem_map.mpr ?_⟩
    refine ⟨c.2.toNat,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),?_⟩,?_⟩
    · exact decide_eq_true (by simpa only [ex,ey] using member)
    · exact Prod.ext ex ey

end LeanTrominoes.CompletionGuardedShape
