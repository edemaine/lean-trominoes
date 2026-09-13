/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingStripStack
import LeanTrominoes.LocalWindowCycle

/-! # Finite placement records for variable-polyomino strip tilings -/

namespace LeanTrominoes.PolyominoStripWindow

def Bounded {ι : Type*} (tiles : ι → Polyomino) (bound : Nat) : Prop :=
  ∀ k, ∀ c ∈ tiles k, -(bound : Int) ≤ c.1 ∧ c.1 ≤ bound ∧
    -(bound : Int) ≤ c.2 ∧ c.2 ≤ bound

theorem act_bounds {ι : Type*} {tiles : ι → Polyomino} {bound : Nat}
    (bounded : Bounded tiles bound) (k : ι) {c : Cell} (hc : c ∈ tiles k) (s : SquareSymmetry) :
    -(bound : Int) ≤ (s.act c).1 ∧ (s.act c).1 ≤ bound ∧
      -(bound : Int) ≤ (s.act c).2 ∧ (s.act c).2 ≤ bound := by
  have h := bounded k c hc
  cases s <;> dsimp [SquareSymmetry.act] <;> omega

/-- Tile kind, orientation, and a bounded vertical offset. -/
abbrev Slot (ι : Type*) (height bound : Nat) := ι × SquareSymmetry × Fin (height+2*bound+1)

def placement {ι : Type*} {height bound : Nat} (x : Int) (slot : Slot ι height bound) : Placement ι :=
  ⟨slot.1,slot.2.1,(x,(slot.2.2.val : Int)-bound)⟩

theorem placement_injective {ι : Type*} {height bound : Nat} (x : Int) :
    Function.Injective (placement (ι := ι) (height := height) (bound := bound) x) := by
  rintro ⟨k,s,y⟩ ⟨l,t,z⟩ eq
  have kinds := congrArg Placement.kind eq
  have syms := congrArg Placement.symmetry eq
  have ys := congrArg (fun p : Placement ι => p.offset.2) eq
  change k = l at kinds
  change s = t at syms
  have yz : y = z := by
    apply Fin.ext
    dsimp [placement] at ys
    omega
  subst l
  subst t
  subst z
  rfl

theorem mem_placement_shift {ι : Type*} (tiles : ι → Polyomino) {height bound : Nat}
    (x : Int) (slot : Slot ι height bound) (c : Cell) :
    Cell.add (x,0) c ∈ (placement x slot).cells tiles ↔ c ∈ (placement 0 slot).cells tiles := by
  have eq : (placement 0 slot).shift (x,0) = placement x slot := by
    simp [placement,Placement.shift,Cell.add]
  rw [← eq,Placement.mem_shift_cells]

/-- Every placement covering a strip cell has a representable vertical offset. -/
theorem covering_slot {ι : Type*} {tiles : ι → Polyomino} {height bound : Nat}
    (bounded : Bounded tiles bound) (p : Placement ι) {c : Cell}
    (inside : c ∈ horizontalStrip height) (covers : c ∈ p.cells tiles) :
    ∃ slot : Slot ι height bound, placement p.offset.1 slot = p := by
  obtain ⟨q,hq,eq⟩ := (Placement.mem_cells_iff _ _ _).mp covers
  have bounds := act_bounds bounded p.kind hq p.symmetry
  have y := congrArg Prod.snd eq
  dsimp [Cell.add] at y
  have lo : 0 ≤ p.offset.2 + (bound : Int) := by have := inside.1; omega
  have hi : (p.offset.2 + (bound : Int)).toNat < height+2*bound+1 := by
    have := inside.2
    omega
  refine ⟨(p.kind,p.symmetry,⟨(p.offset.2+bound).toNat,hi⟩),?_⟩
  apply Placement.ext
  · rfl
  · rfl
  · apply Prod.ext
    · rfl
    · dsimp [placement]
      omega

abbrev Column (ι : Type*) (height bound : Nat) := Slot ι height bound → Bool
abbrev Window (ι : Type*) (height bound : Nat) := LocalWindow.Window (Column ι height bound) (2*bound)
abbrev Candidate (ι : Type*) (height bound : Nat) := Fin (2*bound+1) × Slot ι height bound

def ValidSlot {ι : Type*} (tiles : ι → Polyomino) {height bound : Nat} (slot : Slot ι height bound) : Prop :=
  ∀ c ∈ (placement 0 slot).cells tiles, c ∈ horizontalStrip height

/-- A window checks its first column's containment and its middle column's exact coverage. -/
def ValidWindow {ι : Type*} (tiles : ι → Polyomino) {height bound : Nat} (window : Window ι height bound) : Prop :=
  (∀ slot, window 0 slot = true → ValidSlot tiles slot) ∧
    ∀ y : Fin height, ∃! a : Candidate ι height bound,
      window a.1 a.2 = true ∧ ((bound : Int),(y.val : Int)) ∈ (placement a.1.val a.2).cells tiles

instance {ι : Type*} [Fintype ι] [DecidableEq ι] (tiles : ι → Polyomino) {height bound : Nat}
    (window : Window ι height bound) : Decidable (ValidWindow tiles window) := by
  unfold ValidWindow ValidSlot horizontalStrip ExistsUnique
  simp only [Set.mem_setOf_eq]
  infer_instance

end LeanTrominoes.PolyominoStripWindow
