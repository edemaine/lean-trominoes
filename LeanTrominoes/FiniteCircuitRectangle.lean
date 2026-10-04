/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCircuitCut

/-! # Cutting a periodic circuit to one finite rectangle -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit
set_option maxHeartbeats 2000000

def rectangleInside (width height : Int) (location : Cell) : Prop :=
  0 ≤ location.1 ∧ location.1 < width ∧ 0 ≤ location.2 ∧ location.2 < height
instance (width height : Int) : DecidablePred (rectangleInside width height) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def wrapRectangle (width height : Int) (location : Cell) : Cell :=
  (location.1%width,location.2%height)

theorem wrapRectangle_inside (width height : Int) (wp : 0 < width) (hp : 0 < height)
    (location : Cell) : rectangleInside width height (wrapRectangle width height location) :=
  ⟨Int.emod_nonneg _ (ne_of_gt wp),Int.emod_lt_of_pos _ wp,
    Int.emod_nonneg _ (ne_of_gt hp),Int.emod_lt_of_pos _ hp⟩

theorem wrapRectangle_adjacent (width height : Int) (wp : 0 < width) (hp : 0 < height)
    (location : Cell) (port : Fin 4) :
    gridNeighbor (wrapRectangle width height location) port=
      wrapRectangle width height (gridNeighbor location port) ∨
    (¬rectangleInside width height (gridNeighbor (wrapRectangle width height location) port) ∧
      ¬rectangleInside width height
        (gridNeighbor (wrapRectangle width height (gridNeighbor location port)) (gridOpposite port))) := by
  have bounds := wrapRectangle_inside width height wp hp location
  have negMod (m : Int) (positive : 0 < m) : (-1)%m=m-1 := by
    have eq := Int.emod_eq_of_lt (show 0 ≤ m-1 by omega) (show m-1 < m by omega)
    simpa [Int.sub_emod] using eq
  rcases four_ports port with rfl | rfl | rfl | rfl
  · have step : (location.2-1)%height=(location.2%height-1)%height := by simp [Int.sub_emod]
    by_cases edge : location.2%height=0
    · right
      simp [rectangleInside,wrapRectangle,gridNeighbor,gridOpposite] at bounds ⊢
      rw [step,edge]
      simp only [zero_sub]
      rw [negMod height hp]
      constructor <;> omega
    · left
      have interior : (location.2%height-1)%height=location.2%height-1 :=
        Int.emod_eq_of_lt (by dsimp [rectangleInside,wrapRectangle] at bounds; omega)
          (by dsimp [rectangleInside,wrapRectangle] at bounds; omega)
      simp [wrapRectangle,gridNeighbor,step,interior]
  · have step : (location.1+1)%width=(location.1%width+1)%width := by simp [Int.add_emod]
    by_cases edge : location.1%width=width-1
    · right
      simp [rectangleInside,wrapRectangle,gridNeighbor,gridOpposite] at bounds ⊢
      rw [step,edge]
      have cancel : width-1+1=width := by omega
      rw [cancel,Int.emod_self]
      constructor <;> omega
    · left
      have interior : (location.1%width+1)%width=location.1%width+1 :=
        Int.emod_eq_of_lt (by dsimp [rectangleInside,wrapRectangle] at bounds; omega)
          (by dsimp [rectangleInside,wrapRectangle] at bounds; omega)
      simp [wrapRectangle,gridNeighbor,step,interior]
  · have step : (location.1-1)%width=(location.1%width-1)%width := by simp [Int.sub_emod]
    by_cases edge : location.1%width=0
    · right
      simp [rectangleInside,wrapRectangle,gridNeighbor,gridOpposite] at bounds ⊢
      rw [step,edge]
      simp only [zero_sub]
      rw [negMod width wp]
      constructor <;> omega
    · left
      have interior : (location.1%width-1)%width=location.1%width-1 :=
        Int.emod_eq_of_lt (by dsimp [rectangleInside,wrapRectangle] at bounds; omega)
          (by dsimp [rectangleInside,wrapRectangle] at bounds; omega)
      simp [wrapRectangle,gridNeighbor,step,interior]
  · have step : (location.2+1)%height=(location.2%height+1)%height := by simp [Int.add_emod]
    by_cases edge : location.2%height=height-1
    · right
      simp [rectangleInside,wrapRectangle,gridNeighbor,gridOpposite] at bounds ⊢
      rw [step,edge]
      have cancel : height-1+1=height := by omega
      rw [cancel,Int.emod_self]
      constructor <;> omega
    · left
      have interior : (location.2%height+1)%height=location.2%height+1 :=
        Int.emod_eq_of_lt (by dsimp [rectangleInside,wrapRectangle] at bounds; omega)
          (by dsimp [rectangleInside,wrapRectangle] at bounds; omega)
      simp [wrapRectangle,gridNeighbor,step,interior]

/-- One blank last row and column suffice; no periodicity is imposed on
satisfying Boolean signals. -/
theorem source_rectangle_iff (width height : Int) (wp : 0 < width) (hp : 0 < height)
    (kinds : Cell → CircuitKind)
    (periodic : ∀ location,kinds (wrapRectangle width height location)=kinds location)
    (blank : ∀ location,location.1%width=width-1 ∨ location.2%height=height-1 →
      kinds location=.blank) :
    SourceHolds (cutDomain (rectangleInside width height) kinds) ↔ SourceHolds kinds := by
  constructor
  · exact source_repeat_cutDomain _ kinds (wrapRectangle width height)
      (wrapRectangle_inside width height wp hp) periodic
      (wrapRectangle_adjacent width height wp hp)
  · apply source_cutDomain
    intro location port different
    have negMod (m : Int) (positive : 0 < m) : (-1)%m=m-1 := by
      have eq := Int.emod_eq_of_lt (show 0 ≤ m-1 by omega) (show m-1 < m by omega)
      simpa [Int.sub_emod] using eq
    have lastMod (m : Int) (positive : 0 < m) : (m-1)%m=m-1 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have mismatch : (rectangleInside width height location ∧
        ¬rectangleInside width height (gridNeighbor location port)) ∨
      (¬rectangleInside width height location ∧
        rectangleInside width height (gridNeighbor location port)) := by tauto
    rcases four_ports port with rfl | rfl | rfl | rfl
    · rcases mismatch with ⟨inside,outside⟩|⟨outside,inside⟩
      · right
        apply blank
        right
        simp [rectangleInside,gridNeighbor] at inside outside ⊢
        have eq : location.2-1=-1 := by omega
        rw [eq,negMod height hp]
      · right
        apply blank
        right
        simp [rectangleInside,gridNeighbor] at inside outside ⊢
        have eq : location.2-1=height-1 := by omega
        rw [eq,lastMod height hp]
    · rcases mismatch with ⟨inside,outside⟩|⟨outside,inside⟩
      · left
        apply blank
        left
        simp [rectangleInside,gridNeighbor] at inside outside ⊢
        have eq : location.1=width-1 := by omega
        rw [eq,lastMod width wp]
      · left
        apply blank
        left
        simp [rectangleInside,gridNeighbor] at inside outside ⊢
        have eq : location.1=-1 := by omega
        rw [eq,negMod width wp]
    · rcases mismatch with ⟨inside,outside⟩|⟨outside,inside⟩
      · right
        apply blank
        left
        simp [rectangleInside,gridNeighbor] at inside outside ⊢
        have eq : location.1-1=-1 := by omega
        rw [eq,negMod width wp]
      · right
        apply blank
        left
        simp [rectangleInside,gridNeighbor] at inside outside ⊢
        have eq : location.1-1=width-1 := by omega
        rw [eq,lastMod width wp]
    · rcases mismatch with ⟨inside,outside⟩|⟨outside,inside⟩
      · left
        apply blank
        right
        simp [rectangleInside,gridNeighbor] at inside outside ⊢
        have eq : location.2=height-1 := by omega
        rw [eq,lastMod height hp]
      · left
        apply blank
        right
        simp [rectangleInside,gridNeighbor] at inside outside ⊢
        have eq : location.2=-1 := by omega
        rw [eq,negMod height hp]
end LeanTrominoes.CompletionPattern.LBricks.Circuit
