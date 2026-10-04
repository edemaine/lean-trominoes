/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitReduction

/-! # Finite-window models of blank-supported square networks -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks
set_option maxHeartbeats 2000000

def finiteSquareDomain (width height : Int) (c : Cell) : Prop :=
  -1≤c.1 ∧ c.1≤width ∧ -1≤c.2 ∧ c.2≤height
instance (width height : Int) : DecidablePred (finiteSquareDomain width height) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem blank_network_values {values : Fin 4 → Bool} (valid : Network 0 values) :
    ∀ port,values port=false := by
  rw [network_iff] at valid
  intro port
  exact valid.1 port (by simp [active,bit])

/-- A finite window containing a blank collar supplies a whole-plane model. -/
theorem squareHolds_of_finite_model (width height : Int) (palette : Cell → Fin 24)
    (blank : ∀ c,¬(0≤c.1 ∧ c.1<width ∧ 0≤c.2 ∧ c.2<height) → palette c=0)
    (values : Cell → Fin 4 → Bool) (seams : SquareSeams values)
    (valid : ∀ c,finiteSquareDomain width height c → Network (palette c) (values c)) :
    SquareHolds palette := by
  have boundaryBlank (c : Cell) (port : Fin 4)
      (inside : finiteSquareDomain width height c)
      (outside : ¬finiteSquareDomain width height (gridNeighbor c port)) : palette c=0 := by
    apply blank
    rcases four_ports port with rfl|rfl|rfl|rfl <;>
      simp [finiteSquareDomain,gridNeighbor] at inside outside ⊢ <;> omega
  refine ⟨fun c port => if finiteSquareDomain width height c then values c port else false,?_,?_⟩
  · intro c port
    by_cases first : finiteSquareDomain width height c <;>
      by_cases second : finiteSquareDomain width height (gridNeighbor c port)
    · simpa only [if_pos first,if_pos second] using seams c port
    · have left := blank_network_values (by simpa only [boundaryBlank c port first second] using valid c first) port
      simpa only [if_pos first,if_neg second] using left
    · have back : gridNeighbor (gridNeighbor c port) (gridOpposite port)=c := by
        rcases four_ports port with rfl|rfl|rfl|rfl <;> apply Prod.ext <;> simp [gridNeighbor,gridOpposite] <;> omega
      have blankNeighbor := boundaryBlank (gridNeighbor c port) (gridOpposite port) second (by simpa only [back] using first)
      have right := blank_network_values (by simpa only [blankNeighbor] using valid (gridNeighbor c port) second) (gridOpposite port)
      simpa only [if_neg first,if_pos second] using right.symm
    · simp only [if_neg first,if_neg second]
  · intro c
    by_cases inside : finiteSquareDomain width height c
    · simpa only [if_pos inside] using valid c inside
    · have outside : ¬(0≤c.1 ∧ c.1<width ∧ 0≤c.2 ∧ c.2<height) := by
        dsimp [finiteSquareDomain] at inside
        omega
      simpa only [if_neg inside,blank c outside] using Circuit.blank_network
end LeanTrominoes.CompletionPattern.LBricks
