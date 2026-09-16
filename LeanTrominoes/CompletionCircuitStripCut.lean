/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitReduction

/-! # Cutting a vertically periodic circuit source at blank rows -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit
set_option maxHeartbeats 2000000

def cutKinds (height : Int) (kinds : Cell → CircuitKind) (c : Cell) : CircuitKind :=
  if 0 ≤ c.2 ∧ c.2 < height then kinds c else .blank

theorem blank_source_values {v : Fin 4 → Bool} (h : CircuitKind.blank.SourceRelation v) :
    ∀ p, v p = false := fun p => h.1 p rfl

theorem neighbor_row_near (c : Cell) (p : Fin 4) :
    c.2-1 ≤ (gridNeighbor c p).2 ∧ (gridNeighbor c p).2 ≤ c.2+1 := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;> simp [gridNeighbor] <;> omega

theorem source_cut (height : Int) (kinds : Cell → CircuitKind)
    (blank : ∀ c, c.2 = -1 ∨ c.2 = height → kinds c = .blank) :
    SourceHolds kinds → SourceHolds (cutKinds height kinds) := by
  rintro ⟨v,seams,valid⟩
  refine ⟨fun c p => if 0 ≤ c.2 ∧ c.2 < height then v c p else false,?_,?_⟩
  · intro c p
    have near := neighbor_row_near c p
    have seam := seams c p
    dsimp only
    split_ifs with hc hn hn
    · exact seam
    · have boundary : (gridNeighbor c p).2 = -1 ∨ (gridNeighbor c p).2 = height := by omega
      rw [seam]
      exact blank_source_values (by simpa only [blank _ boundary] using valid (gridNeighbor c p)) _
    · have boundary : c.2 = -1 ∨ c.2 = height := by omega
      rw [← seam]
      exact (blank_source_values (by simpa only [blank _ boundary] using valid c) _).symm
    · rfl
  · intro c
    by_cases hc : 0 ≤ c.2 ∧ c.2 < height
    · simpa [cutKinds,hc] using valid c
    · simp [cutKinds,hc,CircuitKind.SourceRelation,CircuitKind.portEnabled]

def wrapRow (height : Int) (c : Cell) : Cell := (c.1,c.2%height)

theorem source_repeat_cut (height : Int) (positive : 0 < height) (kinds : Cell → CircuitKind)
    (periodic : ∀ c, kinds (wrapRow height c) = kinds c)
    (blank : ∀ c, c.2 = 0 ∨ c.2 = height-1 → kinds c = .blank) :
    SourceHolds (cutKinds height kinds) → SourceHolds kinds := by
  rintro ⟨v,seams,valid⟩
  have bounds (c : Cell) : 0 ≤ (wrapRow height c).2 ∧ (wrapRow height c).2 < height :=
    ⟨Int.emod_nonneg _ (ne_of_gt positive),Int.emod_lt_of_pos _ positive⟩
  have validWrap (c : Cell) : (kinds (wrapRow height c)).SourceRelation (v (wrapRow height c)) := by
    simpa only [cutKinds,if_pos (bounds c)] using valid (wrapRow height c)
  refine ⟨fun c p => v (wrapRow height c) p,?_,?_⟩
  · intro c p
    have bc := bounds c
    have bn := bounds (gridNeighbor c p)
    by_cases same : gridNeighbor (wrapRow height c) p = wrapRow height (gridNeighbor c p)
    · simpa only [same] using seams (wrapRow height c) p
    · have edges : ((wrapRow height c).2 = 0 ∨ (wrapRow height c).2 = height-1) ∧
          ((wrapRow height (gridNeighbor c p)).2 = 0 ∨
            (wrapRow height (gridNeighbor c p)).2 = height-1) := by
        have predMod : (c.2-1)%height = (c.2%height-1)%height := by simp [Int.sub_emod]
        have succMod : (c.2+1)%height = (c.2%height+1)%height := by simp [Int.add_emod]
        have negMod : (-1)%height = height-1 := by
          have eq := Int.emod_eq_of_lt (show 0 ≤ height-1 by omega) (show height-1 < height by omega)
          simpa [Int.sub_emod] using eq
        rcases four_ports p with rfl | rfl | rfl | rfl
        · simp [wrapRow,gridNeighbor,Prod.ext_iff] at same bc bn ⊢
          by_cases edge : c.2%height = 0
          · simp [predMod,edge,negMod]
          · have interior : (c.2%height-1)%height = c.2%height-1 := Int.emod_eq_of_lt (by omega) (by omega)
            exact False.elim (same (by rw [predMod,interior]))
        · exact False.elim (same rfl)
        · exact False.elim (same rfl)
        · simp [wrapRow,gridNeighbor,Prod.ext_iff] at same bc bn ⊢
          by_cases edge : c.2%height = height-1
          · simp [succMod,edge]
          · have interior : (c.2%height+1)%height = c.2%height+1 := Int.emod_eq_of_lt (by omega) (by omega)
            exact False.elim (same (by rw [succMod,interior]))
      have left := blank_source_values (by simpa only [blank _ edges.1] using validWrap c) p
      have right := blank_source_values (by simpa only [blank _ edges.2] using validWrap (gridNeighbor c p)) (gridOpposite p)
      exact left.trans right.symm
  · intro c
    simpa only [periodic] using validWrap c

/-- No periodicity is required of the satisfying signal assignment. -/
theorem source_cut_iff (height : Int) (positive : 0 < height) (kinds : Cell → CircuitKind)
    (periodic : ∀ c, kinds (wrapRow height c) = kinds c)
    (outsideBlank : ∀ c, c.2 = -1 ∨ c.2 = height → kinds c = .blank)
    (insideBlank : ∀ c, c.2 = 0 ∨ c.2 = height-1 → kinds c = .blank) :
    SourceHolds (cutKinds height kinds) ↔ SourceHolds kinds :=
  ⟨source_repeat_cut height positive kinds periodic insideBlank,source_cut height kinds outsideBlank⟩
end LeanTrominoes.CompletionPattern.LBricks.Circuit
