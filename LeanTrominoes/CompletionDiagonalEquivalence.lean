/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionDiagonalNetwork

/-! # Exact satisfiability preservation by diagonal routing -/
namespace LeanTrominoes.CompletionPattern.DiagonalRouting
open LBricks

theorem wire_ports_equal (r : Fin 8) (v : Fin 4 → Bool) (h : Network (wireLabel r) v)
    (p q : Fin 4) (hp : active (wireLabel r) p = true) (hq : active (wireLabel r) q = true) : v p = v q := by
  have bound : (wireLabel r).val < 16 := by fin_cases r <;> decide
  rw [network_iff,if_pos bound] at h
  obtain ⟨value,hvalue⟩ := h.2
  exact (hvalue p hp).trans (hvalue q hq).symm

theorem lift_network (palette : Cell → Fin 24) (v : Cell → Fin 4 → Bool)
    (h : SquareNetwork palette v) : SquareNetwork (refinePalette palette) (liftValue v) := by
  refine ⟨lift_seams v h.1,?_⟩
  intro location
  rw [← place_source_role location,palette_place,lift_place]
  by_cases hr : roleAt location = 0
  · simp only [hr,if_pos rfl,liftAt]
    exact h.2 _
  · rw [if_neg hr]
    exact wire_lift_valid v _ _ hr

def pullValue (v : Cell → Fin 4 → Bool) (c : Cell) : Fin 4 → Bool := v (place c 0)

theorem pull_east_south (palette : Cell → Fin 24) (v : Cell → Fin 4 → Bool)
    (h : SquareNetwork (refinePalette palette) v) (c : Cell) :
    pullValue v c 1 = pullValue v (c.1+1,c.2) 2 ∧
      pullValue v c 3 = pullValue v (c.1,c.2+1) 0 := by
  have seam (c : Cell) (r : Fin 8) (p : Fin 4) :
      v (place c r) p = v (place (Cell.add c (neighborOffset r p)) (neighborRole r p)) (gridOpposite p) := by
    simpa only [neighbor_place] using h.1 (place c r) p
  have wire (r : Fin 8) (hr : r ≠ 0) : Network (wireLabel r) (v (place c r)) := by
    simpa only [palette_place,if_neg hr] using h.2 (place c r)
  have e1 := wire_ports_equal 1 _ (wire 1 (by decide)) 2 3 (by decide) (by decide)
  have e2 := wire_ports_equal 2 _ (wire 2 (by decide)) 0 3 (by decide) (by decide)
  have e3 := wire_ports_equal 3 _ (wire 3 (by decide)) 0 1 (by decide) (by decide)
  have s1 := wire_ports_equal 4 _ (wire 4 (by decide)) 0 2 (by decide) (by decide)
  have s2 := wire_ports_equal 5 _ (wire 5 (by decide)) 1 2 (by decide) (by decide)
  have s3 := wire_ports_equal 6 _ (wire 6 (by decide)) 1 3 (by decide) (by decide)
  have ce := seam c 0 1
  have e12 := seam c 1 3
  have e23 := seam c 2 3
  have ec := seam c 3 1
  have cs := seam c 0 3
  have s12 := seam c 4 2
  have s23 := seam c 5 2
  have sc := seam c 6 3
  simp [neighborOffset,neighborRole,gridOpposite,Cell.add] at ce e12 e23 ec cs s12 s23 sc
  exact ⟨ce.trans (e1.trans (e12.trans (e2.trans (e23.trans (e3.trans ec))))),
    cs.trans (s1.trans (s12.trans (s2.trans (s23.trans (s3.trans sc)))))⟩

theorem pull_network (palette : Cell → Fin 24) (v : Cell → Fin 4 → Bool)
    (h : SquareNetwork (refinePalette palette) v) : SquareNetwork palette (pullValue v) := by
  refine ⟨?_,?_⟩
  · intro c p
    have east := (pull_east_south palette v h c).1
    have south := (pull_east_south palette v h c).2
    have west := (pull_east_south palette v h (c.1-1,c.2)).1.symm
    have north := (pull_east_south palette v h (c.1,c.2-1)).2.symm
    fin_cases p <;> simp [gridNeighbor,gridOpposite] <;>
      first | exact east | exact south | simpa using west | simpa using north
  · intro c
    simpa [pullValue] using h.2 (place c 0)

/-- Routing introduces only two-port copy constraints and unused cells. -/
theorem refine_holds_iff (palette : Cell → Fin 24) :
    SquareHolds (refinePalette palette) ↔ SquareHolds palette := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨pullValue v,pull_network palette v hv⟩
  · rintro ⟨v,hv⟩
    exact ⟨liftValue v,lift_network palette v hv⟩

end LeanTrominoes.CompletionPattern.DiagonalRouting
