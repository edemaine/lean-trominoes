/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPatternIndexed
import LeanTrominoes.TrominoFiniteListExclusion

/-! # Cached regions for finite completion certificates -/

namespace LeanTrominoes.CompletionPattern

theorem Pattern.residual_eq_unfilled (p : Pattern) (outside : Finset Cell) :
    p.residual outside = (p.region \ p.fixedRegion) \ outside := by
  change (p.region \ outside) \ p.fixedRegion = (p.region \ p.fixedRegion) \ outside
  ext c
  simp only [Finset.mem_sdiff]
  exact and_right_comm

theorem Pattern.prefill_inside_of_disjoint (p : Pattern) (outside : Finset Cell)
    (inside : p.fixedRegion ⊆ p.region) (disjoint : Disjoint p.fixedRegion outside) :
    ∀ q ∈ p.prefill, q.cells (fun _ => p.tromino.cells) ⊆ p.target outside := by
  intro q hq c hc
  have fixed : c ∈ p.fixedRegion := Finset.mem_biUnion.mpr ⟨q,hq,hc⟩
  exact Finset.mem_sdiff.mpr ⟨inside fixed,fun ho => Finset.disjoint_left.mp disjoint fixed ho⟩

/-- Once prefill legality is handled separately, exclusion needs only an
area obstruction or membership in the checked exclusion certificate. -/
theorem Pattern.not_completable_of_residual_obstruction (p : Pattern) (outside : Finset Cell)
    (certificate : List TrominoFiniteIndexedExclusion.Node)
    (checked : TrominoFiniteIndexedExclusion.check p.tromino certificate = true)
    (obstruction : ¬ 3 ∣ (p.residual outside).card ∨
      p.residual outside ∈ certificate.map TrominoFiniteIndexedExclusion.Node.region) :
    ¬ p.Completable outside := by
  intro completed
  rcases obstruction with area | member
  · exact area (p.area_dvd outside completed)
  · obtain ⟨node,member,eq⟩ := List.mem_map.mp member
    have tiled := p.residual_tileable outside completed
    rw [← eq] at tiled
    exact TrominoFiniteIndexedExclusion.check_sound _ _ checked node member tiled

theorem Pattern.not_completable_of_list_obstruction (p : Pattern) (outside : Finset Cell)
    (certificate : List TrominoFiniteListExclusion.Node)
    (checked : TrominoFiniteListExclusion.check p.tromino certificate = true)
    (cells : List Cell) (region_eq : cells.toFinset = p.residual outside)
    (obstruction : ¬ 3 ∣ (p.residual outside).card ∨
      ∃ node ∈ certificate, cells = node.cells) : ¬ p.Completable outside := by
  intro completed
  rcases obstruction with area | ⟨node,member,eq⟩
  · exact area (p.area_dvd outside completed)
  · have tiled := p.residual_tileable outside completed
    rw [← region_eq,eq] at tiled
    exact TrominoFiniteListExclusion.check_sound _ _ checked node member tiled

end LeanTrominoes.CompletionPattern
