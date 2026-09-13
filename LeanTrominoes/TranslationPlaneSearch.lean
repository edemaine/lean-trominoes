/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolyominoes
import LeanTrominoes.PlaneTilingSearchComputability

/-! # Finite obstructions with forbidden background orientations -/

namespace LeanTrominoes.TranslationPlaneSearch
open PlaneTilingSearch
open ThreeTranslationPolyominoes (Allowed)

instance (p : Placement Bool) : Decidable (Allowed p) := by unfold Allowed; infer_instance

def FiniteSearch (input : Input) (radius : Nat) : Prop :=
  ∃ selected ∈ subsets (pool input radius), Valid input radius selected ∧ ∀ p ∈ selected, Allowed p

instance (input : Input) (radius : Nat) : Decidable (FiniteSearch input radius) := by
  unfold FiniteSearch
  infer_instance

theorem finiteSearch_of_tileable (input : Input)
    (tiled : TileableWith (tiles input) Set.univ Allowed) (radius : Nat) : FiniteSearch input radius := by
  classical
  obtain ⟨ps,ht,legal⟩ := tiled
  refine ⟨(pool input radius).filter (fun p => decide (p ∈ ps)),filter_mem_subsets _ _,?_,?_⟩
  · intro c hc
    obtain ⟨p,hp,unique⟩ := ht.uniqueCover c (Set.mem_univ _)
    refine ⟨p,?_,hp.2,?_⟩
    · simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨List.mem_flatMap.mpr ⟨c,hc,(mem_candidates input c p).mpr hp.2⟩,hp.1⟩
    · intro q hq covers
      exact unique q ⟨by simpa using (List.mem_filter.mp hq).2,covers⟩
  · intro p hp
    exact legal p (by simpa using (List.mem_filter.mp hp).2)

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
local instance : CompactSpace Bool := Finite.compactSpace

private def patch (input : Input) (radius : Nat) : Set (TilingSelection.Selection Bool) :=
  {f | (∀ c, LeanWang.InBox radius c → TilingSelection.count (tiles input) c f = 1) ∧
    ∀ p, ¬ Allowed p → f p = false}

private theorem patch_closed (input : Input) (radius : Nat) : IsClosed (patch input radius) := by
  have counts : IsClosed {f | ∀ c, LeanWang.InBox radius c → TilingSelection.count (tiles input) c f = 1} := by
    convert isClosed_iInter (fun c => isClosed_iInter (fun (_ : LeanWang.InBox radius c) =>
      TilingSelection.isClosed_count (tiles input) c)) using 1
    ext f
    simp
  have legality : IsClosed {f : TilingSelection.Selection Bool | ∀ p, ¬ Allowed p → f p = false} := by
    convert isClosed_iInter (fun p => isClosed_iInter (fun (_ : ¬ Allowed p) =>
      (isClosed_discrete ({false} : Set Bool)).preimage (continuous_apply p))) using 1
    ext f
    simp
  exact counts.inter legality

theorem tileable_of_all_finiteSearch (input : Input) (finite : ∀ r, FiniteSearch input r) :
    TileableWith (tiles input) Set.univ Allowed := by
  classical
  have nonempty (r : Nat) : (patch input r).Nonempty := by
    obtain ⟨selected,_,valid,legal⟩ := finite r
    let f : TilingSelection.Selection Bool := fun p => decide (p ∈ selected)
    refine ⟨f,?_,?_⟩
    · intro c hc
      rw [TilingSelection.count_eq_one_iff]
      obtain ⟨p,hp,covers,unique⟩ := valid c ((TrominoAssignment.mem_boxCellList_iff r c).mpr hc)
      refine ⟨p,⟨by simpa [TilingSelection.placements,f] using hp,covers⟩,?_⟩
      intro q hq
      exact unique q (by simpa [TilingSelection.placements,f] using hq.1) hq.2
    · intro p forbidden
      have outside : p ∉ selected := fun hp => forbidden (legal p hp)
      simp [f,outside]
  have decreasing (r : Nat) : patch input (r+1) ⊆ patch input r := by
    intro f h
    exact ⟨fun c hc => h.1 c (LeanWang.inBox_mono (by omega) hc),h.2⟩
  obtain ⟨f,hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (patch input) decreasing nonempty (patch_closed input 0).isCompact (patch_closed input)
  have all : ∀ r, f ∈ patch input r := by simpa using hf
  refine ⟨TilingSelection.placements f,(TilingSelection.isTiling_iff_count _ _).mpr ?_,?_⟩
  · intro c
    exact (all (max c.1.natAbs c.2.natAbs)).1 c
      (LeanWang.inBox_of_natAbs_le (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  · intro p hp
    by_contra forbidden
    have zero := (all 0).2 p forbidden
    change f p = true at hp
    rw [zero] at hp
    contradiction

theorem tileable_iff (input : Input) :
    TileableWith (tiles input) Set.univ Allowed ↔ ∀ r, FiniteSearch input r :=
  ⟨finiteSearch_of_tileable input,tileable_of_all_finiteSearch input⟩

theorem allowed_primrec : PrimrecPred Allowed := by
  exact ((Primrec.eq.comp kind_primrec (Primrec.const true)).not.or
    (Primrec.eq.comp symmetry_primrec (Primrec.const SquareSymmetry.identity))).of_eq
    (fun _ => by simp [Allowed,imp_iff_not_or])

theorem finiteSearch_primrec : PrimrecRel FiniteSearch := by
  have legal : PrimrecPred (fun ps : List (Placement Bool) => ∀ p ∈ ps, Allowed p) := by
    exact allowed_primrec.forall_mem_list
  have selected : PrimrecRel (fun (ps : List (Placement Bool)) (a : Input × Nat) =>
      Valid a.1 a.2 ps ∧ ∀ p ∈ ps, Allowed p) :=
    (valid_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))).and (legal.comp Primrec.fst)
  exact selected.exists_mem_list.comp (subsets_primrec.comp pool_primrec) Primrec.id

end LeanTrominoes.TranslationPlaneSearch
