/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicMatchingPeriodOne
import LeanTrominoes.HornWorklistIndex
import LeanTrominoes.BipartiteMatchingSolver

/-! # Linear quotient indexing and necessary input-size checks -/
namespace LeanTrominoes.PeriodicBipartite
variable {L R : Type*} {d : Nat} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

def edgePairs (edges : List (Edge L R d)) : List (L × R) := edges.map (fun e => (e.left,e.right))
def buckets (edges : List (Edge L R d)) : L → List R := (Horn.Worklist.index (edgePairs edges)).bucket

theorem buckets_mem (edges : List (Edge L R d)) (l : L) (r : R) : r ∈ buckets edges l ↔ QuotientAdj edges l r := by
  unfold buckets
  rw [← List.count_pos_iff,Horn.Worklist.index_bucket_count,List.count_pos_iff]
  simp only [edgePairs,List.mem_map,QuotientAdj,Prod.mk.injEq]

theorem buckets_volume (edges : List (Edge L R d)) : (∑ l, (buckets edges l).length)=edges.length := by
  simpa [buckets,edgePairs] using Horn.Worklist.index_volume (edgePairs edges)

theorem finite_iff_quotient (edges : List (Edge L R d)) :
    BipartiteMatching.HasFiniteMatching (buckets edges) ↔ HasQuotientMatching edges := by
  simp only [BipartiteMatching.HasFiniteMatching,HasQuotientMatching,buckets_mem]

theorem quotient_card (edges : List (Edge L R d)) (matching : HasQuotientMatching edges) :
    Fintype.card L=Fintype.card R := by
  obtain ⟨f,_⟩ := matching
  exact Fintype.card_congr f

theorem quotient_edges (edges : List (Edge L R d)) (matching : HasQuotientMatching edges) :
    Fintype.card L ≤ edges.length := by
  obtain ⟨f,supported⟩ := matching
  have all : Finset.univ ⊆ (edges.map Edge.left).toFinset := by
    intro l _
    obtain ⟨e,he,equal,_⟩ := supported l
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,equal⟩)
  have bound := Finset.card_le_card all
  have length := List.toFinset_card_le (edges.map Edge.left)
  simpa using bound.trans length

end LeanTrominoes.PeriodicBipartite
