/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseSearch

/-! # Soundness and completeness of dense alternating-path search -/
namespace LeanTrominoes.BipartiteMatching.DenseSearch
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R]

theorem Prefix.attach {adj : L → R → Prop} {matching : State L R} {l : L} {prior : List (L × R)}
    (path : Prefix adj matching l prior) (suffix : Route L R) (begins : suffix.first=l)
    (alternating : Alternating adj matching suffix) :
    ∃ route : Route L R, Alternating adj matching route ∧
      routePairs route=prior++routePairs suffix ∧ matching.left route.first=none := by
  induction path generalizing suffix with
  | start free => exact ⟨suffix,alternating,by simp,by simpa [begins] using free⟩
  | @step l prior r next earlier edge mate ih =>
    have step := Alternating.cons edge (by simpa [begins] using mate) alternating
    obtain ⟨route,good,pairs,free⟩ := ih (.cons l r suffix) rfl step
    exact ⟨route,good,by simpa [routePairs,List.append_assoc] using pairs,free⟩

variable [Fintype L]

theorem Invariant.finish {adj : L → R → Prop} {matching : State L R} {paths : Paths L R}
    (inv : Invariant adj matching paths) (l : L) (r : R) (marked : reached paths l)
    (edge : adj l r) (free : matching.right r=none) :
    ∃ route : Route L R, Alternating adj matching route ∧ matching.left route.first=none ∧
      route.vertices.Nodup := by
  obtain ⟨prior,marked⟩ := marked
  obtain ⟨route,alternating,pairs,root⟩ :=
    (inv.path l prior marked).attach (.last l r) rfl (Alternating.last edge free)
  refine ⟨route,alternating,root,?_⟩
  rw [← routePairs_fst,pairs]
  simpa [routePairs] using inv.simple l prior marked

theorem search_extends (matching : State L R) (edges : List (L × R)) (rounds : Nat) :
    Extends (search matching edges rounds) (search matching edges (rounds+1)) := by
  simpa only [search,Function.iterate_succ_apply'] using scan_extends matching edges _

theorem search_mono (matching : State L R) (edges : List (L × R)) {a b : Nat} (bound : a≤b) :
    Extends (search matching edges a) (search matching edges b) := by
  induction b, bound using Nat.le_induction with
  | base => exact extends_refl _
  | succ b before ih => exact ih.trans (search_extends matching edges b)

/-- Every source that is reached before an edge sweep propagates to its
matched neighbor by the end of that sweep. -/
theorem search_step (matching : State L R) (edges : List (L × R)) (rounds : Nat)
    (l : L) (r : R) (next : L) (edge : (l,r)∈edges)
    (source : reached (search matching edges rounds) l) (mate : matching.right r=some next) :
    reached (search matching edges (rounds+1)) next := by
  simpa only [search,Function.iterate_succ_apply'] using scan_reaches matching edges _ l r next edge source mate

/-- Following a known alternating route takes at most one complete input
sweep per matched edge, regardless of the edge order and duplicate edges. -/
theorem route_terminal (matching : State L R) (edges : List (L × R)) (route : Route L R)
    (alternating : Alternating (fun l r => (l,r)∈edges) matching route) (rounds : Nat)
    (source : reached (search matching edges rounds) route.first) :
    ∃ l r, (l,r)∈edges ∧ matching.right r=none ∧
      reached (search matching edges (rounds+route.vertices.length-1)) l := by
  induction alternating generalizing rounds with
  | @last l r edge free =>
    exact ⟨l,r,edge,free,by simpa [Route.vertices,Route.first] using source⟩
  | @cons l r rest edge mate alternating ih =>
    have next := search_step matching edges rounds l r rest.first edge source mate
    obtain ⟨a,b,member,free,marked⟩ := ih (rounds+1) next
    exact ⟨a,b,member,free,by
      simpa only [Route.vertices,List.length_cons,Nat.add_right_comm,Nat.add_assoc,Nat.add_comm] using marked⟩

variable [Fintype R]

theorem alternating_of_edge_buckets (edges : List (L × R)) (matching : State L R)
    (route : Route L R)
    (alternating : Alternating (fun l r => r∈(edges.filter (fun e => e.1=l)).map Prod.snd) matching route) :
    Alternating (fun l r => (l,r)∈edges) matching route := by
  induction alternating with
  | @last l r member terminal =>
    obtain ⟨e,inside,hr⟩ := List.mem_map.mp member
    obtain ⟨he,hl⟩ := List.mem_filter.mp inside
    have eq : e=(l,r) := Prod.ext (of_decide_eq_true hl) hr
    exact Alternating.last (eq ▸ he) terminal
  | @cons l r rest member mate good ih =>
    obtain ⟨e,inside,hr⟩ := List.mem_map.mp member
    obtain ⟨he,hl⟩ := List.mem_filter.mp inside
    have eq : e=(l,r) := Prod.ext (of_decide_eq_true hl) hr
    exact Alternating.cons (eq ▸ he) mate ih

/-- A perfect matching guarantees that the dense search finds a free right
neighbor whenever the current partial matching is not full. -/
theorem search_complete (edges : List (L × R)) (matching : State L R)
    (consistent : Consistent matching)
    (perfect : HasFiniteMatching (fun l => (edges.filter (fun e => e.1=l)).map Prod.snd))
    (imperfect : ¬Full matching) :
    ∃ l r, (l,r)∈edges ∧ matching.right r=none ∧
      reached (search matching edges (Fintype.card L)) l := by
  let buckets : L → List R := fun l => (edges.filter (fun e => e.1=l)).map Prod.snd
  obtain ⟨route,alternating,free,simple,_,_⟩ := short_route (List.ofFn (fun i : Fin (Fintype.card L) =>
      (Fintype.equivFin L).symm i)) (by simpa using List.nodup_ofFn.mpr (Fintype.equivFin L).symm.injective)
    (by intro l; exact List.mem_ofFn.mpr ⟨(Fintype.equivFin L) l,by simp⟩) buckets matching consistent perfect imperfect
  have same := alternating_of_edge_buckets edges matching route alternating
  have initialMarked : reached (search matching edges 0) route.first := by
    refine ⟨[],?_⟩
    simp [search,initial,free]
  obtain ⟨l,r,member,terminal,marked⟩ := route_terminal matching edges route same 0 initialMarked
  have length : route.vertices.length≤Fintype.card L := by
    rw [← List.toFinset_card_of_nodup simple]
    exact Finset.card_le_univ _
  obtain ⟨prior,hprior⟩ := marked
  exact ⟨l,r,member,terminal,prior,search_mono matching edges (by omega) l prior hprior⟩

end LeanTrominoes.BipartiteMatching.DenseSearch
