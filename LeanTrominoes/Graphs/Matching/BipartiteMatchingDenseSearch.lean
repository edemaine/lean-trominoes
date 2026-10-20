/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingShortRoute

/-! # Dense alternating-path search

A deliberately simple polynomial algorithm scans the original edge list.
A discovered left vertex stores its entire alternating prefix, so no recursive
stack or unbounded integer is needed by the later array implementation.
-/
namespace LeanTrominoes.BipartiteMatching.DenseSearch
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R]

abbrev Paths (L R : Type*) := L → Option (List (L × R))

def reached (paths : Paths L R) (l : L) : Prop := ∃ p, paths l=some p

def initial (matching : State L R) : Paths L R := fun l =>
  if (matching.left l).isNone then some [] else none

def discover (matching : State L R) (paths : Paths L R) (edge : L × R) : Paths L R :=
  match paths edge.1,matching.right edge.2 with
  | some prior,some next =>
    if (paths next).isNone then Function.update paths next (some (prior++[edge])) else paths
  | _,_ => paths

def scan (matching : State L R) (edges : List (L × R)) (paths : Paths L R) : Paths L R :=
  edges.foldl (discover matching) paths

def search (matching : State L R) (edges : List (L × R)) (rounds : Nat) : Paths L R :=
  (scan matching edges)^[rounds] (initial matching)

def Extends (before after : Paths L R) : Prop := ∀ l p, before l=some p → after l=some p

theorem extends_refl (paths : Paths L R) : Extends paths paths := fun _ _ h => h

theorem Extends.trans {a b c : Paths L R} (first : Extends a b) (second : Extends b c) : Extends a c :=
  fun l p h => second l p (first l p h)

theorem discover_extends (matching : State L R) (paths : Paths L R) (edge : L × R) :
    Extends paths (discover matching paths edge) := by
  intro l p old
  cases source : paths edge.1 <;> cases mate : matching.right edge.2 <;>
    simp only [discover,source,mate]
  all_goals first | exact old | skip
  rename_i prior next
  split
  · rename_i fresh
    have absent : paths next=none := Option.isNone_iff_eq_none.mp fresh
    have different : l≠next := by intro eq; subst l; simp_all
    simp [Function.update_of_ne different,old]
  · exact old

theorem scan_extends (matching : State L R) (edges : List (L × R)) (paths : Paths L R) :
    Extends paths (scan matching edges paths) := by
  induction edges generalizing paths with
  | nil => exact extends_refl paths
  | cons edge edges ih => exact (discover_extends matching paths edge).trans (ih _)

theorem discover_reaches (matching : State L R) (paths : Paths L R) (l : L) (r : R) (next : L)
    (source : reached paths l) (mate : matching.right r=some next) :
    reached (discover matching paths (l,r)) next := by
  obtain ⟨prior,source⟩ := source
  unfold discover
  simp only [source,mate]
  split
  · exact ⟨prior++[(l,r)],Function.update_self ..⟩
  · rename_i present
    exact Option.ne_none_iff_exists'.mp (by simpa using present)

theorem scan_reaches (matching : State L R) (edges : List (L × R)) (paths : Paths L R)
    (l : L) (r : R) (next : L) (edge : (l,r)∈edges) (source : reached paths l)
    (mate : matching.right r=some next) : reached (scan matching edges paths) next := by
  induction edges generalizing paths with
  | nil => simp at edge
  | cons first rest ih =>
    rcases List.mem_cons.mp edge with equal | member
    · subst first
      obtain ⟨p,hp⟩ := discover_reaches matching paths l r next source mate
      exact ⟨p,scan_extends matching rest _ next p hp⟩
    · obtain ⟨p,hp⟩ := source
      exact ih _ member ⟨p,discover_extends matching paths first l p hp⟩

/-- An alternating prefix ends at a left vertex; its list contains only the
already traversed left/right pairs. -/
inductive Prefix (adj : L → R → Prop) (matching : State L R) : L → List (L × R) → Prop
  | start {l} : matching.left l=none → Prefix adj matching l []
  | step {l prior r next} : Prefix adj matching l prior → adj l r → matching.right r=some next →
      Prefix adj matching next (prior++[(l,r)])

structure Invariant (adj : L → R → Prop) (matching : State L R) (paths : Paths L R) : Prop where
  path : ∀ l prior, paths l=some prior → Prefix adj matching l prior
  simple : ∀ l prior, paths l=some prior → (prior.map Prod.fst++[l]).Nodup
  known : ∀ l prior, paths l=some prior → ∀ a∈prior.map Prod.fst, reached paths a

theorem initial_invariant (adj : L → R → Prop) (matching : State L R) :
    Invariant adj matching (initial matching) := by
  constructor
  · intro l prior marked
    unfold initial at marked
    split at marked
    · have eq : prior=[] := Option.some.inj marked.symm
      subst prior
      exact Prefix.start (Option.isNone_iff_eq_none.mp (by assumption))
    · contradiction
  · intro l prior marked
    unfold initial at marked
    split at marked <;> simp_all
  · intro l prior marked a member
    unfold initial at marked
    split at marked <;> simp_all

theorem discover_invariant (adj : L → R → Prop) (matching : State L R)
    (paths : Paths L R) (inv : Invariant adj matching paths) (edge : L × R)
    (supported : adj edge.1 edge.2) : Invariant adj matching (discover matching paths edge) := by
  cases source : paths edge.1 <;> cases mate : matching.right edge.2 <;>
    simp only [discover,source,mate]
  all_goals first | exact inv | skip
  rename_i prior next
  split
  · rename_i fresh
    have absent : paths next=none := Option.isNone_iff_eq_none.mp fresh
    have different : next≠edge.1 := by intro eq; subst next; simp_all
    have oldSimple := inv.simple _ _ source
    have notMember : next ∉ prior.map Prod.fst := by
      intro member
      obtain ⟨p,hp⟩ := inv.known _ _ source next member
      simp [absent] at hp
    constructor
    · intro l p marked
      by_cases equal : l=next
      · subst l
        have eq : p=prior++[edge] := Option.some.inj (by simpa using marked.symm)
        subst p
        exact Prefix.step (inv.path _ _ source) supported mate
      · exact inv.path _ _ (by simpa [Function.update_of_ne equal] using marked)
    · intro l p marked
      by_cases equal : l=next
      · subst l
        have eq : p=prior++[edge] := Option.some.inj (by simpa using marked.symm)
        subst p
        have absentList : next ∉ prior.map Prod.fst++[edge.1] := by simp [notMember,different]
        simpa only [List.map_append,List.map_singleton,List.concat_eq_append,List.append_assoc] using
          oldSimple.concat absentList
      · exact inv.simple _ _ (by simpa [Function.update_of_ne equal] using marked)
    · intro l p marked a member
      by_cases equal : l=next
      · subst l
        have eq : p=prior++[edge] := Option.some.inj (by simpa using marked.symm)
        subst p
        simp only [List.map_append,List.map_singleton,List.mem_append,List.mem_singleton] at member
        rcases member with member | equal
        · obtain ⟨p,hp⟩ := inv.known _ _ source a member
          exact ⟨p,by simpa [discover,source,mate,fresh] using discover_extends matching paths edge a p hp⟩
        · subst a
          exact ⟨prior,by simpa [discover,source,mate,fresh] using discover_extends matching paths edge _ _ source⟩
      · have old := inv.known l p (by simpa [Function.update_of_ne equal] using marked) a member
        obtain ⟨p,hp⟩ := old
        exact ⟨p,by simpa [discover,source,mate,fresh] using discover_extends matching paths edge a p hp⟩
  · exact inv

theorem scan_invariant (adj : L → R → Prop) (matching : State L R)
    (edges : List (L × R)) (paths : Paths L R) (inv : Invariant adj matching paths)
    (supported : ∀ edge∈edges, adj edge.1 edge.2) : Invariant adj matching (scan matching edges paths) := by
  induction edges generalizing paths with
  | nil => exact inv
  | cons edge edges ih =>
    exact ih _ (discover_invariant adj matching paths inv edge (supported edge (by simp)))
      (fun e he => supported e (by simp [he]))

theorem search_invariant (adj : L → R → Prop) (matching : State L R)
    (edges : List (L × R)) (supported : ∀ edge∈edges, adj edge.1 edge.2) (rounds : Nat) :
    Invariant adj matching (search matching edges rounds) := by
  induction rounds with
  | zero => exact initial_invariant adj matching
  | succ rounds ih =>
    simpa only [search,Function.iterate_succ_apply'] using scan_invariant adj matching edges _ ih supported

end LeanTrominoes.BipartiteMatching.DenseSearch
