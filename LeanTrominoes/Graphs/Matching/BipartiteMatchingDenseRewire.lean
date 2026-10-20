/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseSolver

/-! # Rewriting the stored path by sequential pair-array updates -/
namespace LeanTrominoes.BipartiteMatching.DenseSearch
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

def writePairs (matching : State L R) : List (L × R) → State L R
  | [] => matching
  | (l,r)::rest => writePairs (pair matching l r) rest

theorem writePairs_left_outside (matching : State L R) (pairs : List (L × R)) (l : L)
    (outside : l∉pairs.map Prod.fst) : (writePairs matching pairs).left l=matching.left l := by
  induction pairs generalizing matching with
  | nil => rfl
  | cons edge rest ih =>
    rcases edge with ⟨a,b⟩
    have split : l≠a ∧ l∉rest.map Prod.fst := by simpa using outside
    rw [writePairs,ih _ split.2]
    simp [pair,split.1]

theorem writePairs_right_outside (matching : State L R) (pairs : List (L × R)) (r : R)
    (outside : r∉pairs.map Prod.snd) : (writePairs matching pairs).right r=matching.right r := by
  induction pairs generalizing matching with
  | nil => rfl
  | cons edge rest ih =>
    rcases edge with ⟨a,b⟩
    have split : r≠b ∧ r∉rest.map Prod.snd := by simpa using outside
    rw [writePairs,ih _ split.2]
    simp [pair,split.1]

theorem writePairs_left_write (matching : State L R) (pairs : List (L × R))
    (nodup : (pairs.map Prod.fst).Nodup) (l : L) (r : R) (member : (l,r)∈pairs) :
    (writePairs matching pairs).left l=some r := by
  induction pairs generalizing matching with
  | nil => simp at member
  | cons edge rest ih =>
    rcases edge with ⟨a,b⟩
    have split : a∉rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by simpa using nodup
    rcases List.mem_cons.mp member with equal | member
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      rw [writePairs,writePairs_left_outside _ rest l split.1]
      simp [pair]
    · exact ih (pair matching a b) split.2 member

theorem writePairs_right_write (matching : State L R) (pairs : List (L × R))
    (nodup : (pairs.map Prod.snd).Nodup) (l : L) (r : R) (member : (l,r)∈pairs) :
    (writePairs matching pairs).right r=some l := by
  induction pairs generalizing matching with
  | nil => simp at member
  | cons edge rest ih =>
    rcases edge with ⟨a,b⟩
    have split : b∉rest.map Prod.snd ∧ (rest.map Prod.snd).Nodup := by simpa using nodup
    rcases List.mem_cons.mp member with equal | member
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      rw [writePairs,writePairs_right_outside _ rest r split.1]
      simp [pair]
    · exact ih (pair matching a b) split.2 member

theorem writePairs_route (matching : State L R) (route : Route L R)
    (simple : route.vertices.Nodup) (labels : (routeLabels route).Nodup) :
    writePairs matching (routePairs route)=applyRoute matching route := by
  have left : (writePairs matching (routePairs route)).left=(applyRoute matching route).left := by
    funext l
    by_cases inside : l∈route.vertices
    · obtain ⟨r,member⟩ := pair_at_vertex route l inside
      rw [writePairs_left_write _ _ (by simpa [routePairs_fst] using simple) l r member,
        applyRoute_left_write _ _ simple l r member]
    · rw [writePairs_left_outside _ _ l (by simpa [routePairs_fst] using inside),
        applyRoute_left_outside _ _ l inside]
  have right : (writePairs matching (routePairs route)).right=(applyRoute matching route).right := by
    funext r
    by_cases inside : r∈routeLabels route
    · obtain ⟨l,member⟩ := pair_at_label route r inside
      rw [writePairs_right_write _ _ (by simpa [routePairs_snd] using labels) l r member,
        applyRoute_right_write _ _ labels l r member]
    · rw [writePairs_right_outside _ _ r (by simpa [routePairs_snd] using inside),
        applyRoute_right_outside _ _ r inside]
  cases first : writePairs matching (routePairs route)
  cases second : applyRoute matching route
  simp_all

/-- No unpairing instruction is required: the final array values equal the
already verified alternating-route augmentation. Intermediate states may have
a temporary inconsistent inverse array while the next path pair is written. -/
theorem writePairs_correct (adj : L → R → Prop) (matching : State L R) (route : Route L R)
    (consistent : Consistent matching) (supported : Supported adj matching)
    (alternating : Alternating adj matching route) (simple : route.vertices.Nodup)
    (free : matching.left route.first=none) :
    Consistent (writePairs matching (routePairs route)) ∧
      Supported adj (writePairs matching (routePairs route)) ∧
      size (writePairs matching (routePairs route))=size matching+1 := by
  rw [writePairs_route matching route simple (labels_nodup adj matching route alternating simple)]
  exact ⟨(applyRoute_correct adj matching route consistent supported alternating simple free).1,
    (applyRoute_correct adj matching route consistent supported alternating simple free).2,
    applyRoute_size adj matching consistent route alternating simple free⟩

end LeanTrominoes.BipartiteMatching.DenseSearch
