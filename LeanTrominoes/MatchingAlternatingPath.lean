/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoMatchingTrace

/-! # Simple augmenting paths, without a bipartiteness assumption -/
namespace LeanTrominoes.TwoMatching
variable {X Y : Type*} (m : PartialMatching X) (adj : X → X → Prop)

/-- A walk consisting of unmatched/matched pairs, ending before an unmatched edge. -/
inductive AlternatingPrefix (root : X) : X → Type _ where
  | start : AlternatingPrefix root root
  | step {x : X} (previous : AlternatingPrefix root x) (y z : X)
      (edge : adj x y) (unmatched : m.mate x ≠ some y)
      (paired : m.mate y = some z) (matched_edge : adj y z) : AlternatingPrefix root z

def AlternatingPrefix.endpoint {r x : X} (_t : AlternatingPrefix m adj r x) : X := x

def AlternatingPrefix.vertices {r x : X} : AlternatingPrefix m adj r x → List X
  | .start => [r]
  | .step previous y z _ _ _ _ => previous.vertices ++ [y,z]

/-- The walk is simple, has two free ends, and begins and ends with an unmatched edge. -/
structure AugmentingPath (root : X) where
  penultimate : X
  target : X
  walk : AlternatingPrefix m adj root penultimate
  final_edge : adj penultimate target
  final_unmatched : m.mate penultimate ≠ some target
  root_free : m.mate root = none
  target_free : m.mate target = none
  simple : (walk.vertices ++ [target]).Nodup

def AugmentingPath.vertices {r : X} (path : AugmentingPath m adj r) : List X :=
  path.walk.vertices ++ [path.target]

variable {m adj} {p : PerfectMatching X}

theorem Trace.perfect_unmatched {r x : X} (t : Trace m p r x) (free : m.mate r = none) :
    m.mate x ≠ some (p.mate x) := by
  intro matched
  have inv := t.invariant free
  by_cases eq : x = r
  · subst x; rw [free] at matched; contradiction
  · obtain ⟨b,hb,pair⟩ := inv.partial_closed x inv.last_mem eq
    have equal := Option.some.inj (pair.symm.trans matched)
    exact inv.perfect_fresh (equal ▸ hb)

def Trace.toPrefix (supported_m : ∀ x y, m.mate x = some y → adj x y)
    (supported_p : ∀ x, adj x (p.mate x)) {r x : X} (t : Trace m p r x)
    (free : m.mate r = none) : AlternatingPrefix m adj r x :=
  match t with
  | .start => .start
  | .step previous y paired =>
    .step (previous.toPrefix supported_m supported_p free) (p.mate previous.endpoint) y
      (supported_p _) (previous.perfect_unmatched free) paired (supported_m _ _ paired)

theorem Trace.toPrefix_vertices (supported_m : ∀ x y, m.mate x = some y → adj x y)
    (supported_p : ∀ x, adj x (p.mate x)) {r x : X} (t : Trace m p r x)
    (free : m.mate r = none) :
    (t.toPrefix supported_m supported_p free).vertices = t.vertices := by
  induction t with
  | start => rfl
  | step previous y paired ih => simp only [toPrefix,AlternatingPrefix.vertices,vertices,endpoint,ih]

def Trace.finish (supported_m : ∀ x y, m.mate x = some y → adj x y)
    (supported_p : ∀ x, adj x (p.mate x)) {r x : X} (t : Trace m p r x)
    (free : m.mate r = none) (last_free : m.mate (p.mate x) = none) : AugmentingPath m adj r where
  penultimate := x
  target := p.mate x
  walk := t.toPrefix supported_m supported_p free
  final_edge := supported_p x
  final_unmatched := t.perfect_unmatched free
  root_free := free
  target_free := last_free
  simple := by rw [t.toPrefix_vertices]; exact t.finish_simple free


def AlternatingPrefix.map (n : PartialMatching Y) (rel : Y → Y → Prop) (f : X → Y)
    (injective : Function.Injective f)
    (mates : ∀ x, n.mate (f x) = (m.mate x).map f)
    (edges : ∀ x y, adj x y → rel (f x) (f y)) {r x : X} (t : AlternatingPrefix m adj r x) :
    AlternatingPrefix n rel (f r) (f x) :=
  match t with
  | .start => .start
  | .step previous y z edge unmatched paired matched_edge =>
    .step (previous.map n rel f injective mates edges) (f y) (f z) (edges _ _ edge)
      (by
        rw [mates]
        intro h
        apply unmatched
        obtain ⟨v,hv,equal⟩ := Option.map_eq_some_iff.mp h
        exact (injective equal) ▸ hv)
      (by rw [mates,paired]; rfl) (edges _ _ matched_edge)

theorem AlternatingPrefix.map_vertices (n : PartialMatching Y) (rel : Y → Y → Prop) (f : X → Y)
    (injective : Function.Injective f)
    (mates : ∀ x, n.mate (f x) = (m.mate x).map f)
    (edges : ∀ x y, adj x y → rel (f x) (f y)) {r x : X} (t : AlternatingPrefix m adj r x) :
    (t.map n rel f injective mates edges).vertices = t.vertices.map f := by
  induction t with
  | start => rfl
  | step previous y z edge unmatched paired matched_edge ih =>
    simp only [map,vertices,ih,List.map_append,List.map_cons,List.map_nil]

def AugmentingPath.map (n : PartialMatching Y) (rel : Y → Y → Prop) (f : X → Y)
    (injective : Function.Injective f)
    (mates : ∀ x, n.mate (f x) = (m.mate x).map f)
    (edges : ∀ x y, adj x y → rel (f x) (f y)) {r : X} (path : AugmentingPath m adj r) : AugmentingPath n rel (f r) where
  penultimate := f path.penultimate
  target := f path.target
  walk := path.walk.map n rel f injective mates edges
  final_edge := edges _ _ path.final_edge
  final_unmatched := by
    rw [mates]
    intro h
    have same : m.mate path.penultimate = some path.target := by
      obtain ⟨v,hv,equal⟩ := Option.map_eq_some_iff.mp h
      exact (injective equal) ▸ hv
    exact path.final_unmatched same
  root_free := by rw [mates,path.root_free]; rfl
  target_free := by rw [mates,path.target_free]; rfl
  simple := by
    rw [path.walk.map_vertices]
    have simple := path.simple.map injective
    simpa only [List.map_append,List.map_cons,List.map_nil] using simple

theorem AugmentingPath.map_vertices (n : PartialMatching Y) (rel : Y → Y → Prop) (f : X → Y)
    (injective : Function.Injective f)
    (mates : ∀ x, n.mate (f x) = (m.mate x).map f)
    (edges : ∀ x y, adj x y → rel (f x) (f y)) {r : X} (path : AugmentingPath m adj r) :
    (path.map n rel f injective mates edges).vertices = path.vertices.map f := by
  simp only [map,vertices,AlternatingPrefix.map_vertices,List.map_append,List.map_cons,List.map_nil]

end LeanTrominoes.TwoMatching
