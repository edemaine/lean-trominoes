/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGraphBox
import LeanTrominoes.TwoMatchingEscape
import LeanTrominoes.MatchingAlternatingPath

/-! # Lemma 4.3: bounded-diameter augmenting paths in general periodic graphs -/
namespace LeanTrominoes.PeriodicLatticeGraph
open TwoMatching
variable {V : Type*} [DecidableEq V] [Fintype V] {d : Nat}

/-- An undirected matching, allowed to leave some vertices free. -/
structure PeriodOneMatching (arcs : List (Arc V d)) extends PartialMatching (V × Lattice d) where
  supported : ∀ x y, mate x = some y → UndirectedAdj arcs x y
  periodic : ∀ x t, mate (translate t x) = (mate x).map (translate t)

/-- No periodicity is required of the witness perfect matching. -/
def HasPerfectMatching (arcs : List (Arc V d)) : Prop :=
  ∃ p : PerfectMatching (V × Lattice d), ∀ x, UndirectedAdj arcs x (p.mate x)

def DiameterAtMost (vertices : List (V × Lattice d)) (bound : Nat) : Prop :=
  ∀ x ∈ vertices, ∀ y ∈ vertices, ∀ i, (x.2 i-y.2 i).natAbs ≤ bound

theorem box_diameter (k : Nat) (xs : List (V × Lattice d))
    (inside : ∀ x ∈ xs, x ∈ vertexBox k) : DiameterAtMost xs (k-1) := by
  intro x hx y hy i
  have one := mem_box.mp (mem_vertexBox.mp (inside x hx)) i
  have two := mem_box.mp (mem_vertexBox.mp (inside y hy)) i
  omega

theorem translate_injective (t : Lattice d) : Function.Injective (translate (V := V) t) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun a => a.1) h
  · have eq := congrArg (fun a => a.2) h
    change x.2+t = y.2+t at eq
    exact add_right_cancel eq

/-- The volume of a box of side `2*d*|E|+1` exceeds its boundary pool. -/
theorem volume_exceeds_boundary (arcs : List (Arc V d)) :
    (boundaryPool arcs (2*d*arcs.length+1)).card < (2*d*arcs.length+1)^d := by
  have bound := card_boundaryPool arcs (2*d*arcs.length+1)
  cases d with
  | zero => simpa using bound
  | succ d =>
    simp only [Nat.add_sub_cancel,Nat.pow_succ] at bound ⊢
    have positive : 0 < (2*(d+1)*arcs.length+1)^d := by positivity
    nlinarith

/-- Every free vertex starts a simple augmenting path of diameter at most
`2*d*|E|`. Coordinate locality suffices, so in particular Manhattan locality
suffices. This includes nonbipartite graphs and dimension zero. -/
theorem bounded_augmenting_path (arcs : List (Arc V d)) (locality : Local arcs)
    (perfect : HasPerfectMatching arcs) (matching : PeriodOneMatching arcs)
    (root : V × Lattice d) (free : matching.mate root = none) :
    ∃ path : AugmentingPath matching.toPartialMatching (UndirectedAdj arcs) root,
      DiameterAtMost path.vertices (2*d*arcs.length) := by
  classical
  obtain ⟨p,supported_p⟩ := perfect
  let k := 2*d*arcs.length+1
  let s : Finset (V × Lattice d) := vertexBox k
  let f : Finset (V × Lattice d) := rootBox root.1 k
  have roots_free (r : V × Lattice d) (hr : r ∈ f) : matching.mate r = none := by
    obtain ⟨z,_,eq⟩ := Finset.mem_image.mp hr
    subst r
    have translated := matching.periodic root (z-root.2)
    have equal : translate (z-root.2) root = (root.1,z) := by
      apply Prod.ext; rfl
      change root.2+(z-root.2)=z; abel
    rw [equal,free] at translated
    exact translated
  have contained : f ⊆ s := by
    intro r hr
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    exact mem_vertexBox.mpr hz
  have terminal : Terminal matching.toPartialMatching p s f := by
    by_contra none
    have count := roots_le_boundary matching.toPartialMatching p s f (boundaryPool arcs k)
      contained roots_free
      (fun x hx hn => crossing_mem_boundaryPool arcs locality k x (p.mate x) hx hn (supported_p x))
      (fun x hx y paired hn => crossing_mem_boundaryPool arcs locality k x y hx hn
        (matching.supported x y paired)) none
    have root_count : f.card=k^d := card_rootBox _ _
    rw [root_count] at count
    exact (Nat.not_le_of_lt (volume_exceeds_boundary arcs)) count
  obtain ⟨r,rf,x,trace,inside,pin,last_free⟩ := terminal
  let path := trace.finish matching.supported supported_p (roots_free r rf) last_free
  have path_inside : ∀ a ∈ path.vertices, a ∈ s := by
    intro a ha
    change a ∈ (trace.toPrefix matching.supported supported_p (roots_free r rf)).vertices ++ [p.mate x] at ha
    rw [trace.toPrefix_vertices] at ha
    rcases List.mem_append.mp ha with old | final
    · exact inside a old
    · simp only [List.mem_singleton] at final
      exact final ▸ pin
  obtain ⟨z,_,eq⟩ := Finset.mem_image.mp rf
  have kind : r.1 = root.1 := by rw [← eq]
  let t := root.2-r.2
  let shifted := path.map matching.toPartialMatching (UndirectedAdj arcs) (translate t)
    (translate_injective t) (fun x => matching.periodic x t)
    (fun x y h => undirected_translate arcs x y t h)
  have root_equal : translate t r = root := by
    apply Prod.ext
    · exact kind
    · change r.2+(root.2-r.2)=root.2; abel
  have cast_vertices {a b : V × Lattice d} (eq : a=b)
      (path : AugmentingPath matching.toPartialMatching (UndirectedAdj arcs) a) :
      (eq ▸ path).vertices=path.vertices := by subst b; rfl
  refine ⟨root_equal ▸ shifted,?_⟩
  rw [cast_vertices]
  have shifted_vertices : shifted.vertices = path.vertices.map (translate t) :=
    path.map_vertices _ _ _ _ _ _
  change DiameterAtMost shifted.vertices _
  rw [shifted_vertices]
  intro a ha b hb i
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  have bound := box_diameter k path.vertices path_inside u hu v hv i
  change ((u.2+t) i-(v.2+t) i).natAbs ≤ _
  have equal : (u.2+t) i-(v.2+t) i = u.2 i-v.2 i := by simp
  rw [equal]
  simpa only [k,Nat.add_sub_cancel] using bound

/-- The paper's perfect-or-augmenting formulation. -/
theorem perfect_or_bounded_augmenting (arcs : List (Arc V d)) (locality : Local arcs)
    (perfect : HasPerfectMatching arcs) (matching : PeriodOneMatching arcs) :
    (∀ x, (matching.mate x).isSome) ∨
      ∀ root, matching.mate root = none →
        ∃ path : AugmentingPath matching.toPartialMatching (UndirectedAdj arcs) root,
          DiameterAtMost path.vertices (2*d*arcs.length) := by
  exact Or.inr (bounded_augmenting_path arcs locality perfect matching)

end LeanTrominoes.PeriodicLatticeGraph
