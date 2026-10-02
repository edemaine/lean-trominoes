/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicMatchingIndex

/-! # Arbitrary period-one partial matchings and their finite quotients

The input matching consists of partial inverse partner functions on the
infinite lattice, with no finite-table assumption. Translation covariance
allows its quotient and matched offsets to be read at the zero translate.
-/
namespace LeanTrominoes.PeriodicBipartite
open BipartiteMatching
variable {L R : Type*} {d : Nat}

def move {V : Type*} (t : Lattice d) (u : V × Lattice d) : V × Lattice d := (u.1,u.2+t)

structure PeriodOnePartial (edges : List (Edge L R d)) where
  partners : State (L × Lattice d) (R × Lattice d)
  consistent : Consistent partners
  supported : Supported (Adj edges) partners
  left_translate : ∀ l z t, partners.left (l,z+t)=(partners.left (l,z)).map (move t)
  right_translate : ∀ r z t, partners.right (r,z+t)=(partners.right (r,z)).map (move t)

namespace PeriodOnePartial
variable {edges : List (Edge L R d)} (matching : PeriodOnePartial edges)

def quotient : State L R :=
  ⟨fun l => (matching.partners.left (l,0)).map Prod.fst,
   fun r => (matching.partners.right (r,0)).map Prod.fst⟩

def offset (l : L) : Lattice d := ((matching.partners.left (l,0)).map Prod.snd).getD 0

theorem left_at (l : L) (z : Lattice d) : matching.partners.left (l,z)=
    (matching.quotient.left l).map (fun r => (r,z+matching.offset l)) := by
  have shifted := matching.left_translate l 0 z
  cases origin : matching.partners.left (l,0) with
  | none => simpa [origin,quotient,offset] using shifted
  | some pair =>
    obtain ⟨r,a⟩ := pair
    simpa [origin,quotient,offset,move,add_comm] using shifted

theorem quotient_consistent : Consistent matching.quotient := by
  intro l r
  constructor
  · intro paired
    obtain ⟨pair,origin,equal⟩ := Option.map_eq_some_iff.mp paired
    obtain ⟨s,a⟩ := pair
    change s=r at equal
    subst s
    have inverse := (matching.consistent (l,0) (r,a)).mp origin
    have shifted := matching.right_translate r a (-a)
    rw [inverse] at shifted
    have zero : matching.partners.right (r,0)=some (l,-a) := by simpa [move] using shifted
    simp [quotient,zero]
  · intro paired
    obtain ⟨pair,origin,equal⟩ := Option.map_eq_some_iff.mp paired
    obtain ⟨s,a⟩ := pair
    change s=l at equal
    subst s
    have inverse := (matching.consistent (l,a) (r,0)).mpr origin
    have shifted := matching.left_translate l a (-a)
    rw [inverse] at shifted
    have zero : matching.partners.left (l,0)=some (r,-a) := by simpa [move] using shifted
    simp [quotient,zero]

theorem quotient_supported : Supported (QuotientAdj edges) matching.quotient := by
  intro l r paired
  obtain ⟨pair,origin,equal⟩ := Option.map_eq_some_iff.mp paired
  obtain ⟨s,a⟩ := pair
  change s=r at equal
  subst s
  obtain ⟨e,he,left,right,_⟩ := matching.supported (l,0) (r,a) origin
  exact ⟨e,he,left,right⟩

theorem right_at (r : R) (l : L) (paired : matching.quotient.right r=some l) (z : Lattice d) :
    matching.partners.right (r,z)=some (l,z-matching.offset l) := by
  have left := matching.left_at l (z-matching.offset l)
  rw [(matching.quotient_consistent l r).mpr paired] at left
  have mate : matching.partners.left (l,z-matching.offset l)=some (r,z) := by simpa using left
  exact (matching.consistent _ _).mp mate

theorem right_free (r : R) (free : matching.quotient.right r=none) (z : Lattice d) :
    matching.partners.right (r,z)=none := by
  have shifted := matching.right_translate r 0 z
  cases origin : matching.partners.right (r,0) with
  | none => simpa [origin] using shifted
  | some pair => simp [quotient,origin] at free

theorem left_free (l : L) (free : matching.quotient.left l=none) (z : Lattice d) :
    matching.partners.left (l,z)=none := by simp [matching.left_at,free]

end PeriodOnePartial
end LeanTrominoes.PeriodicBipartite
