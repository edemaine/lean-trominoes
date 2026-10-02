/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteReachHornQuery
import LeanTrominoes.PeriodicTwoSATCore
import LeanTrominoes.PeriodicFiniteCoverReach
import Mathlib.Algebra.BigOperators.Fin

/-! # Explicit dense indices and edge generation for a finite 2SAT cover

Coordinates are base-M digit vectors. The equivalences below are executable;
no arbitrary finite-type indexing or classical enumeration is used.
-/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph ImplicationGraph
variable {n d M : Nat} [NeZero M]

def literalIndex (n : Nat) : Signed (Fin n) ≃ Fin (n*2) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

def coordinateIndex (d M : Nat) [NeZero M] : CoverLattice d M ≃ Fin (M^d) :=
  (Equiv.piCongrRight (fun _ : Fin d => (ZMod.finEquiv M).toEquiv.symm)).trans finFunctionFinEquiv

def coverIndex (n d M : Nat) [NeZero M] : Signed (Fin n) × CoverLattice d M ≃ Fin (n*2*M^d) :=
  (Equiv.prodCongr (literalIndex n) (coordinateIndex d M)).trans finProdFinEquiv

def coverEdges (formula : Formula (Fin n) d) (M : Nat) [NeZero M] : List (Fin (n*2*M^d) × Fin (n*2*M^d)) :=
  (List.finRange (M^d)).flatMap fun i => (arcs formula).map fun e =>
    (coverIndex n d M (e.source,(coordinateIndex d M).symm i),
     coverIndex n d M (e.target,(coordinateIndex d M).symm i+wrap M e.offset))

theorem coverEdges_length (formula : Formula (Fin n) d) :
    (coverEdges formula M).length=(arcs formula).length*M^d := by
  simp [coverEdges,List.length_flatMap,List.length_map,List.map_const,Nat.mul_comm]

/-- Edge generation retains all original records, including parallel arcs. -/
theorem coverEdges_mem (formula : Formula (Fin n) d)
    (u v : Signed (Fin n) × CoverLattice d M) :
    (coverIndex n d M u,coverIndex n d M v) ∈ coverEdges formula M ↔ CoverAdj (arcs formula) M u v := by
  constructor
  · intro member
    obtain ⟨i,hi,edge⟩ := List.mem_flatMap.mp member
    obtain ⟨e,he,equal⟩ := List.mem_map.mp edge
    have left := (coverIndex n d M).injective (Prod.mk.inj equal).1
    have right := (coverIndex n d M).injective (Prod.mk.inj equal).2
    refine ⟨e,he,congrArg Prod.fst left,congrArg Prod.fst right,?_⟩
    have one := congrArg Prod.snd left
    have two := congrArg Prod.snd right
    exact two.symm.trans (congrArg (fun z => z+wrap M e.offset) one)
  · rintro ⟨e,he,source,target,displacement⟩
    apply List.mem_flatMap.mpr
    refine ⟨coordinateIndex d M u.2,List.mem_finRange _,List.mem_map.mpr ⟨e,he,?_⟩⟩
    apply Prod.ext
    · apply congrArg (coverIndex n d M)
      exact Prod.ext source (by simp)
    · apply congrArg (coverIndex n d M)
      exact Prod.ext target (by simpa using displacement.symm)

/-- The explicit dense edge table has exactly the finite-cover reachability relation. -/
theorem coverEdges_reach (formula : Formula (Fin n) d)
    (u v : Signed (Fin n) × CoverLattice d M) :
    Relation.ReflTransGen (EdgeAdj (coverEdges formula M)) (coverIndex n d M u) (coverIndex n d M v) ↔
      CoverReach (arcs formula) M u v := by
  have lifted : ∀ s t, Relation.ReflTransGen (EdgeAdj (coverEdges formula M)) s t →
      CoverReach (arcs formula) M ((coverIndex n d M).symm s) ((coverIndex n d M).symm t) := by
    intro s t path
    induction path with
    | refl => exact .refl
    | @tail w v path edge ih =>
      apply ih.tail
      apply (coverEdges_mem formula _ _).mp
      simpa only [EdgeAdj,Equiv.apply_symm_apply] using edge
  have projected : ∀ s t, CoverReach (arcs formula) M s t →
      Relation.ReflTransGen (EdgeAdj (coverEdges formula M)) (coverIndex n d M s) (coverIndex n d M t) := by
    intro s t path
    induction path with
    | refl => exact .refl
    | @tail w v path edge ih => exact ih.tail ((coverEdges_mem formula w v).mpr edge)
  constructor
  · intro path
    simpa only [Equiv.symm_apply_apply] using lifted _ _ path
  · exact projected u v

end LeanTrominoes.PeriodicTwoSAT
