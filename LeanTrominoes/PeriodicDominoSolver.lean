/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDominoBasis

/-! # An executable finite matching decision for periodic domino tilability -/
namespace LeanTrominoes.PeriodicBipartite
variable {V W : Type*} {r : Nat}

def reindex (index : V ≃ W) (edges : List (Edge V V r)) : List (Edge W W r) :=
  edges.map fun e => ⟨index e.left,index e.right,e.offset⟩

theorem reindex_quotient (index : V ≃ W) (edges : List (Edge V V r)) :
    HasQuotientMatching (reindex index edges) ↔ HasQuotientMatching edges := by
  constructor
  · rintro ⟨f,supported⟩
    refine ⟨index.trans (f.trans index.symm),?_⟩
    intro v
    obtain ⟨e,he,left,right⟩ := supported (index v)
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    refine ⟨a,ha,index.injective left,?_⟩
    change a.right=index.symm (f (index v))
    simpa only [Equiv.symm_apply_apply] using congrArg index.symm right
  · rintro ⟨f,supported⟩
    refine ⟨index.symm.trans (f.trans index),?_⟩
    intro w
    obtain ⟨e,he,left,right⟩ := supported (index.symm w)
    refine ⟨⟨index e.left,index e.right,e.offset⟩,List.mem_map.mpr ⟨e,he,rfl⟩,?_,?_⟩
    · simpa only [Equiv.apply_symm_apply] using congrArg index left
    · exact congrArg index right

end LeanTrominoes.PeriodicBipartite
namespace LeanTrominoes.Domino
open PeriodicLatticeGraph
variable {n d : Nat}

def vertexIndex (n d : Nat) : (Fin n × DoubleCover.Phase d) ≃ Fin (n*2^d) :=
  (Equiv.prodCongr (Equiv.refl _) finFunctionFinEquiv).trans finProdFinEquiv

def solverEdges (arcs : List (Arc (Fin n) d)) :
    List (PeriodicBipartite.Edge (Fin (n*2^d)) (Fin (n*2^d)) d) :=
  PeriodicBipartite.reindex (vertexIndex n d) (symmetricEdges (DoubleCover.arcs arcs))

theorem solverEdges_length (arcs : List (Arc (Fin n) d)) :
    (solverEdges arcs).length=2*(arcs.length*2^d) := by
  simp only [solverEdges,PeriodicBipartite.reindex,List.length_map,symmetricEdges_length,DoubleCover.arcs_length]

theorem solverEdges_perfect_iff (C : GraphChart (Fin n) d d) :
    PeriodicBipartite.HasPerfectMatching (solverEdges C.arcs) ↔ Tileable C.toChart.region := by
  rw [PeriodicBipartite.perfect_iff_quotient,solverEdges,PeriodicBipartite.reindex_quotient,
    ← PeriodicBipartite.perfect_iff_quotient]
  let coloring := fun x => color (C.toChart.realize x)
  have proper : ProperColoring C.arcs coloring := fun x y edge => adjacent_color ((C.adjacent_iff x y).mp edge)
  have periodic : TwiceInvariant coloring := by
    intro x t
    change color (C.toChart.realize (translate (t+t) x))=color (C.toChart.realize x)
    rw [Chart.realize_translate,map_add,color_double]
  rw [symmetricEdges_perfect (DoubleCover.arcs C.arcs) (doubledColor coloring)
    (doubledColor_proper C.arcs coloring proper periodic),doubleCover_perfect_iff,← C.tileable_iff]

/-- The decoder is prepared once and shared by all neighbor queries. -/
def BasisData.cellArcs (B : BasisData n d) : List (Arc (Fin n) d) :=
  let inverse := B.inverseData
  neighborArcs B.origin (B.decodeWith inverse) (List.finRange n)

def BasisData.solve (B : BasisData n d) : Bool :=
  (PeriodicBipartite.matchingSolver (solverEdges B.cellArcs)).table.isSome

theorem BasisData.solve_correct (B : BasisData n d) (valid : B.Valid) :
    B.solve=true ↔ Tileable (B.chart valid).region := by
  rw [BasisData.solve,PeriodicBipartite.matchingSolver_iff]
  exact solverEdges_perfect_iff (B.graph valid)

theorem BasisData.cellArcs_size (B : BasisData n d) : B.cellArcs.length ≤ n*d := by
  simpa only [BasisData.cellArcs,List.length_finRange] using
    neighborArcs_length B.origin (B.decodeWith B.inverseData) (List.finRange n)

end LeanTrominoes.Domino
