/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDominoChart

/-! # Constructing the cell adjacency graph from fundamental-domain coordinates -/
namespace LeanTrominoes.Domino
open PeriodicLatticeGraph
variable {V : Type*} {d r : Nat}

def neighborArcs (origin : V → Cell d) (decode : Cell d → Option (V × Lattice r))
    (vertices : List V) : List (Arc V r) :=
  vertices.flatMap fun v => (List.finRange d).filterMap fun i =>
    (decode (origin v+unit i)).map fun w => ⟨v,w.1,w.2⟩

theorem neighborArcs_length (origin : V → Cell d) (decode : Cell d → Option (V × Lattice r))
    (vertices : List V) : (neighborArcs origin decode vertices).length ≤ vertices.length*d := by
  induction vertices with
  | nil => simp [neighborArcs]
  | cons v vertices ih =>
    have h := List.length_filterMap_le (f := fun i : Fin d =>
      (decode (origin v+unit i)).map fun w => (⟨v,w.1,w.2⟩ : Arc V r)) (l := List.finRange d)
    simp only [List.length_finRange] at h
    simp only [neighborArcs,List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul] at ih ⊢
    omega

theorem neighborArcs_mem (origin : V → Cell d) (decode : Cell d → Option (V × Lattice r))
    (vertices : List V) (e : Arc V r) :
    e∈neighborArcs origin decode vertices ↔
      e.source∈vertices ∧ ∃ i, decode (origin e.source+unit i)=some (e.target,e.offset) := by
  constructor
  · intro h
    obtain ⟨v,hv,hi⟩ := List.mem_flatMap.mp h
    obtain ⟨i,_,equal⟩ := List.mem_filterMap.mp hi
    cases found : decode (origin v+unit i) with
    | none => simp [found] at equal
    | some w =>
      have same : (⟨v,w.1,w.2⟩ : Arc V r)=e := by simpa [found] using equal
      subst e
      exact ⟨hv,i,found⟩
  · rintro ⟨hv,i,found⟩
    apply List.mem_flatMap.mpr
    refine ⟨e.source,hv,List.mem_filterMap.mpr ⟨i,List.mem_finRange _,?_⟩⟩
    simp [found]

theorem neighborArcs_adj (C : Chart V d r) (decode : Cell d → Option (V × Lattice r))
    (correct : ∀ x u, decode x=some u ↔ C.realize u=x)
    (vertices : List V) (complete : ∀ v, v∈vertices) (x y : V × Lattice r) :
    UndirectedAdj (neighborArcs C.origin decode vertices) x y ↔ Adjacent (C.realize x) (C.realize y) := by
  have forward (x y : V × Lattice r)
      (edge : Adj (neighborArcs C.origin decode vertices) x y) : Adjacent (C.realize x) (C.realize y) := by
    obtain ⟨e,he,source,target,offset⟩ := edge
    obtain ⟨_,i,found⟩ := (neighborArcs_mem C.origin decode vertices e).mp he
    have point := (correct _ _).mp found
    refine ⟨i,Or.inl ?_⟩
    change C.origin y.1+C.period y.2=C.origin x.1+C.period x.2+unit i
    rw [offset,map_add,← target,← source]
    change C.origin e.target+C.period e.offset=C.origin e.source+unit i at point
    calc
      C.origin e.target+(C.period x.2+C.period e.offset) =
        (C.origin e.target+C.period e.offset)+C.period x.2 := by abel
      _ = (C.origin e.source+unit i)+C.period x.2 := by rw [point]
      _ = C.origin e.source+C.period x.2+unit i := by abel
  have backward (x y : V × Lattice r) (i : Fin d) (equal : C.realize y=C.realize x+unit i) :
      Adj (neighborArcs C.origin decode vertices) x y := by
    have point : C.realize (y.1,y.2-x.2)=C.origin x.1+unit i := by
      calc
        C.realize (y.1,y.2-x.2)=C.realize y-C.period x.2 := by simp [Chart.realize,map_sub,sub_eq_add_neg,add_assoc]
        _ = (C.realize x+unit i)-C.period x.2 := by rw [equal]
        _ = C.origin x.1+unit i := by simp only [Chart.realize]; abel
    have member : (⟨x.1,y.1,y.2-x.2⟩ : Arc V r)∈neighborArcs C.origin decode vertices :=
      (neighborArcs_mem C.origin decode vertices _).mpr ⟨complete _,i,(correct _ _).mpr point⟩
    exact ⟨⟨x.1,y.1,y.2-x.2⟩,member,rfl,rfl,by dsimp; abel⟩
  constructor
  · rintro (h | h)
    · exact forward x y h
    · exact adjacent_symm (forward y x h)
  · rintro ⟨i,h | h⟩
    · exact Or.inl (backward x y i h)
    · exact Or.inr (backward y x i h)

def Chart.graphOfDecoder (C : Chart V d r) (decode : Cell d → Option (V × Lattice r))
    (correct : ∀ x u, decode x=some u ↔ C.realize u=x)
    (vertices : List V) (complete : ∀ v, v∈vertices) : GraphChart V d r where
  toChart := C
  arcs := neighborArcs C.origin decode vertices
  adjacent_iff := neighborArcs_adj C decode correct vertices complete

noncomputable def Chart.decode (C : Chart V d r) (x : Cell d) : Option (V × Lattice r) :=
  by classical exact if h : x∈C.region then some (Classical.choose h) else none

theorem Chart.decode_correct (C : Chart V d r) (x : Cell d) (u : V × Lattice r) :
    C.decode x=some u ↔ C.realize u=x := by
  classical
  unfold Chart.decode
  split_ifs with h
  · have point := Classical.choose_spec h
    constructor
    · intro equal
      exact (congrArg C.realize (Option.some.inj equal)).symm.trans point
    · intro equal
      exact congrArg some (C.injective (point.trans equal.symm))
  · constructor
    · simp
    · intro equal; exact (h ⟨u,equal⟩).elim

noncomputable def Chart.graph [Fintype V] (C : Chart V d r) : GraphChart V d r := by
  classical
  exact C.graphOfDecoder C.decode C.decode_correct Finset.univ.toList (by simp)

/-- Theorem 5.13: no adjacency table or connectedness hypothesis is needed. -/
theorem Chart.doubled_tiling [DecidableEq V] [Fintype V] (C : Chart V d r)
    (tiled : Tileable C.region) :
    ∃ tiles, IsTiling C.region tiles ∧ PeriodicTiles (doubledPeriod C.period) tiles :=
  C.graph.doubled_tiling tiled

end LeanTrominoes.Domino
