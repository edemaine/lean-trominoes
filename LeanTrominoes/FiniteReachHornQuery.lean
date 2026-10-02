/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornIndexedTime
import Mathlib.Logic.Relation

/-! # Finite reachability queries using the verified indexed Horn solver -/
namespace LeanTrominoes.ImplicationGraph
variable {n : Nat}
def EdgeAdj (edges : List (Fin n × Fin n)) (u v : Fin n) : Prop := (u,v) ∈ edges

def queryInput (edges : List (Fin n × Fin n)) (source target : Fin n) : Horn.Indexed.Input n :=
  ⟨(([⟨[],some source⟩,⟨[target],none⟩] ++ edges.map (fun edge => ⟨[edge.1],some edge.2⟩)) : List (Horn.Rule (Fin n))).toArray⟩

/-- A fact at the source and a negative unit at the target encode non-reachability. -/
theorem query_satisfiable_iff (edges : List (Fin n × Fin n)) (source target : Fin n) :
    Horn.Satisfiable (queryInput edges source target).rules.toList ↔
      ¬ Relation.ReflTransGen (EdgeAdj edges) source target := by
  constructor
  · rintro ⟨model,satisfied⟩ path
    have initial : model source := satisfied ⟨[],some source⟩ (by simp [queryInput]) (by simp)
    have forbidden : ¬ model target := by
      intro truth
      exact satisfied ⟨[target],none⟩ (by simp [queryInput]) (by simpa using truth)
    have propagate : ∀ v, Relation.ReflTransGen (EdgeAdj edges) source v → model v := by
      intro v reachable
      induction reachable with
      | refl => exact initial
      | @tail u v path edge ih =>
        have rule : Horn.Rule.Holds ⟨[u],some v⟩ model :=
          satisfied _ (by
            change (⟨[u],some v⟩ : Horn.Rule (Fin n)) ∈ (queryInput edges source target).rules.toList
            simp only [queryInput,List.toList_toArray]
            apply List.mem_append.mpr
            exact Or.inr (List.mem_map.mpr ⟨(u,v),edge,rfl⟩))
        exact rule (by simpa using ih)
    exact forbidden (propagate target path)
  · intro noPath
    let model := Relation.ReflTransGen (EdgeAdj edges) source
    refine ⟨model,?_⟩
    intro rule member premises
    have membership : rule=⟨[],some source⟩ ∨ rule=⟨[target],none⟩ ∨
        ∃ edge ∈ edges, rule=⟨[edge.1],some edge.2⟩ := by
      simpa [queryInput,List.mem_map,eq_comm,or_assoc] using member
    rcases membership with rfl | rfl | ⟨⟨u,v⟩,edge,rfl⟩
    · exact Relation.ReflTransGen.refl
    · exact noPath (premises target (by simp))
    · exact (premises u (by simp)).tail edge

/-- true means reachable; the actual decision uses the indexed worklist implementation. -/
def reachQuery (edges : List (Fin n × Fin n)) (source target : Fin n) : Bool :=
  !Horn.Indexed.check (queryInput edges source target)

theorem reachQuery_correct (edges : List (Fin n × Fin n)) (source target : Fin n) :
    reachQuery edges source target=true ↔ Relation.ReflTransGen (EdgeAdj edges) source target := by
  have check := (Horn.Indexed.check_correct (queryInput edges source target)).trans
    (query_satisfiable_iff edges source target)
  simp only [reachQuery,Bool.not_eq_true']
  simpa using not_congr check

theorem query_size (edges : List (Fin n × Fin n)) (source target : Fin n) :
    Horn.Indexed.inputSize (queryInput edges source target)=n+2*edges.length+5 := by
  induction edges with
  | nil => simp [Horn.Indexed.inputSize,Horn.Indexed.premiseCount,queryInput]
  | cons edge edges ih =>
    simp [Horn.Indexed.inputSize,Horn.Indexed.premiseCount,queryInput,List.map_map] at ih ⊢
    omega

/-- Includes constructing the Horn rule array and the complete verified worklist cost. -/
def queryCost (edges : List (Fin n × Fin n)) (source target : Fin n) : Nat :=
  4*edges.length+8+Horn.Indexed.totalCost (queryInput edges source target)

theorem queryCost_bound (edges : List (Fin n × Fin n)) (source target : Fin n) :
    queryCost edges source target ≤ 140*(n+edges.length+1)+200 := by
  have bound := Horn.Indexed.linear_time (queryInput edges source target)
  rw [query_size] at bound
  unfold queryCost
  omega

end LeanTrominoes.ImplicationGraph
