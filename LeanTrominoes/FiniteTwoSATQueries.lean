/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteReachHornQuery

/-! # Executable batches of opposite-literal reachability tests -/
namespace LeanTrominoes.ImplicationGraph
variable {n : Nat}

def checkPairs (edges : List (Fin n × Fin n)) : List (Fin n × Fin n) → Bool × Nat
  | [] => (true,1)
  | (u,v) :: pairs =>
    let forward := reachQuery edges u v
    let backward := reachQuery edges v u
    let rest := checkPairs edges pairs
    (!(forward && backward) && rest.1, queryCost edges u v+queryCost edges v u+rest.2+4)

theorem reachQuery_false (edges : List (Fin n × Fin n)) (u v : Fin n) :
    reachQuery edges u v=false ↔ ¬ Relation.ReflTransGen (EdgeAdj edges) u v := by
  simpa using not_congr (reachQuery_correct edges u v)

theorem checkPairs_correct (edges : List (Fin n × Fin n)) (pairs : List (Fin n × Fin n)) :
    (checkPairs edges pairs).1=true ↔ ∀ pair ∈ pairs,
      ¬ (Relation.ReflTransGen (EdgeAdj edges) pair.1 pair.2 ∧
        Relation.ReflTransGen (EdgeAdj edges) pair.2 pair.1) := by
  induction pairs with
  | nil => simp [checkPairs]
  | cons pair pairs ih =>
    obtain ⟨u,v⟩ := pair
    simp [checkPairs,Bool.and_eq_true,reachQuery_false,ih] <;> tauto

theorem checkPairs_cost (edges : List (Fin n × Fin n)) (pairs : List (Fin n × Fin n)) :
    (checkPairs edges pairs).2 ≤ pairs.length*(280*(n+edges.length+1)+404)+1 := by
  induction pairs with
  | nil => simp [checkPairs]
  | cons pair pairs ih =>
    obtain ⟨u,v⟩ := pair
    have one := queryCost_bound edges u v
    have two := queryCost_bound edges v u
    simp only [checkPairs,List.length_cons,Prod.snd] at *
    nlinarith

end LeanTrominoes.ImplicationGraph
