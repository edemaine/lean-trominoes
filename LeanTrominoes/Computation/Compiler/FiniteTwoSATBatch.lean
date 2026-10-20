/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteReachHornQuery
import Mathlib.Logic.Equiv.Fin.Basic
import LeanTrominoes.SAT.Horn.HornWordRAMProgram

/-! # A single Horn instance for a batch of opposite reachability queries

Each query has two independent copies of the graph. Source facts start both
searches. A negative binary rule rejects exactly when both opposite targets
are reachable. No reachability answers are supplied in the input.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATBatch

variable {n p : ℕ}

abbrev Atom (n p : ℕ) := Fin p × Bool × Fin n

def source (pairs : Fin p → Fin n × Fin n) (q : Fin p) (direction : Bool) : Fin n :=
  if direction then (pairs q).2 else (pairs q).1

def target (pairs : Fin p → Fin n × Fin n) (q : Fin p) (direction : Bool) : Fin n :=
  if direction then (pairs q).1 else (pairs q).2

def fact (pairs : Fin p → Fin n × Fin n) (q : Fin p) (direction : Bool) : Horn.Rule (Atom n p) :=
  ⟨[],some (q,direction,source pairs q direction)⟩

def negative (pairs : Fin p → Fin n × Fin n) (q : Fin p) : Horn.Rule (Atom n p) :=
  ⟨[(q,false,target pairs q false),(q,true,target pairs q true)],none⟩

def implication (q : Fin p) (direction : Bool) (edge : Fin n × Fin n) : Horn.Rule (Atom n p) :=
  ⟨[(q,direction,edge.1)],some (q,direction,edge.2)⟩

def rules (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) : List (Horn.Rule (Atom n p)) :=
  (List.finRange p).flatMap (fun q => [fact pairs q false,fact pairs q true]) ++
  (List.finRange p).map (negative pairs) ++
  (List.finRange p).flatMap (fun q => [false,true].flatMap fun direction =>
    edges.map (implication q direction))

def Consistent (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) : Prop :=
  ∀ q, ¬(Relation.ReflTransGen (EdgeAdj edges) (pairs q).1 (pairs q).2 ∧
    Relation.ReflTransGen (EdgeAdj edges) (pairs q).2 (pairs q).1)

theorem fact_mem (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n)
    (q : Fin p) (direction : Bool) : fact pairs q direction ∈ rules edges pairs := by
  unfold rules
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange _,?_⟩
  cases direction <;> simp

theorem negative_mem (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n)
    (q : Fin p) : negative pairs q ∈ rules edges pairs := by
  simp only [rules,List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨q,List.mem_finRange _,rfl⟩))

theorem implication_mem (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n)
    (q : Fin p) (direction : Bool) (edge : Fin n × Fin n) (he : edge ∈ edges) :
    implication q direction edge ∈ rules edges pairs := by
  unfold rules
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange _,List.mem_flatMap.mpr ⟨direction,?_,?_⟩⟩
  · cases direction <;> simp
  · exact List.mem_map.mpr ⟨edge,he,rfl⟩

theorem rules_mem_iff (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n)
    (r : Horn.Rule (Atom n p)) : r ∈ rules edges pairs ↔
    (∃ q direction, r=fact pairs q direction) ∨ (∃ q, r=negative pairs q) ∨
      ∃ q direction edge, edge ∈ edges ∧ r=implication q direction edge := by
  constructor
  · intro member
    simp only [rules,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and] at member
    rcases member with (⟨q,hq⟩ | ⟨q,rfl⟩) | ⟨q,direction,hd,edge,he,rfl⟩
    · have : r=fact pairs q false ∨ r=fact pairs q true := by simpa [eq_comm] using hq
      rcases this with rfl | rfl
      · exact Or.inl ⟨q,false,rfl⟩
      · exact Or.inl ⟨q,true,rfl⟩
    · exact Or.inr (Or.inl ⟨q,rfl⟩)
    · exact Or.inr (Or.inr ⟨q,direction,edge,he,rfl⟩)
  · rintro (⟨q,direction,rfl⟩ | ⟨q,rfl⟩ | ⟨q,direction,edge,he,rfl⟩)
    · exact fact_mem edges pairs q direction
    · exact negative_mem edges pairs q
    · exact implication_mem edges pairs q direction edge he

/-- The batch is satisfiable exactly when no opposite pair is mutually reachable. -/
theorem satisfiable_iff (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    Horn.Satisfiable (rules edges pairs) ↔ Consistent edges pairs := by
  constructor
  · rintro ⟨model,satisfied⟩ q ⟨forward,backward⟩
    have propagate (direction : Bool) (v : Fin n)
        (path : Relation.ReflTransGen (EdgeAdj edges) (source pairs q direction) v) : model (q,direction,v) := by
      induction path with
      | refl => exact satisfied _ (fact_mem edges pairs q direction) (by simp [fact])
      | @tail u v path edge ih =>
        exact satisfied _ (implication_mem edges pairs q direction (u,v) edge) (by simpa [implication] using ih)
    apply satisfied _ (negative_mem edges pairs q)
    intro a ha
    have member : a=(q,false,target pairs q false) ∨ a=(q,true,target pairs q true) := by
      simpa [negative] using ha
    rcases member with rfl | rfl
    · exact propagate false _ (by simpa [source,target] using forward)
    · exact propagate true _ (by simpa [source,target] using backward)
  · intro consistent
    let model : Atom n p → Prop := fun a =>
      Relation.ReflTransGen (EdgeAdj edges) (source pairs a.1 a.2.1) a.2.2
    refine ⟨model,?_⟩
    intro r member premises
    rcases (rules_mem_iff edges pairs r).mp member with ⟨q,direction,rfl⟩ | ⟨q,rfl⟩ | ⟨q,direction,⟨u,v⟩,he,rfl⟩
    · exact Relation.ReflTransGen.refl
    · apply consistent q
      constructor
      · simpa [model,source,target] using premises (q,false,target pairs q false) (by simp [negative])
      · simpa [model,source,target] using premises (q,true,target pairs q true) (by simp [negative])
    · exact (premises (q,direction,u) (by simp [implication])).tail he

theorem rules_length (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    (rules edges pairs).length=3*p+2*p*edges.length := by
  simp [rules,List.length_flatMap,List.length_map]
  ring


def atomIndex (n p : ℕ) : Atom n p ≃ Fin (p*2*n) :=
  (Equiv.prodAssoc (Fin p) Bool (Fin n)).symm.trans
    ((Equiv.prodCongr ((Equiv.prodCongr (Equiv.refl (Fin p)) finTwoEquiv.symm).trans finProdFinEquiv)
      (Equiv.refl (Fin n))).trans finProdFinEquiv)

def reindex {V W : Type} (e : V ≃ W) (r : Horn.Rule V) : Horn.Rule W :=
  ⟨r.premises.map e,r.conclusion.map e⟩

theorem reindex_holds {V W : Type} (e : V ≃ W) (r : Horn.Rule V) (model : W → Prop) :
    (reindex e r).Holds model ↔ r.Holds (fun a => model (e a)) := by
  simp only [reindex,Horn.Rule.Holds,List.forall_mem_map]
  cases r.conclusion <;> rfl

theorem reindex_satisfiable {V W : Type} (e : V ≃ W) (rs : List (Horn.Rule V)) :
    Horn.Satisfiable (rs.map (reindex e)) ↔ Horn.Satisfiable rs := by
  constructor
  · rintro ⟨model,satisfied⟩
    refine ⟨fun a => model (e a),?_⟩
    intro r hr
    exact (reindex_holds e r model).mp (satisfied _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
  · rintro ⟨model,satisfied⟩
    refine ⟨fun a => model (e.symm a),?_⟩
    intro r hr
    obtain ⟨original,originalMem,rfl⟩ := List.mem_map.mp hr
    apply (reindex_holds e original _).mpr
    simpa only [Equiv.symm_apply_apply] using satisfied original originalMem

def input (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) : Horn.Indexed.Input (p*2*n) :=
  ⟨((rules edges pairs).map (reindex (atomIndex n p))).toArray⟩

theorem input_correct (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    Horn.Satisfiable (input edges pairs).rules.toList ↔ Consistent edges pairs := by
  simp only [input,List.toList_toArray]
  exact (reindex_satisfiable _ _).trans (satisfiable_iff edges pairs)

theorem input_rules (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    (input edges pairs).rules.size=3*p+2*p*edges.length := by
  simp only [input,List.size_toArray,List.length_map,rules_length]

theorem sum_flatMap_const {V : Type} (xs : List V) (ys : List ℕ) :
    (xs.flatMap (fun _ => ys)).sum=xs.length*ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih,Nat.add_mul,Nat.add_comm]

theorem input_occurrences (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    (Horn.Indexed.edges (input edges pairs)).length=2*p+2*p*edges.length := by
  rw [Horn.Indexed.edges_length]
  simp only [Horn.Indexed.premiseCount,input,List.toList_toArray,List.map_map]
  simp [reindex,rules,fact,negative,implication,List.map_append,List.map_flatMap,
    List.sum_append,List.map_map,Function.comp_def,sum_flatMap_const]
  ring

theorem input_size (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    Horn.WordRAM.size ⟨p*2*n,input edges pairs⟩=2*p*n+5*p+4*p*edges.length+1 := by
  simp only [Horn.WordRAM.size,input_rules,input_occurrences]
  ring

end LeanTrominoes.ImplicationGraph.TwoSATBatch
