/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATEncoding
import Mathlib.Data.List.OfFn

/-! # Explicit dense tables for a batch of opposite reachability queries

All positions are ordinary natural indices. Division and remainder determine
the query, direction, and original edge; no reachability data enters a table.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATBatch
variable {n p : ℕ}

private theorem flatMap_as_flatten {α β : Type} (items : List α) (f : α → List β) :
    items.flatMap f=(items.map f).flatten := by
  induction items with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.map_cons,List.flatten_cons,ih]

@[simp] private theorem flatMap_empty {α β : Type} (xs : List α) :
    xs.flatMap (fun _ => ([] : List β))=[] := by
  induction xs <;> simp_all

@[simp] private theorem flatMap_singletons {α β : Type} (xs : List α) (f : α → β) :
    xs.flatMap (fun x => [f x])=xs.map f := by
  induction xs <;> simp_all

/-- Enumerating fixed-size blocks gives quotient/remainder lookup indices. -/
theorem flatten_ofFn_blocks {α : Type} {m k : ℕ} (f : Fin m → Fin k → α) :
    (List.ofFn fun i => List.ofFn (f i)).flatten=
      List.ofFn (fun i : Fin (m*k) => f
        ⟨i.val/k,by exact Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using i.isLt)⟩
        ⟨i.val%k,Nat.mod_lt _ (by have := i.isLt; nlinarith : 0< k)⟩) := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have positive : 0< k := by have := j.isLt; omega
  congr 1 <;> apply Fin.ext <;>
    simp [Nat.mul_comm,Nat.mul_add_div positive,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]


/-- Two adjacent entries per query, false direction first. -/
theorem flatMap_pairs {α : Type} (f : Fin p → Bool → α) :
    (List.finRange p).flatMap (fun q => [f q false,f q true])=
      List.ofFn (fun i : Fin (p*2) => f ⟨i.val/2,by omega⟩ (i.val%2==1)) := by
  have pair (q : Fin p) : [f q false,f q true]=List.ofFn (fun j : Fin 2 => f q (j.val==1)) := by
    simp [List.ofFn_succ]
  simp_rw [pair]
  rw [flatMap_as_flatten,← List.ofFn_eq_map,flatten_ofFn_blocks]

/-- All edge copies, ordered by query, then direction, then original edge. -/
theorem flatMap_pair_edges {α : Type} (edges : List α) (f : Fin p → Bool → α → ℕ) :
    (List.finRange p).flatMap (fun q => [false,true].flatMap fun direction => edges.map (f q direction))=
      List.ofFn (fun i : Fin ((p*2)*edges.length) =>
        f ⟨(i.val/edges.length)/2,by
          have h := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using i.isLt)
          omega⟩ ((i.val/edges.length)%2==1)
          (edges.get ⟨i.val%edges.length,Nat.mod_lt _ (by have := i.isLt; nlinarith)⟩)) := by
  have regroup : (List.finRange p).flatMap (fun q => [false,true].flatMap fun direction => edges.map (f q direction))=
      ((List.finRange p).flatMap (fun q => [fun e => f q false e,fun e => f q true e])).flatMap
        (fun g => edges.map g) := by
    simp [List.flatMap_assoc]
  rw [regroup,flatMap_pairs (fun q direction => f q direction)]
  rw [flatMap_as_flatten,List.map_ofFn]
  simp_rw [← List.ofFn_getElem_eq_map]
  simp only [Function.comp_def]
  rw [flatten_ofFn_blocks]
  rfl

theorem direction_index (k : ℕ) : 2*(k/2)+(if k%2=1 then 1 else 0)=k := by
  split_ifs <;> omega

def denseRules (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    List (Horn.Rule (Fin (p*2*n))) := (rules edges pairs).map (reindex (atomIndex n p))

def factHeads (pairs : Fin p → Fin n × Fin n) : List ℕ :=
  List.ofFn fun i : Fin (p*2) =>
    i.val*n+(if i.val%2==1 then (pairs ⟨i.val/2,by omega⟩).2.val
      else (pairs ⟨i.val/2,by omega⟩).1.val)+1

def edgeHeads (edges : List (Fin n × Fin n)) : List ℕ :=
  List.ofFn fun i : Fin ((p*2)*edges.length) =>
    (i.val/edges.length)*n+(edges.get ⟨i.val%edges.length,
      Nat.mod_lt _ (by have := i.isLt; nlinarith)⟩).2.val+1

/-- Heads are source facts, negative rules, and unary edge-copy rules. -/
theorem ruleHeads_batch (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    ruleHeads (denseRules edges pairs)=
      factHeads pairs++List.replicate p 0++edgeHeads (p:=p) edges := by
  have facts := flatMap_pairs (fun q direction =>
    (2*q.val+(if direction then 1 else 0))*n+(source pairs q direction).val+1)
  have copies := flatMap_pair_edges (p:=p) edges (fun q direction edge =>
    (2*q.val+(if direction then 1 else 0))*n+edge.2.val+1)
  have factEq : (List.finRange p).flatMap (fun q =>
      [(2*q.val)*n+(pairs q).1.val+1,(2*q.val+1)*n+(pairs q).2.val+1])=factHeads pairs := by
    refine facts.trans ?_
    apply congrArg List.ofFn
    funext i
    simp only [factHeads,source,Fin.val_mk,beq_iff_eq,direction_index]
    split_ifs <;> rfl
  have copyEq : (List.finRange p).flatMap (fun q => [false,true].flatMap fun direction =>
      edges.map (fun edge => (2*q.val+(if direction then 1 else 0))*n+edge.2.val+1))=
        edgeHeads (p:=p) edges := by
    simpa [edgeHeads,direction_index] using copies
  have combined := congrArg₂ (fun xs ys : List ℕ => xs++List.replicate p 0++ys) factEq copyEq
  simp only [List.append_assoc] at combined
  simpa [ruleHeads,denseRules,rules,reindex,fact,negative,implication,Horn.WordRAM.atomCode,
    List.map_append,List.map_flatMap,List.map_map,Function.comp_def,atomIndex_value,source,List.append_assoc]
    using combined

def negativeAtoms (pairs : Fin p → Fin n × Fin n) : List ℕ :=
  List.ofFn fun i : Fin (p*2) =>
    i.val*n+(if i.val%2==1 then (pairs ⟨i.val/2,by omega⟩).1.val
      else (pairs ⟨i.val/2,by omega⟩).2.val)+1

def edgeAtoms (edges : List (Fin n × Fin n)) : List ℕ :=
  List.ofFn fun i : Fin ((p*2)*edges.length) =>
    (i.val/edges.length)*n+(edges.get ⟨i.val%edges.length,
      Nat.mod_lt _ (by have := i.isLt; nlinarith)⟩).1.val+1

/-- Premise atoms are opposite targets followed by source vertices of edges. -/
theorem occurrenceAtoms_batch (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    occurrenceAtoms (denseRules edges pairs)=negativeAtoms pairs++edgeAtoms (p:=p) edges := by
  have negatives := flatMap_pairs (fun q direction =>
    (2*q.val+(if direction then 1 else 0))*n+(target pairs q direction).val+1)
  have copies := flatMap_pair_edges (p:=p) edges (fun q direction edge =>
    (2*q.val+(if direction then 1 else 0))*n+edge.1.val+1)
  have negativeEq : (List.finRange p).flatMap (fun q =>
      [(2*q.val)*n+(pairs q).2.val+1,(2*q.val+1)*n+(pairs q).1.val+1])=negativeAtoms pairs := by
    refine negatives.trans ?_
    apply congrArg List.ofFn
    funext i
    simp only [negativeAtoms,target,Fin.val_mk,beq_iff_eq,direction_index]
    split_ifs <;> rfl
  have copyEq : (List.finRange p).flatMap (fun q => [false,true].flatMap fun direction =>
      edges.map (fun edge => (2*q.val+(if direction then 1 else 0))*n+edge.1.val+1))=
        edgeAtoms (p:=p) edges := by
    simpa [edgeAtoms,direction_index] using copies
  simpa [occurrenceAtoms,denseRules,rules,reindex,fact,negative,implication,
    List.flatMap_append,List.flatMap_map,List.flatMap_assoc,List.map_map,Function.comp_def,
    atomIndex_value,target] using congrArg₂ (fun xs ys : List ℕ => xs++ys) negativeEq copyEq

def occurrenceRulesFrom {V : Type} (offset : ℕ) (rs : List (Horn.Rule V)) : List ℕ :=
  (rs.zipIdx offset).flatMap (fun ar => List.replicate ar.1.premises.length ar.2)

theorem occurrenceRulesFrom_append {V : Type} (offset : ℕ) (rs ss : List (Horn.Rule V)) :
    occurrenceRulesFrom offset (rs++ss)=
      occurrenceRulesFrom offset rs++occurrenceRulesFrom (offset+rs.length) ss := by
  simp only [occurrenceRulesFrom,List.zipIdx_append,List.flatMap_append]

/-- Constant premise lengths make occurrence-to-rule indices contiguous blocks. -/
theorem occurrenceRulesFrom_uniform {V : Type} (offset count : ℕ) (rs : List (Horn.Rule V))
    (uniform : ∀ r∈rs, r.premises.length=count) :
    occurrenceRulesFrom offset rs=
      (List.ofFn fun i : Fin rs.length => List.replicate count (offset+i.val)).flatten := by
  induction rs generalizing offset with
  | nil => simp [occurrenceRulesFrom]
  | cons r rs ih =>
    have hr := uniform r (by simp)
    have rest := ih (offset+1) (fun r hr => uniform r (by simp [hr]))
    change List.replicate r.premises.length offset++occurrenceRulesFrom (offset+1) rs = _
    rw [hr,List.ofFn_succ,List.flatten_cons]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest


theorem occurrenceRulesFrom_reindex {V W : Type} (e : V ≃ W) (offset : ℕ) (rs : List (Horn.Rule V)) :
    occurrenceRulesFrom offset (rs.map (reindex e))=occurrenceRulesFrom offset rs := by
  simp [occurrenceRulesFrom,List.zipIdx_map,List.flatMap_map,reindex]

def negativeRuleIds (p : ℕ) : List ℕ := List.ofFn fun i : Fin (p*2) => 2*p+i.val/2

def edgeRuleIds (p E : ℕ) : List ℕ := List.ofFn fun i : Fin ((p*2)*E) => 3*p+i.val

/-- Every occurrence points to its negative-query or unary-edge rule. -/
theorem occurrenceRules_batch (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    occurrenceRules (denseRules edges pairs)=negativeRuleIds p++edgeRuleIds p edges.length := by
  let fs := (List.finRange p).flatMap (fun q => [fact pairs q false,fact pairs q true])
  let ns := (List.finRange p).map (negative pairs)
  let es := (List.finRange p).flatMap (fun q => [false,true].flatMap fun direction => edges.map (implication q direction))
  have flen : fs.length=2*p := by simp [fs,List.length_flatMap]; omega
  have nlen : ns.length=p := by simp [ns]
  have elen : es.length=(p*2)*edges.length := by
    simp [es,List.length_flatMap]
    ring
  have fzero : occurrenceRulesFrom 0 fs=[] := by
    rw [occurrenceRulesFrom_uniform 0 0 fs]
    · simp
    · intro r hr
      simp only [fs,List.mem_flatMap,List.mem_finRange,true_and] at hr
      obtain ⟨q,hq⟩ := hr
      have choices : r=fact pairs q false ∨ r=fact pairs q true := by simpa [eq_comm] using hq
      rcases choices with rfl | rfl <;> rfl
  have ntwo : occurrenceRulesFrom (2*p) ns=negativeRuleIds p := by
    rw [occurrenceRulesFrom_uniform (2*p) 2 ns]
    · have block := flatten_ofFn_blocks (fun q : Fin p => fun _ : Fin 2 => 2*p+q.val)
      simpa [negativeRuleIds,nlen] using block
    · intro r hr
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp hr
      rfl
  have eone : occurrenceRulesFrom (3*p) es=edgeRuleIds p edges.length := by
    rw [occurrenceRulesFrom_uniform (3*p) 1 es]
    · have blocks : (List.ofFn fun i : Fin es.length => [3*p+i.val]).flatten=
          List.ofFn (fun i : Fin es.length => 3*p+i.val) := by
        rw [List.ofFn_eq_map,←flatMap_as_flatten,flatMap_singletons]
        exact List.ofFn_eq_map.symm
      simpa [edgeRuleIds,elen] using blocks
    · intro r hr
      simp only [es,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map] at hr
      obtain ⟨q,direction,_,edge,_,rfl⟩ := hr
      rfl
  change occurrenceRulesFrom 0 ((rules edges pairs).map (reindex (atomIndex n p)))=_
  rw [occurrenceRulesFrom_reindex]
  change occurrenceRulesFrom 0 (fs++ns++es)=_
  rw [occurrenceRulesFrom_append,occurrenceRulesFrom_append]
  simp only [List.length_append,flen,nlen,Nat.zero_add,fzero,ntwo,List.nil_append]
  rw [show 2*p+p=3*p by omega,eone]

/-- Exact dense Horn encoding, split into its contiguous table regions. -/
theorem words_batch (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n) :
    Horn.WordRAM.words ⟨p*2*n,input edges pairs⟩=
      [p*2*n,3*p+2*p*edges.length,2*p+2*p*edges.length]++
      factHeads pairs++List.replicate p 0++edgeHeads (p:=p) edges++
      negativeAtoms pairs++edgeAtoms (p:=p) edges++negativeRuleIds p++edgeRuleIds p edges.length := by
  have equal := words_of_rules (denseRules edges pairs)
  rw [ruleHeads_batch,occurrenceAtoms_batch,occurrenceRules_batch] at equal
  simpa [input,denseRules,List.length_map,rules_length,negativeAtoms,edgeAtoms,
    Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc,List.append_assoc] using equal

end LeanTrominoes.ImplicationGraph.TwoSATBatch
