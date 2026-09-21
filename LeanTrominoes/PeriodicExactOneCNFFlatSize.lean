/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneCNFLocality
import LeanTrominoes.PartrecBinaryLengthSpace

/-! # Native flat encoding size of the exact-one to CNF translation -/
namespace LeanTrominoes.PeriodicExactOneCNF
open PeriodicCNFFlatEncoding _root_.Computability

private def cost (ns : List Nat) : Nat :=
  (ns.map fun n => (encodeNat n).length+1).sum

private theorem cost_append (xs ys : List Nat) : cost (xs++ys)=cost xs+cost ys := by
  simp [cost]

private theorem cost_flatMap {A : Type} (f : A → List Nat) (xs : List A) :
    cost (xs.flatMap f) = (xs.map fun x => cost (f x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons,cost_append,ih]

private theorem clause_cost (c : PeriodicClause Nat) :
    cost (clauseFields c) = (encodeNat c.length).length+1 +
      (c.map fun l => cost (literalFields l)).sum := by
  change (encodeNat c.length).length+1+cost (c.flatMap literalFields) = _
  rw [cost_flatMap]

private theorem negate_cost (l : PeriodicLiteral Nat) :
    cost (literalFields (PeriodicOneInThree.negate l)) ≤ 2*cost (literalFields l) := by
  rcases l with ⟨a,o,v⟩
  have zero : (encodeNat 0).length=0 := rfl
  have one : (encodeNat 1).length=1 := rfl
  cases v <;> simp [cost,literalFields,PeriodicOneInThree.negate,encodeBoolField,zero,one] <;> omega

private theorem clause_cost_bound (c : PeriodicClause Nat) (hw : c.length≤3) :
    ((clause c).map fun d => cost (clauseFields d)).sum ≤ 5*cost (clauseFields c) := by
  rcases c with _ | ⟨a,c⟩
  · simp only [clause,mutex,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; omega
  have ha := negate_cost a
  rcases c with _ | ⟨b,c⟩
  · simp only [clause,mutex,List.map_cons,List.map_nil,List.append_nil,List.sum_cons,List.sum_nil]; omega
  have hb := negate_cost b
  rcases c with _ | ⟨d,c⟩
  · simp only [clause,mutex,List.map_cons,List.map_nil,List.append_nil,
      List.sum_cons,List.sum_nil,clause_cost,List.length_cons,List.length_nil]
    have e1 : (encodeNat 2).length=2 := rfl
    simp only [e1]
    omega
  have hd := negate_cost d
  cases c with
  | nil =>
    simp only [clause,mutex,List.map_cons,List.map_nil,List.cons_append,List.append_nil,
      List.nil_append,List.sum_cons,List.sum_nil,clause_cost,List.length_cons,List.length_nil]
    have e2 : (encodeNat 2).length=2 := rfl
    have e3 : (encodeNat 3).length=2 := rfl
    simp only [e2,e3]
    omega
  | cons e c => simp only [List.length_cons] at hw; omega

private theorem clause_count (c : PeriodicClause Nat) (hw : c.length≤3) :
    (clause c).length ≤ 4 := by
  rcases c with _ | ⟨a,c⟩
  · simp [clause,mutex]
  rcases c with _ | ⟨b,c⟩
  · simp [clause,mutex]
  rcases c with _ | ⟨d,c⟩
  · simp [clause,mutex]
  cases c with
  | nil => simp [clause,mutex]
  | cons e c => simp only [List.length_cons] at hw; omega

private theorem body_bound (cs : List (PeriodicClause Nat)) (hw : ∀ c∈cs,c.length≤3) :
    cost ((cs.flatMap clause).flatMap clauseFields) ≤ 5*cost (cs.flatMap clauseFields) ∧
    (cs.flatMap clause).length ≤ 4*cs.length ∧ cs.length ≤ cost (cs.flatMap clauseFields) := by
  induction cs with
  | nil => simp [cost]
  | cons c cs ih =>
    have rest := ih (fun d hd => hw d (by simp [hd]))
    have count := clause_count c (hw c (by simp))
    have bound := clause_cost_bound c (hw c (by simp))
    have positive : 1 ≤ cost (clauseFields c) := by rw [clause_cost]; omega
    simp only [List.flatMap_cons,List.flatMap_append,cost_append,List.length_cons,List.length_append]
    rw [cost_flatMap (xs := clause c)]
    omega

/-- A linear bound in the actual binary-and-delimiter input length, including
arbitrary atom names and signed offsets. -/
theorem flatEncoding_length_le (f : PeriodicCNF Nat) (hw : f.WidthAtMost 3) :
    (finEncoding.encode (formula f)).length ≤ 9*(finEncoding.encode f).length+1 := by
  have bounds := body_bound f.clauses hw
  have header := Turing.PartrecToTM2.encodeNat_length_le_self (formula f).clauses.length
  rw [finEncoding_encode_length,finEncoding_encode_length]
  change cost (formulaFields (formula f)) ≤ 9*cost (formulaFields f)+1
  have head_cost (g : PeriodicCNF Nat) : cost (formulaFields g) =
      (encodeNat g.clauses.length).length+1+cost (g.clauses.flatMap clauseFields) := rfl
  rw [head_cost,head_cost]
  change (encodeNat (f.clauses.flatMap clause).length).length ≤ (f.clauses.flatMap clause).length at header
  change (encodeNat (f.clauses.flatMap clause).length).length+1+
    cost ((f.clauses.flatMap clause).flatMap clauseFields) ≤ _
  omega
end LeanTrominoes.PeriodicExactOneCNF
