/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteLiteralLoop

/-! # The clause loop selects exactly the certified clause headers -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr
open RouteInput PeriodicCNF PeriodicCNF.FlatScanner PeriodicCNF.IncidenceFields PeriodicCNFFlatEncoding

theorem variableCount_value (input : Input Nat) :
    variableCount.value (context input) = input.1.variableOccurrences.dedup.length := by
  change Count.count (formulaQuery 0 representativeExpr) (context input) (formulaFields input.1).length = _
  have count := formulaQuery_count representativeExpr input [] (formulaFields input.1).length
  simp only [List.length_nil,List.nil_append] at count
  rw [count,count_representatives]

theorem clauseRank_value (input : Input Nat) (h v : Nat) :
    clauseRank.value ([h,v]++context input) = Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h := by
  change Count.count (formulaQuery 2 clauseMarkExpr) ([h,v]++context input) h = _
  simpa only [List.length_cons,List.length_nil,Nat.reduceAdd] using formulaQuery_count clauseMarkExpr input [h,v] h

theorem literals_truth (input : Input Nat) (valid : IncidenceCounts.Valid input)
    (h : Nat) (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses) :
    literals.value ([Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h,h,input.1.variableOccurrences.dedup.length]++context input) ≠ 0 ↔
      ∀ k, ∀ hk : k<c.length, literalCheck input h c k hk := by
  let ci := Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h
  let v := input.1.variableOccurrences.dedup.length
  rw [literals,NativeScalar.all_value_ne_zero]
  change (∀ k < (formulaField 3 (var 1)).eval ([ci,h,v]++context input), literalBody.value (k::([ci,h,v]++context input)) ≠ 0) ↔ _
  have header := formulaField_eval input [ci,h,v] (var 1)
  change (formulaField 3 (var 1)).eval ([ci,h,v]++context input) = (formulaFields input.1)[h]?.getD 0 at header
  rw [header,clauseEntry_header input.1 hc]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  exact literalBody_truth input valid h c hc k hk

theorem clauseBody_implication (input : Input Nat) (h v : Nat) :
    clauseBody.value ([h,v]++context input) ≠ 0 ↔
      ((clauseMarks 1 input.1.clauses).testBit h=true →
        literals.value ([Count.count clauseMarkExpr (FieldSavitch.suffix input.1) h,h,v]++context input) ≠ 0) := by
  rw [clauseBody,NativeScalar.implies_value_ne_zero]
  change ((Expr.testBit (var 3) (var 0)).Truth ([h,v]++context input) →
    literals.value (clauseRank.value ([h,v]++context input)::([h,v]++context input)) ≠ 0) ↔ _
  rw [truth_bit,clauseRank_value]
  rfl

theorem clauseBody_truth (input : Input Nat) (valid : IncidenceCounts.Valid input)
    (h : Nat) (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses) :
    clauseBody.value ([h,input.1.variableOccurrences.dedup.length]++context input) ≠ 0 ↔
      ∀ k, ∀ hk : k<c.length, literalCheck input h c k hk := by
  rw [clauseBody_implication]
  have selected := (clauseMarks_testBit 1 input.1.clauses h).mpr ⟨c,hc⟩
  simp only [selected,true_implies]
  exact literals_truth input valid h c hc

theorem program_truth_headers (input : Input Nat) (valid : IncidenceCounts.Valid input) :
    program.value (context input) ≠ 0 ↔
      ∀ h c, (h,c)∈clauseEntries 1 input.1.clauses → ∀ k, ∀ hk : k<c.length, literalCheck input h c k hk := by
  change clauses.value (variableCount.value (context input)::context input) ≠ 0 ↔ _
  rw [variableCount_value,clauses,NativeScalar.all_value_ne_zero]
  change (∀ h < (formulaFields input.1).length, clauseBody.value ([h,input.1.variableOccurrences.dedup.length]++context input) ≠ 0) ↔ _
  constructor
  · intro run h c hc
    exact (clauseBody_truth input valid h c hc).mp (run h (FieldPredicate.clause_bound input.1 hc))
  · intro checked h _
    apply (clauseBody_implication input h _).mpr
    intro selected
    obtain ⟨c,hc⟩ := (clauseMarks_testBit 1 input.1.clauses h).mp selected
    exact (literals_truth input valid h c hc).mpr (checked h c hc)

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
