/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteCNFCompiler
import LeanTrominoes.SAT.CNF.PeriodicCNFFlatEncodingSize

/-! # Encoded size of finite Boolean compiler requests -/
namespace LeanTrominoes.FiniteCNFCompiler
open PeriodicCNF

theorem programFields_sum_le (expression : TransitionExpr) (fresh : Nat)
    (bound : expression.AtomsBelow fresh) :
    (transitionProgramFields expression.program).sum ≤ expression.gateCount*(fresh+4) := by
  induction expression with
  | constant b => cases b <;> simp [TransitionExpr.program,transitionProgramFields,TransitionInstruction.fields,TransitionExpr.gateCount]
  | wire w =>
    have small : w.atom < fresh := bound
    cases w with
    | mk slice atom =>
      dsimp only at small
      cases slice <;> simp [TransitionExpr.program,transitionProgramFields,TransitionInstruction.fields,TransitionExpr.gateCount] <;> omega
  | not e ih =>
    have old := ih bound
    simp only [transitionProgramFields] at old
    simp only [TransitionExpr.program,transitionProgramFields,List.flatMap_append,
      List.flatMap_singleton,List.sum_append,TransitionInstruction.fields,List.sum_cons,List.sum_nil,
      TransitionExpr.gateCount,Nat.add_mul,Nat.one_mul]
    omega
  | and e f ih1 ih2 =>
    have left := ih1 bound.1
    have right := ih2 bound.2
    simp only [transitionProgramFields] at left right
    simp only [TransitionExpr.program,transitionProgramFields,List.flatMap_append,
      List.flatMap_singleton,List.sum_append,TransitionInstruction.fields,List.sum_cons,List.sum_nil,
      TransitionExpr.gateCount,Nat.add_mul,Nat.one_mul]
    omega
  | or e f ih1 ih2 =>
    have left := ih1 bound.1
    have right := ih2 bound.2
    simp only [transitionProgramFields] at left right
    simp only [TransitionExpr.program,transitionProgramFields,List.flatMap_append,
      List.flatMap_singleton,List.sum_append,TransitionInstruction.fields,List.sum_cons,List.sum_nil,
      TransitionExpr.gateCount,Nat.add_mul,Nat.one_mul]
    omega

theorem Request.encode_length_le (request : Request) :
    request.encode.length ≤ request.fresh+3+request.expression.gateCount*(request.fresh+10) := by
  have encoded := PeriodicCNFFlatEncoding.encodeNatFields_length_le_sum_add_length
    (transitionCompilerInputFields request.expression.atCurrent request.fresh)
  rw [PeriodicCNFFlatEncoding.encodeNatFields_eq_trList] at encoded
  have programSum := programFields_sum_le request.expression.atCurrent request.fresh
    (TransitionExpr.atCurrent_atomsBelow request.sourceBound)
  have programLength := expression_program_fields_length_le request.expression.atCurrent
  have clauses := FiniteCNF.clauseCount_le request.expression.atCurrent
  simp only [transitionCompilerInputFields,List.sum_cons,List.length_cons,
    TransitionExpr.atCurrent_gateCount] at encoded programSum programLength clauses
  change (Turing.PartrecToTM2.trList
    (transitionCompilerInputFields request.expression.atCurrent request.fresh)).length ≤ _
  simp only [transitionCompilerInputFields]
  nlinarith

end LeanTrominoes.FiniteCNFCompiler
