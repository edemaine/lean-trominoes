/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceFieldEntries
import LeanTrominoes.BoundedArithmeticCountSpace
import LeanTrominoes.PeriodicCNFFieldEvaluator

/-! # Compiled counts of distinct incidence variables

A literal address represents its atom precisely when no later literal has
that atom. Counting those addresses recovers the actual deduplicated vertex
list without bounding the numeric atom names.
-/
namespace LeanTrominoes.PeriodicCNF.IncidenceFields
open FlatScanner FieldPredicate PeriodicCNFFlatEncoding
open BoundedArithmetic BoundedArithmetic.Expr
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def representativeExpr : Expr := andE (.testBit (var 3) (var 0))
  (.all (var 1) (impE (andE (ltE (var 1) (var 0)) (.testBit (var 4) (var 0)))
    (notE (eqE (field 2 (var 0)) (field 2 (var 1))))))

theorem representativeExpr_truth (f : PeriodicCNF Nat) (p : Nat) :
    representativeExpr.Truth (p :: FieldSavitch.suffix f) ↔ representative f p := by
  simp only [representativeExpr,truth_and,truth_bit,truth_all,truth_imp,truth_lt,truth_not,truth_eq,
    FieldSavitch.suffix,input,context,List.cons_append,List.nil_append,eval_var,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [representative]
  constructor
  · rintro ⟨hp,h⟩
    exact ⟨hp,fun q hq hl hm => h q hq ⟨hl,hm⟩⟩
  · rintro ⟨hp,h⟩
    exact ⟨hp,fun q hq hh => h q hq hh.1 hh.2⟩

theorem count_representatives (f : PeriodicCNF Nat) :
    Count.count representativeExpr (FieldSavitch.suffix f) (formulaFields f).length =
      f.variableOccurrences.dedup.length := by
  rw [Count.count_eq_length_filter]
  let addresses := (representatives f).map Prod.fst
  have filtered : ((List.range (formulaFields f).length).filter
      (fun p => decide (representativeExpr.eval (p::FieldSavitch.suffix f) ≠ 0))).toFinset = addresses.toFinset := by
    ext p
    simp only [List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact (and_congr Iff.rfl (representativeExpr_truth f p)).trans (mem_representatives f p).symm
  have nodup := (List.nodup_range (n := (formulaFields f).length)).filter
    (fun p => decide (representativeExpr.eval (p::FieldSavitch.suffix f) ≠ 0))
  rw [← List.toFinset_card_of_nodup nodup,filtered,
    List.toFinset_card_of_nodup (representatives_addresses_nodup f)]
  have h := congrArg List.length (representatives_atoms f)
  simpa only [addresses,List.length_map] using h

def variableCountCode : Code := (Count.code representativeExpr).comp
  ((Code.prepend (Code.get 0) Code.id).comp FieldSavitch.suffixCode)

theorem variableCountCode_eval (f : PeriodicCNF Nat) :
    variableCountCode.eval (formulaFields f) = pure [f.variableOccurrences.dedup.length] := by
  have header : (FieldSavitch.suffix f)[0]?.getD 0 = (formulaFields f).length := rfl
  simp [variableCountCode,FieldSavitch.suffixCode_eval,Code.prepend,header,
    Count.code_eval,count_representatives,Part.bind_eq_bind]

def variableCountCoefficient : Nat :=
  Count.coefficient representativeExpr *
    ((4*(10000+10+1))*(FieldSavitch.suffixCoefficient+1)+FieldSavitch.suffixCoefficient+1)+
    ((4*(10000+10+1))*(FieldSavitch.suffixCoefficient+1)+FieldSavitch.suffixCoefficient)

theorem variableCountCode_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits variableCountCode (formulaFields f) [f.variableOccurrences.dedup.length]
      (variableCountCoefficient*((finEncoding.encode f).length+1)) := by
  have ident := (EvaluatorCodeFits.id (FieldSavitch.suffix f)).mono (idCost_bound _)
  have headed := prepend_linear (get_linear 0 (FieldSavitch.suffix f)) ident
  have init := FieldSavitch.suffixCode_fits f
  rw [← FieldSavitch.fields_space] at init
  have args := comp_linear headed init
  have counter := Count.code_fits representativeExpr (by decide) (FieldSavitch.suffix f) (formulaFields f).length
  rw [count_representatives] at counter
  have fit := comp_linear counter args
  rw [FieldSavitch.fields_space] at fit
  exact fit

end LeanTrominoes.PeriodicCNF.IncidenceFields
