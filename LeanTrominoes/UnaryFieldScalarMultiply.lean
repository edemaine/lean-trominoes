/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldAggregateCompiler
import LeanTrominoes.UnaryFieldCartesianCompiler
import LeanTrominoes.UnaryFieldConstantOffsetCompiler
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Polynomial-time multiplication of unary columns by a computed scalar -/

noncomputable section
namespace LeanTrominoes.UnaryFieldScalarMultiply
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

/-- A complete multiplication table through the largest queried value. -/
def table (factor : Nat) (values : List Nat) : List Nat :=
  PrefixSums.starts (List.replicate (values.sum+1) factor)

theorem startsAux_replicate (start factor count : Nat) :
    PrefixSums.startsAux start (List.replicate count factor) =
      (List.range count).map (fun i => start+i*factor) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [List.replicate_succ,PrefixSums.startsAux_cons,ih,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.comp_def,Nat.zero_mul,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [Nat.succ_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem table_eq (factor : Nat) (values : List Nat) :
    table factor values = (List.range (values.sum+1)).map (·*factor) := by
  simp [table,PrefixSums.starts,startsAux_replicate]

theorem query_lt {values : List Nat} {q : Nat} (h : q ∈ values) : q < values.sum+1 := by
  induction values with
  | nil => simp at h
  | cons n values ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp only [List.sum_cons]; omega
    · have := ih h; simp only [List.sum_cons]; omega

theorem lookup_table (factor : Nat) (values : List Nat) :
    UnaryIndexedValueLookup.values values (table factor values) = values.map (·*factor) := by
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by
    intro q hq; simpa [table_eq] using query_lt hq)]
  apply List.map_congr_left
  intro q hq
  rw [table_eq,List.getD_eq_getElem _ _ (by simpa using query_lt hq),List.getElem_map,List.getElem_range]

variable {Source Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (encode : Source → List Symbol) (factor : Source → Nat) (values : Source → List Nat)
    (factorCompiler : TM2ComputableInPolyTime encode unaryFields (fun s => [factor s]))
    (valuesCompiler : TM2ComputableInPolyTime encode unaryFields values)

def tableCompiler : TM2ComputableInPolyTime encode unaryFields (fun s => table (factor s) (values s)) := by
  let sum := TM2CompositionMachine.computableInPolyTime valuesCompiler UnaryFieldAggregate.sumCompiler
  let bound := TM2CompositionMachine.computableInPolyTime sum (UnaryFieldConstantOffsets.computableInPolyTime 1)
  let range := TM2CompositionMachine.computableInPolyTime bound UnaryFieldAggregate.rangeSumCompiler
  let repeats := UnaryFieldCartesian.computableInPolyTime encode _ _ factorCompiler range .first
  let starts := TM2CompositionMachine.computableInPolyTime repeats UnaryPrefixSumsMachine.computableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq starts
  intro s
  congr 1
  simp [UnaryFieldConstantOffsets.values,UnaryFieldSquareProjection.choose,table,List.map_const']

def computableInPolyTime : TM2ComputableInPolyTime encode unaryFields
    (fun s => (values s).map (·*factor s)) := by
  let lookup := UnaryIndexedValueLookup.valuesComputableInPolyTime encode values _ valuesCompiler
    (tableCompiler encode factor values factorCompiler valuesCompiler)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq lookup
    (fun s => congrArg unaryFields (lookup_table (factor s) (values s)))

end LeanTrominoes.UnaryFieldScalarMultiply
