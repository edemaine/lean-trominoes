/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnLookupSupport
import LeanTrominoes.UnaryFieldAggregateCompiler
import LeanTrominoes.ListRangeGetD

/-! # Total indexed lookup in compiled unary field lists -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Turing
variable {Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Row} {query : List Symbol → Row → Nat}
  {fields : List Symbol → List Nat}

def fieldLookup (queries : Compiler rows query)
    (values : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields fields) :
    Compiler rows (fun s r => (fields s).getD (query s r) 0) := by
  let count := TM2CompositionMachine.computableInPolyTime values UnaryFieldAggregate.countCompiler
  let keys := naturalRange count
  have table : Compiler (fun s => List.range (fields s).length) (fun s i => (fields s).getD i 0) :=
    TM2ComputableInPolyTime.of_eq values (fun s => (List.map_range_getD (fields s) 0).symm)
  apply keyedSupported queries keys table (fun s i => (fields s).getD i 0)
  · intro s i _
    rfl
  · intro s r _ absent
    apply List.getD_eq_default
    by_contra h
    exact absent ⟨query s r,List.mem_range.mpr (by omega),rfl⟩

end LeanTrominoes.UnaryColumn
end
