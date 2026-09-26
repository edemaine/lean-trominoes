/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BinaryFieldWords
import LeanTrominoes.DelimitedBinaryWordKeyedValueLookupCompiler
import LeanTrominoes.DelimitedBinaryWordKeyedValueLookupMappedSemantics
import LeanTrominoes.UnaryColumnScalarCompiler
import LeanTrominoes.UnaryFieldClosure

/-! # Polynomial-time bounded decoding of native binary fields

Candidate values below a unary bound are compared as binary words. A decoded
value is returned plus one; zero marks an out-of-range field. No large binary
integer is expanded into unary. One trailing sentinel decodes to one.
-/
noncomputable section
namespace LeanTrominoes.BinaryFieldBoundedDecoder
open Turing _root_.Computability UnaryColumn
abbrev Symbol := PeriodicCNFFlatEncoding.Symbol

def candidates (bound : Nat) : DelimitedBinaryWords.Input :=
  BinaryFieldWords.input (PeriodicCNFFlatEncoding.encodeNatFields (List.range bound))

def candidateValues (bound : Nat) : List Nat := (List.range bound).map (·+1) ++ [1]

def cap (bound n : Nat) : Nat := if n < bound then n+1 else 0

def values (bound : Nat) (s : List Symbol) : List Nat :=
  DelimitedBinaryWordKeyedValueLookup.values (BinaryFieldWords.input s) (candidates bound) (candidateValues bound)

theorem words_fields (fields : List Nat) :
    (BinaryFieldWords.input (PeriodicCNFFlatEncoding.encodeNatFields fields)).words =
      (fields ++ [0]).map encodeNat := by
  rw [BinaryFieldWords.input,BinaryFieldWords.read_fields,List.map_append]
  rfl

theorem candidateValues_eq (bound : Nat) : candidateValues bound = (List.range bound ++ [0]).map (·+1) := by
  simp [candidateValues]

theorem values_fields (bound : Nat) (positive : 0 < bound) (fields : List Nat) :
    values bound (PeriodicCNFFlatEncoding.encodeNatFields fields) = (fields ++ [0]).map (cap bound) := by
  have queries : BinaryFieldWords.input (PeriodicCNFFlatEncoding.encodeNatFields fields) =
      ⟨(fields ++ [0]).map encodeNat⟩ := by
    apply congrArg DelimitedBinaryWords.Input.mk
    exact words_fields fields
  have table : candidates bound = ⟨(List.range bound ++ [0]).map encodeNat⟩ := by
    apply congrArg DelimitedBinaryWords.Input.mk
    exact words_fields (List.range bound)
  rw [values,queries,table,candidateValues_eq]
  apply DelimitedBinaryWordKeyedValueLookup.values_map_candidates
  · intro q _ n hn eq
    have same : q = n := by
      have h := congrArg decodeNat eq
      simpa using h
    subst q
    have small : n < bound := by
      simp only [List.mem_append,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hn
      omega
    simp [cap,small]
  · intro q _ missing
    have outside : ¬ q < bound := by
      intro small
      apply missing
      exact List.mem_map.mpr ⟨q,by simp [small],rfl⟩
    simp [cap,outside]

theorem values_fields_bounded (bound : Nat) (positive : 0 < bound) (fields : List Nat)
    (small : ∀ n ∈ fields, n < bound) :
    values bound (PeriodicCNFFlatEncoding.encodeNatFields fields) = fields.map (·+1) ++ [1] := by
  rw [values_fields bound positive fields,List.map_append]
  have eq : fields.map (cap bound) = fields.map (·+1) := List.map_congr_left (fun n hn => by simp [cap,small n hn])
  simp [eq,cap,positive]

variable {bound : List Symbol → Nat}

def compiler (cb : ScalarCompiler bound) : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => values (bound s) s) := by
  let range := naturalRange cb
  let binary := TM2CompositionMachine.computableInPolyTime range UnaryFieldEncoderMachine.computableInPolyTime
  have raw : TM2ComputableInPolyTime id id (fun s => PeriodicCNFFlatEncoding.encodeNatFields (List.range (bound s))) := by
    apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq binary
    intro s
    change PartrecToTM2.trList ((List.range (bound s)).map id) = _
    rw [List.map_id]
    exact (PeriodicCNFFlatEncoding.encodeNatFields_eq_trList (List.range (bound s))).symm
  have keys : TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode (fun s => candidates (bound s)) := by
    have composed := TM2CompositionMachine.computableInPolyTime raw BinaryFieldWords.compiler
    exact composed.of_eq (fun s => rfl)
  have vals : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s => candidateValues (bound s)) :=
    UnaryFieldClosure.appendCompiler id _ _ (add range (constant range 1))
      (TM2ConstantValueCompiler.computableInPolyTime id UnaryFieldEncoderMachine.unaryFields [1])
  exact DelimitedBinaryWordKeyedValueLookup.valuesComputableInPolyTime BinaryFieldWords.input
    (fun s => candidates (bound s)) (fun s => candidateValues (bound s))
    (fun s => by simp [candidateValues,candidates,BinaryFieldWords.input,BinaryFieldWords.read_fields])
    BinaryFieldWords.compiler keys vals

end LeanTrominoes.BinaryFieldBoundedDecoder
end
