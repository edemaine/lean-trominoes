/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockIndexLookupSemantics
import LeanTrominoes.SignedUnaryCoordinateRefinementLookup
import LeanTrominoes.UnaryIndexedValueLookupCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Signed coordinates expanded through finite metadata-selected tables -/

noncomputable section
namespace LeanTrominoes.SignedUnaryCoordinateIndexedTableExpansion
open Computability Turing SignedUnaryCoordinateRefinement

/-- Broadcast each origin over the local table selected by its finite metadata. -/
def bases {Metadata : Type} (table : Metadata → List Int)
    (metadata : List Metadata) (source : List Nat) : List Nat :=
  UnaryIndexedValueLookup.values
    (FiniteBlockIndices.indices (fun item => (table item).length) metadata) source

def offsets {Metadata : Type} (table : Metadata → List Int)
    (positive : Bool) (metadata : List Metadata) : List Nat :=
  metadata.flatMap fun item => (table item).map (field positive)

def values {Metadata : Type} (table : Metadata → List Int)
    (keepPositive : Bool) (metadata : List Metadata) (source : Bool → List Nat) : List Nat :=
  SignedUnaryCoordinateRefinement.values 1 keepPositive
    (fun positive => bases table metadata (source positive))
    (fun positive => offsets table positive metadata)

@[simp] theorem bases_length {Metadata : Type} (table : Metadata → List Int)
    (metadata : List Metadata) (source : List Nat) :
    (bases table metadata source).length = (metadata.map fun item => (table item).length).sum := by
  rw [bases, UnaryIndexedValueLookup.values_length, FiniteBlockIndices.indices_length]

@[simp] theorem offsets_length {Metadata : Type} (table : Metadata → List Int)
    (positive : Bool) (metadata : List Metadata) :
    (offsets table positive metadata).length = (metadata.map fun item => (table item).length).sum := by
  simp [offsets, List.length_flatMap]

noncomputable def basesNativeListComputableInPolyTime
    {Symbol Metadata : Type} [Fintype Symbol] [Fintype Metadata]
    (table : Metadata → List Int) (metadata : List Symbol → List Metadata)
    (source : List Symbol → List Nat)
    (metadataCompiler : TM2ComputableInPolyTime id id metadata)
    (sourceCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields source) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun input => bases table (metadata input) (source input)) := by
  classical
  exact if nonemptyAlphabet : Nonempty Symbol then by
    letI : Inhabited Symbol := ⟨Classical.choice nonemptyAlphabet⟩
    unfold bases
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime id _ _
      (TM2CompositionMachine.computableInPolyTime metadataCompiler
        (FiniteBlockIndices.indicesComputableInPolyTime (fun item => (table item).length)))
      sourceCompiler
  else by
    letI : IsEmpty Symbol := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

noncomputable def offsetsComputableInPolyTime
    {Metadata : Type} [Fintype Metadata] (table : Metadata → List Int) (positive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (offsets table positive) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (FiniteBlockTransducer.computableInPolyTime
      (fun item => UnaryFieldEncoderMachine.unaryFields ((table item).map (field positive))))
    (fun metadata => by
      induction metadata with
      | nil => rfl
      | cons item metadata ih =>
          simpa only [id_eq, offsets, List.flatMap_cons, UnaryFieldEncoderMachine.unaryFields_append] using
            congrArg (UnaryFieldEncoderMachine.unaryFields ((table item).map (field positive)) ++ ·) ih)

noncomputable def nativeListComputableInPolyTime
    {Symbol Metadata : Type} [Fintype Symbol] [Fintype Metadata]
    (table : Metadata → List Int) (keepPositive : Bool)
    (metadata : List Symbol → List Metadata) (source : Bool → List Symbol → List Nat)
    (metadataCompiler : TM2ComputableInPolyTime id id metadata)
    (sourceCompiler : ∀ positive, TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (source positive)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun input => values table keepPositive (metadata input) (fun positive => source positive input)) := by
  unfold values
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 1 keepPositive
    (fun positive input => bases table (metadata input) (source positive input))
    (fun positive input => offsets table positive (metadata input))
    (fun positive input => by rw [bases_length, bases_length])
    (fun positive input => by rw [offsets_length, bases_length])
    (fun positive => basesNativeListComputableInPolyTime table metadata (source positive)
      metadataCompiler (sourceCompiler positive))
    (fun positive => TM2CompositionMachine.computableInPolyTime metadataCompiler
      (offsetsComputableInPolyTime table positive))

@[simp] theorem values_length {Metadata : Type} (table : Metadata → List Int)
    (keepPositive : Bool) (metadata : List Metadata) (source : Bool → List Nat) :
    (values table keepPositive metadata source).length =
      (metadata.map fun item => (table item).length).sum := by
  unfold values
  rw [SignedUnaryCoordinateRefinement.values_length_of_aligned _ _ _ _
    (fun positive => by rw [bases_length, bases_length])
    (fun positive => by rw [offsets_length, bases_length]), bases_length]

private theorem broadcast_map {Index Metadata Value : Type}
    (indices : List Index) (metadata : Index → Metadata) (coordinate : Index → Value)
    (width : Metadata → Nat) :
    FiniteBlockIndices.broadcastValues width (indices.map metadata) (indices.map coordinate) =
      indices.flatMap fun index => List.replicate (width (metadata index)) (coordinate index) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simpa only [FiniteBlockIndices.broadcastValues, List.map_cons, List.zipWith_cons_cons,
        List.flatten_cons, List.flatMap_cons] using congrArg
          (List.replicate (width (metadata index)) (coordinate index) ++ ·) ih

/-- On aligned coordinates and nonempty local tables, expansion keeps exact
source-major and local-table-minor order. -/
theorem values_map {Index Metadata : Type} (indices : List Index)
    (metadata : Index → Metadata) (coordinate : Index → Int)
    (table : Metadata → List Int) (keepPositive : Bool)
    (positive : ∀ index ∈ indices, 0 < (table (metadata index)).length) :
    values table keepPositive (indices.map metadata)
        (fun sign => indices.map fun index => field sign (coordinate index)) =
      indices.flatMap fun index => (table (metadata index)).map
        fun offset => field keepPositive (coordinate index + offset) := by
  let pairs := indices.flatMap fun index => (table (metadata index)).map fun offset => (index, offset)
  have base (sign : Bool) :
      bases table (indices.map metadata) (indices.map fun index => field sign (coordinate index)) =
        pairs.map (fun pair => field sign (coordinate pair.1)) := by
    unfold bases
    rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (fun query member => by
      simpa only [List.length_map] using FiniteBlockIndices.mem_indices_lt_length _ _ query member),
      FiniteBlockIndices.indices_eq_expected,
      FiniteBlockIndices.expected_lookup_eq_broadcastValues _ _ _ _ (by simp) (by
        intro item member
        obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp member
        exact positive index indexMember), broadcast_map]
    simp only [pairs, List.map_flatMap, List.map_map, Function.comp_def, List.map_const']
  have offset (sign : Bool) :
      offsets table sign (indices.map metadata) = pairs.map (fun pair => field sign pair.2) := by
    simp only [offsets, pairs, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  unfold values
  simp only [base, offset]
  rw [SignedUnaryCoordinateRefinement.values_map]
  simp only [pairs, List.map_flatMap, List.map_map, Function.comp_def, Nat.cast_one, one_mul]

end LeanTrominoes.SignedUnaryCoordinateIndexedTableExpansion
end
