/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreeAtomDescriptors
import LeanTrominoes.UnaryPrefixSumsTime
import LeanTrominoes.TM2ConstantValueCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler

/-! # Polynomial-time columns for exact-one atom names -/
noncomputable section
namespace LeanTrominoes.PeriodicOneInThree.AtomDescriptors
open Turing

def queries (ds : List Descriptor) := PrefixSums.starts (ds.map originalStep)
def clauseIndices (ds : List Descriptor) := PrefixSums.starts (ds.map clauseStep)
def controls (ds : List Descriptor) := ds.map (fun d => d.1.isSome)
def fresh (ds : List Descriptor) := AlignedUnaryListClosure.added
  (UnaryFieldConstantScale.values 28 (clauseIndices ds)) (ds.map auxiliaryOffset)
def inherited (ds : List Descriptor) (original : List Nat) :=
  UnaryFieldConstantScale.values 2 (UnaryIndexedValueLookup.values (queries ds) (original ++ [0]))
def output (ds : List Descriptor) (original : List Nat) :=
  AlignedUnaryBooleanChoice.selectedValues (controls ds) (inherited ds original) (fresh ds)

@[simp] theorem queries_length (ds : List Descriptor) : (queries ds).length=ds.length := by
  simp [queries]
@[simp] theorem fresh_length (ds : List Descriptor) : (fresh ds).length=ds.length := by
  simp [fresh,UnaryFieldConstantScale.values,clauseIndices]
@[simp] theorem inherited_length (ds : List Descriptor) (original : List Nat) :
    (inherited ds original).length=ds.length := by
  simp [inherited,UnaryFieldConstantScale.values]

variable {Input InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
variable (encodeInput : Input → List InputSymbol)
variable (descriptors : Input → List Descriptor) (original : Input → List Nat)
variable (descriptorCompiler : TM2ComputableInPolyTime encodeInput id descriptors)
variable (originalCompiler : TM2ComputableInPolyTime encodeInput UnaryFieldEncoderMachine.unaryFields original)

private noncomputable def prefixCompiler (step : Descriptor → Nat) :
    TM2ComputableInPolyTime encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => PrefixSums.starts ((descriptors input).map step)) :=
  TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime descriptorCompiler
      (FiniteUnaryFieldMap.computableInPolyTime step))
    UnaryPrefixSumsMachine.computableInPolyTime

private noncomputable def candidatesCompiler :
    TM2ComputableInPolyTime encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => original input ++ [0]) := by
  let first : TM2ComputableInPolyTime encodeInput id
      (fun input => UnaryFieldEncoderMachine.unaryFields (original input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq originalCompiler (fun _ => rfl)
  let second := TM2ConstantValueCompiler.computableInPolyTime encodeInput id
    (UnaryFieldEncoderMachine.unaryFields [0])
  let appended := TM2ListAppend.computableInPolyTime first second
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    (fun input => (UnaryFieldEncoderMachine.unaryFields_append (original input) [0]).symm)

noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => output (descriptors input) (original input)) := by
  let queryCompiler := prefixCompiler encodeInput descriptors descriptorCompiler originalStep
  let indexCompiler := prefixCompiler encodeInput descriptors descriptorCompiler clauseStep
  let scaledCompiler := TM2CompositionMachine.computableInPolyTime indexCompiler
    (UnaryFieldConstantScale.computableInPolyTime 28)
  let offsetCompiler := TM2CompositionMachine.computableInPolyTime descriptorCompiler
    (FiniteUnaryFieldMap.computableInPolyTime auxiliaryOffset)
  let freshCompiler := AlignedUnaryListClosure.addedComputableInPolyTime encodeInput
    (fun input => UnaryFieldConstantScale.values 28 (clauseIndices (descriptors input)))
    (fun input => (descriptors input).map auxiliaryOffset)
    (fun input => by simp [UnaryFieldConstantScale.values,clauseIndices])
    scaledCompiler offsetCompiler
  let lookupCompiler := UnaryIndexedValueLookup.valuesComputableInPolyTime encodeInput
    (fun input => queries (descriptors input)) (fun input => original input ++ [0])
    queryCompiler (candidatesCompiler encodeInput original originalCompiler)
  let inheritedCompiler := TM2CompositionMachine.computableInPolyTime lookupCompiler
    (UnaryFieldConstantScale.computableInPolyTime 2)
  let controlCompiler := TM2CompositionMachine.computableInPolyTime descriptorCompiler
    (FiniteBlockTransducer.computableInPolyTime (fun d : Descriptor => [d.1.isSome]))
  exact AlignedUnaryBooleanChoice.selectedValuesComputableInPolyTime encodeInput
    (fun input => controls (descriptors input))
    (fun input => inherited (descriptors input) (original input))
    (fun input => fresh (descriptors input))
    (fun input => by simp [controls]) (fun input => by simp)
    (TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq controlCompiler (by
      intro input
      change (descriptors input).flatMap (fun d => [d.1.isSome]) = controls (descriptors input)
      induction descriptors input with
      | nil => rfl
      | cons d ds ih => simpa [controls] using congrArg (List.cons d.1.isSome) ih)) inheritedCompiler freshCompiler

end LeanTrominoes.PeriodicOneInThree.AtomDescriptors
