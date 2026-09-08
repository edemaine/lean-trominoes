/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedDifferenceCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Fixed affine refinements of signed unary coordinate columns -/

noncomputable section
namespace LeanTrominoes.SignedUnaryCoordinateRefinement
open Computability Turing

def component (factor : Nat) (source offset : List Nat) : List Nat :=
  UnaryAlignedAddMachine.sums (UnaryFieldConstantScale.values factor source) offset

def values (factor : Nat) (keepPositive : Bool)
    (source offset : Bool → List Nat) : List Nat :=
  UnaryAlignedDifference.values keepPositive
    (component factor (source true) (offset true))
    (component factor (source false) (offset false))

noncomputable def nativeListComputableInPolyTime {Symbol : Type} [Fintype Symbol]
    (factor : Nat) (keepPositive : Bool)
    (source offset : Bool → List Symbol → List Nat)
    (sourceAligned : ∀ positive input, (source positive input).length = (source true input).length)
    (offsetAligned : ∀ positive input, (offset positive input).length = (source true input).length)
    (sourceCompiler : ∀ positive, TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields (source positive))
    (offsetCompiler : ∀ positive, TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields (offset positive)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun input => values factor keepPositive (fun positive => source positive input)
        (fun positive => offset positive input)) := by
  have aligned : ∀ positive input,
      (UnaryFieldConstantScale.values factor (source positive input)).length =
        (offset positive input).length := by
    intro positive input
    rw [UnaryFieldConstantScale.values, List.length_map,
      sourceAligned positive input, offsetAligned positive input]
  let compiledComponent := fun positive =>
    UnaryAlignedAddMachine.nativeListComputableInPolyTime
      (fun input => UnaryFieldConstantScale.values factor (source positive input))
      (offset positive) (aligned positive)
      (TM2CompositionMachine.computableInPolyTime (sourceCompiler positive)
        (UnaryFieldConstantScale.computableInPolyTime factor))
      (offsetCompiler positive)
  exact UnaryAlignedDifference.nativeListComputableInPolyTime keepPositive
    (fun input => component factor (source true input) (offset true input))
    (fun input => component factor (source false input) (offset false input))
    (fun input => by
      unfold component
      rw [UnaryAlignedAddMachine.sums_length (UnaryAlignedAddMachine.Valid.of_length_eq (aligned true input)),
        UnaryAlignedAddMachine.sums_length (UnaryAlignedAddMachine.Valid.of_length_eq (aligned false input))]
      simp only [UnaryFieldConstantScale.values, List.length_map, sourceAligned false input])
    (compiledComponent true) (compiledComponent false)

def field (keepPositive : Bool) (value : Int) : Nat :=
  if keepPositive then value.toNat else (-value).toNat

private theorem reconstructed (factor : Nat) (source offset : Int) :
    ((source.toNat * factor + offset.toNat : Nat) : Int) -
      (((-source).toNat * factor + (-offset).toNat : Nat) : Int) =
        (factor : Int) * source + offset := by
  have sourceEq : (source.toNat : Int) - (-source).toNat = source := by omega
  have offsetEq : (offset.toNat : Int) - (-offset).toNat = offset := by omega
  push_cast
  calc
    _ = ((source.toNat : Int) - (-source).toNat) * factor +
        ((offset.toNat : Int) - (-offset).toNat) := by ring
    _ = _ := by rw [sourceEq, offsetEq]; ring

/-- Refinement acts pointwise on the actual signed integer coordinates. -/
theorem values_map {Index : Type} (indices : List Index) (factor : Nat)
    (keepPositive : Bool) (source offset : Index → Int) :
    values factor keepPositive
        (fun positive => indices.map fun index => field positive (source index))
        (fun positive => indices.map fun index => field positive (offset index)) =
      indices.map fun index => field keepPositive ((factor : Int) * source index + offset index) := by
  unfold values component UnaryFieldConstantScale.values
  simp only [List.map_map]
  rw [UnaryAlignedAddMachine.sums_map, UnaryAlignedAddMachine.sums_map,
    UnaryAlignedDifference.values_map]
  apply List.map_congr_left
  intro index _member
  simp only [field, Function.comp_apply, Bool.false_eq_true, ↓reduceIte]
  rw [reconstructed]

theorem values_map_length {Index : Type} (indices : List Index) (factor : Nat)
    (keepPositive : Bool) (source offset : Index → Int) :
    (values factor keepPositive
      (fun positive => indices.map fun index => field positive (source index))
      (fun positive => indices.map fun index => field positive (offset index))).length = indices.length := by
  rw [values_map, List.length_map]

end LeanTrominoes.SignedUnaryCoordinateRefinement
end
