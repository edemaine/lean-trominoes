/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SignedUnaryCoordinateRefinementLookup
import LeanTrominoes.UnaryFieldFixedCopiesCompiler
import LeanTrominoes.UnaryFieldConstantTableCompiler

/-! # Expand each signed coordinate through a fixed translation table -/

noncomputable section
namespace LeanTrominoes.SignedUnaryCoordinateTableExpansion
open Computability Turing SignedUnaryCoordinateRefinement

private theorem fixedCopies_length (copies : Nat) (source : List Nat) :
    (UnaryFieldFixedCopies.values copies source).length = source.length * copies := by
  simp [UnaryFieldFixedCopies.values]

/-- For every source coordinate, emit all fixed translated coordinates in table order. -/
def values (table : List Int) (keepPositive : Bool) (source : Bool → List Nat) : List Nat :=
  SignedUnaryCoordinateRefinement.values 1 keepPositive
    (fun positive => UnaryFieldFixedCopies.values table.length (source positive))
    (fun positive => UnaryFieldConstantTable.values (table.map (field positive)) (source true))

noncomputable def nativeListComputableInPolyTime {Symbol : Type} [Fintype Symbol]
    (table : List Int) (keepPositive : Bool) (source : Bool → List Symbol → List Nat)
    (aligned : ∀ positive input, (source positive input).length = (source true input).length)
    (compiler : ∀ positive, TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (source positive)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun input => values table keepPositive (fun positive => source positive input)) := by
  unfold values
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 1 keepPositive
    (fun positive input => UnaryFieldFixedCopies.values table.length (source positive input))
    (fun positive input => UnaryFieldConstantTable.values (table.map (field positive)) (source true input))
    (fun positive input => by rw [fixedCopies_length, fixedCopies_length, aligned positive input])
    (fun positive input => by rw [UnaryFieldConstantTable.values_length, fixedCopies_length, List.length_map])
    (fun positive => TM2CompositionMachine.computableInPolyTime (compiler positive)
      (UnaryFieldFixedCopies.computableInPolyTime table.length))
    (fun positive => TM2CompositionMachine.computableInPolyTime (compiler true)
      (UnaryFieldConstantTable.computableInPolyTime (table.map (field positive))))

@[simp] theorem values_length (table : List Int) (keepPositive : Bool) (source : Bool → List Nat)
    (aligned : ∀ positive, (source positive).length = (source true).length) :
    (values table keepPositive source).length = (source true).length * table.length := by
  unfold values
  rw [SignedUnaryCoordinateRefinement.values_length_of_aligned _ _ _ _
    (fun positive => by rw [fixedCopies_length, fixedCopies_length, aligned positive])
    (fun positive => by rw [UnaryFieldConstantTable.values_length, List.length_map, fixedCopies_length]), fixedCopies_length]

/-- The native expansion has exact origin-major, table-minor affine semantics. -/
theorem values_map {Index : Type} (indices : List Index) (coordinate : Index → Int)
    (table : List Int) (keepPositive : Bool) :
    values table keepPositive (fun positive => indices.map fun index => field positive (coordinate index)) =
      indices.flatMap fun index => table.map fun offset => field keepPositive (coordinate index + offset) := by
  let pairs := indices.flatMap fun index => table.map fun offset => (index, offset)
  have base (positive : Bool) :
      UnaryFieldFixedCopies.values table.length (indices.map fun index => field positive (coordinate index)) =
        pairs.map (fun pair => field positive (coordinate pair.1)) := by
    simp only [UnaryFieldFixedCopies.values, pairs, List.flatMap_map, List.map_flatMap, List.map_map,
      Function.comp_def, List.map_const']
  have offsets (positive : Bool) :
      UnaryFieldConstantTable.values (table.map (field positive))
        (indices.map fun index => field true (coordinate index)) =
        pairs.map (fun pair => field positive pair.2) := by
    simp only [UnaryFieldConstantTable.values, pairs, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  unfold values
  simp only [base, offsets]
  rw [SignedUnaryCoordinateRefinement.values_map]
  simp only [pairs, List.map_flatMap, List.map_map, Function.comp_def, Nat.cast_one, one_mul]

end LeanTrominoes.SignedUnaryCoordinateTableExpansion
end
