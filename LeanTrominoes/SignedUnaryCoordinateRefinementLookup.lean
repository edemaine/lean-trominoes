/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SignedUnaryCoordinateRefinementCompiler

/-! # Pointwise lookup through signed coordinate refinements -/

namespace LeanTrominoes.SignedUnaryCoordinateRefinement

private theorem sums_eq_zipWith (first second : List Nat) :
    UnaryAlignedAddMachine.sums first second = List.zipWith (· + ·) first second := by
  induction first generalizing second with
  | nil => rfl
  | cons value first induction =>
    cases second with
    | nil => rfl
    | cons other second => simp only [UnaryAlignedAddMachine.sums, List.zipWith_cons_cons, induction]

private theorem component_lookup (factor : Nat) (source offset : List Nat) (index first second : Nat)
    (sourceLookup : source[index]? = some first) (offsetLookup : offset[index]? = some second) :
    (component factor source offset)[index]? = some (first * factor + second) := by
  simp only [component, UnaryFieldConstantScale.values, sums_eq_zipWith, List.getElem?_zipWith,
    List.getElem?_map, sourceLookup, offsetLookup, Option.map_some]

/-- Aligned source and offset columns retain their common number of fields. -/
theorem values_length_of_aligned (factor : Nat) (keepPositive : Bool) (source offset : Bool → List Nat)
    (sourceAligned : ∀ positive, (source positive).length = (source true).length)
    (offsetAligned : ∀ positive, (offset positive).length = (source true).length) :
    (values factor keepPositive source offset).length = (source true).length := by
  simp only [values, UnaryAlignedDifference.values_length, component, sums_eq_zipWith,
    UnaryFieldConstantScale.values, List.length_zipWith, List.length_map,
    sourceAligned false, offsetAligned true, offsetAligned false, Nat.min_self]

/-- A signed affine refinement preserves exact coordinates at every valid
aligned lookup, independently of the lengths of unrelated suffixes. -/
theorem values_lookup (factor : Nat) (keepPositive : Bool) (source offset : Bool → List Nat)
    (index : Nat) (first second : Int)
    (sourceLookup : ∀ positive, (source positive)[index]? = some (field positive first))
    (offsetLookup : ∀ positive, (offset positive)[index]? = some (field positive second)) :
    (values factor keepPositive source offset)[index]? =
      some (field keepPositive ((factor : Int) * first + second)) := by
  rw [values, UnaryAlignedDifference.values_eq_zipWith, List.getElem?_zipWith,
    component_lookup factor (source true) (offset true) index _ _ (sourceLookup true) (offsetLookup true),
    component_lookup factor (source false) (offset false) index _ _ (sourceLookup false) (offsetLookup false)]
  have arithmetic := values_map [()] factor keepPositive (fun _ => first) (fun _ => second)
  simp only [values, component, UnaryFieldConstantScale.values, List.map_cons, List.map_nil,
    UnaryAlignedAddMachine.sums, UnaryAlignedDifference.values_eq_zipWith,
    List.zipWith_cons_cons, List.zipWith_nil_left] at arithmetic
  exact congrArg some (List.cons.inj arithmetic).1

end LeanTrominoes.SignedUnaryCoordinateRefinement
