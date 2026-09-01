/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceCompiler

/-! # Semantics of counted contraction plans -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace CountedContractedIncidence

open PeriodicThreeDM

/-- Declarative query-key block of one degree-two-or-three element. -/
def queryBlock (elementCode size : Nat) : List Nat :=
  if size = 3 then
    [3 * elementCode, 3 * elementCode + 1, 3 * elementCode + 2]
  else
    [3 * elementCode, 3 * elementCode + 1]

/-- Declarative role block of one degree-two-or-three element. -/
def expectedRoleBlock (size : Nat) :
    List ContractedDirectionAssembler.Role :=
  if size = 3 then
    [.retained, .retained, .retained]
  else
    [.throughFirst, .throughSecond]

@[simp] theorem activeControls_cons_two (sizes : List Nat) :
    activeControls (2 :: sizes) =
      [true, true, false] ++ activeControls sizes := by
  rfl

@[simp] theorem activeControls_cons_three (sizes : List Nat) :
    activeControls (3 :: sizes) =
      [true, true, true] ++ activeControls sizes := by
  rfl

@[simp] theorem roles_cons_two (sizes : List Nat) :
    roles (2 :: sizes) =
      [.throughFirst, .throughSecond] ++ roles sizes := by
  rfl

@[simp] theorem roles_cons_three (sizes : List Nat) :
    roles (3 :: sizes) =
      [.retained, .retained, .retained] ++ roles sizes := by
  rfl

@[simp] theorem queryKeys_cons_two
    (elementCode : Nat) (elementCodes sizes : List Nat) :
    queryKeys (elementCode :: elementCodes) (2 :: sizes) =
      [3 * elementCode, 3 * elementCode + 1] ++
        queryKeys elementCodes sizes := by
  rw [queryKeys, UnaryFieldBooleanFilter.selectedValues_eq,
    UnaryFieldThreeBlockOrdinals.values_eq_flatMap]
  simp only [List.flatMap_cons, activeControls_cons_two]
  simp [DelimitedBinaryWordBooleanFilter.selected, queryKeys,
    UnaryFieldBooleanFilter.selectedValues_eq,
    UnaryFieldThreeBlockOrdinals.values_eq_flatMap]

@[simp] theorem queryKeys_cons_three
    (elementCode : Nat) (elementCodes sizes : List Nat) :
    queryKeys (elementCode :: elementCodes) (3 :: sizes) =
      [3 * elementCode, 3 * elementCode + 1,
          3 * elementCode + 2] ++
        queryKeys elementCodes sizes := by
  rw [queryKeys, UnaryFieldBooleanFilter.selectedValues_eq,
    UnaryFieldThreeBlockOrdinals.values_eq_flatMap]
  simp only [List.flatMap_cons, activeControls_cons_three]
  simp [DelimitedBinaryWordBooleanFilter.selected, queryKeys,
    UnaryFieldBooleanFilter.selectedValues_eq,
    UnaryFieldThreeBlockOrdinals.values_eq_flatMap]

/-- With aligned canonical elements and valid degrees, the compiled query
stream is exactly the element-major concatenation of the required two or
three stable occurrence keys. -/
theorem queryKeys_eq_zipWith
    (elementCodes sizes : List Nat)
    (lengthEq : elementCodes.length = sizes.length)
    (valid : ∀ size ∈ sizes, size = 2 ∨ size = 3) :
    queryKeys elementCodes sizes =
      (List.zipWith queryBlock elementCodes sizes).flatten := by
  induction sizes generalizing elementCodes with
  | nil =>
      have : elementCodes = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq)
      subst elementCodes
      rfl
  | cons size sizes induction =>
      cases elementCodes with
      | nil => simp at lengthEq
      | cons elementCode elementCodes =>
          have tailLength : elementCodes.length = sizes.length := by
            simpa using lengthEq
          have headValid : size = 2 ∨ size = 3 := valid size (by simp)
          have tailValid : ∀ other ∈ sizes,
              other = 2 ∨ other = 3 := by
            intro other member
            exact valid other (by simp [member])
          rcases headValid with rfl | rfl <;>
            simp [queryBlock, induction elementCodes tailLength tailValid]

/-- The aligned role compiler has the same exact element-major block
semantics. -/
theorem roles_eq_map
    (sizes : List Nat)
    (valid : ∀ size ∈ sizes, size = 2 ∨ size = 3) :
    roles sizes = (sizes.map expectedRoleBlock).flatten := by
  induction sizes with
  | nil => rfl
  | cons size sizes induction =>
      have headValid : size = 2 ∨ size = 3 := valid size (by simp)
      have tailValid : ∀ other ∈ sizes,
          other = 2 ∨ other = 3 := by
        intro other member
        exact valid other (by simp [member])
      rcases headValid with rfl | rfl <;>
        simp [expectedRoleBlock, induction tailValid]

/-- Incidence block keys have precisely the stable base-three occurrence-key
semantics used by the ordered query stream. -/
theorem incidenceBlockKeys_eq_candidateKeys
    (incidenceElementCodes : List Nat) :
    incidenceBlockKeys incidenceElementCodes =
      StableOccurrenceRanks.candidateKeys incidenceElementCodes := by
  exact UnaryFieldStableOccurrenceKeys.keys_eq_candidateKeys
    incidenceElementCodes

end CountedContractedIncidence
end PeriodicCNFStripReduction
end LeanTrominoes
