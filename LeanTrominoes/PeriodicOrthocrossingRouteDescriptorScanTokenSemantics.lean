/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokens

/-! # Exact semantics of normalized route-descriptor scan tokens -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorScanTokens

@[simp] theorem normalize_append
    (first second : List PeriodicCNF.UnaryProgramTokens.Token) :
    normalize (first ++ second) = normalize first ++ normalize second := by
  simp [normalize]

@[simp] theorem normalize_cons
    (token : PeriodicCNF.UnaryProgramTokens.Token)
    (tokens : List PeriodicCNF.UnaryProgramTokens.Token) :
    normalize (token :: tokens) = normalizeBlock token ++ normalize tokens := by
  rfl

@[simp] theorem flatMap_normalizeBlock_replicate_atomUnit (number : Nat) :
    List.flatMap normalizeBlock
        (List.replicate number
          PeriodicCNF.UnaryProgramTokens.Token.atomUnit) =
      List.replicate number .unit := by
  induction number with
  | zero => rfl
  | succ number induction =>
      simp only [List.replicate_succ, List.flatMap_cons, normalizeBlock,
        induction, List.singleton_append]

@[simp] theorem normalize_field (number : Nat) :
    normalize (CountedUnaryFieldTokens.field number) = field number := by
  simp only [normalize, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.flatMap_append,
    flatMap_normalizeBlock_replicate_atomUnit, List.flatMap_cons,
    normalizeBlock, List.flatMap_nil, List.singleton_append, field]

@[simp] theorem normalize_fields (numbers : List Nat) :
    normalize (CountedUnaryFieldTokens.fields numbers) = fields numbers := by
  induction numbers with
  | nil => rfl
  | cons number numbers induction =>
      rw [show CountedUnaryFieldTokens.fields (number :: numbers) =
          CountedUnaryFieldTokens.field number ++
            CountedUnaryFieldTokens.fields numbers by rfl]
      rw [show fields (number :: numbers) =
          field number ++ fields numbers by rfl]
      rw [normalize_append, normalize_field, induction]

@[simp] theorem normalize_countedFieldBlock (numbers : List Nat) :
    normalize (CountedUnaryFieldTokens.countedFieldBlock numbers) =
      .recordStart :: fields numbers := by
  unfold CountedUnaryFieldTokens.countedFieldBlock
  rw [normalize_cons, normalize_fields]
  rfl

/-- Normalizing canonical counted route tokens recovers precisely one
minimal eleven-field record per descriptor. -/
@[simp] theorem normalize_routeDescriptorTokens
    (descriptors : List RouteDescriptor) :
    normalize (routeDescriptorTokens descriptors) = encode descriptors := by
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors induction =>
      change normalize
          (CountedUnaryFieldTokens.countedFieldBlock
              descriptor.unaryFields ++
            CountedUnaryFieldTokens.countedFieldBlocks
              (descriptors.map RouteDescriptor.unaryFields)) = _
      rw [show normalize
          (CountedUnaryFieldTokens.countedFieldBlock
              descriptor.unaryFields ++
            CountedUnaryFieldTokens.countedFieldBlocks
              (descriptors.map RouteDescriptor.unaryFields)) =
          normalize (CountedUnaryFieldTokens.countedFieldBlock
            descriptor.unaryFields) ++
          normalize (CountedUnaryFieldTokens.countedFieldBlocks
            (descriptors.map RouteDescriptor.unaryFields)) by
        simp [normalize]]
      rw [normalize_countedFieldBlock]
      change .recordStart :: fields descriptor.unaryFields ++
          normalize (routeDescriptorTokens descriptors) =
        encode (descriptor :: descriptors)
      rw [induction]
      rfl

end RouteDescriptorScanTokens
end PeriodicOrthocrossing
end LeanTrominoes
