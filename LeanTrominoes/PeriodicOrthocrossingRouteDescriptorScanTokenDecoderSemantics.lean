/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokenDecoder
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnarySemantics

/-! # Correctness of normalized route-descriptor decoding -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorScanTokens

@[simp] theorem takeField_field_append
    (number : Nat) (suffix : List Token) :
    takeField (field number ++ suffix) = some (number, suffix) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [show field (number + 1) = .unit :: field number by
        simp [field, List.replicate_succ]]
      simp [takeField, induction]

@[simp] theorem takeFields_fields_append
    (numbers : List Nat) (suffix : List Token) :
    takeFields numbers.length (fields numbers ++ suffix) =
      some (numbers, suffix) := by
  induction numbers with
  | nil => rfl
  | cons number numbers induction =>
      rw [show fields (number :: numbers) =
        field number ++ fields numbers by rfl]
      simp [takeFields, takeField_field_append, induction]

@[simp] theorem unaryFields_length (descriptor : RouteDescriptor) :
    descriptor.unaryFields.length = 11 := by
  simp [RouteDescriptor.unaryFields, signedUnaryFields]

@[simp] theorem takeFields_record_append
    (descriptor : RouteDescriptor) (suffix : List Token) :
    takeFields 11 (fields descriptor.unaryFields ++ suffix) =
      some (descriptor.unaryFields, suffix) := by
  simpa [unaryFields_length] using
    takeFields_fields_append descriptor.unaryFields suffix

theorem encode_length_ge (descriptors : List RouteDescriptor) :
    descriptors.length ≤ (encode descriptors).length := by
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors induction =>
      rw [show encode (descriptor :: descriptors) =
        record descriptor ++ encode descriptors by rfl]
      simp only [List.length_cons, List.length_append]
      have recordPositive : 1 ≤ (record descriptor).length := by
        simp [record]
      omega

theorem decodeAux_encode (descriptors : List RouteDescriptor) (fuel : Nat)
    (enough : descriptors.length < fuel) :
    decodeAux fuel (encode descriptors) = some descriptors := by
  induction descriptors generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel => rfl
  | cons descriptor descriptors induction =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have tailEnough : descriptors.length < fuel := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using enough
          change decodeAux (fuel + 1)
              (.recordStart ::
                (fields descriptor.unaryFields ++ encode descriptors)) = _
          rw [decodeAux, takeFields_record_append]
          change (do
              let parsed ←
                RouteDescriptor.ofUnaryFields? descriptor.unaryFields
              let remaining ← decodeAux fuel (encode descriptors)
              pure (parsed :: remaining)) =
            some (descriptor :: descriptors)
          rw [RouteDescriptor.ofUnaryFields?_unaryFields]
          rw [induction fuel tailEnough]
          rfl

/-- Canonical normalized records round-trip through the total decoder. -/
@[simp] theorem decode_encode (descriptors : List RouteDescriptor) :
    decode (encode descriptors) = some descriptors := by
  apply decodeAux_encode
  have lengthBound := encode_length_ge descriptors
  omega

end RouteDescriptorScanTokens
end PeriodicOrthocrossing
end LeanTrominoes
