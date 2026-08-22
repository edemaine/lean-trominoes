/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordDecoder
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokenDecoderSemantics

/-! # Correctness of binary route-descriptor word decoding -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorBinaryWords

@[simp] theorem map_bitToken_fieldWord (number : Nat) :
    (fieldWord number).map bitToken =
      RouteDescriptorScanTokens.field number := by
  simp [fieldWord, bitToken, RouteDescriptorScanTokens.field]

@[simp] theorem map_bitToken_descriptorWord
    (descriptor : RouteDescriptor) :
    (descriptorWord descriptor).map bitToken =
      RouteDescriptorScanTokens.fields descriptor.unaryFields := by
  unfold descriptorWord RouteDescriptorScanTokens.fields
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro number numberMember
  exact map_bitToken_fieldWord number

/-- Every canonical binary descriptor word decodes exactly. -/
@[simp] theorem decodeWord_descriptorWord
    (descriptor : RouteDescriptor) :
    decodeWord (descriptorWord descriptor) = some descriptor := by
  unfold decodeWord
  rw [map_bitToken_descriptorWord]
  have parsed :=
    RouteDescriptorScanTokens.takeFields_record_append descriptor []
  simp only [List.append_nil] at parsed
  rw [parsed]
  exact RouteDescriptor.ofUnaryFields?_unaryFields descriptor

/-- Canonical ordered descriptor pairs likewise decode exactly. -/
@[simp] theorem decodePair_descriptorWords
    (first second : RouteDescriptor) :
    decodePair (descriptorWord first, descriptorWord second) =
      some (first, second) := by
  simp [decodePair]

end RouteDescriptorBinaryWords
end PeriodicOrthocrossing
end LeanTrominoes
