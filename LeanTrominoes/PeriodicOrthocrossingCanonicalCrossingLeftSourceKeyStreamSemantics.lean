/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics

/-! # Semantics of canonical-left crossing source-key streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingLeftSourceKeyStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Mapping the inner compiler over canonical pair blocks emits exactly the
encoding of their concatenated guarded candidate words. -/
@[simp] theorem emittedStream_encodeDescriptorSlotPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    emittedStream
        (RouteDescriptorOccurrenceSlotPairFieldTags.encodeDescriptorSlotPairs
          pairs) =
      DelimitedBinaryWords.encode ⟨guardedWords pairs⟩ := by
  unfold emittedStream
  rw [RouteDescriptorOccurrenceSlotPairFieldTags.mappedOutput_encodeDescriptorSlotPairs]
  simp only [CanonicalCrossingLeftSourceKeyEmitter.emittedTokens_eq_candidates]
  unfold guardedWords DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

end CanonicalCrossingLeftSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing
