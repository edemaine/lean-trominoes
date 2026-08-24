/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeStreamData

/-! # Semantic data of the complete source-key component stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

open RouteDescriptorOccurrenceSlotBinaryWords

def guardedWords (descriptors : List RouteDescriptor) : List (List Bool) :=
  TerminalSourceKeyRecipeStream.guardedWords
      (descriptors ×ˢ descriptors) ++
    CrossingSourceKeyRecipeStream.guardedWords
      (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
