/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyStreamData
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordData

/-! # Compact crossover atom words from fixed common-shift candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftCompactAtomWordStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- The padded guarded source-pair stream for a route-descriptor list. -/
def guardedSourceWords (descriptors : List RouteDescriptor) :
    List (List Bool) :=
  CanonicalCrossingShiftLeftSourceKeyStream.guardedWords
    (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

/-- Expand every active physical common-shift candidate to its fixed
Figure 8(b) compact atom-word block; inactive candidates disappear. -/
def words (descriptors : List RouteDescriptor) : List (List Bool) :=
  CrossoverCompactAtomWords.words (guardedSourceWords descriptors)

def input (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  ⟨words descriptors⟩

end CanonicalCrossingShiftCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing
