/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Lightweight semantic occurrence-slot tags -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotBinaryWords

/-- A descriptor paired with one of its eighty-one fixed occurrence slots. -/
abbrev TaggedDescriptor := RouteDescriptor × Fin 81

/-- Descriptor-major enumeration with increasing slot index inside every
descriptor block. -/
def taggedDescriptors (descriptors : List RouteDescriptor) :
    List TaggedDescriptor :=
  descriptors.flatMap fun descriptor =>
    (List.finRange 81).map fun slot => (descriptor, slot)

end RouteDescriptorOccurrenceSlotBinaryWords
end LeanTrominoes.PeriodicOrthocrossing
