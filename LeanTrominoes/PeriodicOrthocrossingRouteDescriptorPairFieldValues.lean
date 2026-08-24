/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagData

/-! # Numeric values represented by tagged descriptor-pair fields -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

/-- Numeric value at one of the eleven canonical descriptor positions. -/
def descriptorFieldValue
    (descriptor : RouteDescriptor) (field : Fin 11) : Nat :=
  descriptor.unaryFields.getD field.val 0

/-- Semantic field valuation of an ordered descriptor pair. -/
def pairFieldValue
    (pair : RouteDescriptor × RouteDescriptor)
    (side : Side) (field : Fin 11) : Nat :=
  match side with
  | .first => descriptorFieldValue pair.1 field
  | .second => descriptorFieldValue pair.2 field

/-- Field valuation read physically by counting matching tagged units. -/
def tokenFieldValue
    (tokens : List Token) (side : Side) (field : Fin 11) : Nat :=
  tokens.count (.unit side field)

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
