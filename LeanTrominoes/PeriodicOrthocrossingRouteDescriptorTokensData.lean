/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CountedUnaryFieldTokens
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnaryData

/-! # Counted finite-token streams for numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Eleven-field payload blocks, one per numeric route descriptor. -/
def routeDescriptorFieldBlocks
    (descriptors : List RouteDescriptor) : List (List Nat) :=
  descriptors.map RouteDescriptor.unaryFields

/-- Counted, delimiter-terminated unary records for a route-descriptor list. -/
def routeDescriptorTokens
    (descriptors : List RouteDescriptor) :
    List PeriodicCNF.UnaryProgramTokens.Token :=
  CountedUnaryFieldTokens.countedFieldBlocks
    (routeDescriptorFieldBlocks descriptors)

end PeriodicOrthocrossing
end LeanTrominoes
