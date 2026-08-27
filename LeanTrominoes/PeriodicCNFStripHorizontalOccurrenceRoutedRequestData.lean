/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceDirectionRequestData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteDirectionRequestData

/-! # Compact routed requests for complete horizontal occurrences -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalOccurrenceRoutedRequest

/-- Explicit finite occurrence frame around one compact routed source-word
request. -/
inductive Token
  | leading (query : HorizontalFiniteIncidenceDirectionQuery)
  | lane (color : Gadget.WireColor)
  | routed (token : HorizontalRoutedRouteDirectionRequest.Token)
  | trailing (query : HorizontalFiniteIncidenceDirectionQuery)
  deriving DecidableEq, Fintype

instance : Inhabited Token := ⟨.lane .red⟩

def tokens
    (leading : HorizontalFiniteIncidenceDirectionQuery)
    (lane : Gadget.WireColor)
    (route : HorizontalRoutedRouteDirectionBlock)
    (trailing : HorizontalFiniteIncidenceDirectionQuery) : List Token :=
  [.leading leading, .lane lane] ++
    (HorizontalRoutedRouteDirectionRequest.tokens route).map .routed ++
    [.trailing trailing]

end HorizontalOccurrenceRoutedRequest
end PeriodicCNFStripReduction
end LeanTrominoes
