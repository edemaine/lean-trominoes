/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceRoutedRequestData
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalTypedIncidenceDirectionRequestData

/-! # Compact routed requests for horizontal typed incidences -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalTypedIncidenceRoutedRequest

/-- A complete typed incidence contains a finite local prefix and optionally
one compact routed occurrence request. -/
inductive Token
  | finite (query : HorizontalFiniteIncidenceDirectionQuery)
  | occurrence (token : HorizontalOccurrenceRoutedRequest.Token)
  deriving DecidableEq, Fintype

instance : Inhabited Token := ⟨.finite default⟩

end HorizontalTypedIncidenceRoutedRequest
end PeriodicCNFStripReduction
end LeanTrominoes
