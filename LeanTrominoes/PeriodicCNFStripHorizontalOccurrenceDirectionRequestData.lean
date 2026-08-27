/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalFiniteIncidenceDirectionQueryData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorDirectionData

/-! # Compact requests for complete horizontal occurrence directions -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalOccurrenceDirectionRequest

open PeriodicPlanarOneInThreeToThreeDM

/-- A complete occurrence request surrounds one dynamic source-direction word
by two finite endpoint queries and selects its physical ribbon lane. -/
inductive Token where
  | finite (query : HorizontalFiniteIncidenceDirectionQuery)
  | lane (color : Gadget.WireColor)
  | direction (value : AxisDirection)
  deriving DecidableEq, Fintype, Inhabited

def tokens
    (leading : HorizontalFiniteIncidenceDirectionQuery)
    (lane : Gadget.WireColor)
    (source : List AxisDirection)
    (trailing : HorizontalFiniteIncidenceDirectionQuery) : List Token :=
  [.finite leading, .lane lane] ++
    source.map .direction ++ [.finite trailing]

/-- Exact semantic word represented by one compact occurrence request. -/
def requestedOutput
    (leading : HorizontalFiniteIncidenceDirectionQuery)
    (lane : Gadget.WireColor)
    (source : List AxisDirection)
    (trailing : HorizontalFiniteIncidenceDirectionQuery) :
    List AxisDirection :=
  HorizontalFiniteIncidenceDirectionQuery.directions leading ++
    ribbonCorridorDirectionWord lane source ++
    HorizontalFiniteIncidenceDirectionQuery.directions trailing

end HorizontalOccurrenceDirectionRequest
end PeriodicCNFStripReduction
end LeanTrominoes
