/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRouteDirectionWords
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirectionWords
import LeanTrominoes.RetainedAngularTerminalDataProfile

/-! # Terminal data of retained carrier and bend routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT

/-- Exact backwards terminal direction and primitive-block length of one
route in an east- or north-facing equality lens. -/
def carrierLensRouteTerminalData
    (horizontal : Bool) (span : Int) : Nat → Nat → RetainedTerminalData
  | 0, 0 =>
      (.compass (if horizontal then .east else .south), 3)
  | 0, 1 =>
      (.compass (if horizontal then .north else .east), 2)
  | 1, 0 =>
      (.compass (if horizontal then .south else .west), 1)
  | 1, 1 =>
      (.compass (if horizontal then .west else .north),
        (span - 6).toNat)
  | _, _ => (.compass .east, 1)

/-- Exact finite-table terminal datum of one bend-corner route. -/
def bendRouteTerminalData
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) : RetainedTerminalData :=
  classifiedRetainedTerminalData
    (PeriodicThreeSATThree.routeTerminalVector
      (cornerEqualityRoutes firstPort secondPort
        localClauseIndex literalIndex))

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
