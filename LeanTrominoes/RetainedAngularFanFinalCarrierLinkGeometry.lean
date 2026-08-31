/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordGeometryData
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedDirectionData

/-! # Physical-link geometry of final retained-carrier routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- Supplying the semantic next-slice bit makes the final-carrier route
geometry exactly the geometry projected from its physical retained link. -/
theorem finalCarrierRouteGeometryAt_eq_ofLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (forward : Bool) :
    finalCarrierRouteGeometryAt source (link, forward)
        (carrierLinkNextSlice
          (PeriodicThreeSATThree.formula source) link) =
      CarrierFallbackRouteTailRecords.Geometry.ofLink
        (PeriodicThreeSATThree.formula source) link := by
  rfl

/-- With that physical geometry, the finite final-carrier model is exactly
the normalized fallback route word at the tagged implication's local index. -/
theorem finalCarrierModelDirectionWord_eq_ofLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (forward : Bool)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot) :
    finalCarrierModelDirectionWord source (link, forward)
        (carrierLinkNextSlice
          (PeriodicThreeSATThree.formula source) link)
        literalIndex slot =
      CarrierNormalizedFallbackRouteTailRecords.routeDirections
        (CarrierFallbackRouteTailRecords.Geometry.ofLink
          (PeriodicThreeSATThree.formula source) link)
        (if forward then 0 else 1) literalIndex slot := by
  unfold finalCarrierModelDirectionWord
  rw [finalCarrierRouteGeometryAt_eq_ofLink]
  rw [finalCarrierLocalClauseIndex_val]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
