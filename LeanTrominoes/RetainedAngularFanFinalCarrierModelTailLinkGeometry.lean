/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierLinkGeometry

/-! # Physical-link geometry of final carrier model tails -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- Taking a route tail preserves the existing identification of a named
carrier model word with the normalized geometry of its physical link. -/
theorem finalCarrierModelDirectionWord_tail_eq_ofLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (forward : Bool)
    (literalIndex : Fin 2)
    (slot : RetainedTerminalSlot) :
    (finalCarrierModelDirectionWord source (link, forward)
        (carrierLinkNextSlice
          (PeriodicThreeSATThree.formula source) link)
        literalIndex slot).tail =
      (CarrierNormalizedFallbackRouteTailRecords.routeDirections
        (CarrierFallbackRouteTailRecords.Geometry.ofLink
          (PeriodicThreeSATThree.formula source) link)
        (if forward then 0 else 1) literalIndex
        slot).tail :=
  congrArg List.tail
    (finalCarrierModelDirectionWord_eq_ofLink source link forward
      literalIndex slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
