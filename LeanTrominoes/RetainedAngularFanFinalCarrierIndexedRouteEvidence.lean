/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierNormalizedRouteDirectionModel
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedScaledRouteEvidence

/-! # Scaled-route evidence at indexed final carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- The original lookup package supplies both route consequences needed by
the normalized public theorem. -/
theorem FinalCarrierIndexedOccurrence.routeDirectionEvidence
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable) :
    occurrence.RouteDirectionEvidence := by
  constructor
  · exact occurrence.scaledRouteEvidence
  · exact
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_carrier_directions_eq_model
        occurrence.source occurrence.sourceLocal occurrence.sourceWidth
        occurrence.sourceClausesNonempty occurrence.positiveOffsets
        occurrence.taggedLink occurrence.clauseIndex
        occurrence.taggedLinkIndexed occurrence.clauseMember
        occurrence.literalIndex occurrence.literalMember

/-- Consume the packaged occurrence evidence without forcing downstream
elaboration to normalize the evidence constructor's indexed result. -/
theorem FinalCarrierIndexedOccurrence.withScaledRouteEvidence
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    {P : Prop}
    (consume : occurrence.ScaledRouteEvidence → P) :
    P :=
  consume occurrence.scaledRouteEvidence

end PeriodicEightOccurrenceSplit
end LeanTrominoes
