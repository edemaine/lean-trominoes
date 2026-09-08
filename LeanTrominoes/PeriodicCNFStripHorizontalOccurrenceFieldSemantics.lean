/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceFieldLookup
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirections
import LeanTrominoes.GadgetSparseRouteDirectionEndpoints

/-! # Tagged occurrence fields are the actual variable-fan inputs -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM

/-- The tagged field tuple contains the actual connector, polarity, and
outgoing direction of a genuine source incidence. -/
theorem taggedPresentedOccurrenceFields_eq_semantic
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source.erase entry.1.1 entry.1.2 = some tagged) :
    taggedPresentedOccurrenceFields presentation.routes tagged =
      ((occurrenceConnectorKind source.erase entry.1.1 entry.1.2,
        occurrencePolarity source.erase entry.1.1 entry.1.2),
        occurrenceSourceVariableDirection presentation entry) := by
  let data := occurrenceSpliceData presentation entry
  have taggedEq : data.tagged = tagged := Option.some.inj (data.occurrenceLookup.symm.trans lookup)
  have metadata := data.metadataEq.trans taggedEq
  have clauseEq : data.indexed.1.clauseIndex = tagged.2.1 := by
    simpa only [incidenceTaggedOccurrence] using
      congrArg (fun item : TaggedOccurrence Variable => item.2.1) metadata
  have literalEq : data.indexed.1.literalIndex = tagged.2.2 := by
    simpa only [incidenceTaggedOccurrence] using
      congrArg (fun item : TaggedOccurrence Variable => item.2.2) metadata
  apply Prod.ext
  · simp only [taggedPresentedOccurrenceFields, occurrenceConnectorKind,
      occurrenceLiteralIndex, occurrencePolarity, lookup]
  · have orthogonal := presentation.route_orthogonal_of_tagged data.indexedMember
    rw [clauseEq, literalEq] at orthogonal
    have direction := occurrenceSourceVariableDirection_eq_storedRoute presentation entry
    change occurrenceSourceVariableDirection presentation entry =
      (AxisDirection.polylineLastDirection
        (presentation.routes data.indexed.1.clauseIndex data.indexed.1.literalIndex)).opposite at direction
    rw [clauseEq, literalEq] at direction
    exact (congrArg AxisDirection.opposite (unitSubdivisionDirections_getLastD _ orthogonal)).trans direction.symm

end LeanTrominoes.PeriodicCNFStripReduction
