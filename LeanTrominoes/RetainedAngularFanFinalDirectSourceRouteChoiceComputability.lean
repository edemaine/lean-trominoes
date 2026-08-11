import LeanTrominoes.PeriodicCNFPlanarRetainedGaugedRoutesComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedRepresentativeItemComputability
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoiceComputability
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoicePairs

/-!
# Computability of final retained direct-source route choices

The raw coordinated-route selector is indexed by finite retained clause
metadata.  The final retained formula instead uses anchor-normalized,
deduplicated clause representatives.  This module proves that the exact
representative lookup, origin translation, and final route-equality check are
primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT

set_option maxHeartbeats 500000

/-! ## Choice and metadata translations -/

theorem RetainedDirectSourceRouteChoice.translateOrigin_primrec :
    Primrec fun input : RetainedDirectSourceRouteChoice × Cell =>
      input.1.translateOrigin input.2 := by
  have data : Primrec fun input :
      RetainedDirectSourceRouteChoice × Cell =>
      (Cell.add input.2 input.1.origin,
        (RetainedDirectSourceRouteChoice.equivData input.1).2) :=
    Primrec.pair
      (Computability.cell_add_primrec.comp Primrec.snd
        (RetainedDirectSourceRouteChoice.origin_primrec.comp Primrec.fst))
      (Primrec.snd.comp
        (RetainedDirectSourceRouteChoice.equivData_primrec.comp Primrec.fst))
  exact (RetainedDirectSourceRouteChoice.equivData_symm_primrec.comp
    data).of_eq fun input => by
      rfl

private theorem metadataGaugedPositionedClause_anchor_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        DrawingPlanarSATClauseMetadata Variable =>
      PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause input.1 input.2).literals := by
  let Input := PeriodicCNF Variable ×
    DrawingPlanarSATClauseMetadata Variable
  have metadataClause : Primrec fun input : PeriodicCNF Variable ×
      DrawingPlanarSATClauseMetadata Variable =>
      input.2.clause :=
    DrawingPlanarSATClauseMetadata.clause_primrec.comp Primrec.snd
  have firstLiteral : Primrec fun input : Input =>
      input.2.clause.literals.head? :=
    Primrec.list_head?.comp
      (EmbeddedClause.literals_primrec.comp metadataClause)
  have someLiteral : Primrec₂ fun (input : Input)
      (literal : PlanarSATVariable Variable × Bool) =>
      Cell.add (periodicizePlanarSATLiteral input.1 literal).offset
        (drawingPeriodicizedPlanarSATLiteralGauge
          (input.1, literal)) := by
    change Primrec fun combined : Input ×
        (PlanarSATVariable Variable × Bool) =>
      Cell.add
        (periodicizePlanarSATLiteral combined.1.1 combined.2).offset
        (drawingPeriodicizedPlanarSATLiteralGauge
          (combined.1.1, combined.2))
    have periodicized : Primrec fun combined : Input ×
        (PlanarSATVariable Variable × Bool) =>
        periodicizePlanarSATLiteral combined.1.1 combined.2 :=
      (PeriodicOrthocrossing.periodicizePlanarSATLiteral_primrec
        (Variable := Variable)).comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd
    have gaugeInput : Primrec fun combined : Input ×
        (PlanarSATVariable Variable × Bool) =>
        ((combined.1.1, combined.2) :
          PeriodicCNF Variable ×
            (PlanarSATVariable Variable × Bool)) :=
      Primrec.pair
        (Primrec.fst.comp Primrec.fst) Primrec.snd
    have gaugeAt : Primrec fun combined : Input ×
        (PlanarSATVariable Variable × Bool) =>
        drawingPeriodicizedPlanarSATLiteralGauge
          (combined.1.1, combined.2) :=
      (PeriodicOrthocrossing.drawingPeriodicizedPlanarSATLiteralGauge_primrec
        (Variable := Variable)).comp gaugeInput
    exact Computability.cell_add_primrec.comp
      (PeriodicThreeCNF.literal_offset_primrec.comp periodicized) gaugeAt
  exact (Primrec.option_casesOn firstLiteral
    (Primrec.const (0, 0)) someLiteral).of_eq fun input => by
      unfold metadataGaugedPositionedClause PeriodicCNF.clauseAnchor
      cases h : input.2.clause.literals with
      | nil => simp [h, periodicizePlanarSATClause,
          wrapPeriodicPlanarSATClause,
          PeriodicClause.variableGauge,
          retainedDrawingWrappedPeriodicPlanarSATVariableGauge,
          drawingPeriodicizedPlanarSATLiteralGauge]
      | cons head tail => simp [h, periodicizePlanarSATClause,
          wrapPeriodicPlanarSATClause, wrapPeriodicPlanarSATLiteral,
          PeriodicClause.variableGauge,
          retainedDrawingWrappedPeriodicPlanarSATVariableGauge,
          drawingPeriodicizedPlanarSATLiteralGauge]

theorem retainedFinalDirectSourceMetadataTranslation_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        DrawingPlanarSATClauseMetadata Variable =>
      retainedFinalDirectSourceMetadataTranslation input.1 input.2 := by
  have period : Primrec fun input : PeriodicCNF Variable ×
      DrawingPlanarSATClauseMetadata Variable =>
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        input.1).period := by
    change Primrec fun input : PeriodicCNF Variable ×
        DrawingPlanarSATClauseMetadata Variable =>
      planarMacroScale.toNat *
        drawingGridSize (PeriodicCNF.incidenceGraph input.1)
    exact Primrec.nat_mul.comp
      (Primrec.const planarMacroScale.toNat)
      (drawingGridSize_primrec.comp
        (PeriodicCNF.incidenceGraph_primrec.comp Primrec.fst))
  have anchor : Primrec fun input : PeriodicCNF Variable ×
      DrawingPlanarSATClauseMetadata Variable =>
      PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause input.1 input.2).literals :=
    metadataGaugedPositionedClause_anchor_primrec
  have relative : Primrec fun input : PeriodicCNF Variable ×
      DrawingPlanarSATClauseMetadata Variable =>
      Cell.sub (0, 0)
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause input.1 input.2).literals) :=
    Computability.cell_sub_primrec.comp (Primrec.const (0, 0)) anchor
  exact (Computability.cell_scale_primrec.comp
    (Computability.int_ofNat_primrec.comp period) relative).of_eq
      fun input => by
        rfl

/-! ## Representative metadata selection -/

private abbrev RetainedFinalDirectMetadataInput (Variable : Type*) :=
  (PeriodicCNF Variable × Nat) ×
    DrawingPlanarSATClauseMetadata Variable

private def retainedFinalDirectSourceRouteChoiceForMetadata?
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalDirectMetadataInput Variable) :
    Option RetainedDirectSourceRouteChoice :=
  match retainedDirectSourceRouteChoice?
      input.1.1 input.2.source input.1.2 with
  | none => none
  | some choice =>
      some (choice.translateOrigin
        (retainedFinalDirectSourceMetadataTranslation
          input.1.1 input.2))

private theorem retainedFinalDirectSourceRouteChoiceForMetadata?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalDirectSourceRouteChoiceForMetadata?
      (Variable := Variable)) := by
  let Input := RetainedFinalDirectMetadataInput Variable
  have rawQuery : Primrec fun input : Input =>
      ((input.1.1, input.2.source), input.1.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (DrawingPlanarSATClauseMetadata.source_primrec.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)
  have rawChoice : Primrec fun input : Input =>
      retainedDirectSourceRouteChoice?
        input.1.1 input.2.source input.1.2 :=
    retainedDirectSourceRouteChoice?_primrec.comp rawQuery
  have someChoice : Primrec₂ fun (input : Input)
      (choice : RetainedDirectSourceRouteChoice) =>
      some (choice.translateOrigin
        (retainedFinalDirectSourceMetadataTranslation
          input.1.1 input.2)) := by
    change Primrec fun combined : Input ×
        RetainedDirectSourceRouteChoice =>
      some (combined.2.translateOrigin
        (retainedFinalDirectSourceMetadataTranslation
          combined.1.1.1 combined.1.2))
    have translated : Primrec fun combined : Input ×
        RetainedDirectSourceRouteChoice =>
        combined.2.translateOrigin
          (retainedFinalDirectSourceMetadataTranslation
            combined.1.1.1 combined.1.2) :=
      RetainedDirectSourceRouteChoice.translateOrigin_primrec.comp
        (Primrec.pair Primrec.snd
          (retainedFinalDirectSourceMetadataTranslation_primrec.comp
            (Primrec.pair
              (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst))
              (Primrec.snd.comp Primrec.fst))))
    exact Primrec.option_some_iff.mpr translated
  exact (Primrec.option_casesOn rawChoice
    (Primrec.const none) someChoice).of_eq fun input => by
      unfold retainedFinalDirectSourceRouteChoiceForMetadata?
      cases retainedDirectSourceRouteChoice?
        input.1.1 input.2.source input.1.2 <;> rfl

theorem retainedFinalDirectSourceRouteChoiceFromMetadata?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) ×
        Option (DrawingPlanarSATClauseMetadata Variable) =>
      retainedFinalDirectSourceRouteChoiceFromMetadata?
        input.1.1 input.1.2 input.2 := by
  let Input := (PeriodicCNF Variable × Nat) ×
    Option (DrawingPlanarSATClauseMetadata Variable)
  have metadata : Primrec fun input : Input => input.2 :=
    Primrec.snd
  have someMetadata : Primrec₂ fun (input : Input)
      (metadata : DrawingPlanarSATClauseMetadata Variable) =>
      retainedFinalDirectSourceRouteChoiceForMetadata?
        (input.1, metadata) := by
    change Primrec fun combined : Input ×
        DrawingPlanarSATClauseMetadata Variable =>
      retainedFinalDirectSourceRouteChoiceForMetadata?
        (combined.1.1, combined.2)
    exact retainedFinalDirectSourceRouteChoiceForMetadata?_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (Primrec.option_casesOn metadata
    (Primrec.const none) someMetadata).of_eq fun input => by
      unfold retainedFinalDirectSourceRouteChoiceFromMetadata?
      cases input.2 <;> rfl

private theorem retainedFinalDirectSourceRouteChoiceFromMetadataInput?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalDirectSourceRouteChoiceFromMetadataInput?
      (Variable := Variable)) :=
  (retainedFinalDirectSourceRouteChoiceFromMetadata?_primrec
    (Variable := Variable)).of_eq fun input => by
      rfl

/-! ## Final quotient selector -/

private theorem RetainedDirectSourceRouteChoice.positionedLocalRoute_primrec :
    Primrec fun choice : RetainedDirectSourceRouteChoice =>
      translatePolyline choice.origin
        (retainedDirectSourceLocalRouteAt choice.kind choice.index) := by
  have atlasIndex : Primrec fun choice :
      RetainedDirectSourceRouteChoice =>
      (RetainedDirectSourceRouteChoice.equivData choice).2 :=
    Primrec.snd.comp RetainedDirectSourceRouteChoice.equivData_primrec
  have localRoute : Primrec fun data :
      RetainedDirectSourceAtlasIndexData =>
      retainedDirectSourceLocalRouteAt
        data.1.1 ⟨data.1.2, data.2⟩ :=
    Primrec.dom_finite _
  exact PeriodicOrthocrossing.translatePolyline_primrec.comp
    RetainedDirectSourceRouteChoice.origin_primrec
    (localRoute.comp atlasIndex)

private def retainedFinalDirectSourceRouteChoiceChecked?
    {Variable : Type*} [DecidableEq Variable]
    (input : RetainedFinalDirectQuery Variable ×
      RetainedDirectSourceRouteChoice) :
    Option RetainedDirectSourceRouteChoice :=
  if translatePolyline input.2.origin
        (retainedDirectSourceLocalRouteAt
          input.2.kind input.2.index) =
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        input.1.1.1 input.1.1.2 input.1.2 then
    some input.2
  else
    none

private theorem retainedFinalDirectSourceRouteChoiceChecked?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalDirectSourceRouteChoiceChecked?
      (Variable := Variable)) := by
  let Input := RetainedFinalDirectQuery Variable ×
    RetainedDirectSourceRouteChoice
  have selectedRoute : Primrec fun input : Input =>
      translatePolyline input.2.origin
        (retainedDirectSourceLocalRouteAt
          input.2.kind input.2.index) :=
    RetainedDirectSourceRouteChoice.positionedLocalRoute_primrec.comp
      Primrec.snd
  have actualRoute : Primrec fun input : Input =>
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        input.1.1.1 input.1.1.2 input.1.2 :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec.comp
      Primrec.fst
  have represented : PrimrecPred fun input : Input =>
      translatePolyline input.2.origin
          (retainedDirectSourceLocalRouteAt
            input.2.kind input.2.index) =
        retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          input.1.1.1 input.1.1.2 input.1.2 :=
    Primrec.eq.comp selectedRoute actualRoute
  exact (Primrec.ite represented
    (Primrec.option_some_iff.mpr Primrec.snd)
    (Primrec.const none)).of_eq fun input => by
      simp [retainedFinalDirectSourceRouteChoiceChecked?]

theorem retainedFinalDirectSourceMetadata?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable × Nat =>
      retainedFinalDirectSourceMetadata? input.1 input.2 := by
  unfold retainedFinalDirectSourceMetadata?
  exact PeriodicOrthocrossing.retainedRepresentativeItem?_primrec
    (Variable := Variable)
    (Item := DrawingPlanarSATClauseMetadata Variable)
    retainedDrawingPlanarSATClauseMetadata
    PeriodicOrthocrossing.retainedDrawingPlanarSATClauseMetadata_primrec

private theorem retainedFinalDirectSourceRouteChoiceSelect?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : RetainedFinalDirectQuery Variable ×
        Option RetainedDirectSourceRouteChoice =>
      retainedFinalDirectSourceRouteChoiceSelect?
        input.1.1.1 input.1.1.2 input.1.2 input.2 := by
  let Input := RetainedFinalDirectQuery Variable ×
    Option RetainedDirectSourceRouteChoice
  have someChoice : Primrec₂ fun (input : Input)
      (choice : RetainedDirectSourceRouteChoice) =>
      retainedFinalDirectSourceRouteChoiceChecked?
        (input.1, choice) := by
    change Primrec fun combined : Input ×
        RetainedDirectSourceRouteChoice =>
      retainedFinalDirectSourceRouteChoiceChecked?
        (combined.1.1, combined.2)
    exact retainedFinalDirectSourceRouteChoiceChecked?_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (Primrec.option_casesOn Primrec.snd
    (Primrec.const none) someChoice).of_eq fun input => by
      unfold retainedFinalDirectSourceRouteChoiceSelect?
      cases input.2 <;> rfl

private theorem retainedFinalDirectSourceRouteChoiceSelectInput?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalDirectSourceRouteChoiceSelectInput?
      (Variable := Variable)) :=
  (retainedFinalDirectSourceRouteChoiceSelect?_primrec
    (Variable := Variable)).of_eq fun input => by
      rfl

private theorem retainedFinalDirectSourceRouteChoiceCandidateInput_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalDirectSourceRouteChoiceCandidateInput
      (Variable := Variable)) := by
  have result : Primrec fun input : RetainedFinalDirectQuery Variable =>
      ((input.1.1, input.2),
        retainedFinalDirectSourceMetadata? input.1.1 input.1.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((retainedFinalDirectSourceMetadata?_primrec
        (Variable := Variable)).comp Primrec.fst)
  exact result.of_eq fun input => by
    rfl

private theorem retainedFinalDirectSourceRouteChoiceCandidate?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalDirectSourceRouteChoiceCandidate?
      (Variable := Variable)) :=
  (retainedFinalDirectSourceRouteChoiceFromMetadataInput?_primrec
    (Variable := Variable)).comp
    (retainedFinalDirectSourceRouteChoiceCandidateInput_primrec
      (Variable := Variable))

private theorem retainedFinalDirectSourceRouteChoiceQuery?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFinalDirectSourceRouteChoiceQuery?
      (Variable := Variable)) := by
  exact (retainedFinalDirectSourceRouteChoiceSelectInput?_primrec
    (Variable := Variable)).comp
    (Primrec.pair Primrec.id
      (retainedFinalDirectSourceRouteChoiceCandidate?_primrec
        (Variable := Variable)))

/-- The checked coordinated direct-source selector on the final retained
quotient is primitive recursive. -/
theorem retainedFinalDirectSourceRouteChoice?_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : RetainedFinalDirectQuery Variable =>
      retainedFinalDirectSourceRouteChoice?
        input.1.1 input.1.2 input.2 := by
  exact (retainedFinalDirectSourceRouteChoiceQuery?_primrec
    (Variable := Variable)).of_eq fun input => by
    rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
