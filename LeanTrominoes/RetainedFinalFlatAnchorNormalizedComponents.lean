import LeanTrominoes.RetainedFinalFlatCarrierMacrocellOverlapNormalization
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierNoncarrierContactReduction

/-!
# Anchor-normalized components behind flat final routes

Flat final routes are listed at external period shift zero.  Their recovered
physical shift is therefore the negative of the finite clause anchor.  The
existing gauged-component API proves that this exact translation puts a
carrier in the raw neighboring window and realizes every noncarrier orbit by
a retained finite source.

These packages express the final carrier rectangle and noncarrier macrocell
directly in that shared anchor-normalized frame.  They avoid introducing a
second relative reindexing when applying the finite carrier proximity
theorems.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- At external shift zero, the recovered physical shift is the negative of
the selected finite clause anchor. -/
theorem
    FinalGaugedFlatRouteOccurrenceWitness.physicalShift_eq_neg_anchor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteOccurrenceWitness
        formula taggedRoute) :
    witness.routeWitness.physicalShift =
      Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula witness.routeWitness.metadata).literals) := by
  unfold FinalGaugedRouteOccurrenceWitness.physicalShift
  rcases
      PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause
          formula witness.routeWitness.metadata).literals with
    ⟨anchorX, anchorY⟩
  simp [Cell.sub, Cell.neg]

/-- The carrier link translated by its own final anchor-normalizing physical
shift. -/
def FinalGaugedFlatCarrierRouteWitness.normalizedLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    EqualityLink CarrierNode :=
  carrierLinkPeriodTranslate formula.incidenceGraph carrier.link
    carrier.routeWitness.physicalShift

/-- The final lower rectangle corner is definitionally the lower corner of
the anchor-normalized raw carrier link. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.rectangleLower_eq_normalizedLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    carrier.rectangleLower =
      drawingCompleteCarrierLinkRectangleLower
        formula.incidenceGraph carrier.normalizedLink := by
  unfold FinalGaugedFlatCarrierRouteWitness.normalizedLink
  rw [drawingCompleteCarrierLinkRectangleLower_periodTranslate]
  unfold FinalGaugedFlatCarrierRouteWitness.rectangleLower
    FinalGaugedFlatCarrierRouteWitness.physicalOffset
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
  apply Prod.ext <;> simp [Cell.add] <;> ring

/-- The final upper rectangle corner is definitionally the upper corner of
the anchor-normalized raw carrier link. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.rectangleUpper_eq_normalizedLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    carrier.rectangleUpper =
      drawingCompleteCarrierLinkRectangleUpper
        formula.incidenceGraph carrier.normalizedLink := by
  unfold FinalGaugedFlatCarrierRouteWitness.normalizedLink
  rw [drawingCompleteCarrierLinkRectangleUpper_periodTranslate]
  unfold FinalGaugedFlatCarrierRouteWitness.rectangleUpper
    FinalGaugedFlatCarrierRouteWitness.physicalOffset
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
  apply Prod.ext <;> simp [Cell.add] <;> ring

/-- Every carrier package yields an anchor-normalized link in the raw
retained carrier window. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.normalizedLink_mem_raw
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    carrier.normalizedLink ∈
      retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph := by
  rcases
      carrier.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          carrier.link carrier.componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have nonempty :
      carrier.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := carrier.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have anchorNormalized :=
    carrier.routeWitness.metadata.carrier_anchorNormalize_mem_raw
      wellFormed degree isLocal
      carrier.routeWitness.metadata_retainedValid
      nonempty carrier.link localClauseIndex sourceEq
  simpa [FinalGaugedFlatCarrierRouteWitness.normalizedLink,
    carrier.toFinalGaugedFlatRouteOccurrenceWitness
      |>.physicalShift_eq_neg_anchor] using
        anchorNormalized

/-- The first occurrence of the anchor-normalized carrier link is one of the
nine neighboring drawing translations. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.normalizedLink_first_neighbor
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    IsNeighborTranslation carrier.normalizedLink.first.translate := by
  rcases
      carrier.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          carrier.link carrier.componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have nonempty :
      carrier.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := carrier.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have anchorNormalized :=
    carrier.routeWitness.metadata
      |>.carrier_first_anchorNormalize_translate_neighbor
        wellFormed degree isLocal
        carrier.routeWitness.metadata_retainedValid
        nonempty carrier.link localClauseIndex sourceEq
  simpa [FinalGaugedFlatCarrierRouteWitness.normalizedLink,
    carrier.toFinalGaugedFlatRouteOccurrenceWitness
      |>.physicalShift_eq_neg_anchor] using
        anchorNormalized

/-- A retained finite source realizing the anchor-normalized component of a
flat noncarrier route.  The source presentation may change at a retained
window boundary (notably its routed-variable arm index), while its component
and local clause index remain exact. -/
structure FinalGaugedFlatNormalizedMacrocellSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {taggedRoute : List Cell × Nat}
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute) where
  source : DrawingPlanarSATClauseSource Variable
  sourceMember : source.RetainedComponentMember formula
  componentEq :
    source.component =
      (macrocell.routeWitness.metadata.source.periodTranslate
        formula macrocell.routeWitness.physicalShift).component
  localClauseIndexEq :
    source.localClauseIndex =
      macrocell.routeWitness.metadata.source.localClauseIndex

/-- Every flat noncarrier package has a retained source realizing its exact
anchor-normalized physical component. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.exists_normalizedSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute) :
    Nonempty
      (FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell) := by
  have notCarrier :
      ¬∃ link,
        macrocell.routeWitness.metadata.source.component =
          .carrier link := by
    rintro ⟨link, componentEq⟩
    have centerEq := macrocell.centerEq
    rw [componentEq] at centerEq
    simp [DrawingPlanarSATComponent.macrocellCenter]
      at centerEq
  have nonempty :
      macrocell.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := macrocell.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have orbitCondition :=
    macrocell.routeWitness.metadata
      |>.noncarrier_anchorNormalize_retainedOrbitCondition
        wellFormed degree isLocal
        macrocell.routeWitness.metadata_retainedValid
        nonempty notCarrier
  have sourceMember :
      macrocell.routeWitness.metadata.source.RetainedComponentMember
        formula :=
    (macrocell.routeWitness.metadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp
          macrocell.routeWitness.metadata_retainedValid |>.1
  have physicalOrbitCondition :
      macrocell.routeWitness.metadata.source.RetainedOrbitCondition
        formula macrocell.routeWitness.physicalShift := by
    simpa [
      macrocell.toFinalGaugedFlatRouteOccurrenceWitness
        |>.physicalShift_eq_neg_anchor] using
          orbitCondition
  rcases
      macrocell.routeWitness.metadata.source
        |>.exists_retainedTarget_periodTranslate
          formula degree sourceMember
          macrocell.routeWitness.physicalShift
          physicalOrbitCondition with
    ⟨source, sourceRetained, componentEq, localClauseIndexEq⟩
  exact ⟨⟨source, sourceRetained,
    componentEq, localClauseIndexEq⟩⟩

/-- The component realized by a normalized noncarrier source advertises the
same center as the final translated macrocell package. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.centerEq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell) :
    normalized.source.component.macrocellCenter formula =
      some macrocell.translatedCenter := by
  rw [normalized.componentEq,
    DrawingPlanarSATClauseSource.component_periodTranslate,
    DrawingPlanarSATComponent.macrocellCenter_periodTranslate,
    macrocell.centerEq]
  rfl

/-- Failure of the final rectangle-separation test is already the overlap
hypothesis between the raw anchor-normalized carrier link and the normalized
noncarrier component center. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.normalizedLink_macrocell_overlap
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph carrier.normalizedLink)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph carrier.normalizedLink)
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter) := by
  simpa [carrier.rectangleLower_eq_normalizedLink,
    carrier.rectangleUpper_eq_normalizedLink] using notSeparated

end PeriodicOrthocrossing
end LeanTrominoes
