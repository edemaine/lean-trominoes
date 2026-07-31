import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoiceSpokePairs
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoicePairs

/-!
# Figure 7 spokes for final direct-source route choices

Final direct-source choices add the anchor-normalization translation of
their canonical raw metadata representative.  This module proves that the
translation acts identically on a choice's coordinated prefix and selected
Figure 7 spoke, then transports the raw cross-separation theorem to the
final retained quotient.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Translating a component origin translates its selected Figure 7 spoke
by the same fully refined physical offset as its coordinated prefix. -/
theorem RetainedDirectSourceRouteChoice.translateOrigin_figure7Spoke
    (choice : RetainedDirectSourceRouteChoice)
    (offset : Cell)
    (slot : RetainedTerminalSlot) :
    (choice.translateOrigin offset).figure7Spoke slot =
      translatePolyline
        (retainedDirectSourceFanPositioningOffset offset)
        (choice.figure7Spoke slot) := by
  rw [RetainedDirectSourceRouteChoice.figure7Spoke,
    RetainedDirectSourceRouteChoice.figure7Spoke,
    translatePolyline_add]
  apply congrArg₂ translatePolyline
  · rcases choice with ⟨origin, kind, index⟩
    rcases origin with ⟨originX, originY⟩
    rcases offset with ⟨offsetX, offsetY⟩
    simp [RetainedDirectSourceRouteChoice.translateOrigin,
      retainedDirectSourceFanPositioningOffset,
      Cell.add, Cell.scale]
    constructor <;> ring
  · rfl

/-- Successful final choices for distinct literals of one clause retain
both directed prefix--spoke strict-separation statements. -/
theorem
    retainedFinalDirectSourceRouteChoices_crossFigure7Spokes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    (firstLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex =
        some firstChoice)
    (secondLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex secondLiteralIndex =
        some secondChoice)
    (indicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    RoutesStrictlyAvoidEachOther
        (firstChoice.completeRoute firstSlot)
        (secondChoice.figure7Spoke secondSlot) ∧
      RoutesStrictlyAvoidEachOther
        (firstChoice.figure7Spoke firstSlot)
        (secondChoice.completeRoute secondSlot) := by
  rcases retainedFinalDirectSourceRouteChoice_exists_raw
      formula clauseIndex firstLiteralIndex firstChoice firstLookup with
    ⟨firstMetadata, firstRawChoice, firstMetadataLookup,
      firstRawLookup, firstChoiceEq⟩
  rcases retainedFinalDirectSourceRouteChoice_exists_raw
      formula clauseIndex secondLiteralIndex secondChoice secondLookup with
    ⟨secondMetadata, secondRawChoice, secondMetadataLookup,
      secondRawLookup, secondChoiceEq⟩
  have metadataEq : firstMetadata = secondMetadata := by
    apply Option.some.inj
    rw [← firstMetadataLookup, ← secondMetadataLookup]
  subst secondMetadata
  have firstMatches :=
    retainedDirectSourceRouteChoice?_matches_of_eq_some
      formula firstMetadata.source
      firstLiteralIndex firstRawChoice firstRawLookup
  have secondMatches :=
    retainedDirectSourceRouteChoice?_matches_of_eq_some
      formula firstMetadata.source
      secondLiteralIndex secondRawChoice secondRawLookup
  have separated :=
    retainedDirectSourceRouteChoices_crossFigure7Spokes_strictlyAvoid
      formula degree firstMetadata.source
      firstLiteralIndex secondLiteralIndex
      firstRawChoice secondRawChoice
      firstRawLookup secondRawLookup
      firstMatches secondMatches indicesDifferent
      firstSlot secondSlot
  subst firstChoice
  subst secondChoice
  rw [RetainedDirectSourceRouteChoice.translateOrigin_completeRoute,
    RetainedDirectSourceRouteChoice.translateOrigin_figure7Spoke,
    RetainedDirectSourceRouteChoice.translateOrigin_figure7Spoke,
    RetainedDirectSourceRouteChoice.translateOrigin_completeRoute]
  exact
    ⟨separated.1.map_add
        (retainedDirectSourceFanPositioningOffset
          (retainedFinalDirectSourceMetadataTranslation
            formula firstMetadata)),
      separated.2.map_add
        (retainedDirectSourceFanPositioningOffset
          (retainedFinalDirectSourceMetadataTranslation
            formula firstMetadata))⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
