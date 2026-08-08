import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFanSystemSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedStubs
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteElements

/-!
# Separation of translated coordinated source fans

The finite coordinated fan tables already prove contact-free separation
inside one standard macrocell.  This file transports those certificates to
actual source vertices.  The first result handles all strands incident to one
source variable; subsequent results will combine the analogous clause-local
fact with separation between different source macrocells.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- Distinct colored strands incident to one source variable have strictly
separated translated coordinated stubs. -/
theorem occurrenceCoordinatedRibbonVariableStubs_strictlyAvoidEachOther_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (sameAtom : first.1.1 = second.1.1)
    (different :
      RibbonStrandsDifferent first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation second secondColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  let data := sourceVariableRibbonFanData planar first
  let firstSlot := occurrenceVariableSiteSlot first.1.2
  let secondSlot := occurrenceVariableSiteSlot second.1.2
  have firstActive : data.SlotActive firstSlot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      planar first
  have secondActive : data.SlotActive secondSlot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive_of_same_atom
      planar first second sameAtom.symm
  have localDifferent :
      (firstSlot, firstColor) ≠ (secondSlot, secondColor) := by
    intro equal
    apply different
    have slotEqual : first.1.2 = second.1.2 :=
      occurrenceVariableSiteSlot_injective
        (congrArg Prod.fst equal)
    have colorEqual : firstColor = secondColor :=
      congrArg Prod.snd equal
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext sameAtom slotEqual
    · exact colorEqual
  have localAvoid :
      RoutesStrictlyAvoidEachOther
        (data.coordinatedRoute firstSlot firstColor)
        (data.coordinatedRoute secondSlot secondColor) :=
    VariableRibbonFanData.coordinatedRoutes_strictlyAvoidEachOther
      data (compatible.1 first)
      firstSlot secondSlot firstActive secondActive
      firstColor secondColor localDifferent
  have translatedAvoid :=
    localAvoid.translatePolyline
      (ribbonMacrocellOrigin (placement.position first.1.1))
  have dataEqual :
      sourceVariableRibbonFanData planar first =
        sourceVariableRibbonFanData planar second :=
    VariableRibbonFanData.sourceVariableRibbonFanData_eq_of_same_atom
      planar first second sameAtom
  simpa [occurrenceCoordinatedRibbonVariableStub,
    planar, data, firstSlot, secondSlot, sameAtom, dataEqual] using
      translatedAvoid

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
