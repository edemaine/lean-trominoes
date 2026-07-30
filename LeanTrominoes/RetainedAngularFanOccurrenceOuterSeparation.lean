import LeanTrominoes.RetainedAngularFanOuterCompleteSeparation
import LeanTrominoes.RetainedAngularTerminalGateDistinctness
import LeanTrominoes.RetainedAngularTerminalSlotLookup

/-!
# Outer-fan separation for genuine retained occurrences

The finite outer-fan theorem is phrased in terms of profile slots.  Source
incidences are instead named by their occurrence triples.  This file bridges
those interfaces and proves that two occurrences appearing in strict angular
order select strictly separated replacement suffixes.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Earlier genuine occurrences in one variable's angular list select
strictly separated complete outer-fan replacement routes. -/
theorem retainedOccurrenceOuterCompleteRoutes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (retained :
      RetainedOccurrenceTerminalCertificate source routes)
    (vectorsInjective :
      RetainedOccurrenceTerminalVectorsInjective source routes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source routes))
    (atom : Variable)
    (first second : ThreeOccurrenceVariable Variable)
    (firstMember : first ∈ occurrenceVariables source atom)
    (secondMember : second ∈ occurrenceVariables source atom)
    (before :
      (angularOccurrenceVariables source routes atom).idxOf first <
        (angularOccurrenceVariables source routes atom).idxOf second)
    (center : Cell) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute center
        (classifiedRetainedTerminalData
          (occurrenceTerminalVector routes first))
        (retainedAngularTerminalSlot
          source routes fits atom first firstMember))
      (retainedTerminalFanOuterCompleteRoute center
        (classifiedRetainedTerminalData
          (occurrenceTerminalVector routes second))
        (retainedAngularTerminalSlot
          source routes fits atom second secondMember)) := by
  let profile :=
    retainedAngularTerminalProfile
      source routes retained fits atom
  let firstSlot :=
    retainedAngularTerminalSlot
      source routes fits atom first firstMember
  let secondSlot :=
    retainedAngularTerminalSlot
      source routes fits atom second secondMember
  have distinct : profile.GatesDistinct := by
    exact retainedAngularTerminalProfile_gatesDistinct
      source routes retained vectorsInjective fits atom
  have firstLookup :
      profile.terminals[firstSlot.val]? =
        some
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes first)) := by
    exact retainedAngularTerminalProfile_getElem_slot
      source routes retained fits atom first firstMember
  have secondLookup :
      profile.terminals[secondSlot.val]? =
        some
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes second)) := by
    exact retainedAngularTerminalProfile_getElem_slot
      source routes retained fits atom second secondMember
  apply profile.outerCompleteRoutes_strictlyAvoid
    distinct center firstSlot secondSlot
    (classifiedRetainedTerminalData
      (occurrenceTerminalVector routes first))
    (classifiedRetainedTerminalData
      (occurrenceTerminalVector routes second))
    firstLookup secondLookup
  simpa [firstSlot, secondSlot] using before

end PeriodicEightOccurrenceSplit
end LeanTrominoes
