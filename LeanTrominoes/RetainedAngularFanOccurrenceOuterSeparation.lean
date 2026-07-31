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

/-- Any two distinct genuine occurrences of one variable select strictly
separated complete outer-fan routes; the angular list itself chooses the
orientation used by the ordered theorem. -/
theorem retainedOccurrenceOuterCompleteRoutes_strictlyAvoid_of_ne
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
    (different : first ≠ second)
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
  let ordered :=
    angularOccurrenceVariables source routes atom
  have firstOrdered : first ∈ ordered := by
    exact
      (angularOccurrenceVariables_perm
        source routes atom).mem_iff.mpr firstMember
  have secondOrdered : second ∈ ordered := by
    exact
      (angularOccurrenceVariables_perm
        source routes atom).mem_iff.mpr secondMember
  have indicesDifferent :
      ordered.idxOf first ≠ ordered.idxOf second := by
    intro equal
    apply different
    exact
      idxOf_injective_on ordered
        firstOrdered secondOrdered equal
  rcases lt_or_gt_of_ne indicesDifferent with before | after
  · exact
      retainedOccurrenceOuterCompleteRoutes_strictlyAvoid
        source routes retained vectorsInjective fits
        atom first second firstMember secondMember
        (by simpa [ordered] using before) center
  · exact
      (retainedOccurrenceOuterCompleteRoutes_strictlyAvoid
        source routes retained vectorsInjective fits
        atom second first secondMember firstMember
        (by simpa [ordered] using after) center).symm

/-- Positive source refinement preserves the complete outer-fan separation
selected by two ordered genuine occurrences. -/
theorem retainedOccurrenceScaledOuterCompleteRoutes_strictlyAvoid
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
    {factor : Nat} (factorPositive : 0 < factor)
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
        (scaleRetainedTerminalData factor
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes first)))
        (retainedAngularTerminalSlot
          source routes fits atom first firstMember))
      (retainedTerminalFanOuterCompleteRoute center
        (scaleRetainedTerminalData factor
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes second)))
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
  let firstTerminal :=
    classifiedRetainedTerminalData
      (occurrenceTerminalVector routes first)
  let secondTerminal :=
    classifiedRetainedTerminalData
      (occurrenceTerminalVector routes second)
  have distinct : profile.GatesDistinct := by
    exact retainedAngularTerminalProfile_gatesDistinct
      source routes retained vectorsInjective fits atom
  have scaledDistinct :
      (profile.scale factor factorPositive).GatesDistinct :=
    profile.scale_gatesDistinct
      factor factorPositive distinct
  have firstLookup :
      profile.terminals[firstSlot.val]? =
        some firstTerminal := by
    exact retainedAngularTerminalProfile_getElem_slot
      source routes retained fits atom first firstMember
  have secondLookup :
      profile.terminals[secondSlot.val]? =
        some secondTerminal := by
    exact retainedAngularTerminalProfile_getElem_slot
      source routes retained fits atom second secondMember
  have firstScaledLookup :
      (profile.scale factor
        factorPositive).terminals[firstSlot.val]? =
          some
            (scaleRetainedTerminalData
              factor firstTerminal) := by
    simp [RetainedAngularTerminalProfile.scale_terminals,
      firstLookup]
  have secondScaledLookup :
      (profile.scale factor
        factorPositive).terminals[secondSlot.val]? =
          some
            (scaleRetainedTerminalData
              factor secondTerminal) := by
    simp [RetainedAngularTerminalProfile.scale_terminals,
      secondLookup]
  apply
    (profile.scale factor
      factorPositive).outerCompleteRoutes_strictlyAvoid
        scaledDistinct center firstSlot secondSlot
        (scaleRetainedTerminalData factor firstTerminal)
        (scaleRetainedTerminalData factor secondTerminal)
        firstScaledLookup secondScaledLookup
  simpa [firstSlot, secondSlot] using before

/-- Positive source refinement preserves order-free complete outer-fan
separation for any two distinct genuine occurrences of one variable. -/
theorem retainedOccurrenceScaledOuterCompleteRoutes_strictlyAvoid_of_ne
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
    {factor : Nat} (factorPositive : 0 < factor)
    (atom : Variable)
    (first second : ThreeOccurrenceVariable Variable)
    (firstMember : first ∈ occurrenceVariables source atom)
    (secondMember : second ∈ occurrenceVariables source atom)
    (different : first ≠ second)
    (center : Cell) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute center
        (scaleRetainedTerminalData factor
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes first)))
        (retainedAngularTerminalSlot
          source routes fits atom first firstMember))
      (retainedTerminalFanOuterCompleteRoute center
        (scaleRetainedTerminalData factor
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes second)))
        (retainedAngularTerminalSlot
          source routes fits atom second secondMember)) := by
  let ordered :=
    angularOccurrenceVariables source routes atom
  have firstOrdered : first ∈ ordered := by
    exact
      (angularOccurrenceVariables_perm
        source routes atom).mem_iff.mpr firstMember
  have secondOrdered : second ∈ ordered := by
    exact
      (angularOccurrenceVariables_perm
        source routes atom).mem_iff.mpr secondMember
  have indicesDifferent :
      ordered.idxOf first ≠ ordered.idxOf second := by
    intro equal
    apply different
    exact
      idxOf_injective_on ordered
        firstOrdered secondOrdered equal
  rcases lt_or_gt_of_ne indicesDifferent with before | after
  · exact
      retainedOccurrenceScaledOuterCompleteRoutes_strictlyAvoid
        source routes retained vectorsInjective fits factorPositive
        atom first second firstMember secondMember
        (by simpa [ordered] using before) center
  · exact
      (retainedOccurrenceScaledOuterCompleteRoutes_strictlyAvoid
        source routes retained vectorsInjective fits factorPositive
        atom second first secondMember firstMember
        (by simpa [ordered] using after) center).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
