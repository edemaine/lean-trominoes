import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplit
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedTerminalDirectionOrder

/-!
# Finite retained angular direction profiles

The local fixed-eight adapter should depend only on the terminal directions
seen around one source variable, not on the surrounding SAT construction.
This file packages exactly that finite interface.

A total extractor reads the direction component of the retained terminal
classifier, with an irrelevant east fallback off the certified domain.  It
maps an angular occurrence list to a direction list and proves that, for the
final retained source, this list is sorted by the explicit eleven-direction
rank.  Supplying the already-established eight-slot bound yields a compact
`RetainedAngularDirectionProfile` for local geometric construction.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Total direction projection from the retained terminal classifier.  The
east fallback is used only for malformed vectors; certified retained
terminal rays always take the successful branch. -/
def classifiedRetainedTerminalDirection
    (vector : Cell) : RetainedTerminalDirection :=
  match retainedTerminalDirectionClassify vector with
  | some (direction, _length) => direction
  | none => .compass .east

/-- A successful classification determines the total direction projection
exactly. -/
theorem classifiedRetainedTerminalDirection_eq_of_classified
    {vector : Cell}
    {direction : RetainedTerminalDirection}
    {length : Nat}
    (classified :
      retainedTerminalDirectionClassify vector =
        some (direction, length)) :
    classifiedRetainedTerminalDirection vector = direction := by
  simp [classifiedRetainedTerminalDirection, classified]

/-- Directions read from an angular occurrence list, in that list's
presentation order. -/
def angularRetainedTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    List RetainedTerminalDirection :=
  (angularOccurrenceVariables source routes atom).map
    fun occurrence =>
      classifiedRetainedTerminalDirection
        (occurrenceTerminalVector routes occurrence)

@[simp]
theorem angularRetainedTerminalDirections_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (angularRetainedTerminalDirections
      source routes atom).length =
      (angularOccurrenceVariables
        source routes atom).length := by
  simp [angularRetainedTerminalDirections]

@[simp]
theorem angularRetainedTerminalDirections_getElem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (index : Nat)
    (indexLt :
      index <
        (angularOccurrenceVariables
          source routes atom).length) :
    (angularRetainedTerminalDirections
      source routes atom)[index]'(by
        simpa [angularRetainedTerminalDirections]
          using indexLt) =
      classifiedRetainedTerminalDirection
        (occurrenceTerminalVector routes
          (angularOccurrenceVariables
            source routes atom)[index]) := by
  simp [angularRetainedTerminalDirections]

/-- The finite local data required by an order-preserving retained-ray
adapter. -/
structure RetainedAngularDirectionProfile where
  directions : List RetainedTerminalDirection
  rankSorted :
    directions.Pairwise fun first second =>
      first.angularRank ≤ second.angularRank
  fitsEight : directions.length ≤ 8

/-- Every syntactically genuine occurrence uses one of the retained
terminal rays. -/
def RetainedOccurrenceTerminalCertificate
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : Prop :=
  ∀ atom copy,
    copy ∈ occurrenceVariables source atom →
      RetainedTerminalRayVector
        (occurrenceTerminalVector routes copy)

/-- Every indexed angular direction under a retained occurrence certificate
keeps an exact positive-length classification of its occurrence vector. -/
theorem angularRetainedTerminalDirections_getElem_classified
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (atom : Variable) (index : Nat)
    (indexLt :
      index <
        (angularOccurrenceVariables
          source routes atom).length) :
    ∃ length : Nat,
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes
            (angularOccurrenceVariables
              source routes atom)[index]) =
        some
          ((angularRetainedTerminalDirections
            source routes atom)[index]'(by
              simpa [angularRetainedTerminalDirections]
                using indexLt), length) := by
  have angularMember :
      (angularOccurrenceVariables
        source routes atom)[index] ∈
          angularOccurrenceVariables source routes atom :=
    List.getElem_mem indexLt
  have occurrenceMember :
      (angularOccurrenceVariables
        source routes atom)[index] ∈
          occurrenceVariables source atom :=
    (angularOccurrenceVariables_perm
      source routes atom).mem_iff.mp angularMember
  have retained :=
    certificate atom
      (angularOccurrenceVariables
        source routes atom)[index]
      occurrenceMember
  have classifiedSome :
      (retainedTerminalDirectionClassify
        (occurrenceTerminalVector routes
          (angularOccurrenceVariables
            source routes atom)[index])).isSome :=
    (retainedTerminalDirectionClassify_isSome_iff _).2
      retained
  rcases Option.isSome_iff_exists.mp classifiedSome with
    ⟨classified, classifiedEq⟩
  have projected :=
    classifiedRetainedTerminalDirection_eq_of_classified
      classifiedEq
  have directionsIndexLt :
      index <
        (angularRetainedTerminalDirections
          source routes atom).length := by
    simpa [angularRetainedTerminalDirections] using
      indexLt
  have directionAt :
      (angularRetainedTerminalDirections
        source routes atom)[index]'directionsIndexLt =
          classified.1 := by
    rw [angularRetainedTerminalDirections_getElem
      source routes atom index indexLt]
    exact projected
  refine ⟨classified.2, ?_⟩
  rw [directionAt]
  exact classifiedEq

/-- Angular sorting plus retained classification makes the extracted finite
direction list nondecreasing by rank. -/
theorem angularRetainedTerminalDirections_rankSorted
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (atom : Variable) :
    (angularRetainedTerminalDirections
      source routes atom).Pairwise fun first second =>
        first.angularRank ≤ second.angularRank := by
  rw [List.pairwise_iff_getElem]
  intro first second firstLt secondLt before
  have firstAngularLt :
      first <
        (angularOccurrenceVariables
          source routes atom).length := by
    simpa [angularRetainedTerminalDirections] using
      firstLt
  have secondAngularLt :
      second <
        (angularOccurrenceVariables
          source routes atom).length := by
    simpa [angularRetainedTerminalDirections] using
      secondLt
  rcases
      angularRetainedTerminalDirections_getElem_classified
        source routes certificate atom first firstAngularLt with
    ⟨firstLength, firstClassified⟩
  rcases
      angularRetainedTerminalDirections_getElem_classified
        source routes certificate atom second secondAngularLt with
    ⟨secondLength, secondClassified⟩
  have ordered :
      occurrenceAngleLE routes
          (angularOccurrenceVariables
            source routes atom)[first]
          (angularOccurrenceVariables
            source routes atom)[second] =
        true :=
    angularOccurrenceVariables_getElem_angleLE
      source routes atom first second
      firstAngularLt secondAngularLt before
  exact
    occurrenceAngleLE_rank_le_of_classified
      routes
      (angularOccurrenceVariables
        source routes atom)[first]
      (angularOccurrenceVariables
        source routes atom)[second]
      firstClassified secondClassified ordered

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- The direction list attached to one variable of the final retained
planar-SAT source. -/
def retainedDrawingAngularTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    List RetainedTerminalDirection :=
  angularRetainedTerminalDirections
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)
    atom

/-- The terminal-ray theorem for final retained incidences, packaged in the
generic occurrence-certificate interface. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    RetainedOccurrenceTerminalCertificate
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula) := by
  intro atom copy copyMember
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalRay
      formula wellFormed degree isLocal clausesNonempty
      atom copy copyMember

/-- The final retained direction list is nondecreasing in the explicit
east-first eleven-direction rank. -/
theorem retainedDrawingAngularTerminalDirections_rankSorted
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    (retainedDrawingAngularTerminalDirections
      formula atom).Pairwise fun first second =>
        first.angularRank ≤ second.angularRank := by
  exact
    angularRetainedTerminalDirections_rankSorted
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        formula wellFormed degree isLocal clausesNonempty)
      atom

/-- The retained SAT construction supplies a complete local direction
profile as soon as its already-proved fixed-eight occurrence bound is
provided. -/
def retainedDrawingAngularDirectionProfile
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (fits :
      FitsEightSlots
        (retainedDrawingAngularOccurrenceOrder formula))
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    RetainedAngularDirectionProfile where
  directions :=
    retainedDrawingAngularTerminalDirections formula atom
  rankSorted :=
    retainedDrawingAngularTerminalDirections_rankSorted
      formula wellFormed degree isLocal clausesNonempty atom
  fitsEight := by
    simpa [retainedDrawingAngularTerminalDirections,
      retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula] using fits atom

end PeriodicOrthocrossing
end LeanTrominoes
