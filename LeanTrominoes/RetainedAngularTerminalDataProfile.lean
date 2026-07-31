import LeanTrominoes.RetainedAngularDirectionProfile

/-!
# Length-aware retained angular terminal profiles

Figure 8(b) intentionally contains angular ties: distinct incidences can
approach one variable on the same retained ray.  A direction-only profile
therefore does not contain enough information to choose distinct splice
points.  The angular occurrence order resolves such ties canonically from
the variable endpoint outward.

This file retains the positive primitive-block length returned by the exact
terminal classifier.  The resulting local profile records an ordered list of
`(direction, length)` pairs, proves nondecreasing direction ranks, proves
nondecreasing lengths inside each tied direction block, proves every length
positive, and retains the eight-slot bound.  Its natural splice point is the
beginning of the final source segment, at the classified radial distance
from the common variable endpoint.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Exact finite data carried by one retained terminal ray. -/
abbrev RetainedTerminalData :=
  RetainedTerminalDirection × Nat

/-- Total projection of the retained classifier, with an irrelevant
positive east fallback outside the certified domain. -/
def classifiedRetainedTerminalData
    (vector : Cell) : RetainedTerminalData :=
  (retainedTerminalDirectionClassify vector).getD
    (.compass .east, 1)

/-- Successful classification determines the total length-aware projection
exactly. -/
theorem classifiedRetainedTerminalData_eq_of_classified
    {vector : Cell}
    {direction : RetainedTerminalDirection}
    {length : Nat}
    (classified :
      retainedTerminalDirectionClassify vector =
        some (direction, length)) :
    classifiedRetainedTerminalData vector =
      (direction, length) := by
  simp [classifiedRetainedTerminalData, classified]

/-- On every certified retained terminal ray, the total length-aware
projection is classified back to exactly itself. -/
theorem retainedTerminalDirectionClassify_classifiedRetainedTerminalData
    {vector : Cell}
    (retained : RetainedTerminalRayVector vector) :
    retainedTerminalDirectionClassify vector =
      some (classifiedRetainedTerminalData vector) := by
  have classifiedSome :
      (retainedTerminalDirectionClassify vector).isSome :=
    (retainedTerminalDirectionClassify_isSome_iff vector).2
      retained
  rcases Option.isSome_iff_exists.mp classifiedSome with
    ⟨terminal, classified⟩
  rw [classifiedRetainedTerminalData_eq_of_classified classified]
  exact classified

/-- The total terminal-data projection has positive length on every
retained terminal ray. -/
theorem classifiedRetainedTerminalData_length_positive
    {vector : Cell}
    (retained : RetainedTerminalRayVector vector) :
    0 < (classifiedRetainedTerminalData vector).2 := by
  have classified :=
    retainedTerminalDirectionClassify_classifiedRetainedTerminalData
      retained
  exact (retainedTerminalDirectionClassify_sound classified).1

@[simp]
theorem classifiedRetainedTerminalData_fst
    (vector : Cell) :
    (classifiedRetainedTerminalData vector).1 =
      classifiedRetainedTerminalDirection vector := by
  unfold classifiedRetainedTerminalData
    classifiedRetainedTerminalDirection
  cases retainedTerminalDirectionClassify vector <;>
    rfl

/-- Length-aware terminal data in angular occurrence-list order. -/
def angularRetainedTerminalData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    List RetainedTerminalData :=
  (angularOccurrenceVariables source routes atom).map
    fun occurrence =>
      classifiedRetainedTerminalData
        (occurrenceTerminalVector routes occurrence)

@[simp]
theorem angularRetainedTerminalData_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (angularRetainedTerminalData source routes atom).length =
      (angularOccurrenceVariables source routes atom).length := by
  simp [angularRetainedTerminalData]

@[simp]
theorem angularRetainedTerminalData_getElem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (index : Nat)
    (indexLt :
      index <
        (angularOccurrenceVariables
          source routes atom).length) :
    (angularRetainedTerminalData
      source routes atom)[index]'(by
        simpa [angularRetainedTerminalData] using indexLt) =
      classifiedRetainedTerminalData
        (occurrenceTerminalVector routes
          (angularOccurrenceVariables
            source routes atom)[index]) := by
  simp [angularRetainedTerminalData]

/-- Forgetting lengths recovers the previously defined direction list. -/
@[simp]
theorem angularRetainedTerminalData_map_fst
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (angularRetainedTerminalData
      source routes atom).map Prod.fst =
        angularRetainedTerminalDirections
          source routes atom := by
  simp [angularRetainedTerminalData,
    angularRetainedTerminalDirections, List.map_map,
    Function.comp_def]

/-- Every indexed length-aware datum under a retained occurrence
certificate is the exact output of the terminal classifier. -/
theorem angularRetainedTerminalData_getElem_classified
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
    retainedTerminalDirectionClassify
        (occurrenceTerminalVector routes
          (angularOccurrenceVariables
            source routes atom)[index]) =
      some
        ((angularRetainedTerminalData
          source routes atom)[index]'(by
            simpa [angularRetainedTerminalData]
              using indexLt)) := by
  rcases
      angularRetainedTerminalDirections_getElem_classified
        source routes certificate atom index indexLt with
    ⟨length, classified⟩
  have dataIndexLt :
      index <
        (angularRetainedTerminalData
          source routes atom).length := by
    simpa [angularRetainedTerminalData] using
      indexLt
  have directionIndexLt :
      index <
        (angularRetainedTerminalDirections
          source routes atom).length := by
    simpa [angularRetainedTerminalDirections] using
      indexLt
  have dataAt :
      (angularRetainedTerminalData
        source routes atom)[index]'dataIndexLt =
          ((angularRetainedTerminalDirections
            source routes atom)[index]'directionIndexLt,
            length) := by
    rw [angularRetainedTerminalData_getElem
      source routes atom index indexLt]
    exact
      classifiedRetainedTerminalData_eq_of_classified
        classified
  rw [dataAt]
  exact classified

/-- Complete finite input for a local length-aware retained-ray adapter. -/
structure RetainedAngularTerminalProfile where
  terminals : List RetainedTerminalData
  rankSorted :
    terminals.Pairwise fun first second =>
      first.1.angularRank ≤ second.1.angularRank
  tiesRadiallySorted :
    terminals.Pairwise fun first second =>
      first.1 = second.1 → first.2 ≤ second.2
  lengthsPositive :
    ∀ terminal ∈ terminals, 0 < terminal.2
  fitsEight : terminals.length ≤ 8

/-- A retained occurrence certificate and an eight-slot bound assemble the
complete length-aware local profile. -/
def retainedAngularTerminalProfile
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source routes))
    (atom : Variable) :
    RetainedAngularTerminalProfile where
  terminals :=
    angularRetainedTerminalData source routes atom
  rankSorted := by
    have directionsSorted :=
      angularRetainedTerminalDirections_rankSorted
        source routes certificate atom
    rw [← angularRetainedTerminalData_map_fst]
      at directionsSorted
    rw [List.pairwise_map] at directionsSorted
    exact directionsSorted
  tiesRadiallySorted := by
    rw [List.pairwise_iff_getElem]
    intro first second firstLt secondLt before
      directionsEqual
    have firstAngularLt :
        first <
          (angularOccurrenceVariables
            source routes atom).length := by
      simpa [angularRetainedTerminalData] using firstLt
    have secondAngularLt :
        second <
          (angularOccurrenceVariables
            source routes atom).length := by
      simpa [angularRetainedTerminalData] using secondLt
    have firstClassified :=
      angularRetainedTerminalData_getElem_classified
        source routes certificate atom first firstAngularLt
    have secondClassified :=
      angularRetainedTerminalData_getElem_classified
        source routes certificate atom second secondAngularLt
    generalize firstDataEq :
        (angularRetainedTerminalData
          source routes atom)[first]'firstLt =
            firstData at firstClassified directionsEqual ⊢
    generalize secondDataEq :
        (angularRetainedTerminalData
          source routes atom)[second]'secondLt =
            secondData at secondClassified directionsEqual ⊢
    rcases firstData with ⟨firstDirection, firstLength⟩
    rcases secondData with ⟨secondDirection, secondLength⟩
    simp only at directionsEqual ⊢
    subst secondDirection
    apply
      (occurrenceAngleLE_iff_length_le_of_same_direction_classified
        routes
        (angularOccurrenceVariables
          source routes atom)[first]
        (angularOccurrenceVariables
          source routes atom)[second]
        firstClassified secondClassified).mp
    exact
      angularOccurrenceVariables_getElem_angleLE
        source routes atom first second
        firstAngularLt secondAngularLt before
  lengthsPositive := by
    intro terminal terminalMember
    rcases List.mem_iff_getElem.mp terminalMember with
      ⟨index, indexLt, rfl⟩
    have angularIndexLt :
        index <
          (angularOccurrenceVariables
            source routes atom).length := by
      simpa [angularRetainedTerminalData] using
        indexLt
    have classified :=
      angularRetainedTerminalData_getElem_classified
        source routes certificate atom index angularIndexLt
    exact
      (retainedTerminalDirectionClassify_sound
        classified).1
  fitsEight := by
    simpa [angularRetainedTerminalData] using fits atom

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- Length-aware local terminal data for one variable of the final retained
planar-SAT source. -/
def retainedDrawingAngularTerminalProfile
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
    RetainedAngularTerminalProfile :=
  retainedAngularTerminalProfile
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
      formula wellFormed degree isLocal clausesNonempty)
    (by
      simpa [retainedDrawingAngularOccurrenceOrder,
        retainedPlanarSATFormula] using fits)
    atom

end PeriodicOrthocrossing
end LeanTrominoes
