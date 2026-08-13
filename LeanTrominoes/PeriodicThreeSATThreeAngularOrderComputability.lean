/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularPorts
import LeanTrominoes.PeriodicEightOccurrenceSplitComputability
import LeanTrominoes.PeriodicGridDrawingComputability
import LeanTrominoes.PeriodicThreeSATThreeAngularOrderSorted
import LeanTrominoes.PrimrecListSort

/-!
# Computability of angular occurrence orders

Terminal vectors, their angular-radial comparison, stable occurrence sorting,
and the resulting east-first fixed-eight compass-port lookup are primitive
recursive from a primitive-recursive finite source formula and incidence-route
lookup.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeSATThree

theorem routeTerminalVector_primrec : Primrec routeTerminalVector := by
  have lastSegment : Primrec fun route : List Cell =>
      (gridPolylineSegments route).getLast? := by
    exact (Primrec.list_head?.comp
      (Primrec.list_reverse.comp gridPolylineSegments_primrec)).of_eq
        fun route => by simp
  have fallback : Primrec fun _route : List Cell => ((0, 0) : Cell) :=
    Primrec.const (0, 0)
  have selected : Primrec₂ fun (_route : List Cell)
      (segment : GridSegment) =>
      Cell.sub segment.start segment.finish := by
    exact Computability.cell_sub_primrec.comp₂
      (GridSegment.start_primrec.comp₂ Primrec₂.right)
      (GridSegment.finish_primrec.comp₂ Primrec₂.right)
  exact (Primrec.option_casesOn lastSegment fallback selected).of_eq
    fun route => by
      simp only [routeTerminalVector]
      cases (gridPolylineSegments route).getLast? <;> rfl

theorem terminalVectorUpperHalf_primrec :
    Primrec terminalVectorUpperHalf := by
  have positiveY : PrimrecPred fun vector : Cell => 0 < vector.2 :=
    Computability.int_lt_primrec.comp
      (Primrec.const (0 : Int)) Primrec.snd
  have zeroY : PrimrecPred fun vector : Cell => vector.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const (0 : Int))
  have nonnegativeX : PrimrecPred fun vector : Cell => 0 ≤ vector.1 :=
    Computability.int_le_primrec.comp
      (Primrec.const (0 : Int)) Primrec.fst
  exact (positiveY.or (zeroY.and nonnegativeX)).decide.of_eq
    fun _ => by simp [terminalVectorUpperHalf]

theorem terminalVectorCross_primrec :
    Primrec₂ terminalVectorCross := by
  have firstProduct : Primrec fun input : Cell × Cell =>
      input.1.1 * input.2.2 :=
    Computability.int_multiply_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have secondProduct : Primrec fun input : Cell × Cell =>
      input.1.2 * input.2.1 :=
    Computability.int_multiply_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  exact Computability.int_subtract_primrec.comp
    firstProduct secondProduct

theorem terminalVectorAngleLE_primrec :
    Primrec₂ terminalVectorAngleLE := by
  change Primrec fun input : Cell × Cell =>
    terminalVectorAngleLE input.1 input.2
  have firstZero : Primrec fun input : Cell × Cell =>
      decide (input.1 = (0, 0)) :=
    (Primrec.eq.comp Primrec.fst
      (Primrec.const ((0, 0) : Cell))).decide
  have secondZero : Primrec fun input : Cell × Cell =>
      decide (input.2 = (0, 0)) :=
    (Primrec.eq.comp Primrec.snd
      (Primrec.const ((0, 0) : Cell))).decide
  have firstUpper : Primrec fun input : Cell × Cell =>
      terminalVectorUpperHalf input.1 :=
    terminalVectorUpperHalf_primrec.comp Primrec.fst
  have secondUpper : Primrec fun input : Cell × Cell =>
      terminalVectorUpperHalf input.2 :=
    terminalVectorUpperHalf_primrec.comp Primrec.snd
  have crossNonnegative : Primrec fun input : Cell × Cell =>
      decide (0 ≤ terminalVectorCross input.1 input.2) :=
    (Computability.int_le_primrec.comp
      (Primrec.const (0 : Int)) terminalVectorCross_primrec).decide
  exact (Primrec.cond firstZero secondZero
    (Primrec.cond secondZero (Primrec.const true)
      (Primrec.cond firstUpper
        (Primrec.cond secondUpper crossNonnegative (Primrec.const true))
        (Primrec.cond secondUpper (Primrec.const false)
          crossNonnegative)))).of_eq fun input => by
      simp [terminalVectorAngleLE, Bool.cond_eq_ite]

theorem terminalVectorRadiusSq_primrec :
    Primrec terminalVectorRadiusSq := by
  have xSquare : Primrec fun vector : Cell => vector.1 * vector.1 :=
    Computability.int_multiply_primrec.comp Primrec.fst Primrec.fst
  have ySquare : Primrec fun vector : Cell => vector.2 * vector.2 :=
    Computability.int_multiply_primrec.comp Primrec.snd Primrec.snd
  exact Computability.int_add_primrec.comp xSquare ySquare

theorem terminalVectorAngleRadialLE_primrec :
    Primrec₂ terminalVectorAngleRadialLE := by
  change Primrec fun input : Cell × Cell =>
    terminalVectorAngleRadialLE input.1 input.2
  have forward : Primrec fun input : Cell × Cell =>
      terminalVectorAngleLE input.1 input.2 :=
    terminalVectorAngleLE_primrec
  have reverse : Primrec fun input : Cell × Cell =>
      terminalVectorAngleLE input.2 input.1 :=
    terminalVectorAngleLE_primrec.comp Primrec.snd Primrec.fst
  have forwardPred : PrimrecPred fun input : Cell × Cell =>
      terminalVectorAngleLE input.1 input.2 = true :=
    Primrec.eq.comp forward (Primrec.const true)
  have reversePred : PrimrecPred fun input : Cell × Cell =>
      terminalVectorAngleLE input.2 input.1 = true :=
    Primrec.eq.comp reverse (Primrec.const true)
  have radiusLE : PrimrecPred fun input : Cell × Cell =>
      terminalVectorRadiusSq input.1 ≤
        terminalVectorRadiusSq input.2 :=
    Computability.int_le_primrec.comp
      (terminalVectorRadiusSq_primrec.comp Primrec.fst)
      (terminalVectorRadiusSq_primrec.comp Primrec.snd)
  exact (forwardPred.and (reversePred.not.or radiusLE)).decide.of_eq
    fun input => by
      simp [terminalVectorAngleRadialLE]

theorem occurrenceTerminalVector_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : Input × ThreeOccurrenceVariable Variable =>
      occurrenceTerminalVector (routes input.1) input.2 := by
  have route : Primrec fun input :
      Input × ThreeOccurrenceVariable Variable =>
      routes input.1 input.2.2.1 input.2.2.2 :=
    routesPrimrec.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact (routeTerminalVector_primrec.comp route).of_eq fun _ => rfl

theorem occurrenceAngleLE_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input :
        (Input × ThreeOccurrenceVariable Variable) ×
          ThreeOccurrenceVariable Variable =>
      occurrenceAngleLE (routes input.1.1) input.1.2 input.2 := by
  have first : Primrec fun input :
      (Input × ThreeOccurrenceVariable Variable) ×
        ThreeOccurrenceVariable Variable =>
      occurrenceTerminalVector (routes input.1.1) input.1.2 :=
    occurrenceTerminalVector_primrec routes routesPrimrec |>.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst))
  have second : Primrec fun input :
      (Input × ThreeOccurrenceVariable Variable) ×
        ThreeOccurrenceVariable Variable =>
      occurrenceTerminalVector (routes input.1.1) input.2 :=
    occurrenceTerminalVector_primrec routes routesPrimrec |>.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (terminalVectorAngleRadialLE_primrec.comp
    first second).of_eq fun _ => rfl

theorem angularOccurrenceVariables_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : Input × Variable =>
      angularOccurrenceVariables
        (source input.1) (routes input.1) input.2 := by
  let SortInput := Input × Variable
  let Copy := ThreeOccurrenceVariable Variable
  let items : SortInput → List Copy := fun input =>
    occurrenceVariables (source input.1) input.2
  let lessEq : SortInput → Copy → Copy → Bool := fun input =>
    occurrenceAngleLE (routes input.1)
  have itemsPrimrec : Primrec items :=
    PeriodicThreeSATThree.occurrenceVariables_primrec.comp
      (sourcePrimrec.comp Primrec.fst) Primrec.snd
  have lessEqPrimrec : Primrec fun input :
      (SortInput × Copy) × Copy =>
      lessEq input.1.1 input.1.2 input.2 := by
    exact occurrenceAngleLE_primrec routes routesPrimrec |>.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have sorted := Computability.boolStableSort_primrec
    items lessEq itemsPrimrec lessEqPrimrec
  exact sorted.of_eq fun input => by
    exact Computability.boolStableSort_eq_mergeSort
      (lessEq input)
      (occurrenceAngleLE_transitive (routes input.1))
      (occurrenceAngleLE_total (routes input.1))
      (items input)

end PeriodicThreeSATThree

namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

private theorem occurrence_idxOf_decidableEq_eq
    {Variable : Type*} [DecidableEq Variable]
    (item : ThreeOccurrenceVariable Variable)
    (items : List (ThreeOccurrenceVariable Variable)) :
    @List.idxOf (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq item items =
      items.idxOf item := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite,
        beq_iff_eq]
      rw [induction]

theorem angularPortOfIndex_primrec : Primrec angularPortOfIndex := by
  let portList : List Port :=
    [.east, .southeast, .south, .southwest, .west,
      .northwest, .north, .northeast]
  have implementation : Primrec fun index : Nat =>
      portList.getD index .northeast :=
    (Primrec.list_getD (.northeast : Port)).comp
      (Primrec.const portList) Primrec.id
  exact implementation.of_eq fun index => by
    unfold portList
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index <;> rfl

theorem literalAt_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      literalAt input.1.1 input.1.2 input.2 := by
  have clause : Primrec fun input :
      (PeriodicCNF Variable × Nat) × Nat =>
      input.1.1.clauses[input.1.2]? :=
    Primrec.list_getElem?.comp
      (PeriodicCNF.equivData_primrec.comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have literal : Primrec₂ fun
      (input : (PeriodicCNF Variable × Nat) × Nat)
      (sourceClause : PeriodicClause Variable) =>
      sourceClause[input.2]? := by
    exact Primrec.list_getElem?.comp
      Primrec.snd (Primrec.snd.comp Primrec.fst) |>.to₂
  exact (Primrec.option_bind clause literal).of_eq fun input => by
    simp [literalAt]

theorem angularOccurrencePort_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : Input × ThreeOccurrenceVariable Variable =>
      angularPortOfIndex
        ((angularOccurrenceVariables
          (source input.1) (routes input.1) input.2.1).idxOf input.2) := by
  let Copy := ThreeOccurrenceVariable Variable
  have copies : Primrec fun input :
      Input × Copy =>
      angularOccurrenceVariables
        (source input.1) (routes input.1) input.2.1 :=
    angularOccurrenceVariables_primrec
      source routes sourcePrimrec routesPrimrec |>.comp
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd))
  have computedIndex : Primrec fun input : Input × Copy =>
      @List.idxOf Copy instBEqOfDecidableEq input.2
        (angularOccurrenceVariables
          (source input.1) (routes input.1) input.2.1) :=
    Primrec.list_idxOf.comp Primrec.snd copies
  have index := computedIndex.of_eq fun input =>
    occurrence_idxOf_decidableEq_eq input.2
      (angularOccurrenceVariables
        (source input.1) (routes input.1) input.2.1)
  exact angularPortOfIndex_primrec.comp index

/-- The total port lookup induced by an angular occurrence order is
primitive recursive without encoding the proof-carrying order itself. -/
theorem occurrencePortsOfAngularOrder_port_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      (occurrencePortsOfAngularOrder
        (source input.1.1)
        (angularOccurrenceOrder
          (source input.1.1) (routes input.1.1))).port
        input.1.2 input.2 := by
  let LookupInput := (Input × Nat) × Nat
  have sourceLiteral : Primrec fun input : LookupInput =>
      literalAt (source input.1.1) input.1.2 input.2 :=
    literalAt_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have fallback : Primrec fun _input : LookupInput =>
      (Port.east : Port) := Primrec.const Port.east
  have selected : Primrec₂ fun (input : LookupInput)
      (literal : PeriodicLiteral Variable) =>
      angularPortOfIndex
        ((angularOccurrenceVariables
          (source input.1.1) (routes input.1.1) literal.atom).idxOf
            (literal.atom, input.1.2, input.2)) := by
    change Primrec fun combined :
        LookupInput × PeriodicLiteral Variable =>
      angularPortOfIndex
        ((angularOccurrenceVariables
          (source combined.1.1.1) (routes combined.1.1.1)
            combined.2.atom).idxOf
              (combined.2.atom, combined.1.1.2, combined.1.2))
    have occurrence : Primrec fun combined :
        LookupInput × PeriodicLiteral Variable =>
        (combined.2.atom, combined.1.1.2, combined.1.2) :=
      Primrec.pair
        (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd)
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
    exact angularOccurrencePort_primrec
      source routes sourcePrimrec routesPrimrec |>.comp
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          occurrence) |>.to₂
  exact (Primrec.option_casesOn sourceLiteral fallback selected).of_eq
    fun input => by
      simp only [occurrencePortsOfAngularOrder,
        angularOrderedOccurrencePort, angularOccurrenceOrder_copies]
      cases literalAt (source input.1.1) input.1.2 input.2 <;> rfl

/-- Fixed-eight splitting with the route-induced angular port assignment is
primitive recursive from the finite source and route lookup. -/
theorem angularFormula_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input => PeriodicEightOccurrenceSplit.formula
      (source input)
      (occurrencePortsOfAngularOrder
        (source input)
        (angularOccurrenceOrder (source input) (routes input))) := by
  let ports : Input → Nat → Nat → Port := fun input =>
    (occurrencePortsOfAngularOrder
      (source input)
      (angularOccurrenceOrder (source input) (routes input))).port
  have portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      ports input.1.1 input.1.2 input.2 :=
    occurrencePortsOfAngularOrder_port_primrec
      source routes sourcePrimrec routesPrimrec
  exact PeriodicEightOccurrenceSplit.formula_primrec
    source ports sourcePrimrec portsPrimrec

theorem angularFormula_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Computable fun input => PeriodicEightOccurrenceSplit.formula
      (source input)
      (occurrencePortsOfAngularOrder
        (source input)
        (angularOccurrenceOrder (source input) (routes input))) :=
  (angularFormula_primrec
    source routes sourcePrimrec routesPrimrec).to_comp

end PeriodicEightOccurrenceSplit
end LeanTrominoes
