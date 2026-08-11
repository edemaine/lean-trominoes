import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedOccurrenceRouteComputability

/-!
# Computable copied-clause route lookup

The single-occurrence geometry is primitive recursive.  This module adds the
nested clause/literal presentation lookup and uses a flat product encoding for
selected clauses and literals, so the option dispatch does not expose the
larger structure encodings to Lean's computability normalizer.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

set_option maxHeartbeats 1000000

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Flat data used while dispatching on a selected periodic literal. -/
abbrev AngularLiteralRouteData (Variable : Type*) :=
  Variable × Cell × Bool

/-- Flat data used while dispatching on a selected positioned clause. -/
abbrev AngularClauseRouteData (Variable : Type*) :=
  Cell × List (AngularLiteralRouteData Variable)

def angularLiteralOfRouteData {Variable : Type*}
    (data : AngularLiteralRouteData Variable) : PeriodicLiteral Variable :=
  PeriodicLiteral.equivData.symm data

def angularClauseRouteData {Variable : Type*}
    (clause : PositionedPeriodicClause Variable) :
    AngularClauseRouteData Variable :=
  (clause.position, clause.literals.map PeriodicLiteral.equivData)

def angularClauseOfRouteData {Variable : Type*}
    (data : AngularClauseRouteData Variable) :
    PositionedPeriodicClause Variable :=
  ⟨data.1, data.2.map angularLiteralOfRouteData⟩

@[simp]
theorem angularLiteralOfRouteData_equivData
    {Variable : Type*} (literal : PeriodicLiteral Variable) :
    angularLiteralOfRouteData (PeriodicLiteral.equivData literal) = literal :=
  PeriodicLiteral.equivData.symm_apply_apply literal

@[simp]
theorem angularClauseOfRouteData_routeData
    {Variable : Type*} (clause : PositionedPeriodicClause Variable) :
    angularClauseOfRouteData (angularClauseRouteData clause) = clause := by
  cases clause
  simp [angularClauseOfRouteData, angularClauseRouteData,
    angularLiteralOfRouteData, Function.comp_def, List.map_map]

theorem angularLiteralOfRouteData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@angularLiteralOfRouteData Variable) :=
  PeriodicLiteral.equivData_symm_primrec

theorem angularClauseRouteData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@angularClauseRouteData Variable) := by
  have literals : Primrec fun clause : PositionedPeriodicClause Variable =>
      clause.literals.map PeriodicLiteral.equivData :=
    Primrec.list_map PositionedPeriodicClause.literals_primrec
      (PeriodicLiteral.equivData_primrec.comp Primrec.snd).to₂
  exact Primrec.pair PositionedPeriodicClause.position_primrec literals

theorem angularClauseOfRouteData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@angularClauseOfRouteData Variable) := by
  have literals : Primrec fun data : AngularClauseRouteData Variable =>
      data.2.map angularLiteralOfRouteData :=
    Primrec.list_map Primrec.snd
      (angularLiteralOfRouteData_primrec.comp Primrec.snd).to₂
  exact (PositionedPeriodicClause.mk_primrec.comp
    (Primrec.pair Primrec.fst literals)).of_eq fun _ => rfl

theorem prodAssocRight_primrec
    {First Second Third : Type*}
    [Primcodable First] [Primcodable Second] [Primcodable Third] :
    Primrec fun input : (First × Second) × Third =>
      (input.1.1, (input.1.2, input.2)) :=
  Primrec.pair (Primrec.fst.comp Primrec.fst)
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

/-- Flat input for one already selected copied incidence. -/
abbrev AngularCopiedIncidenceRouteInput (Input Variable : Type*) :=
  (Input × (Nat × Nat)) ×
    (AngularClauseRouteData Variable × AngularLiteralRouteData Variable)

def angularCopiedIncidenceSourcePoint
    {Input Variable : Type*}
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (ports : Input → OccurrencePorts)
    (input : AngularCopiedIncidenceRouteInput Input Variable) : Cell :=
  PositionedPeriodicCNF.canonicalClausePosition
    (placement (sourcePlacement input.1.1))
    (occurrenceClause (ports input.1.1) input.1.2.1
      (angularClauseOfRouteData input.2.1))

def angularCopiedIncidenceFanGeometry
    {Input Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (copies : Input → Variable →
      List (ThreeOccurrenceVariable Variable))
    (input : AngularCopiedIncidenceRouteInput Input Variable) :
    Cell × List Cell :=
  let clause := angularClauseOfRouteData input.2.1
  let literal := angularLiteralOfRouteData input.2.2
  let relative := incidenceRelativeOffset clause literal
  let occurrenceIndex :=
    (copies input.1.1 literal.atom).idxOf
      (indexedOccurrence literal input.1.2.1 input.1.2.2)
  (angularFanBoundaryPositionAt
      (sourcePlacement input.1.1) literal.atom
      relative occurrenceIndex,
    angularFanSpokeRouteAt
      (sourcePlacement input.1.1) literal.atom
      relative occurrenceIndex)

theorem angularCopiedIncidenceSourcePoint_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (ports : Input → OccurrencePorts)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (ports input.1.1).port input.1.2 input.2) :
    Primrec (angularCopiedIncidenceSourcePoint sourcePlacement ports) := by
  let Full := AngularCopiedIncidenceRouteInput Input Variable
  change Primrec fun input : Full =>
    PositionedPeriodicCNF.canonicalClausePosition
      (placement (sourcePlacement input.1.1))
      (occurrenceClause (ports input.1.1) input.1.2.1
        (angularClauseOfRouteData input.2.1))
  have root : Primrec fun input : Full => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have clauseIndex : Primrec fun input : Full => input.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have fullPeriod : Primrec fun input : Full =>
      (sourcePlacement input.1.1).period :=
    periodPrimrec.comp root
  have fullPorts : Primrec fun input : (Full × Nat) × Nat =>
      (ports input.1.1.1.1).port input.1.2 input.2 :=
    portsPrimrec.comp
      (Primrec.pair
        (Primrec.pair
          (root.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have clause : Primrec fun input : Full =>
      angularClauseOfRouteData input.2.1 :=
    angularClauseOfRouteData_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have copiedClause : Primrec fun input : Full =>
      occurrenceClause (ports input.1.1)
        input.1.2.1 (angularClauseOfRouteData input.2.1) :=
    occurrenceClause_primrec
      (fun input => ports input.1.1) fullPorts |>.comp
        (Primrec.pair
          (Primrec.pair Primrec.id clauseIndex) clause)
  have splitPeriod : Primrec fun input : Full =>
      (placement (sourcePlacement input.1.1)).period :=
    placement_period_primrec
      (fun input : Full => sourcePlacement input.1.1) fullPeriod
  exact PositionedPeriodicCNF.canonicalClausePosition_primrec
    (fun input : Full =>
      (placement (sourcePlacement input.1.1)).period)
    splitPeriod |>.comp (Primrec.pair Primrec.id copiedClause)

theorem angularCopiedIncidenceFanGeometry_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (copies : Input → Variable →
      List (ThreeOccurrenceVariable Variable))
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      copies input.1 input.2) :
    Primrec (angularCopiedIncidenceFanGeometry
      sourcePlacement copies) := by
  let Full := AngularCopiedIncidenceRouteInput Input Variable
  change Primrec fun input : Full =>
    let clause := angularClauseOfRouteData input.2.1
    let literal := angularLiteralOfRouteData input.2.2
    let relative := incidenceRelativeOffset clause literal
    let occurrenceIndex :=
      (copies input.1.1 literal.atom).idxOf
        (indexedOccurrence literal input.1.2.1 input.1.2.2)
    (angularFanBoundaryPositionAt
        (sourcePlacement input.1.1) literal.atom
        relative occurrenceIndex,
      angularFanSpokeRouteAt
        (sourcePlacement input.1.1) literal.atom
        relative occurrenceIndex)
  have root : Primrec fun input : Full => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have clauseIndex : Primrec fun input : Full => input.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have literalIndex : Primrec fun input : Full => input.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have fullPeriod : Primrec fun input : Full =>
      (sourcePlacement input.1.1).period :=
    periodPrimrec.comp root
  have fullPosition : Primrec fun input : Full × Variable =>
      (sourcePlacement input.1.1.1).position input.2 :=
    positionPrimrec.comp
      (Primrec.pair (root.comp Primrec.fst) Primrec.snd)
  have fullCopies : Primrec fun input : Full × Variable =>
      copies input.1.1.1 input.2 :=
    copiesPrimrec.comp
      (Primrec.pair (root.comp Primrec.fst) Primrec.snd)
  have clause : Primrec fun input : Full =>
      angularClauseOfRouteData input.2.1 :=
    angularClauseOfRouteData_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have literal : Primrec fun input : Full =>
      angularLiteralOfRouteData input.2.2 :=
    angularLiteralOfRouteData_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  have relative : Primrec fun input : Full =>
      incidenceRelativeOffset
        (angularClauseOfRouteData input.2.1)
        (angularLiteralOfRouteData input.2.2) :=
    incidenceRelativeOffset_primrec.comp (Primrec.pair clause literal)
  have atom : Primrec fun input : Full =>
      (angularLiteralOfRouteData input.2.2).atom :=
    PeriodicThreeCNF.literal_atom_primrec.comp literal
  have copyList : Primrec fun input : Full =>
      copies input.1.1 (angularLiteralOfRouteData input.2.2).atom :=
    fullCopies.comp (Primrec.pair Primrec.id atom)
  have occurrence : Primrec fun input : Full =>
      indexedOccurrence (angularLiteralOfRouteData input.2.2)
        input.1.2.1 input.1.2.2 :=
    Primrec.pair atom (Primrec.pair clauseIndex literalIndex)
  have occurrenceIndex : Primrec fun input : Full =>
      (copies input.1.1
        (angularLiteralOfRouteData input.2.2).atom).idxOf
          (indexedOccurrence (angularLiteralOfRouteData input.2.2)
            input.1.2.1 input.1.2.2) :=
    (Primrec.list_idxOf.comp occurrence copyList).of_eq fun input =>
      occurrence_idxOf_decidableEq_eq
        (indexedOccurrence (angularLiteralOfRouteData input.2.2)
          input.1.2.1 input.1.2.2)
        (copies input.1.1
          (angularLiteralOfRouteData input.2.2).atom)
  have boundaryPoint : Primrec fun input : Full =>
      angularFanBoundaryPositionAt
        (sourcePlacement input.1.1)
        (angularLiteralOfRouteData input.2.2).atom
        (incidenceRelativeOffset
          (angularClauseOfRouteData input.2.1)
          (angularLiteralOfRouteData input.2.2))
        ((copies input.1.1
          (angularLiteralOfRouteData input.2.2).atom).idxOf
            (indexedOccurrence (angularLiteralOfRouteData input.2.2)
              input.1.2.1 input.1.2.2)) :=
    angularFanBoundaryPositionAt_primrec
      (fun input => sourcePlacement input.1.1)
      fullPeriod fullPosition |>.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair Primrec.id atom) relative)
          occurrenceIndex)
  have suffix : Primrec fun input : Full =>
      angularFanSpokeRouteAt
        (sourcePlacement input.1.1)
        (angularLiteralOfRouteData input.2.2).atom
        (incidenceRelativeOffset
          (angularClauseOfRouteData input.2.1)
          (angularLiteralOfRouteData input.2.2))
        ((copies input.1.1
          (angularLiteralOfRouteData input.2.2).atom).idxOf
            (indexedOccurrence (angularLiteralOfRouteData input.2.2)
              input.1.2.1 input.1.2.2)) :=
    angularFanSpokeRouteAt_primrec
      (fun input => sourcePlacement input.1.1)
      fullPeriod fullPosition |>.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair Primrec.id atom) relative)
          occurrenceIndex)
  exact Primrec.pair boundaryPoint suffix

/-- Given flat data for an already selected source clause and literal, the
corresponding copied-incidence route is computable. -/
theorem canonicalAngularCopiedIncidenceSomeLiteral_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (ports : Input → OccurrencePorts)
    (copies : Input → Variable →
      List (ThreeOccurrenceVariable Variable))
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (ports input.1.1).port input.1.2 input.2)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      copies input.1 input.2) :
    Computable₂ fun
        (input : (((Input × Nat) × Nat) ×
          AngularClauseRouteData Variable))
        (literal : AngularLiteralRouteData Variable) =>
      canonicalAngularOccurrenceRouteData
        (sourcePlacement input.1.1.1) (ports input.1.1.1)
        (copies input.1.1.1) (angularClauseOfRouteData input.2)
        (angularLiteralOfRouteData literal) input.1.1.2 input.1.2 := by
  let Full := AngularCopiedIncidenceRouteInput Input Variable
  let Packed := ((((Input × Nat) × Nat) ×
    AngularClauseRouteData Variable) × AngularLiteralRouteData Variable)
  let Stage := ((Input × Nat) × Nat) ×
    (AngularClauseRouteData Variable × AngularLiteralRouteData Variable)
  change Computable fun input : Packed =>
    canonicalAngularOccurrenceRouteData
      (sourcePlacement input.1.1.1.1)
      (ports input.1.1.1.1) (copies input.1.1.1.1)
      (angularClauseOfRouteData input.1.2)
      (angularLiteralOfRouteData input.2)
      input.1.1.1.2 input.1.1.2
  have gatherIncidence : Primrec fun input : Packed =>
      (input.1.1, (input.1.2, input.2)) :=
    prodAssocRight_primrec
  have gatherIndices : Primrec fun input : (Input × Nat) × Nat =>
      (input.1.1, (input.1.2, input.2)) :=
    prodAssocRight_primrec
  have balance : Primrec fun input : Stage =>
      ((input.1.1.1, (input.1.1.2, input.1.2)), input.2) :=
    Primrec.pair (gatherIndices.comp Primrec.fst) Primrec.snd
  have pack : Primrec fun input : Packed =>
      ((input.1.1.1.1, (input.1.1.1.2, input.1.1.2)),
        (input.1.2, input.2)) :=
    balance.comp gatherIncidence
  have sourcePoint := angularCopiedIncidenceSourcePoint_primrec
    sourcePlacement ports periodPrimrec portsPrimrec
  have fan := angularCopiedIncidenceFanGeometry_primrec
    sourcePlacement copies periodPrimrec positionPrimrec copiesPrimrec
  have routePrefix : Primrec fun input : Full =>
      PositionedPeriodicCNF.orthogonalDetour
        (angularCopiedIncidenceSourcePoint sourcePlacement ports input)
        (angularCopiedIncidenceFanGeometry
          sourcePlacement copies input).1 :=
    PositionedPeriodicCNF.orthogonalDetour_primrec.comp
      sourcePoint (Primrec.fst.comp fan)
  have route : Primrec fun input : Full =>
      joinAtEndpoint
        (PositionedPeriodicCNF.orthogonalDetour
          (angularCopiedIncidenceSourcePoint sourcePlacement ports input)
          (angularCopiedIncidenceFanGeometry
            sourcePlacement copies input).1)
        (angularCopiedIncidenceFanGeometry
          sourcePlacement copies input).2 :=
    joinAtEndpoint_primrec _ _ routePrefix (Primrec.snd.comp fan)
  exact (route.to_comp.comp pack.to_comp).of_eq fun _ => rfl

/-- Given flat data for a selected source clause, its literal-indexed copied
route lookup is computable. -/
theorem canonicalAngularCopiedIncidenceSomeClause_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (ports : Input → OccurrencePorts)
    (copies : Input → Variable →
      List (ThreeOccurrenceVariable Variable))
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (ports input.1.1).port input.1.2 input.2)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      copies input.1 input.2) :
    Computable₂ fun (input : (Input × Nat) × Nat)
        (clause : AngularClauseRouteData Variable) =>
      match clause.2[input.2]? with
      | none => []
      | some literal =>
          canonicalAngularOccurrenceRouteData
            (sourcePlacement input.1.1) (ports input.1.1)
            (copies input.1.1) (angularClauseOfRouteData clause)
            (angularLiteralOfRouteData literal) input.1.2 input.2 := by
  let Combined := (((Input × Nat) × Nat) ×
    AngularClauseRouteData Variable)
  change Computable fun input : Combined =>
    match input.2.2[input.1.2]? with
    | none => []
    | some literal =>
        canonicalAngularOccurrenceRouteData
          (sourcePlacement input.1.1.1) (ports input.1.1.1)
          (copies input.1.1.1) (angularClauseOfRouteData input.2)
          (angularLiteralOfRouteData literal)
          input.1.1.2 input.1.2
  have selectedLiteral : Primrec fun input : Combined =>
      input.2.2[input.1.2]? :=
    Primrec.list_getElem?.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact (Computable.option_casesOn selectedLiteral.to_comp
    (Computable.const [])
    (canonicalAngularCopiedIncidenceSomeLiteral_computable
      sourcePlacement ports copies periodPrimrec positionPrimrec
      portsPrimrec copiesPrimrec)).of_eq fun input => by
        cases input.2.2[input.1.2]? <;> rfl

/-- The proof-free copied-clause route lookup is computable. -/
theorem canonicalAngularCopiedIncidenceRoutesData_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (ports : Input → OccurrencePorts)
    (copies : Input → Variable →
      List (ThreeOccurrenceVariable Variable))
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (ports input.1.1).port input.1.2 input.2)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      copies input.1 input.2) :
    Computable fun input : (Input × Nat) × Nat =>
      canonicalAngularCopiedIncidenceRoutesData
        (sourcePlacement input.1.1) (ports input.1.1)
        (copies input.1.1) (source input.1.1)
        input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have clauses : Primrec fun input : Query =>
      (source input.1.1).clauses :=
    PositionedPeriodicCNF.clauses_primrec.comp
      (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst))
  have selectedClause : Primrec fun input : Query =>
      (source input.1.1).clauses[input.1.2]? :=
    Primrec.list_getElem?.comp clauses (Primrec.snd.comp Primrec.fst)
  have selectedClauseData : Primrec fun input : Query =>
      ((source input.1.1).clauses[input.1.2]?).map
        angularClauseRouteData :=
    Primrec.option_map selectedClause
      (angularClauseRouteData_primrec.comp Primrec.snd).to₂
  have copied : Computable fun input : Query =>
      match ((source input.1.1).clauses[input.1.2]?).map
          angularClauseRouteData with
      | none => []
      | some clause =>
          match clause.2[input.2]? with
          | none => []
          | some literal =>
              canonicalAngularOccurrenceRouteData
                (sourcePlacement input.1.1) (ports input.1.1)
                (copies input.1.1) (angularClauseOfRouteData clause)
                (angularLiteralOfRouteData literal)
                input.1.2 input.2 :=
    (Computable.option_casesOn selectedClauseData.to_comp
      (Computable.const [])
      (canonicalAngularCopiedIncidenceSomeClause_computable
        sourcePlacement ports copies periodPrimrec positionPrimrec
        portsPrimrec copiesPrimrec)).of_eq fun input => by
          cases ((source input.1.1).clauses[input.1.2]?).map
            angularClauseRouteData <;> rfl
  exact copied.of_eq fun input => by
    unfold canonicalAngularCopiedIncidenceRoutesData
    cases hClause : (source input.1.1).clauses[input.1.2]? with
    | none => rfl
    | some clause =>
        simp only [Option.map_some]
        cases hLiteral : clause.literals[input.2]? with
        | none => simp [angularClauseRouteData, hLiteral]
        | some literal =>
            rw [show angularClauseOfRouteData
              (angularClauseRouteData clause) = clause from
                angularClauseOfRouteData_routeData clause]
            simp [angularClauseRouteData, List.getElem?_map, hLiteral]

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
