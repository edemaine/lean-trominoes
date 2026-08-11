import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineMetadataComputability
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineRouteFamily
import LeanTrominoes.PeriodicOrthocrossingConstructionComputability
import LeanTrominoes.PositionedPeriodicCNFRouteTransportComputability

/-!
# Computability of composed Figure 9 local routes

The composed metadata projection selects one of four fixed finite route
tables.  This module identifies that proof-free lookup with the certified
drawing routes, computes the twice-refined placement, and proves the exact
anchor-normalized local route family primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

set_option maxHeartbeats 2000000
set_option linter.overlappingInstances false

open PlanarThreeSAT

namespace LocalRouteData

/-- Lookup in a fixed row-major table of finite routes. -/
def tableRoute (table : List (List (List Cell)))
    (clauseIndex literalIndex : Nat) : List Cell :=
  (table.getD clauseIndex []).getD literalIndex []

theorem tableRoute_primrec (table : List (List (List Cell))) :
    Primrec fun input : Nat × Nat =>
      tableRoute table input.1 input.2 := by
  have row : Primrec fun input : Nat × Nat =>
      table.getD input.1 [] :=
    (Primrec.list_getD ([] : List (List Cell))).comp
      (Primrec.const table) Primrec.fst
  exact (Primrec.list_getD ([] : List Cell)).comp row Primrec.snd

def fullTable : List (List (List Cell)) :=
  [[fullRoute 0 0, fullRoute 0 1, fullRoute 0 2],
    [fullRoute 1 0, fullRoute 1 1, fullRoute 1 2],
    [fullRoute 2 0, fullRoute 2 1, fullRoute 2 2]]

def twoTable : List (List (List Cell)) :=
  [[twoRoute 0 0, twoRoute 0 1, twoRoute 0 2],
    [twoRoute 1 0, twoRoute 1 1, twoRoute 1 2],
    [twoRoute 2 0, twoRoute 2 1, twoRoute 2 2],
    [twoRoute 3 0, twoRoute 3 1, twoRoute 3 2],
    [twoRoute 4 0, twoRoute 4 1, twoRoute 4 2]]

def oneTable : List (List (List Cell)) :=
  [[oneRoute 0 0, oneRoute 0 1, oneRoute 0 2],
    [oneRoute 1 0, oneRoute 1 1, oneRoute 1 2],
    [oneRoute 2 0, oneRoute 2 1, oneRoute 2 2],
    [oneRoute 3 0, oneRoute 3 1, oneRoute 3 2],
    [oneRoute 4 0, oneRoute 4 1, oneRoute 4 2],
    [oneRoute 5 0, oneRoute 5 1, oneRoute 5 2],
    [oneRoute 6 0, oneRoute 6 1, oneRoute 6 2]]

def zeroTable : List (List (List Cell)) :=
  [[zeroRoute 0 0, zeroRoute 0 1, zeroRoute 0 2],
    [zeroRoute 1 0, zeroRoute 1 1, zeroRoute 1 2],
    [zeroRoute 2 0, zeroRoute 2 1, zeroRoute 2 2],
    [zeroRoute 3 0, zeroRoute 3 1, zeroRoute 3 2],
    [zeroRoute 4 0, zeroRoute 4 1, zeroRoute 4 2],
    [zeroRoute 5 0, zeroRoute 5 1, zeroRoute 5 2],
    [zeroRoute 6 0, zeroRoute 6 1, zeroRoute 6 2],
    [zeroRoute 7 0, zeroRoute 7 1, zeroRoute 7 2],
    [zeroRoute 8 0, zeroRoute 8 1, zeroRoute 8 2]]

theorem fullTable_eq (clauseIndex literalIndex : Nat) :
    tableRoute fullTable clauseIndex literalIndex =
      fullRoute clauseIndex literalIndex := by
  rcases clauseIndex with _ | _ | _ | clauseIndex <;>
    rcases literalIndex with _ | _ | _ | literalIndex <;> rfl

theorem twoTable_eq (clauseIndex literalIndex : Nat) :
    tableRoute twoTable clauseIndex literalIndex =
      twoRoute clauseIndex literalIndex := by
  rcases clauseIndex with _ | _ | _ | _ | _ | clauseIndex <;>
    rcases literalIndex with _ | _ | _ | literalIndex <;> rfl

theorem oneTable_eq (clauseIndex literalIndex : Nat) :
    tableRoute oneTable clauseIndex literalIndex =
      oneRoute clauseIndex literalIndex := by
  rcases clauseIndex with _ | _ | _ | _ | _ | _ | _ | clauseIndex <;>
    rcases literalIndex with _ | _ | _ | literalIndex <;> rfl

theorem zeroTable_eq (clauseIndex literalIndex : Nat) :
    tableRoute zeroTable clauseIndex literalIndex =
      zeroRoute clauseIndex literalIndex := by
  rcases clauseIndex with
    _ | _ | _ | _ | _ | _ | _ | _ | _ | clauseIndex <;>
    rcases literalIndex with _ | _ | _ | literalIndex <;> rfl

/-- Local composed route selected only by source arity and presentation
indices. -/
def routeForArity
    (arity clauseIndex literalIndex : Nat) : List Cell :=
  if arity = 0 then tableRoute zeroTable clauseIndex literalIndex
  else if arity = 1 then tableRoute oneTable clauseIndex literalIndex
  else if arity = 2 then tableRoute twoTable clauseIndex literalIndex
  else tableRoute fullTable clauseIndex literalIndex

theorem routeForArity_primrec :
    Primrec fun input : (Nat × Nat) × Nat =>
      routeForArity input.1.1 input.1.2 input.2 := by
  let Query := (Nat × Nat) × Nat
  have indices : Primrec fun input : Query =>
      (input.1.2, input.2) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  have zero : PrimrecPred fun input : Query => input.1.1 = 0 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)
  have one : PrimrecPred fun input : Query => input.1.1 = 1 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1)
  have two : PrimrecPred fun input : Query => input.1.1 = 2 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 2)
  exact Primrec.ite zero
    ((tableRoute_primrec zeroTable).comp indices)
    (Primrec.ite one
      ((tableRoute_primrec oneTable).comp indices)
      (Primrec.ite two
        ((tableRoute_primrec twoTable).comp indices)
        ((tableRoute_primrec fullTable).comp indices)))

end LocalRouteData

/-- Proof-free local composed route translated into its source macrocell. -/
def localRouteData {Variable : Type*}
    (sourceClause : PositionedPeriodicClause Variable)
    (localClauseIndex literalIndex : Nat) : List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (Cell.scale composedGadgetScale sourceClause.position)
    (LocalRouteData.routeForArity sourceClause.literals.length
      localClauseIndex literalIndex)

/-- The route field of the selected certified drawing is exactly the
proof-free translated finite table. -/
theorem instantiatedDrawing_routes_eq_localRouteData
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    (localClauseIndex literalIndex : Nat) :
    (instantiatedDrawing sourceClauseIndex figureNineClauseStart
      sourceClause).routes localClauseIndex literalIndex =
      localRouteData sourceClause localClauseIndex literalIndex := by
  rw [instantiatedDrawing_eq]
  change
    ((templateDrawing sourceClause).routes
      localClauseIndex literalIndex).map
        (Cell.add (Cell.scale composedGadgetScale sourceClause.position)) =
      localRouteData sourceClause localClauseIndex literalIndex
  rcases sourceClause with ⟨position, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · change
      (zeroRoute localClauseIndex literalIndex).map
          (Cell.add (Cell.scale composedGadgetScale position)) = _
    simp [localRouteData, LocalRouteData.routeForArity,
      LocalRouteData.zeroTable_eq,
      PeriodicOrthocrossing.translatePolyline]
  · rcases rest with _ | ⟨second, rest⟩
    · change
        (oneRoute localClauseIndex literalIndex).map
            (Cell.add (Cell.scale composedGadgetScale position)) = _
      simp [localRouteData, LocalRouteData.routeForArity,
        LocalRouteData.oneTable_eq,
        PeriodicOrthocrossing.translatePolyline]
    · rcases rest with _ | ⟨third, tail⟩
      · change
          (twoRoute localClauseIndex literalIndex).map
              (Cell.add (Cell.scale composedGadgetScale position)) = _
        simp [localRouteData, LocalRouteData.routeForArity,
          LocalRouteData.twoTable_eq,
          PeriodicOrthocrossing.translatePolyline]
      · change
          (fullRoute localClauseIndex literalIndex).map
              (Cell.add (Cell.scale composedGadgetScale position)) = _
        simp [localRouteData, LocalRouteData.routeForArity,
          LocalRouteData.fullTable_eq,
          PeriodicOrthocrossing.translatePolyline]

theorem localRouteData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        (PositionedPeriodicClause Variable × Nat) × Nat =>
      localRouteData input.1.1 input.1.2 input.2 := by
  let Query := (PositionedPeriodicClause Variable × Nat) × Nat
  have offset : Primrec fun input : Query =>
      Cell.scale composedGadgetScale input.1.1.position :=
    Computability.cell_scale_primrec.comp
      (Primrec.const composedGadgetScale)
      (PositionedPeriodicClause.position_primrec.comp
        (Primrec.fst.comp Primrec.fst))
  have route : Primrec fun input : Query =>
      LocalRouteData.routeForArity input.1.1.literals.length
        input.1.2 input.2 :=
    LocalRouteData.routeForArity_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.list_length.comp
            (PositionedPeriodicClause.literals_primrec.comp
              (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  exact PeriodicOrthocrossing.translatePolyline_primrec.comp offset route

/-- The exact metadata-selected local composed route lookup is primitive
recursive. -/
theorem localRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePrimrec : Primrec source) :
    Primrec fun input : (Input × Nat) × Nat =>
      localRoutes (source input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have metadata : Primrec fun input : Query =>
      (formulaClauseIndexData (source input.1.1))[input.1.2]? :=
    Primrec.list_getElem?.comp
      (formulaClauseIndexData_primrec.comp
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst)
  have none : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (metadata : ClauseIndexData Variable) =>
      localRouteData metadata.1.1 metadata.2.2
        input.2 := by
    exact localRouteData_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.option_casesOn metadata none some).of_eq fun input => by
    rw [formulaClauseIndexData_eq, List.getElem?_map]
    unfold localRoutes
    cases lookup :
        (formulaClauseMetadata (source input.1.1))[input.1.2]? with
    | none => simp
    | some selected =>
        simp [ClauseMetadata.indexData]
        rw [instantiatedDrawing_routes_eq_localRouteData]

/-- The period of the twice-refined composed placement is primitive
recursive from the source period. -/
theorem composedPlacement_period_primrec
    {Input Variable : Type*} [Primcodable Input]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period) :
    Primrec fun input =>
      (composedPlacement (source input) (sourcePlacement input)).period := by
  have firstPeriod : Primrec fun input =>
      (PeriodicOneInThreePositioned.placement
        (source input) (sourcePlacement input)).period :=
    PeriodicOneInThreePositioned.placement_period_primrec
      source sourcePlacement periodPrimrec
  exact PeriodicOneInThreeNoUnitsPositioned.placement_period_primrec
    (fun input => PeriodicOneInThreePositioned.formula (source input))
    (fun input => PeriodicOneInThreePositioned.placement
      (source input) (sourcePlacement input))
    firstPeriod

/-- Positions in the twice-refined composed placement are primitive
recursive from the source formula, period, and position lookup. -/
theorem composedPlacement_position_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input :
        Input ×
          (OneInThreeNoUnitVariable
            (OneInThreeVariable Variable)) =>
      (composedPlacement
        (source input.1) (sourcePlacement input.1)).position input.2 := by
  have firstFormula : Primrec fun input =>
      PeriodicOneInThreePositioned.formula (source input) :=
    PeriodicOneInThreePositioned.formula_primrec.comp sourcePrimrec
  have firstPeriod : Primrec fun input =>
      (PeriodicOneInThreePositioned.placement
        (source input) (sourcePlacement input)).period :=
    PeriodicOneInThreePositioned.placement_period_primrec
      source sourcePlacement periodPrimrec
  have firstPosition : Primrec fun input :
      Input × OneInThreeVariable Variable =>
      (PeriodicOneInThreePositioned.placement
        (source input.1) (sourcePlacement input.1)).position input.2 :=
    PeriodicOneInThreePositioned.placement_position_primrec
      source sourcePlacement sourcePrimrec periodPrimrec positionPrimrec
  exact PeriodicOneInThreeNoUnitsPositioned.placement_position_primrec
    (fun input => PeriodicOneInThreePositioned.formula (source input))
    (fun input => PeriodicOneInThreePositioned.placement
      (source input) (sourcePlacement input))
    firstFormula firstPeriod firstPosition

private def defaultComposedClause (Variable : Type*) :
    PositionedPeriodicClause
      (OneInThreeNoUnitVariable (OneInThreeVariable Variable)) :=
  ⟨(0, 0), []⟩

/-- Proof-free normalization using the flat metadata projection and the
already computable twice-replaced output formula. -/
private def normalizedLocalRoutesComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  match (formulaClauseIndexData source)[clauseIndex]? with
  | none => []
  | some _ =>
      let target :=
        PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)
      PositionedPeriodicCNF.normalizeIncidenceRoute
        (composedPlacement source sourcePlacement)
        (target.clauses.getD clauseIndex
          (defaultComposedClause Variable))
        (localRoutes source clauseIndex literalIndex)

private theorem normalizedLocalRoutesComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) :
    normalizedLocalRoutesComputed source sourcePlacement
        clauseIndex literalIndex =
      normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex := by
  unfold normalizedLocalRoutesComputed normalizedLocalRoutes
  rw [formulaClauseIndexData_eq, List.getElem?_map]
  cases lookup : (formulaClauseMetadata source)[clauseIndex]? with
  | none => simp
  | some metadata =>
      simp only [Option.map_some]
      have clauseLookup :
          (PeriodicOneInThreeNoUnitsPositioned.formula
            (PeriodicOneInThreePositioned.formula source)).clauses[
              clauseIndex]? = some metadata.clause := by
        rw [← formulaClauseMetadata_clauses, List.getElem?_map,
          lookup]
        rfl
      have clauseIndexLt :=
        (List.getElem?_eq_some_iff.mp clauseLookup).1
      rw [List.getD_eq_getElem
          (l := (PeriodicOneInThreeNoUnitsPositioned.formula
            (PeriodicOneInThreePositioned.formula source)).clauses)
          (d := defaultComposedClause Variable) clauseIndexLt,
        (List.getElem?_eq_some_iff.mp clauseLookup).2]

/-- Anchor normalization of the exact composed local route lookup remains
primitive recursive. -/
theorem normalizedLocalRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period) :
    Primrec fun input : (Input × Nat) × Nat =>
      normalizedLocalRoutes (source input.1.1)
        (sourcePlacement input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have metadata : Primrec fun input : Query =>
      (formulaClauseIndexData (source input.1.1))[input.1.2]? :=
    Primrec.list_getElem?.comp
      (formulaClauseIndexData_primrec.comp
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst)
  have target : Primrec fun input : Query =>
      PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula
          (source input.1.1)) :=
    (PeriodicOneInThreeNoUnitsPositioned.formula_primrec.comp
      (PeriodicOneInThreePositioned.formula_primrec.comp
        sourcePrimrec)).comp (Primrec.fst.comp Primrec.fst)
  have clause : Primrec fun input : Query =>
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula
          (source input.1.1))).clauses.getD input.1.2
            (defaultComposedClause Variable) :=
    (Primrec.list_getD (defaultComposedClause Variable)).comp
      (PositionedPeriodicCNF.clauses_primrec.comp target)
      (Primrec.snd.comp Primrec.fst)
  have none : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (_metadata : ClauseIndexData Variable) =>
      PositionedPeriodicCNF.normalizeIncidenceRoute
        (composedPlacement
          (source input.1.1) (sourcePlacement input.1.1))
        ((PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (source input.1.1))).clauses.getD input.1.2
              (defaultComposedClause Variable))
        (localRoutes (source input.1.1)
          input.1.2 input.2) := by
    exact PositionedPeriodicCNF.normalizeIncidenceRoute_primrec
      (Input := Query × ClauseIndexData Variable)
      (fun combined =>
        (composedPlacement
          (source combined.1.1.1)
          (sourcePlacement combined.1.1.1)).period)
      (fun _combined => fun _atom => (0, 0))
      (fun combined =>
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula
            (source combined.1.1.1))).clauses.getD
              combined.1.1.2 (defaultComposedClause Variable))
      (fun combined => localRoutes (source combined.1.1.1)
        combined.1.1.2 combined.1.2)
      ((composedPlacement_period_primrec
        source sourcePlacement periodPrimrec).comp
          (Primrec.fst.comp
            (Primrec.fst.comp Primrec.fst)))
      (clause.comp Primrec.fst)
      ((localRoutes_primrec source sourcePrimrec).comp Primrec.fst)
  have computed : Primrec fun input : Query =>
      normalizedLocalRoutesComputed (source input.1.1)
        (sourcePlacement input.1.1) input.1.2 input.2 :=
    (Primrec.option_casesOn metadata none some).of_eq fun input => by
      unfold normalizedLocalRoutesComputed
      cases (formulaClauseIndexData (source input.1.1))[input.1.2]?
      <;> rfl
  exact computed.of_eq fun input =>
    normalizedLocalRoutesComputed_eq
      (source input.1.1) (sourcePlacement input.1.1)
      input.1.2 input.2

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
