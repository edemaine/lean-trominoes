/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePositionedNormalizedLocalRoutes
import LeanTrominoes.PeriodicOneInThreePositionedComputability
import LeanTrominoes.PositionedPeriodicCNFRouteTransportComputability

/-!
# Computability of positioned Figure 9 local routes

The certified Figure 9 drawings carry arbitrary variable names and proof
fields, but their route geometry depends only on the source clause position,
its arity, and the two finite presentation indices.  This module exposes that
proof-free route table, identifies it with the existing instantiated drawing,
and proves the flattened metadata and anchor-normalized local route lookup
primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

set_option maxHeartbeats 1000000

namespace ClauseMetadata

/-- Product representation of one flattened Figure 9 clause index. -/
def equivData {Variable : Type*} :
    ClauseMetadata Variable ≃
      (PositionedPeriodicClause Variable × Nat) ×
        (PositionedPeriodicClause (OneInThreeVariable Variable) × Nat) where
  toFun metadata :=
    ((metadata.sourceClause, metadata.sourceClauseIndex),
      (metadata.clause, metadata.localClauseIndex))
  invFun data :=
    ⟨data.1.1, data.1.2, data.2.1, data.2.2⟩
  left_inv metadata := by cases metadata; rfl
  right_inv data := by rcases data with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (ClauseMetadata Variable) :=
  Primcodable.ofEquiv _ equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@equivData Variable) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@equivData Variable).symm :=
  Primrec.of_equiv_symm

theorem sourceClause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@ClauseMetadata.sourceClause Variable) :=
  (Primrec.fst.comp (Primrec.fst.comp equivData_primrec)).of_eq fun _ => rfl

theorem sourceClauseIndex_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@ClauseMetadata.sourceClauseIndex Variable) :=
  (Primrec.snd.comp (Primrec.fst.comp equivData_primrec)).of_eq fun _ => rfl

theorem clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@ClauseMetadata.clause Variable) :=
  (Primrec.fst.comp (Primrec.snd.comp equivData_primrec)).of_eq fun _ => rfl

theorem localClauseIndex_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@ClauseMetadata.localClauseIndex Variable) :=
  (Primrec.snd.comp (Primrec.snd.comp equivData_primrec)).of_eq fun _ => rfl

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (PositionedPeriodicClause Variable × Nat) ×
          (PositionedPeriodicClause (OneInThreeVariable Variable) × Nat) =>
      ClauseMetadata.mk data.1.1 data.1.2 data.2.1 data.2.2 :=
  equivData_symm_primrec

end ClauseMetadata

/-- The metadata parallel to one Figure 9 replacement block is primitive
recursive. -/
theorem clauseMetadataFor_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × PositionedPeriodicClause Variable =>
      clauseMetadataFor input.1 input.2 := by
  have generated : Primrec fun input :
      Nat × PositionedPeriodicClause Variable =>
      (clauseGadget input.1 input.2).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp clauseGadget_primrec
  have one : Primrec₂ fun
      (input : Nat × PositionedPeriodicClause Variable)
      (tagged : PositionedPeriodicClause
          (OneInThreeVariable Variable) × Nat) =>
      ClauseMetadata.mk input.2 input.1 tagged.1 tagged.2 := by
    exact ClauseMetadata.mk_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (Primrec.fst.comp Primrec.fst))
        Primrec.snd)
  exact (Primrec.list_map generated one).of_eq fun _ => rfl

/-- The complete flattened Figure 9 clause metadata is primitive recursive. -/
theorem formulaClauseMetadata_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (formulaClauseMetadata :
      PositionedPeriodicCNF Variable → List (ClauseMetadata Variable)) := by
  have tagged : Primrec fun source : PositionedPeriodicCNF Variable =>
      source.clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PositionedPeriodicCNF.clauses_primrec
  have one : Primrec₂ fun (_source : PositionedPeriodicCNF Variable)
      (taggedClause : PositionedPeriodicClause Variable × Nat) =>
      clauseMetadataFor taggedClause.2 taggedClause.1 := by
    exact clauseMetadataFor_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
  exact (Primrec.list_flatMap tagged one).of_eq fun _ => rfl

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

def threeTable : List (List (List Cell)) :=
  [[PlanarOneInThree.figureNineRoute 0 0,
      PlanarOneInThree.figureNineRoute 0 1,
      PlanarOneInThree.figureNineRoute 0 2],
    [PlanarOneInThree.figureNineRoute 1 0,
      PlanarOneInThree.figureNineRoute 1 1,
      PlanarOneInThree.figureNineRoute 1 2],
    [PlanarOneInThree.figureNineRoute 2 0,
      PlanarOneInThree.figureNineRoute 2 1,
      PlanarOneInThree.figureNineRoute 2 2]]

def twoTable : List (List (List Cell)) :=
  [[PlanarOneInThree.figureNineTwoRoute 0 0,
      PlanarOneInThree.figureNineTwoRoute 0 1,
      PlanarOneInThree.figureNineTwoRoute 0 2],
    [PlanarOneInThree.figureNineTwoRoute 1 0,
      PlanarOneInThree.figureNineTwoRoute 1 1,
      PlanarOneInThree.figureNineTwoRoute 1 2],
    [PlanarOneInThree.figureNineTwoRoute 2 0,
      PlanarOneInThree.figureNineTwoRoute 2 1,
      PlanarOneInThree.figureNineTwoRoute 2 2],
    [PlanarOneInThree.figureNineTwoRoute 3 0]]

def oneTable : List (List (List Cell)) :=
  [[PlanarOneInThree.figureNineOneRoute 0 0,
      PlanarOneInThree.figureNineOneRoute 0 1,
      PlanarOneInThree.figureNineOneRoute 0 2],
    [PlanarOneInThree.figureNineOneRoute 1 0,
      PlanarOneInThree.figureNineOneRoute 1 1,
      PlanarOneInThree.figureNineOneRoute 1 2],
    [PlanarOneInThree.figureNineOneRoute 2 0,
      PlanarOneInThree.figureNineOneRoute 2 1,
      PlanarOneInThree.figureNineOneRoute 2 2],
    [PlanarOneInThree.figureNineOneRoute 3 0],
    [PlanarOneInThree.figureNineOneRoute 4 0]]

def zeroTable : List (List (List Cell)) :=
  [[PlanarOneInThree.figureNineZeroRoute 0 0,
      PlanarOneInThree.figureNineZeroRoute 0 1,
      PlanarOneInThree.figureNineZeroRoute 0 2],
    [PlanarOneInThree.figureNineZeroRoute 1 0,
      PlanarOneInThree.figureNineZeroRoute 1 1,
      PlanarOneInThree.figureNineZeroRoute 1 2],
    [PlanarOneInThree.figureNineZeroRoute 2 0,
      PlanarOneInThree.figureNineZeroRoute 2 1,
      PlanarOneInThree.figureNineZeroRoute 2 2],
    [PlanarOneInThree.figureNineZeroRoute 3 0],
    [PlanarOneInThree.figureNineZeroRoute 4 0],
    [PlanarOneInThree.figureNineZeroRoute 5 0]]

theorem threeTable_eq (clauseIndex literalIndex : Nat) :
    tableRoute threeTable clauseIndex literalIndex =
      PlanarOneInThree.figureNineRoute clauseIndex literalIndex := by
  rcases clauseIndex with _ | _ | _ | clauseIndex <;>
    rcases literalIndex with _ | _ | _ | literalIndex <;> rfl

theorem twoTable_eq (clauseIndex literalIndex : Nat) :
    tableRoute twoTable clauseIndex literalIndex =
      PlanarOneInThree.figureNineTwoRoute clauseIndex literalIndex := by
  rcases clauseIndex with _ | _ | _ | _ | clauseIndex <;>
    rcases literalIndex with _ | _ | _ | literalIndex <;> rfl

theorem oneTable_eq (clauseIndex literalIndex : Nat) :
    tableRoute oneTable clauseIndex literalIndex =
      PlanarOneInThree.figureNineOneRoute clauseIndex literalIndex := by
  rcases clauseIndex with _ | _ | _ | _ | _ | clauseIndex <;>
    rcases literalIndex with _ | _ | _ | literalIndex <;> rfl

theorem zeroTable_eq (clauseIndex literalIndex : Nat) :
    tableRoute zeroTable clauseIndex literalIndex =
      PlanarOneInThree.figureNineZeroRoute clauseIndex literalIndex := by
  rcases clauseIndex with _ | _ | _ | _ | _ | _ | clauseIndex <;>
    rcases literalIndex with _ | _ | _ | literalIndex <;> rfl

/-- Local Figure 9 route selected only by source arity and presentation
indices. -/
def routeForArity (arity clauseIndex literalIndex : Nat) : List Cell :=
  if arity = 0 then tableRoute zeroTable clauseIndex literalIndex
  else if arity = 1 then tableRoute oneTable clauseIndex literalIndex
  else if arity = 2 then tableRoute twoTable clauseIndex literalIndex
  else tableRoute threeTable clauseIndex literalIndex

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
        ((tableRoute_primrec threeTable).comp indices)))

end LocalRouteData

/-- Proof-free local route: translate the fixed arity table into the source
clause's Figure 9 macrocell. -/
def localRouteData {Variable : Type*}
    (sourceClause : PositionedPeriodicClause Variable)
    (localClauseIndex literalIndex : Nat) : List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (Cell.scale PlanarOneInThree.gadgetScale sourceClause.position)
    (LocalRouteData.routeForArity sourceClause.literals.length
      localClauseIndex literalIndex)

/-- The route field of the certified instantiated drawing is exactly the
proof-free translated table. -/
theorem instantiatedDrawing_routes_eq_localRouteData
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    (localClauseIndex literalIndex : Nat) :
    (PlanarOneInThreePositioned.instantiatedDrawing
      sourceClauseIndex sourceClause).routes
        localClauseIndex literalIndex =
      localRouteData sourceClause localClauseIndex literalIndex := by
  rcases sourceClause with ⟨position, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · simp [PlanarOneInThreePositioned.instantiatedDrawing,
      PlanarOneInThreePositioned.instantiatedZeroDrawing,
      PlanarOneInThreePositioned.rescopeDrawing,
      PlanarOneInThree.instantiatedZeroDrawing,
      PlanarOneInThree.figureNineZeroDrawing,
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
      localRouteData, LocalRouteData.routeForArity,
      LocalRouteData.zeroTable_eq,
      PeriodicOrthocrossing.translatePolyline]
  · rcases rest with _ | ⟨second, rest⟩
    · simp [PlanarOneInThreePositioned.instantiatedDrawing,
        PlanarOneInThreePositioned.instantiatedOneDrawing,
        PlanarOneInThreePositioned.rescopeDrawing,
        PlanarOneInThree.instantiatedOneDrawing,
        PlanarOneInThree.figureNineOneDrawingFor,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
        localRouteData, LocalRouteData.routeForArity,
        LocalRouteData.oneTable_eq,
        PeriodicOrthocrossing.translatePolyline]
    · rcases rest with _ | ⟨third, tail⟩
      · simp [PlanarOneInThreePositioned.instantiatedDrawing,
          PlanarOneInThreePositioned.instantiatedTwoDrawing,
          PlanarOneInThreePositioned.rescopeDrawing,
          PlanarOneInThree.instantiatedTwoDrawing,
          PlanarOneInThree.figureNineTwoDrawingFor,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
          localRouteData, LocalRouteData.routeForArity,
          LocalRouteData.twoTable_eq,
          PeriodicOrthocrossing.translatePolyline]
      · simp [PlanarOneInThreePositioned.instantiatedDrawing,
          PlanarOneInThreePositioned.instantiatedThreeDrawing,
          PlanarOneInThreePositioned.rescopeDrawing,
          PlanarOneInThree.instantiatedThreeDrawing,
          PlanarOneInThree.figureNineDrawingFor,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
          localRouteData, LocalRouteData.routeForArity,
          LocalRouteData.threeTable_eq,
          PeriodicOrthocrossing.translatePolyline]

theorem localRouteData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        (PositionedPeriodicClause Variable × Nat) × Nat =>
      localRouteData input.1.1 input.1.2 input.2 := by
  let Query := (PositionedPeriodicClause Variable × Nat) × Nat
  have offset : Primrec fun input : Query =>
      Cell.scale PlanarOneInThree.gadgetScale input.1.1.position :=
    Computability.cell_scale_primrec.comp
      (Primrec.const PlanarOneInThree.gadgetScale)
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
  exact (Primrec.list_map route
    (Computability.cell_add_primrec.comp₂
      (offset.comp₂ Primrec₂.left) Primrec₂.right)).of_eq fun _ => rfl

/-- The exact metadata-selected local Figure 9 route lookup is primitive
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
      (formulaClauseMetadata (source input.1.1))[input.1.2]? :=
    Primrec.list_getElem?.comp
      (formulaClauseMetadata_primrec.comp
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst)
  have none : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (metadata : ClauseMetadata Variable) =>
      localRouteData metadata.sourceClause metadata.localClauseIndex
        input.2 := by
    exact localRouteData_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (ClauseMetadata.sourceClause_primrec.comp Primrec.snd)
          (ClauseMetadata.localClauseIndex_primrec.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.option_casesOn metadata none some).of_eq fun input => by
    unfold localRoutes
    cases lookup :
        (formulaClauseMetadata (source input.1.1))[input.1.2]? with
    | none => rfl
    | some selected =>
        simp only
        rw [instantiatedDrawing_routes_eq_localRouteData]

/-- Anchor normalization of the exact local Figure 9 route lookup remains
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
      (formulaClauseMetadata (source input.1.1))[input.1.2]? :=
    Primrec.list_getElem?.comp
      (formulaClauseMetadata_primrec.comp
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst)
  have none : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (metadata : ClauseMetadata Variable) =>
      PositionedPeriodicCNF.normalizeIncidenceRoute
        (placement (source input.1.1) (sourcePlacement input.1.1))
        metadata.clause
        (localRoutes (source input.1.1) input.1.2 input.2) := by
    exact PositionedPeriodicCNF.normalizeIncidenceRoute_primrec
      (Input := Query × ClauseMetadata Variable)
      (fun combined =>
        (placement (source combined.1.1.1)
          (sourcePlacement combined.1.1.1)).period)
      (fun combined =>
        (placement (source combined.1.1.1)
          (sourcePlacement combined.1.1.1)).position)
      (fun combined => combined.2.clause)
      (fun combined => localRoutes (source combined.1.1.1)
        combined.1.1.2 combined.1.2)
      ((placement_period_primrec source sourcePlacement periodPrimrec).comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (ClauseMetadata.clause_primrec.comp Primrec.snd)
      ((localRoutes_primrec source sourcePrimrec).comp Primrec.fst)
  exact (Primrec.option_casesOn metadata none some).of_eq fun input => by
    unfold normalizedLocalRoutes
    cases (formulaClauseMetadata (source input.1.1))[input.1.2]?
    <;> rfl

end PeriodicOneInThreePositioned
end LeanTrominoes
