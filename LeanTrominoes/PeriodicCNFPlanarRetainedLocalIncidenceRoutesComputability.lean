/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedClauseMetadataComputability
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing
import LeanTrominoes.PeriodicThreeDMNormalizationEncoding

/-!
# Computability of retained planar-SAT local incidence routes

The retained clause metadata selects one of five explicit finite incidence
drawings.  This module computes their presentation-indexed route functions
directly, then combines them with the retained metadata lookup.  Encoding the
whole drawing structure is unnecessary: variable-position functions are
proof infrastructure, while the downstream angular ordering consumes only
the finite route at a clause and literal index.
-/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PlanarThreeSAT

namespace DuplicatorArmVariable

def equivBool : DuplicatorArmVariable ≃ Bool where
  toFun
    | .port => false
    | .center => true
  invFun
    | false => .port
    | true => .center
  left_inv value := by cases value <;> rfl
  right_inv value := by cases value <;> rfl

noncomputable instance : Primcodable DuplicatorArmVariable :=
  Primcodable.ofEquiv Bool equivBool

theorem equivBool_primrec : Primrec equivBool :=
  Primrec.of_equiv

theorem equivBool_symm_primrec : Primrec equivBool.symm :=
  Primrec.of_equiv_symm

end DuplicatorArmVariable

theorem straightIncidenceRoute_primrec :
    Primrec₂ straightIncidenceRoute := by
  change Primrec fun input : Cell × Cell => [input.1, input.2]
  exact Primrec.list_cons.comp Primrec.fst
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))

theorem straightIncidenceRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (formula : Input → List (EmbeddedClause Variable))
    (variablePosition : Input → Variable → Cell)
    (formulaPrimrec : Primrec formula)
    (variablePositionPrimrec : Primrec fun input : Input × Variable =>
      variablePosition input.1 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      straightIncidenceRoutes (formula input.1.1)
        (variablePosition input.1.1) input.1.2 input.2 := by
  have clauseOption : Primrec fun input : (Input × Nat) × Nat =>
      (formula input.1.1)[input.1.2]? :=
    Primrec.list_getElem?.comp
      (formulaPrimrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have noClause : Primrec fun _input : (Input × Nat) × Nat =>
      ([] : List Cell) :=
    Primrec.const []
  have someClause : Primrec₂ fun
      (input : (Input × Nat) × Nat)
      (clause : EmbeddedClause Variable) =>
      match clause.literals[input.2]? with
      | none => []
      | some literal =>
          straightIncidenceRoute clause.position
            (variablePosition input.1.1 literal.1) := by
    change Primrec fun combined :
        ((Input × Nat) × Nat) × EmbeddedClause Variable =>
      match combined.2.literals[combined.1.2]? with
      | none => []
      | some literal =>
          straightIncidenceRoute combined.2.position
            (variablePosition combined.1.1.1 literal.1)
    have literalOption : Primrec fun combined :
        ((Input × Nat) × Nat) × EmbeddedClause Variable =>
        combined.2.literals[combined.1.2]? :=
      Primrec.list_getElem?.comp
        (EmbeddedClause.literals_primrec.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    have noLiteral : Primrec fun _combined :
        ((Input × Nat) × Nat) × EmbeddedClause Variable =>
        ([] : List Cell) :=
      Primrec.const []
    have someLiteral : Primrec₂ fun
        (combined :
          ((Input × Nat) × Nat) × EmbeddedClause Variable)
        (literal : Variable × Bool) =>
        straightIncidenceRoute combined.2.position
          (variablePosition combined.1.1.1 literal.1) := by
      have source : Primrec fun input :
          (((Input × Nat) × Nat) × EmbeddedClause Variable) ×
            (Variable × Bool) =>
          input.1.2.position :=
        EmbeddedClause.position_primrec.comp
          (Primrec.snd.comp Primrec.fst)
      have target : Primrec fun input :
          (((Input × Nat) × Nat) × EmbeddedClause Variable) ×
            (Variable × Bool) =>
          variablePosition input.1.1.1.1 input.2.1 :=
        variablePositionPrimrec.comp
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.fst.comp Primrec.snd))
      exact straightIncidenceRoute_primrec.comp source target
    exact (Primrec.option_casesOn literalOption noLiteral someLiteral).of_eq
      fun combined => by cases combined.2.literals[combined.1.2]? <;> rfl
  exact (Primrec.option_casesOn clauseOption noClause someClause).of_eq
    fun input => by
      simp only [straightIncidenceRoutes]
      cases (formula input.1.1)[input.1.2]? <;> rfl

end PlanarThreeSAT

namespace AxisDirection

theorem between_primrec : Primrec₂ AxisDirection.between := by
  change Primrec fun input : Cell × Cell =>
    AxisDirection.between input.1 input.2
  have firstX : Primrec fun input : Cell × Cell => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have firstY : Primrec fun input : Cell × Cell => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have secondX : Primrec fun input : Cell × Cell => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have secondY : Primrec fun input : Cell × Cell => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have sameX := Primrec.eq.comp firstX secondX
  have sameY := Primrec.eq.comp firstY secondY
  have east := Computability.int_lt_primrec.comp firstX secondX
  have west := Computability.int_lt_primrec.comp secondX firstX
  have north := Computability.int_lt_primrec.comp firstY secondY
  have south := Computability.int_lt_primrec.comp secondY firstY
  exact (Primrec.ite sameY
    (Primrec.ite east (Primrec.const .east)
      (Primrec.ite west (Primrec.const .west)
        (Primrec.const .invalid)))
    (Primrec.ite sameX
      (Primrec.ite north (Primrec.const .north)
        (Primrec.ite south (Primrec.const .south)
          (Primrec.const .invalid)))
      (Primrec.const .invalid))).of_eq fun input => by
        simp [AxisDirection.between]

private def intAbs (value : Int) : Int :=
  if 0 ≤ value then value else -value

private theorem intAbs_primrec : Primrec intAbs := by
  exact (Primrec.ite
    (Computability.int_le_primrec.comp
      (Primrec.const (0 : Int)) Primrec.id)
    Primrec.id Computability.int_negate_primrec).of_eq fun _ => rfl

private theorem intAbs_eq_abs (value : Int) :
    intAbs value = |value| := by
  by_cases nonnegative : 0 ≤ value
  · simp [intAbs, nonnegative, abs_of_nonneg]
  · have negative : value < 0 := lt_of_not_ge nonnegative
    simp [intAbs, nonnegative, abs_of_neg negative]

theorem axisSpan_primrec : Primrec₂ AxisDirection.axisSpan := by
  change Primrec fun input : Cell × Cell =>
    |input.2.1 - input.1.1| + |input.2.2 - input.1.2|
  have xDifference : Primrec fun input : Cell × Cell =>
      input.2.1 - input.1.1 :=
    Computability.int_subtract_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have yDifference : Primrec fun input : Cell × Cell =>
      input.2.2 - input.1.2 :=
    Computability.int_subtract_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact (Computability.int_add_primrec.comp
    (intAbs_primrec.comp xDifference)
    (intAbs_primrec.comp yDifference)).of_eq fun input => by
      rw [intAbs_eq_abs, intAbs_eq_abs]

theorem orientPoint_primrec : Primrec₂ AxisDirection.orientPoint := by
  change Primrec fun input : AxisDirection × Cell =>
    input.1.orientPoint input.2
  have east : PrimrecPred fun input : AxisDirection × Cell =>
      input.1 = AxisDirection.east :=
    Primrec.eq.comp Primrec.fst (Primrec.const AxisDirection.east)
  have north : PrimrecPred fun input : AxisDirection × Cell =>
      input.1 = AxisDirection.north :=
    Primrec.eq.comp Primrec.fst (Primrec.const AxisDirection.north)
  have west : PrimrecPred fun input : AxisDirection × Cell =>
      input.1 = AxisDirection.west :=
    Primrec.eq.comp Primrec.fst (Primrec.const AxisDirection.west)
  have south : PrimrecPred fun input : AxisDirection × Cell =>
      input.1 = AxisDirection.south :=
    Primrec.eq.comp Primrec.fst (Primrec.const AxisDirection.south)
  have northPoint : Primrec fun input : AxisDirection × Cell =>
      (-input.2.2, input.2.1) :=
    Primrec.pair
      (Computability.int_negate_primrec.comp
        (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)
  have westPoint : Primrec fun input : AxisDirection × Cell =>
      (-input.2.1, -input.2.2) :=
    Primrec.pair
      (Computability.int_negate_primrec.comp
        (Primrec.fst.comp Primrec.snd))
      (Computability.int_negate_primrec.comp
        (Primrec.snd.comp Primrec.snd))
  have southPoint : Primrec fun input : AxisDirection × Cell =>
      (input.2.2, -input.2.1) :=
    Primrec.pair (Primrec.snd.comp Primrec.snd)
      (Computability.int_negate_primrec.comp
        (Primrec.fst.comp Primrec.snd))
  exact (Primrec.ite east Primrec.snd
    (Primrec.ite north northPoint
      (Primrec.ite west westPoint
        (Primrec.ite south southPoint Primrec.snd)))).of_eq
          fun input => by cases input.1 <;> rfl

theorem placePoint_primrec :
    Primrec fun input : (Cell × AxisDirection) × Cell =>
      input.1.2.placePoint input.1.1 input.2 := by
  exact (Computability.cell_add_primrec.comp
    (Primrec.fst.comp Primrec.fst)
    (orientPoint_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd)).of_eq
        fun _ => rfl

end AxisDirection

namespace PlanarThreeSAT

namespace CornerPort

def equivBools : CornerPort ≃ Bool × Bool where
  toFun
    | .west => (false, false)
    | .east => (false, true)
    | .south => (true, false)
    | .north => (true, true)
  invFun
    | (false, false) => .west
    | (false, true) => .east
    | (true, false) => .south
    | (true, true) => .north
  left_inv value := by cases value <;> rfl
  right_inv value := by
    rcases value with ⟨first, second⟩
    cases first <;> cases second <;> rfl

noncomputable instance : Fintype CornerPort :=
  Fintype.ofEquiv (Bool × Bool) equivBools.symm

noncomputable instance : Primcodable CornerPort :=
  Primcodable.ofEquiv (Bool × Bool) equivBools

theorem equivBools_primrec : Primrec equivBools :=
  Primrec.of_equiv

theorem equivBools_symm_primrec : Primrec equivBools.symm :=
  Primrec.of_equiv_symm

end CornerPort

theorem cornerEqualityRouteTable_primrec :
    Primrec₂ cornerEqualityRouteTable :=
  Primrec.dom_finite fun input : CornerPort × CornerPort =>
    cornerEqualityRouteTable input.1 input.2

theorem cornerEqualityRoutes_primrec :
    Primrec fun input : ((CornerPort × CornerPort) × Nat) × Nat =>
      cornerEqualityRoutes input.1.1.1 input.1.1.2
        input.1.2 input.2 := by
  have table : Primrec fun input :
      ((CornerPort × CornerPort) × Nat) × Nat =>
      cornerEqualityRouteTable input.1.1.1 input.1.1.2 :=
    cornerEqualityRouteTable_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have routeIndex : Primrec fun input :
      ((CornerPort × CornerPort) × Nat) × Nat =>
      2 * input.1.2 + input.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  exact (Primrec.list_getD ([] : List Cell) |>.comp
    table routeIndex).of_eq fun _ => rfl

theorem horizontalEqualityLensRoutes_primrec :
    Primrec fun input : (Int × Nat) × Nat =>
      horizontalEqualityLensRoutes input.1.1 input.1.2 input.2 := by
  have clauseZero : PrimrecPred fun input : (Int × Nat) × Nat =>
      input.1.2 = 0 :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.const 0)
  have clauseOne : PrimrecPred fun input : (Int × Nat) × Nat =>
      input.1.2 = 1 :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.const 1)
  have literalZero : PrimrecPred fun input : (Int × Nat) × Nat =>
      input.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have literalOne : PrimrecPred fun input : (Int × Nat) × Nat =>
      input.2 = 1 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 1)
  have upperLeft : Primrec fun _input : (Int × Nat) × Nat =>
      horizontalEqualityLensUpperLeftRoute :=
    Primrec.const horizontalEqualityLensUpperLeftRoute
  have upperRight : Primrec fun input : (Int × Nat) × Nat =>
      horizontalEqualityLensUpperRightRoute input.1.1 := by
    change Primrec fun input : (Int × Nat) × Nat =>
      [(3, 0), (3, -2), (input.1.1, -2), (input.1.1, 0)]
    have spanMinusTwo : Primrec fun input : (Int × Nat) × Nat =>
        (input.1.1, (-2 : Int)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const (-2 : Int))
    have spanZero : Primrec fun input : (Int × Nat) × Nat =>
        (input.1.1, (0 : Int)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const (0 : Int))
    exact Primrec.list_cons.comp (Primrec.const ((3, 0) : Cell))
      (Primrec.list_cons.comp (Primrec.const ((3, -2) : Cell))
        (Primrec.list_cons.comp spanMinusTwo
          (Primrec.list_cons.comp spanZero (Primrec.const []))))
  have lowerLeft : Primrec fun _input : (Int × Nat) × Nat =>
      horizontalEqualityLensLowerLeftRoute :=
    Primrec.const horizontalEqualityLensLowerLeftRoute
  have lowerRight : Primrec fun input : (Int × Nat) × Nat =>
      horizontalEqualityLensLowerRightRoute input.1.1 := by
    change Primrec fun input : (Int × Nat) × Nat =>
      [(6, 0), (input.1.1, 0)]
    have spanZero : Primrec fun input : (Int × Nat) × Nat =>
        (input.1.1, (0 : Int)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const (0 : Int))
    exact Primrec.list_cons.comp (Primrec.const ((6, 0) : Cell))
      (Primrec.list_cons.comp spanZero (Primrec.const []))
  exact (Primrec.ite clauseZero
    (Primrec.ite literalZero upperLeft
      (Primrec.ite literalOne upperRight (Primrec.const [])))
    (Primrec.ite clauseOne
      (Primrec.ite literalZero lowerLeft
        (Primrec.ite literalOne lowerRight (Primrec.const [])))
      (Primrec.const []))).of_eq fun input => by
        rcases input with ⟨⟨span, clauseIndex⟩, literalIndex⟩
        rcases clauseIndex with _ | clauseIndex
        · rcases literalIndex with _ | literalIndex
          · rfl
          · rcases literalIndex with _ | literalIndex <;> rfl
        · rcases clauseIndex with _ | clauseIndex
          · rcases literalIndex with _ | literalIndex
            · rfl
            · rcases literalIndex with _ | literalIndex <;> rfl
          · rfl

theorem crossoverStraightRoutes_primrec :
    Primrec fun input :
        (PeriodicOrthocrossing.CrossingRecord × Nat) × Nat =>
      crossoverStraightIncidenceDrawing.routes input.1.2 input.2 := by
  have position : Primrec fun input :
      PeriodicOrthocrossing.CrossingRecord × CrossoverVariable =>
      CrossoverVariable.position input.2 :=
    (Primrec.dom_finite CrossoverVariable.position).comp Primrec.snd
  exact (straightIncidenceRoutes_primrec
    (fun _crossing : PeriodicOrthocrossing.CrossingRecord =>
      crossoverFormula)
    (fun _crossing role => CrossoverVariable.position role)
    (Primrec.const crossoverFormula) position).of_eq fun _ => rfl

theorem duplicatorArmFormula_primrec :
    Primrec duplicatorArmFormula :=
  Primrec.dom_finite duplicatorArmFormula

theorem duplicatorArmVariablePosition_primrec :
    Primrec fun input : DuplicatorArm × DuplicatorArmVariable =>
      DuplicatorArmVariable.position input.1 input.2 :=
  Primrec.dom_finite fun input : DuplicatorArm × DuplicatorArmVariable =>
    DuplicatorArmVariable.position input.1 input.2

theorem duplicatorArmStraightRoutes_primrec :
    Primrec fun input : (DuplicatorArm × Nat) × Nat =>
      (duplicatorArmStraightIncidenceDrawing input.1.1).routes
        input.1.2 input.2 := by
  exact (straightIncidenceRoutes_primrec duplicatorArmFormula
    DuplicatorArmVariable.position duplicatorArmFormula_primrec
    duplicatorArmVariablePosition_primrec).of_eq fun _ => rfl

theorem routedClausePortFormula_primrec :
    Primrec routedClausePortFormula := by
  have clause : Primrec fun literals : List (DuplicatorArm × Bool) =>
      EmbeddedClause.mk (10, 10) literals :=
    EmbeddedClause.mk_primrec.comp
      (Primrec.pair (Primrec.const ((10, 10) : Cell)) Primrec.id)
  exact (Primrec.list_cons.comp clause (Primrec.const [])).of_eq
    fun _ => rfl

theorem duplicatorArmPortPosition_primrec :
    Primrec DuplicatorArm.portPosition :=
  Primrec.dom_finite DuplicatorArm.portPosition

end PlanarThreeSAT

namespace PeriodicOrthocrossing

open PlanarThreeSAT

theorem CornerPort.ofDirection_primrec :
    Primrec CornerPort.ofDirection :=
  Primrec.dom_finite CornerPort.ofDirection

theorem AxisDirection.opposite_primrec :
    Primrec AxisDirection.opposite :=
  Primrec.dom_finite AxisDirection.opposite

theorem RouteBend.incomingPort_primrec :
    Primrec RouteBend.incomingPort := by
  have direction : Primrec fun routeBend : RouteBend =>
      AxisDirection.between routeBend.incomingStart routeBend.bend :=
    AxisDirection.between_primrec.comp
      RouteBend.incomingStart_primrec RouteBend.bend_primrec
  exact (CornerPort.ofDirection_primrec.comp
    (AxisDirection.opposite_primrec.comp direction)).of_eq fun _ => rfl

theorem RouteBend.outgoingPort_primrec :
    Primrec RouteBend.outgoingPort := by
  exact (CornerPort.ofDirection_primrec.comp
    (AxisDirection.between_primrec.comp
      RouteBend.bend_primrec
      RouteBend.outgoingFinish_primrec)).of_eq fun _ => rfl

private theorem mapRoute_primrec
    {Input : Type*} [Primcodable Input]
    (route : Input → List Cell)
    (transform : Input → Cell → Cell)
    (routePrimrec : Primrec route)
    (transformPrimrec : Primrec fun input : Input × Cell =>
      transform input.1 input.2) :
    Primrec fun input : Input =>
      (route input).map (transform input) :=
  Primrec.list_map routePrimrec transformPrimrec.to₂

abbrev CrossoverRouteInput (Variable : Type*) :=
  ((PeriodicCNF Variable × CrossingRecord) × Nat) × Nat

def crossoverRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : CrossoverRouteInput Variable) : List Cell :=
  (drawingPlanarSATCrossoverIncidenceDrawing
    input.1.1.1 input.1.1.2).routes input.1.2 input.2

theorem crossoverRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (crossoverRoute (Variable := Variable)) := by
  change Primrec fun input : CrossoverRouteInput Variable =>
    (drawingPlanarSATCrossoverIncidenceDrawing
      input.1.1.1 input.1.1.2).routes input.1.2 input.2
  have base : Primrec fun input :
      ((PeriodicCNF Variable × CrossingRecord) × Nat) × Nat =>
      crossoverStraightIncidenceDrawing.routes input.1.2 input.2 :=
    crossoverStraightRoutes_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have origin : Primrec fun input :
      ((PeriodicCNF Variable × CrossingRecord) × Nat) × Nat =>
      crossingMacroOrigin input.1.1.2 :=
    crossingMacroOrigin_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have transform : Primrec fun input :
      (((PeriodicCNF Variable × CrossingRecord) × Nat) × Nat) ×
        Cell =>
      Cell.add (crossingMacroOrigin input.1.1.1.2) input.2 :=
    Computability.cell_add_primrec.comp
      (origin.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map base transform.to₂

theorem routedClausePortLiterals_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable × ClauseRouteSite =>
      routedClausePortLiterals input.1 input.2 := by
  have occurrences : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      clauseRouteOccurrencesAt input.1 input.2 :=
    clauseRouteOccurrencesAt_primrec
  have one : Primrec₂ fun
      (input : PeriodicCNF Variable × ClauseRouteSite)
      (occurrence : CNFRouteOccurrence Variable) =>
      (sourceOccurrenceArm input.1 occurrence,
        occurrence.incidence.literal.value) := by
    have terminal : Primrec fun combined :
        (PeriodicCNF Variable × ClauseRouteSite) ×
          CNFRouteOccurrence Variable =>
        combined.2.sourceTerminal combined.1.1 :=
      CNFRouteOccurrence.sourceTerminal_primrec.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd
    have arm : Primrec fun combined :
        (PeriodicCNF Variable × ClauseRouteSite) ×
          CNFRouteOccurrence Variable =>
        sourceOccurrenceArm combined.1.1 combined.2 :=
      (SegmentTerminal.duplicatorArm_primrec.comp terminal).of_eq
        fun combined => (sourceOccurrenceArm_eq
          combined.1.1 combined.2).symm
    have value : Primrec fun combined :
        (PeriodicCNF Variable × ClauseRouteSite) ×
          CNFRouteOccurrence Variable =>
        combined.2.incidence.literal.value :=
      PeriodicThreeCNF.literal_value_primrec.comp
        (CNFIncidence.literal_primrec.comp
          (CNFRouteOccurrence.incidence_primrec.comp Primrec.snd))
    exact Primrec.pair arm value
  exact (Primrec.list_map occurrences one).of_eq fun _ => rfl

theorem routedClauseOrigin_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable × ClauseRouteSite =>
      routedClauseOrigin input.1 input.2 := by
  have vertex : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      (CNFVertex.clause input.2.1 : CNFVertex Variable) :=
    CNFVertex.clause_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  exact (liftedIncidenceVertexMacroOrigin_primrec.comp
    (Primrec.pair
      (Primrec.pair Primrec.fst vertex)
      (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

abbrev RoutedClauseRouteInput (Variable : Type*) :=
  ((PeriodicCNF Variable × ClauseRouteSite) × Nat) × Nat

def routedClauseRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RoutedClauseRouteInput Variable) : List Cell :=
  (drawingPlanarSATRoutedClauseIncidenceDrawing
    input.1.1.1 input.1.1.2).routes input.1.2 input.2

theorem routedClauseRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedClauseRoute (Variable := Variable)) := by
  change Primrec fun input : RoutedClauseRouteInput Variable =>
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      input.1.1.1 input.1.1.2).routes input.1.2 input.2
  have formula : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      routedClausePortFormula
        (routedClausePortLiterals input.1 input.2) :=
    routedClausePortFormula_primrec.comp
      routedClausePortLiterals_primrec
  have position : Primrec fun input :
      (PeriodicCNF Variable × ClauseRouteSite) × DuplicatorArm =>
      DuplicatorArm.portPosition input.2 :=
    duplicatorArmPortPosition_primrec.comp Primrec.snd
  have base : Primrec fun input :
      ((PeriodicCNF Variable × ClauseRouteSite) × Nat) × Nat =>
      (routedClausePortStraightIncidenceDrawing
        (routedClausePortLiterals input.1.1.1 input.1.1.2)).routes
          input.1.2 input.2 :=
    (straightIncidenceRoutes_primrec
      (fun input : PeriodicCNF Variable × ClauseRouteSite =>
        routedClausePortFormula
          (routedClausePortLiterals input.1 input.2))
      (fun (_input : PeriodicCNF Variable × ClauseRouteSite) arm =>
        DuplicatorArm.portPosition arm)
      formula position).of_eq fun _ => rfl
  have origin : Primrec fun input :
      ((PeriodicCNF Variable × ClauseRouteSite) × Nat) × Nat =>
      routedClauseOrigin input.1.1.1 input.1.1.2 :=
    routedClauseOrigin_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  have transform : Primrec fun input :
      (((PeriodicCNF Variable × ClauseRouteSite) × Nat) × Nat) ×
        Cell =>
      Cell.add
        (routedClauseOrigin input.1.1.1.1 input.1.1.1.2) input.2 :=
    Computability.cell_add_primrec.comp
      (origin.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map base transform.to₂

abbrev RoutedVariableRouteInput (Variable : Type*) :=
  (((PeriodicCNF Variable × VariableRouteSite Variable) ×
    DuplicatorArm) × Nat) × Nat

def routedVariableRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RoutedVariableRouteInput Variable) : List Cell :=
  ((duplicatorArmStraightIncidenceDrawing
    input.1.1.2).routes input.1.2 input.2).map
      (Cell.add
        (routedVariableOrigin input.1.1.1.1 input.1.1.1.2))

theorem routedVariableRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    @Primrec (RoutedVariableRouteInput Variable) (List Cell)
      inferInstance inferInstance
      (routedVariableRoute (Variable := Variable)) := by
  have baseInput : Primrec fun input :
      (((PeriodicCNF Variable × VariableRouteSite Variable) ×
        DuplicatorArm) × Nat) × Nat =>
      ((input.1.1.2, input.1.2), input.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  have base : Primrec fun input :
      (((PeriodicCNF Variable × VariableRouteSite Variable) ×
        DuplicatorArm) × Nat) × Nat =>
      (duplicatorArmStraightIncidenceDrawing input.1.1.2).routes
        input.1.2 input.2 :=
    duplicatorArmStraightRoutes_primrec.comp baseInput
  have origin : Primrec fun input :
      (((PeriodicCNF Variable × VariableRouteSite Variable) ×
        DuplicatorArm) × Nat) × Nat =>
      routedVariableOrigin input.1.1.1.1 input.1.1.1.2 :=
    routedVariableOrigin_primrec.comp
      (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have transform : Primrec fun input :
      ((((PeriodicCNF Variable × VariableRouteSite Variable) ×
        DuplicatorArm) × Nat) × Nat) × Cell =>
      Cell.add
        (routedVariableOrigin input.1.1.1.1.1
          input.1.1.1.1.2) input.2 :=
    Computability.cell_add_primrec.comp
      (origin.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map base transform.to₂

private abbrev CarrierLensRouteInput (Vertex : Type*) :=
  ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat

private abbrev PlacedHorizontalLensRouteInput :=
  ((((Cell × Cell) × Int) × Nat) × Nat)

private def placedHorizontalLensRoute
    (input : PlacedHorizontalLensRouteInput) : List Cell :=
  (horizontalEqualityLensRoutes input.1.1.2
    input.1.2 input.2).map
      ((AxisDirection.between input.1.1.1.1 input.1.1.1.2).placePoint
        input.1.1.1.1)

set_option maxHeartbeats 4000000 in
private theorem placedHorizontalLensRoute_primrec :
    Primrec placedHorizontalLensRoute := by
  change Primrec fun input : PlacedHorizontalLensRouteInput =>
    (horizontalEqualityLensRoutes input.1.1.2
      input.1.2 input.2).map
        ((AxisDirection.between input.1.1.1.1 input.1.1.1.2).placePoint
          input.1.1.1.1)
  have baseInput : Primrec fun input : PlacedHorizontalLensRouteInput =>
      ((input.1.1.2, input.1.2), input.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  have base : Primrec fun input : PlacedHorizontalLensRouteInput =>
      horizontalEqualityLensRoutes input.1.1.2
        input.1.2 input.2 :=
    horizontalEqualityLensRoutes_primrec.comp baseInput
  have transform : Primrec fun input :
      PlacedHorizontalLensRouteInput × Cell =>
      (AxisDirection.between input.1.1.1.1.1
        input.1.1.1.1.2).placePoint input.1.1.1.1.1 input.2 := by
    have origin : Primrec fun input :
        PlacedHorizontalLensRouteInput × Cell =>
        input.1.1.1.1.1 :=
      Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have finish : Primrec fun input :
        PlacedHorizontalLensRouteInput × Cell =>
        input.1.1.1.1.2 :=
      Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have direction : Primrec fun input :
        PlacedHorizontalLensRouteInput × Cell =>
        AxisDirection.between input.1.1.1.1.1 input.1.1.1.1.2 :=
      AxisDirection.between_primrec.comp origin finish
    exact AxisDirection.placePoint_primrec.comp
      (Primrec.pair (Primrec.pair origin direction) Primrec.snd)
  exact Primrec.list_map base transform.to₂

private def carrierLensRouteData
    {Vertex : Type*} [DecidableEq Vertex]
    (input : CarrierLensRouteInput Vertex) :
    PlacedHorizontalLensRouteInput := by
  let origin := input.1.1.2.first.position input.1.1.1
  let finish := input.1.1.2.second.position input.1.1.1
  exact ((((origin, finish),
    AxisDirection.axisSpan origin finish), input.1.2), input.2)

private def carrierLensRoute
    {Vertex : Type*} [DecidableEq Vertex]
    (input : CarrierLensRouteInput Vertex) : List Cell :=
  placedHorizontalLensRoute (carrierLensRouteData input)

private theorem carrierLensRouteData_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (carrierLensRouteData (Vertex := Vertex)) := by
  have firstNode : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.2.first :=
    EqualityLink.first_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have secondNode : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.2.second :=
    EqualityLink.second_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have graph : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have firstPosition : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.2.first.position input.1.1.1 :=
    CarrierNode.position_primrec.comp graph firstNode
  have secondPosition : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.2.second.position input.1.1.1 :=
    CarrierNode.position_primrec.comp graph secondNode
  have span : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      AxisDirection.axisSpan
        (input.1.1.2.first.position input.1.1.1)
        (input.1.1.2.second.position input.1.1.1) :=
    AxisDirection.axisSpan_primrec.comp firstPosition secondPosition
  have endpointsSpan : Primrec fun input :
      CarrierLensRouteInput Vertex =>
      ((input.1.1.2.first.position input.1.1.1,
        input.1.1.2.second.position input.1.1.1),
        AxisDirection.axisSpan
          (input.1.1.2.first.position input.1.1.1)
          (input.1.1.2.second.position input.1.1.1)) :=
    Primrec.pair (Primrec.pair firstPosition secondPosition) span
  have throughClause : Primrec fun input :
      CarrierLensRouteInput Vertex =>
      (((input.1.1.2.first.position input.1.1.1,
        input.1.1.2.second.position input.1.1.1),
        AxisDirection.axisSpan
          (input.1.1.2.first.position input.1.1.1)
          (input.1.1.2.second.position input.1.1.1)), input.1.2) :=
    Primrec.pair endpointsSpan (Primrec.snd.comp Primrec.fst)
  exact (Primrec.pair throughClause Primrec.snd).of_eq fun _ => rfl

private theorem carrierLensRoute_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (carrierLensRoute (Vertex := Vertex)) :=
  placedHorizontalLensRoute_primrec.comp carrierLensRouteData_primrec

abbrev CarrierRouteInput (Variable : Type*) :=
  ((PeriodicCNF Variable × EqualityLink CarrierNode) × Nat) × Nat

def carrierRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : CarrierRouteInput Variable) : List Cell :=
  carrierLensRoute
    (((PeriodicCNF.incidenceGraph input.1.1.1,
      input.1.1.2), input.1.2), input.2)

theorem carrierRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (carrierRoute (Variable := Variable)) := by
  exact (carrierLensRoute_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (PeriodicCNF.incidenceGraph_primrec.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)).of_eq
        fun _ => rfl

abbrev TranslatedCornerRouteInput :=
  (((Cell × (CornerPort × CornerPort)) × Nat) × Nat)

def translatedCornerRoute
    (input : TranslatedCornerRouteInput) : List Cell :=
  (cornerEqualityRoutes input.1.1.2.1 input.1.1.2.2
    input.1.2 input.2).map (Cell.add input.1.1.1)

set_option maxHeartbeats 4000000 in
theorem translatedCornerRoute_primrec :
    Primrec translatedCornerRoute := by
  change Primrec fun input : TranslatedCornerRouteInput =>
    (cornerEqualityRoutes input.1.1.2.1 input.1.1.2.2
      input.1.2 input.2).map (Cell.add input.1.1.1)
  have baseInput : Primrec fun input : TranslatedCornerRouteInput =>
      ((input.1.1.2, input.1.2), input.2) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  have base : Primrec fun input : TranslatedCornerRouteInput =>
      cornerEqualityRoutes input.1.1.2.1 input.1.1.2.2
        input.1.2 input.2 :=
    cornerEqualityRoutes_primrec.comp baseInput
  have transform : Primrec fun input :
      TranslatedCornerRouteInput × Cell =>
      Cell.add input.1.1.1.1 input.2 :=
    Computability.cell_add_primrec.comp
      (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd
  exact Primrec.list_map base transform.to₂

end PeriodicOrthocrossing

end LeanTrominoes
