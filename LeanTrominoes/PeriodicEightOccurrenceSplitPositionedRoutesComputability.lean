import LeanTrominoes.PeriodicEightOccurrenceSplitCanonicalAngularRoutes
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedComputability
import LeanTrominoes.PeriodicGridDrawingGeometryComputability
import LeanTrominoes.PeriodicThreeSATThreeAngularOrderComputability

/-!
# Computability of positioned fixed-eight routes

The canonical fixed-eight route family has two finite, executable branches.
Copied source incidences use a Manhattan detour followed by one translated
Figure 7 fan spoke.  Appended implication clauses select a route from the
fixed nine-clause ring and translate it to the source variable's macrocell.

This module proves primitive recursiveness of their local geometry and the
flattened Figure 7 cycle metadata.  Subsequent modules assemble these pieces
into the presentation-indexed copied and total route lookups.
-/

noncomputable section

namespace LeanTrominoes

set_option maxHeartbeats 3000000

theorem joinAtEndpoint_primrec {Input α : Type*}
    [Primcodable Input] [Primcodable α]
    (first second : Input → List α)
    (firstPrimrec : Primrec first)
    (secondPrimrec : Primrec second) :
    Primrec fun input => joinAtEndpoint (first input) (second input) := by
  exact (Primrec.list_append.comp firstPrimrec
    (Primrec.list_tail.comp secondPrimrec)).of_eq fun _ => rfl

namespace PositionedPeriodicCNF

theorem freshDetourCoordinate_primrec :
    Primrec₂ freshDetourCoordinate := by
  unfold freshDetourCoordinate
  exact Computability.int_add_primrec.comp
    Computability.int_max_primrec (Primrec.const 1)

theorem orthogonalDetour_primrec : Primrec₂ orthogonalDetour := by
  change Primrec fun input : Cell × Cell =>
    orthogonalDetour input.1 input.2
  have detourX : Primrec fun input : Cell × Cell =>
      freshDetourCoordinate input.1.1 input.2.1 :=
    freshDetourCoordinate_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have detourY : Primrec fun input : Cell × Cell =>
      freshDetourCoordinate input.1.2 input.2.2 :=
    freshDetourCoordinate_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have second : Primrec fun input : Cell × Cell =>
      (freshDetourCoordinate input.1.1 input.2.1, input.1.2) :=
    Primrec.pair detourX (Primrec.snd.comp Primrec.fst)
  have third : Primrec fun input : Cell × Cell =>
      (freshDetourCoordinate input.1.1 input.2.1,
        freshDetourCoordinate input.1.2 input.2.2) :=
    Primrec.pair detourX detourY
  have fourth : Primrec fun input : Cell × Cell =>
      (input.2.1, freshDetourCoordinate input.1.2 input.2.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd) detourY
  have output : Primrec fun input : Cell × Cell =>
      [input.1,
        (freshDetourCoordinate input.1.1 input.2.1, input.1.2),
        (freshDetourCoordinate input.1.1 input.2.1,
          freshDetourCoordinate input.1.2 input.2.2),
        (input.2.1, freshDetourCoordinate input.1.2 input.2.2),
        input.2] :=
    Primrec.list_cons.comp Primrec.fst <|
    Primrec.list_cons.comp second <|
    Primrec.list_cons.comp third <|
    Primrec.list_cons.comp fourth <|
    Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  exact output.of_eq fun _ => rfl

theorem canonicalLiteralPosition_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat)
    (position : Input → Variable → Cell)
    (periodPrimrec : Primrec period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      position input.1 input.2) :
    Primrec fun input :
        (Input × PositionedPeriodicClause Variable) ×
          PeriodicLiteral Variable =>
      canonicalLiteralPosition
        { period := period input.1.1
          position := position input.1.1 }
        input.1.2 input.2 := by
  have anchor : Primrec fun input :
      (Input × PositionedPeriodicClause Variable) ×
        PeriodicLiteral Variable =>
      PeriodicCNF.clauseAnchor input.1.2.literals :=
    PeriodicCNF.clauseAnchor_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp
        (Primrec.snd.comp Primrec.fst))
  have relative : Primrec fun input :
      (Input × PositionedPeriodicClause Variable) ×
        PeriodicLiteral Variable =>
      Cell.sub input.2.offset
        (PeriodicCNF.clauseAnchor input.1.2.literals) :=
    Computability.cell_sub_primrec.comp
      (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
      anchor
  have translation : Primrec fun input :
      (Input × PositionedPeriodicClause Variable) ×
        PeriodicLiteral Variable =>
      Cell.scale (period input.1.1)
        (Cell.sub input.2.offset
          (PeriodicCNF.clauseAnchor input.1.2.literals)) :=
    Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp
        (periodPrimrec.comp (Primrec.fst.comp Primrec.fst)))
      relative
  have variablePosition : Primrec fun input :
      (Input × PositionedPeriodicClause Variable) ×
        PeriodicLiteral Variable =>
      position input.1.1 input.2.atom :=
    positionPrimrec.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd))
  exact (Computability.cell_add_primrec.comp
    variablePosition translation).of_eq fun _ => rfl

end PositionedPeriodicCNF

namespace OccurrenceSplitRing

theorem spokeClausePosition_primrec : Primrec spokeClausePosition :=
  Primrec.dom_finite spokeClausePosition

theorem spokeRoute_primrec : Primrec spokeRoute :=
  Primrec.dom_finite spokeRoute

theorem RingVertex.next_primrec : Primrec RingVertex.next :=
  Primrec.dom_finite RingVertex.next

theorem cycleRoute_primrec :
    Primrec fun input : RingVertex × Nat =>
      cycleRoute input.1 input.2 := by
  have zeroRoute : Primrec fun input : RingVertex × Nat =>
      [cycleClausePosition input.1, ringVariablePosition input.1] :=
    Primrec.list_cons.comp
      (cycleClausePosition_primrec.comp Primrec.fst)
      (Primrec.list_cons.comp
        (ringVariablePosition_primrec.comp Primrec.fst)
        (Primrec.const []))
  have one : Primrec fun input : RingVertex × Nat =>
      [cycleClausePosition input.1,
        ringVariablePosition input.1.next] :=
    Primrec.list_cons.comp
      (cycleClausePosition_primrec.comp Primrec.fst)
      (Primrec.list_cons.comp
        (ringVariablePosition_primrec.comp
          (RingVertex.next_primrec.comp Primrec.fst))
        (Primrec.const []))
  have implementation : Primrec fun input : RingVertex × Nat =>
      if input.2 = 0 then
        [cycleClausePosition input.1, ringVariablePosition input.1]
      else if input.2 = 1 then
        [cycleClausePosition input.1,
          ringVariablePosition input.1.next]
      else [] :=
    Primrec.ite
      (Primrec.eq.comp Primrec.snd (Primrec.const 0)) zeroRoute <|
    Primrec.ite
      (Primrec.eq.comp Primrec.snd (Primrec.const 1)) one
      (Primrec.const [])
  exact implementation.of_eq fun input => by
    unfold cycleRoute
    rcases input.2 with _ | index
    · rfl
    rcases index with _ | index <;> rfl

theorem cycleRoutes_primrec :
    Primrec fun input : Nat × Nat => cycleRoutes input.1 input.2 := by
  have implementation : Primrec fun input : Nat × Nat =>
      if input.1 < presentedCycleVertices.length then
        cycleRoute
          (presentedCycleVertices.getD input.1 .separator)
          input.2
      else [] := by
    have clauseValid : PrimrecPred fun input : Nat × Nat =>
        input.1 < presentedCycleVertices.length :=
      Primrec.nat_lt.comp Primrec.fst
        (Primrec.const presentedCycleVertices.length)
    have vertex : Primrec fun input : Nat × Nat =>
        presentedCycleVertices.getD input.1 .separator :=
      (Primrec.list_getD (.separator : RingVertex)).comp
        (Primrec.const presentedCycleVertices) Primrec.fst
    have route : Primrec fun input : Nat × Nat =>
        cycleRoute
          (presentedCycleVertices.getD input.1 .separator)
          input.2 := by
      exact cycleRoute_primrec.comp (Primrec.pair vertex Primrec.snd)
    exact Primrec.ite clauseValid route (Primrec.const [])
  exact implementation.of_eq fun _ => rfl

end OccurrenceSplitRing

namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

namespace CycleClauseMetadata

def equivData {Variable : Type*} :
    CycleClauseMetadata Variable ≃
      (PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable) × Variable) × Nat where
  toFun metadata :=
    ((metadata.clause, metadata.atom), metadata.localClauseIndex)
  invFun data := ⟨data.1.1, data.1.2, data.2⟩
  left_inv metadata := by cases metadata; rfl
  right_inv data := by rcases data with ⟨⟨clause, atom⟩, index⟩; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (CycleClauseMetadata Variable) :=
  Primcodable.ofEquiv _ equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CycleClauseMetadata.clause :
      CycleClauseMetadata Variable →
        PositionedPeriodicClause (ThreeOccurrenceVariable Variable)) :=
  ((Primrec.fst.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem atom_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CycleClauseMetadata.atom :
      CycleClauseMetadata Variable → Variable) :=
  ((Primrec.snd.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem localClauseIndex_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CycleClauseMetadata.localClauseIndex :
      CycleClauseMetadata Variable → Nat) :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (PositionedPeriodicClause
          (ThreeOccurrenceVariable Variable) × Variable) × Nat =>
      CycleClauseMetadata.mk data.1.1 data.1.2 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end CycleClauseMetadata

private theorem occurrence_idxOf_decidableEq_eq
    {Variable : Type*} [DecidableEq Variable]
    (item : ThreeOccurrenceVariable Variable)
    (items : List (ThreeOccurrenceVariable Variable)) :
    @List.idxOf (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq item items = items.idxOf item := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
      rw [induction]

theorem incidenceRelativeOffset_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        PositionedPeriodicClause Variable × PeriodicLiteral Variable =>
      incidenceRelativeOffset input.1 input.2 := by
  exact Computability.cell_sub_primrec.comp
    (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
    (PeriodicCNF.clauseAnchor_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.fst))

theorem angularOccurrenceIndex_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (copies : Input → Variable →
      List (ThreeOccurrenceVariable Variable))
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      copies input.1 input.2) :
    Primrec fun input :
        (((Input × PositionedPeriodicClause Variable) ×
          PeriodicLiteral Variable) × Nat) × Nat =>
      (copies input.1.1.1.1 input.1.1.2.atom).idxOf
        (indexedOccurrence input.1.1.2 input.1.2 input.2) := by
  let Query :=
    (((Input × PositionedPeriodicClause Variable) ×
      PeriodicLiteral Variable) × Nat) × Nat
  have atom : Primrec fun input : Query => input.1.1.2.atom :=
    PeriodicThreeCNF.literal_atom_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have items : Primrec fun input : Query =>
      copies input.1.1.1.1 input.1.1.2.atom :=
    copiesPrimrec.comp
      (Primrec.pair
        (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        atom)
  have occurrence : Primrec fun input : Query =>
      indexedOccurrence input.1.1.2 input.1.2 input.2 :=
    Primrec.pair atom
      (Primrec.pair
        (Primrec.snd.comp Primrec.fst)
        Primrec.snd)
  exact (Primrec.list_idxOf.comp occurrence items).of_eq fun input =>
    occurrence_idxOf_decidableEq_eq
      (indexedOccurrence input.1.1.2 input.1.2 input.2)
      (copies input.1.1.1.1 input.1.1.2.atom)

/-- The east-first port lookup is primitive recursive from the finite source
and the computational `copies` field of an occurrence order. -/
theorem occurrencePortsOfOrder_port_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (order : (input : Input) → OccurrenceOrder (source input))
    (sourcePrimrec : Primrec source)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      (order input.1).copies input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      (occurrencePortsOfAngularOrder
        (source input.1.1) (order input.1.1)).port
          input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have selectedLiteral : Primrec fun input : Query =>
      literalAt (source input.1.1) input.1.2 input.2 :=
    PeriodicEightOccurrenceSplit.literalAt_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have none : Primrec fun _input : Query => Port.east :=
    Primrec.const Port.east
  have some : Primrec₂ fun (input : Query)
      (literal : PeriodicLiteral Variable) =>
      angularPortOfIndex
        (((order input.1.1).copies literal.atom).idxOf
          (literal.atom, input.1.2, input.2)) := by
    let Combined := Query × PeriodicLiteral Variable
    have atom : Primrec fun input : Combined => input.2.atom :=
      PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd
    have items : Primrec fun input : Combined =>
        (order input.1.1.1).copies input.2.atom :=
      copiesPrimrec.comp
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          atom)
    have occurrence : Primrec fun input : Combined =>
        (input.2.atom, input.1.1.2, input.1.2) :=
      Primrec.pair atom
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
    exact PeriodicEightOccurrenceSplit.angularPortOfIndex_primrec.comp
      ((Primrec.list_idxOf.comp occurrence items).of_eq fun input =>
        occurrence_idxOf_decidableEq_eq
          (input.2.atom, input.1.1.2, input.1.2)
          ((order input.1.1.1).copies input.2.atom)) |>.to₂
  exact (Primrec.option_casesOn selectedLiteral none some).of_eq
    fun input => by
      simp only [occurrencePortsOfAngularOrder,
        angularOrderedOccurrencePort]
      cases literalAt (source input.1.1) input.1.2 input.2 <;> rfl

theorem angularFanBoundaryPositionAt_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : (((Input × Variable) × Cell) × Nat) =>
      angularFanBoundaryPositionAt
        (sourcePlacement input.1.1.1) input.1.1.2 input.1.2 input.2 := by
  let Query := (((Input × Variable) × Cell) × Nat)
  have origin : Primrec fun input : Query =>
      macroOrigin (sourcePlacement input.1.1.1) input.1.1.2 :=
    macroOrigin_primrec sourcePlacement positionPrimrec |>.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have port : Primrec fun input : Query => angularPortOfIndex input.2 :=
    PeriodicEightOccurrenceSplit.angularPortOfIndex_primrec.comp Primrec.snd
  have boundary : Primrec fun input : Query =>
      Cell.add
        (macroOrigin (sourcePlacement input.1.1.1) input.1.1.2)
        (spokeClausePosition (angularPortOfIndex input.2)) :=
    Computability.cell_add_primrec.comp origin
      (OccurrenceSplitRing.spokeClausePosition_primrec.comp port)
  have translation : Primrec fun input : Query =>
      Cell.scale
        (refinementScale.toNat *
          (sourcePlacement input.1.1.1).period)
        input.1.2 :=
    Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp
        (Primrec.nat_mul.comp
          (Primrec.const refinementScale.toNat)
          (periodPrimrec.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
      (Primrec.snd.comp Primrec.fst)
  exact (Computability.cell_add_primrec.comp
    boundary translation).of_eq fun _ => rfl

theorem angularFanSpokeRouteAt_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : (((Input × Variable) × Cell) × Nat) =>
      angularFanSpokeRouteAt
        (sourcePlacement input.1.1.1) input.1.1.2 input.1.2 input.2 := by
  let Query := (((Input × Variable) × Cell) × Nat)
  have origin : Primrec fun input : Query =>
      macroOrigin (sourcePlacement input.1.1.1) input.1.1.2 :=
    macroOrigin_primrec sourcePlacement positionPrimrec |>.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have spoke : Primrec fun input : Query =>
      spokeRoute (angularPortOfIndex input.2) :=
    OccurrenceSplitRing.spokeRoute_primrec.comp
      (PeriodicEightOccurrenceSplit.angularPortOfIndex_primrec.comp
        Primrec.snd)
  have localSpoke : Primrec fun input : Query =>
      (spokeRoute (angularPortOfIndex input.2)).map
        (Cell.add
          (macroOrigin (sourcePlacement input.1.1.1) input.1.1.2)) :=
    Primrec.list_map spoke
      (Computability.cell_add_primrec.comp
        (origin.comp Primrec.fst) Primrec.snd).to₂
  have translation : Primrec fun input : Query =>
      Cell.scale
        (refinementScale.toNat *
          (sourcePlacement input.1.1.1).period)
        input.1.2 :=
    Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp
        (Primrec.nat_mul.comp
          (Primrec.const refinementScale.toNat)
          (periodPrimrec.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.list_map localSpoke
    (Computability.cell_add_primrec.comp
      (translation.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

theorem angularOccurrenceSuffix_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (order : (input : Input) → OccurrenceOrder (source input).erase)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (copiesPrimrec : Primrec fun input : Input × Variable =>
      (order input.1).copies input.2) :
    Primrec fun input :
        (((Input × PositionedPeriodicClause Variable) ×
          PeriodicLiteral Variable) × Nat) × Nat =>
      angularOccurrenceSuffix
        (sourcePlacement input.1.1.1.1)
        (order input.1.1.1.1) input.1.1.1.2 input.1.1.2
        input.1.2 input.2 := by
  let Query :=
    (((Input × PositionedPeriodicClause Variable) ×
      PeriodicLiteral Variable) × Nat) × Nat
  have relative : Primrec fun input : Query =>
      incidenceRelativeOffset input.1.1.1.2 input.1.1.2 :=
    incidenceRelativeOffset_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have index : Primrec fun input : Query =>
      angularOccurrenceIndex (order input.1.1.1.1)
        input.1.1.2 input.1.2 input.2 :=
    angularOccurrenceIndex_primrec
      (fun input atom => (order input).copies atom)
      copiesPrimrec
  exact (angularFanSpokeRouteAt_primrec
    sourcePlacement periodPrimrec positionPrimrec).comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (PeriodicThreeCNF.literal_atom_primrec.comp
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
          relative)
        index) |>.of_eq fun _ => rfl

theorem positionedCycleRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : ((Input × Variable) × Nat) × Nat =>
      positionedCycleRoutes
        (sourcePlacement input.1.1.1) input.1.1.2 input.1.2 input.2 := by
  let Query := ((Input × Variable) × Nat) × Nat
  have origin : Primrec fun input : Query =>
      macroOrigin (sourcePlacement input.1.1.1) input.1.1.2 :=
    macroOrigin_primrec sourcePlacement positionPrimrec |>.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have route : Primrec fun input : Query =>
      OccurrenceSplitRing.cycleRoutes input.1.2 input.2 :=
    OccurrenceSplitRing.cycleRoutes_primrec.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (Primrec.list_map route
    (Computability.cell_add_primrec.comp
      (origin.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

theorem cycleClauseMetadataFor_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : Input × Variable =>
      cycleClauseMetadataFor (sourcePlacement input.1) input.2 := by
  have clauses : Primrec fun input : Input × Variable =>
      cycleClausesFor (sourcePlacement input.1) input.2 :=
    cycleClausesFor_primrec sourcePlacement positionPrimrec
  have tagged : Primrec fun input : Input × Variable =>
      (cycleClausesFor (sourcePlacement input.1) input.2).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp clauses
  have metadata : Primrec₂ fun (input : Input × Variable)
      (taggedClause :
        PositionedPeriodicClause (ThreeOccurrenceVariable Variable) × Nat) =>
      CycleClauseMetadata.mk taggedClause.1 input.2 taggedClause.2 := by
    exact CycleClauseMetadata.mk_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)) |>.to₂
  exact (Primrec.list_map tagged metadata).of_eq fun _ => rfl

theorem allCycleClauseMetadata_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input =>
      allCycleClauseMetadata (source input) (sourcePlacement input) := by
  have atoms : Primrec fun input : Input =>
      sourceVariables (source input).erase :=
    PeriodicThreeSATThree.sourceVariables_primrec.comp
      (PositionedPeriodicCNF.erase_primrec.comp sourcePrimrec)
  have block : Primrec₂ fun (input : Input) (atom : Variable) =>
      cycleClauseMetadataFor (sourcePlacement input) atom :=
    (cycleClauseMetadataFor_primrec
      sourcePlacement positionPrimrec).to₂
  exact (Primrec.list_flatMap atoms block).of_eq fun _ => rfl

theorem allCycleRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      allCycleRoutes (source input.1.1) (sourcePlacement input.1.1)
        input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have metadataList : Primrec fun input : Query =>
      allCycleClauseMetadata
        (source input.1.1) (sourcePlacement input.1.1) :=
    allCycleClauseMetadata_primrec
      source sourcePlacement sourcePrimrec positionPrimrec |>.comp
        (Primrec.fst.comp Primrec.fst)
  have selected : Primrec fun input : Query =>
      (allCycleClauseMetadata
        (source input.1.1) (sourcePlacement input.1.1))[input.1.2]? :=
    Primrec.list_getElem?.comp metadataList (Primrec.snd.comp Primrec.fst)
  have none : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (metadata : CycleClauseMetadata Variable) =>
      positionedCycleRoutes (sourcePlacement input.1.1)
        metadata.atom metadata.localClauseIndex input.2 := by
    exact positionedCycleRoutes_primrec
      sourcePlacement positionPrimrec |>.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              (CycleClauseMetadata.atom_primrec.comp Primrec.snd))
            (CycleClauseMetadata.localClauseIndex_primrec.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst)) |>.to₂
  exact (Primrec.option_casesOn selected none some).of_eq fun input => by
    unfold allCycleRoutes
    cases (allCycleClauseMetadata
      (source input.1.1) (sourcePlacement input.1.1))[input.1.2]? <;> rfl


end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
