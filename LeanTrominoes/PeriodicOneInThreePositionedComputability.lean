/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PeriodicCNFPlanarPeriodicizationComputability
import LeanTrominoes.PeriodicOneInThreeReductionComputability
import LeanTrominoes.PositionedPeriodicCNFComputability

/-!
# Computability of the positioned Figure 9 reduction

The clause positions and companion variable placement of the positioned
Figure 9 exact-one compiler are primitive recursive.  The parameterized
placement lemmas consume only the finite source formula and the period and
position queries of its companion placement.
-/

noncomputable section

namespace LeanTrominoes

set_option maxHeartbeats 800000

namespace PeriodicOrthocrossing.WrappedPeriodicVariable

/-- A primitive-recursive position query transports through the opaque
periodic-variable wrapper. -/
theorem position_primrec
    {Input Original : Type*} [Primcodable Input] [Primcodable Original]
    (position : Input → Original → Cell)
    (positionPrimrec : Primrec fun input : Input × Original =>
      position input.1 input.2) :
    Primrec fun input : Input × WrappedPeriodicVariable Original =>
      position input.1 input.2.original :=
  positionPrimrec.comp
    (Primrec.pair Primrec.fst
      (original_primrec.comp Primrec.snd))

end WrappedPeriodicVariable
end PeriodicOrthocrossing

namespace PlanarOneInThree

theorem generatedClausePosition_primrec :
    Primrec fun input : Cell × Nat =>
      generatedClausePosition input.1 input.2 := by
  let offsets : List Cell :=
    [(6, 2), (3, 5), (9, 5), (3, 10), (6, 10)]
  have localOffset : Primrec fun input : Cell × Nat =>
      offsets.getD input.2 (9, 10) :=
    (Primrec.list_getD ((9, 10) : Cell)).comp
      (Primrec.const offsets) Primrec.snd
  have implementation : Primrec fun input : Cell × Nat =>
      Cell.add (Cell.scale gadgetScale input.1)
        (offsets.getD input.2 (9, 10)) :=
    Computability.cell_add_primrec.comp
      (Computability.cell_scale_primrec.comp
        (Primrec.const gadgetScale) Primrec.fst)
      localOffset
  exact implementation.of_eq fun input => by
    unfold offsets
    rcases input with ⟨position, index⟩
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

end PlanarOneInThree

namespace PeriodicOneInThreePositioned

theorem clauseGadget_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × PositionedPeriodicClause Variable =>
      clauseGadget input.1 input.2 := by
  have generated : Primrec fun input :
      Nat × PositionedPeriodicClause Variable =>
      (PeriodicOneInThree.clauseClauses
        input.1 input.2.literals).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicOneInThree.clauseClauses_primrec.comp
        (Primrec.pair Primrec.fst
          (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)))
  have one : Primrec₂ fun
      (input : Nat × PositionedPeriodicClause Variable)
      (taggedClause :
        PeriodicClause (OneInThreeVariable Variable) × Nat) =>
      PositionedPeriodicClause.mk
        (PlanarOneInThree.generatedClausePosition
          input.2.position taggedClause.2)
        taggedClause.1 := by
    change Primrec fun combined :
        (Nat × PositionedPeriodicClause Variable) ×
          (PeriodicClause (OneInThreeVariable Variable) × Nat) =>
      PositionedPeriodicClause.mk
        (PlanarOneInThree.generatedClausePosition
          combined.1.2.position combined.2.2)
        combined.2.1
    have position : Primrec fun combined :
        (Nat × PositionedPeriodicClause Variable) ×
          (PeriodicClause (OneInThreeVariable Variable) × Nat) =>
      PlanarOneInThree.generatedClausePosition
        combined.1.2.position combined.2.2 :=
      PlanarOneInThree.generatedClausePosition_primrec.comp
        (Primrec.pair
          (PositionedPeriodicClause.position_primrec.comp
            (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd))
    exact (PositionedPeriodicClause.mk_primrec
      (Variable := OneInThreeVariable Variable)).comp
      (Primrec.pair position (Primrec.fst.comp Primrec.snd))
  exact Primrec.list_map generated one

theorem formula_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (formula : PositionedPeriodicCNF Variable →
      PositionedPeriodicCNF (OneInThreeVariable Variable)) := by
  have tagged : Primrec fun source : PositionedPeriodicCNF Variable =>
      source.clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PositionedPeriodicCNF.clauses_primrec
  have one : Primrec₂ fun (_source : PositionedPeriodicCNF Variable)
      (taggedClause : PositionedPeriodicClause Variable × Nat) =>
      clauseGadget taggedClause.2 taggedClause.1 := by
    change Primrec fun combined : PositionedPeriodicCNF Variable ×
        (PositionedPeriodicClause Variable × Nat) =>
      clauseGadget combined.2.2 combined.2.1
    exact clauseGadget_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
  have clauses : Primrec fun source : PositionedPeriodicCNF Variable =>
      source.clauses.zipIdx.flatMap fun taggedClause =>
        clauseGadget taggedClause.2 taggedClause.1 :=
    Primrec.list_flatMap tagged one
  exact (PositionedPeriodicCNF.mk_primrec.comp clauses).of_eq
    fun _ => rfl

theorem auxiliaryLocalPosition_primrec :
    Primrec auxiliaryLocalPosition :=
  Primrec.dom_finite auxiliaryLocalPosition

theorem auxiliaryOccurrencePosition_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePrimrec : Primrec source) :
    Primrec fun input : (Input × Nat) × OneInThreeAux =>
      auxiliaryOccurrencePosition
        (source input.1.1) input.1.2 input.2 := by
  have clausePosition : Primrec fun input :
      (Input × Nat) × OneInThreeAux =>
      (source input.1.1).clausePosition input.1.2 :=
    PositionedPeriodicCNF.clausePosition_primrec.comp
      (Primrec.pair
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
  exact Computability.cell_add_primrec.comp
    (Computability.cell_scale_primrec.comp
      (Primrec.const PlanarOneInThree.gadgetScale) clausePosition)
    (auxiliaryLocalPosition_primrec.comp Primrec.snd)

theorem placement_period_primrec
    {Input Variable : Type*} [Primcodable Input]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period) :
    Primrec fun input =>
      (placement (source input) (sourcePlacement input)).period := by
  exact (Primrec.nat_mul.comp
    (Primrec.const PlanarOneInThree.gadgetScale.toNat)
    periodPrimrec).of_eq fun _ => rfl

theorem placement_position_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : Input × OneInThreeVariable Variable =>
      (placement (source input.1)
        (sourcePlacement input.1)).position input.2 := by
  have original : Primrec₂ fun
      (input : Input × OneInThreeVariable Variable) (atom : Variable) =>
      Cell.scale PlanarOneInThree.gadgetScale
        ((sourcePlacement input.1).position atom) := by
    exact Computability.cell_scale_primrec.comp₂
      (Primrec.const PlanarOneInThree.gadgetScale).to₂
      (positionPrimrec.comp
        (Primrec.pair
          (Primrec.fst.comp₂ Primrec₂.left)
          Primrec₂.right)).to₂
  have auxiliary : Primrec₂ fun
      (input : Input × OneInThreeVariable Variable)
      (data : (Nat × PeriodicClause Variable) × OneInThreeAux) =>
      Cell.sub
        (auxiliaryOccurrencePosition
          (source input.1) data.1.1 data.2)
        (Cell.scale
          (PlanarOneInThree.gadgetScale *
            ((sourcePlacement input.1).period : Int))
          (PeriodicOneInThree.anchor data.1.2)) := by
    change Primrec fun combined :
        (Input × OneInThreeVariable Variable) ×
          ((Nat × PeriodicClause Variable) × OneInThreeAux) =>
      Cell.sub
        (auxiliaryOccurrencePosition
          (source combined.1.1) combined.2.1.1 combined.2.2)
        (Cell.scale
          (PlanarOneInThree.gadgetScale *
            ((sourcePlacement combined.1.1).period : Int))
          (PeriodicOneInThree.anchor combined.2.1.2))
    have occurrencePosition : Primrec fun combined :
        (Input × OneInThreeVariable Variable) ×
          ((Nat × PeriodicClause Variable) × OneInThreeAux) =>
      auxiliaryOccurrencePosition
        (source combined.1.1) combined.2.1.1 combined.2.2 :=
      auxiliaryOccurrencePosition_primrec source sourcePrimrec |>.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.snd))
    have scale : Primrec fun combined :
        (Input × OneInThreeVariable Variable) ×
          ((Nat × PeriodicClause Variable) × OneInThreeAux) =>
      PlanarOneInThree.gadgetScale *
        ((sourcePlacement combined.1.1).period : Int) :=
      Computability.int_multiply_primrec.comp
        (Primrec.const PlanarOneInThree.gadgetScale)
        (Computability.int_ofNat_primrec.comp
          (periodPrimrec.comp
            (Primrec.fst.comp Primrec.fst)))
    have anchor : Primrec fun combined :
        (Input × OneInThreeVariable Variable) ×
          ((Nat × PeriodicClause Variable) × OneInThreeAux) =>
      PeriodicOneInThree.anchor combined.2.1.2 :=
      PeriodicOneInThree.anchor_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    exact Computability.cell_sub_primrec.comp occurrencePosition
      (Computability.cell_scale_primrec.comp scale anchor)
  exact (Primrec.sumCasesOn Primrec.snd original auxiliary).of_eq
    fun input => by cases input.2 <;> rfl

end PeriodicOneInThreePositioned
end LeanTrominoes
