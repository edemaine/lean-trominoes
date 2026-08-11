import LeanTrominoes.PeriodicCNFPlanarOneInThreeNoUnitsPositioned
import LeanTrominoes.PeriodicOneInThreeNoUnitsComputability
import LeanTrominoes.PeriodicOneInThreePositionedComputability

/-!
# Computability of positioned exact-one unit elimination

The constant-size empty- and unit-clause replacement gadgets, their positioned
formula, and the period and position queries of their companion placement are
primitive recursive from the corresponding finite source data.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

set_option maxHeartbeats 800000

theorem generatedClausePosition_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : PositionedPeriodicClause Variable × Nat =>
      generatedClausePosition input.1 input.2 := by
  have length : Primrec fun input :
      PositionedPeriodicClause Variable × Nat =>
      input.1.literals.length :=
    Primrec.list_length.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.fst)
  have emptyOffset : Primrec fun input :
      PositionedPeriodicClause Variable × Nat =>
      ([(3, 1), (5, 4)] : List Cell).getD input.2 (1, 4) :=
    (Primrec.list_getD ((1, 4) : Cell)).comp
      (Primrec.const ([(3, 1), (5, 4)] : List Cell)) Primrec.snd
  have singletonOffset : Primrec fun input :
      PositionedPeriodicClause Variable × Nat =>
      ([(3, 2)] : List Cell).getD input.2 (3, 4) :=
    (Primrec.list_getD ((3, 4) : Cell)).comp
      (Primrec.const ([(3, 2)] : List Cell)) Primrec.snd
  have localOffset : Primrec fun input :
      PositionedPeriodicClause Variable × Nat =>
      if input.1.literals.length = 0 then
        ([(3, 1), (5, 4)] : List Cell).getD input.2 (1, 4)
      else if input.1.literals.length = 1 then
        ([(3, 2)] : List Cell).getD input.2 (3, 4)
      else (3, 3) :=
    Primrec.ite
      (Primrec.eq.comp length (Primrec.const 0))
      emptyOffset
      (Primrec.ite
        (Primrec.eq.comp length (Primrec.const 1))
        singletonOffset (Primrec.const (3, 3)))
  have implementation : Primrec fun input :
      PositionedPeriodicClause Variable × Nat =>
      Cell.add (Cell.scale gadgetScale input.1.position)
        (if input.1.literals.length = 0 then
          ([(3, 1), (5, 4)] : List Cell).getD input.2 (1, 4)
        else if input.1.literals.length = 1 then
          ([(3, 2)] : List Cell).getD input.2 (3, 4)
        else (3, 3)) :=
    Computability.cell_add_primrec.comp
      (Computability.cell_scale_primrec.comp
        (Primrec.const gadgetScale)
        (PositionedPeriodicClause.position_primrec.comp Primrec.fst))
      localOffset
  exact implementation.of_eq fun input => by
    rcases input with ⟨⟨position, literals⟩, index⟩
    rcases literals with _ | ⟨first, rest⟩
    · rcases index with _ | index
      · rfl
      rcases index with _ | index <;> rfl
    · cases rest with
      | nil =>
          rcases index with _ | index <;> rfl
      | cons second rest => rfl

theorem clauseGadget_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × PositionedPeriodicClause Variable =>
      clauseGadget input.1 input.2 := by
  have generated : Primrec fun input :
      Nat × PositionedPeriodicClause Variable =>
      (PeriodicOneInThreeNoUnits.clauseClauses
        input.1 input.2.literals).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicOneInThreeNoUnits.clauseClauses_primrec.comp
        (Primrec.pair Primrec.fst
          (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)))
  have one : Primrec₂ fun
      (input : Nat × PositionedPeriodicClause Variable)
      (taggedClause :
        PeriodicClause (OneInThreeNoUnitVariable Variable) × Nat) =>
      PositionedPeriodicClause.mk
        (generatedClausePosition input.2 taggedClause.2)
        taggedClause.1 := by
    change Primrec fun combined :
        (Nat × PositionedPeriodicClause Variable) ×
          (PeriodicClause (OneInThreeNoUnitVariable Variable) × Nat) =>
      PositionedPeriodicClause.mk
        (generatedClausePosition combined.1.2 combined.2.2)
        combined.2.1
    have position : Primrec fun combined :
        (Nat × PositionedPeriodicClause Variable) ×
          (PeriodicClause (OneInThreeNoUnitVariable Variable) × Nat) =>
      generatedClausePosition combined.1.2 combined.2.2 :=
      generatedClausePosition_primrec.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))
    exact (PositionedPeriodicClause.mk_primrec
      (Variable := OneInThreeNoUnitVariable Variable)).comp
        (Primrec.pair position (Primrec.fst.comp Primrec.snd))
  exact Primrec.list_map generated one

theorem formula_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (formula : PositionedPeriodicCNF Variable →
      PositionedPeriodicCNF (OneInThreeNoUnitVariable Variable)) := by
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
    Primrec fun input : (Input × Nat) × OneInThreeNoUnitAux =>
      auxiliaryOccurrencePosition
        (source input.1.1) input.1.2 input.2 := by
  have clausePosition : Primrec fun input :
      (Input × Nat) × OneInThreeNoUnitAux =>
      (source input.1.1).clausePosition input.1.2 :=
    PositionedPeriodicCNF.clausePosition_primrec.comp
      (Primrec.pair
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
  exact Computability.cell_add_primrec.comp
    (Computability.cell_scale_primrec.comp
      (Primrec.const gadgetScale) clausePosition)
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
    (Primrec.const gadgetScale.toNat) periodPrimrec).of_eq
      fun _ => rfl

theorem placement_position_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : Input × OneInThreeNoUnitVariable Variable =>
      (placement (source input.1)
        (sourcePlacement input.1)).position input.2 := by
  have original : Primrec₂ fun
      (input : Input × OneInThreeNoUnitVariable Variable)
      (atom : Variable) =>
      Cell.scale gadgetScale
        ((sourcePlacement input.1).position atom) := by
    exact Computability.cell_scale_primrec.comp₂
      (Primrec.const gadgetScale).to₂
      (positionPrimrec.comp
        (Primrec.pair
          (Primrec.fst.comp₂ Primrec₂.left)
          Primrec₂.right)).to₂
  have auxiliary : Primrec₂ fun
      (input : Input × OneInThreeNoUnitVariable Variable)
      (data : (Nat × PeriodicClause Variable) × OneInThreeNoUnitAux) =>
      Cell.sub
        (auxiliaryOccurrencePosition
          (source input.1) data.1.1 data.2)
        (Cell.scale
          (gadgetScale * ((sourcePlacement input.1).period : Int))
          (PeriodicOneInThree.anchor data.1.2)) := by
    change Primrec fun combined :
        (Input × OneInThreeNoUnitVariable Variable) ×
          ((Nat × PeriodicClause Variable) × OneInThreeNoUnitAux) =>
      Cell.sub
        (auxiliaryOccurrencePosition
          (source combined.1.1) combined.2.1.1 combined.2.2)
        (Cell.scale
          (gadgetScale *
            ((sourcePlacement combined.1.1).period : Int))
          (PeriodicOneInThree.anchor combined.2.1.2))
    have occurrencePosition : Primrec fun combined :
        (Input × OneInThreeNoUnitVariable Variable) ×
          ((Nat × PeriodicClause Variable) × OneInThreeNoUnitAux) =>
      auxiliaryOccurrencePosition
        (source combined.1.1) combined.2.1.1 combined.2.2 :=
      auxiliaryOccurrencePosition_primrec source sourcePrimrec |>.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.snd))
    have scale : Primrec fun combined :
        (Input × OneInThreeNoUnitVariable Variable) ×
          ((Nat × PeriodicClause Variable) × OneInThreeNoUnitAux) =>
      gadgetScale * ((sourcePlacement combined.1.1).period : Int) :=
      Computability.int_multiply_primrec.comp
        (Primrec.const gadgetScale)
        (Computability.int_ofNat_primrec.comp
          (periodPrimrec.comp (Primrec.fst.comp Primrec.fst)))
    have anchor : Primrec fun combined :
        (Input × OneInThreeNoUnitVariable Variable) ×
          ((Nat × PeriodicClause Variable) × OneInThreeNoUnitAux) =>
      PeriodicOneInThree.anchor combined.2.1.2 :=
      PeriodicOneInThree.anchor_primrec.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    exact Computability.cell_sub_primrec.comp occurrencePosition
      (Computability.cell_scale_primrec.comp scale anchor)
  exact (Primrec.sumCasesOn Primrec.snd original auxiliary).of_eq
    fun input => by cases input.2 <;> rfl

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
