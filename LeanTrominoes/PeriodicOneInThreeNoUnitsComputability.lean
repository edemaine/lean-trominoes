import LeanTrominoes.PeriodicOneInThreeReductionComputability
import LeanTrominoes.PeriodicOneInThreeNoUnits

/-!
# Computability of periodic exact-one unit elimination

The unit-elimination gadget is primitive recursive under the canonical
encodings.  An indexed-lookup presentation separates the three possible
source arities and is proved extensionally equal to `clauseClauses`.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

noncomputable instance : Primcodable OneInThreeNoUnitAux :=
  Primcodable.ofEquiv (Fin (Fintype.card OneInThreeNoUnitAux))
    (Fintype.equivFin OneInThreeNoUnitAux)

noncomputable instance oneInThreeNoUnitVariablePrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (OneInThreeNoUnitVariable Variable) :=
  inferInstance

theorem liftLiteral_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (liftLiteral :
      PeriodicLiteral Variable →
        PeriodicLiteral (OneInThreeNoUnitVariable Variable)) := by
  have data : Primrec fun literal : PeriodicLiteral Variable =>
      ((Sum.inl literal.atom :
          OneInThreeNoUnitVariable Variable),
        literal.offset, literal.value) :=
    Primrec.pair
      (Primrec.sumInl.comp
        PeriodicThreeCNF.literal_atom_primrec)
      (Primrec.pair
        PeriodicThreeCNF.literal_offset_primrec
        PeriodicThreeCNF.literal_value_primrec)
  exact
    (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq
      fun _ => rfl

theorem auxiliary_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        (Nat × PeriodicClause Variable) × OneInThreeNoUnitAux =>
      auxiliary input.1.1 input.1.2 input.2 := by
  have atom : Primrec fun input :
      (Nat × PeriodicClause Variable) × OneInThreeNoUnitAux =>
      (Sum.inr input :
        OneInThreeNoUnitVariable Variable) :=
    Primrec.sumInr
  have data : Primrec fun input :
      (Nat × PeriodicClause Variable) × OneInThreeNoUnitAux =>
      ((Sum.inr input :
          OneInThreeNoUnitVariable Variable),
        PeriodicOneInThree.anchor input.1.2, true) :=
    Primrec.pair atom
      (Primrec.pair
        (PeriodicOneInThree.anchor_primrec.comp
          (Primrec.snd.comp Primrec.fst))
        (Primrec.const true))
  exact
    (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq
      fun _ => rfl

/-- Indexed-lookup implementation of one unit-elimination gadget. -/
def computableClauseClauses {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    List (PeriodicClause (OneInThreeNoUnitVariable Variable)) :=
  let first :=
    (source[0]?).map liftLiteral |>.getD
      (auxiliary clauseIndex source .first)
  let firstAux := auxiliary clauseIndex source .first
  let secondAux := auxiliary clauseIndex source .second
  let thirdAux := auxiliary clauseIndex source .third
  if source.length = 0 then
    [[firstAux, secondAux],
      [secondAux, thirdAux],
      [firstAux, thirdAux]]
  else if source.length = 1 then
    [[PeriodicOneInThree.negate first, firstAux, secondAux],
      [firstAux, secondAux]]
  else
    [source.map liftLiteral]

theorem computableClauseClauses_eq {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    computableClauseClauses clauseIndex source =
      clauseClauses clauseIndex source := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · cases rest with
    | nil => rfl
    | cons second rest => rfl

theorem computableClauseClauses_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × PeriodicClause Variable =>
      computableClauseClauses input.1 input.2 := by
  let Input := Nat × PeriodicClause Variable
  have source : Primrec fun input : Input => input.2 :=
    Primrec.snd
  have length : Primrec fun input : Input => input.2.length :=
    Primrec.list_length.comp source
  have aux (kind : OneInThreeNoUnitAux) :
      Primrec fun input : Input =>
        auxiliary input.1 input.2 kind :=
    auxiliary_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const kind))
  have selected :
      Primrec fun input : Input => input.2[0]? :=
    Primrec.list_getElem?.comp source (Primrec.const 0)
  have lifted :
      Primrec fun input : Input =>
        (input.2[0]?).map liftLiteral :=
    Primrec.option_map selected
      (liftLiteral_primrec.comp Primrec.snd).to₂
  have first :
      Primrec fun input : Input =>
        (input.2[0]?).map liftLiteral |>.getD
          (auxiliary input.1 input.2 .first) :=
    Primrec.option_getD.comp lifted (aux .first)
  have negativeFirst :
      Primrec fun input : Input =>
        PeriodicOneInThree.negate
          ((input.2[0]?).map liftLiteral |>.getD
            (auxiliary input.1 input.2 .first)) :=
    PeriodicOneInThree.negate_primrec.comp first
  have emptyOutput :
      Primrec fun input : Input =>
        [[auxiliary input.1 input.2 .first,
            auxiliary input.1 input.2 .second],
          [auxiliary input.1 input.2 .second,
            auxiliary input.1 input.2 .third],
          [auxiliary input.1 input.2 .first,
            auxiliary input.1 input.2 .third]] :=
    Primrec.list_cons.comp
      (Primrec.list_cons.comp (aux .first)
        (Primrec.list_cons.comp (aux .second)
          (Primrec.const [])))
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (aux .second)
          (Primrec.list_cons.comp (aux .third)
            (Primrec.const [])))
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (aux .first)
            (Primrec.list_cons.comp (aux .third)
              (Primrec.const [])))
          (Primrec.const [])))
  have singletonOutput :
      Primrec fun input : Input =>
        [[PeriodicOneInThree.negate
            ((input.2[0]?).map liftLiteral |>.getD
              (auxiliary input.1 input.2 .first)),
            auxiliary input.1 input.2 .first,
            auxiliary input.1 input.2 .second],
          [auxiliary input.1 input.2 .first,
            auxiliary input.1 input.2 .second]] :=
    Primrec.list_cons.comp
      (Primrec.list_cons.comp negativeFirst
        (Primrec.list_cons.comp (aux .first)
          (Primrec.list_cons.comp (aux .second)
            (Primrec.const []))))
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (aux .first)
          (Primrec.list_cons.comp (aux .second)
            (Primrec.const [])))
        (Primrec.const []))
  have mapped :
      Primrec fun input : Input =>
        input.2.map liftLiteral :=
    Primrec.list_map source
      (liftLiteral_primrec.comp Primrec.snd).to₂
  have embedded :
      Primrec fun input : Input =>
        [input.2.map liftLiteral] :=
    Primrec.list_cons.comp mapped (Primrec.const [])
  have lengthEq (value : Nat) :
      PrimrecPred fun input : Input =>
        input.2.length = value :=
    Primrec.eq.comp length (Primrec.const value)
  exact
    Primrec.ite (lengthEq 0) emptyOutput
      (Primrec.ite (lengthEq 1) singletonOutput embedded)

/-- The clause-local unit-elimination construction is primitive recursive. -/
theorem clauseClauses_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × PeriodicClause Variable =>
      clauseClauses input.1 input.2 :=
  computableClauseClauses_primrec.of_eq fun input =>
    computableClauseClauses_eq input.1 input.2

/-- The complete unit-elimination transformation is primitive recursive. -/
theorem formula_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (formula :
      PeriodicCNF Variable →
        PeriodicCNF (OneInThreeNoUnitVariable Variable)) := by
  have tagged : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicCNF.equivData_primrec
  have one : Primrec₂ fun (_source : PeriodicCNF Variable)
      (taggedClause : PeriodicClause Variable × Nat) =>
      clauseClauses taggedClause.2 taggedClause.1 := by
    change Primrec fun combined :
        PeriodicCNF Variable ×
          (PeriodicClause Variable × Nat) =>
      clauseClauses combined.2.2 combined.2.1
    exact clauseClauses_primrec.comp
      (Primrec.pair
        (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
  have clauses : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.zipIdx.flatMap fun taggedClause =>
        clauseClauses taggedClause.2 taggedClause.1 :=
    Primrec.list_flatMap tagged one
  exact
    (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq
      fun _ => rfl

/-- The complete unit-elimination transformation is computable. -/
theorem formula_computable
    {Variable : Type*} [Primcodable Variable] :
    Computable (formula :
      PeriodicCNF Variable →
        PeriodicCNF (OneInThreeNoUnitVariable Variable)) :=
  formula_primrec.to_comp

end PeriodicOneInThreeNoUnits
end LeanTrominoes
