import LeanTrominoes.PeriodicOneInThreeComputability

/-!
# Clause traversal for the periodic 1-in-3SAT reduction

The first three source positions are selected with primitive-recursive indexed
lookup and default to their corresponding padding literals.  The source
length determines which padding variables receive unit forcing clauses.  This
range-free implementation is extensionally equal to the nested pattern match
in `clauseClauses`.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThree

/-- Indexed-lookup implementation of the complete clause gadget. -/
def computableClauseClauses {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    List (PeriodicClause (OneInThreeVariable Variable)) :=
  let first :=
    (source[0]?).map liftLiteral |>.getD
      (padding clauseIndex source .firstPadding)
  let second :=
    (source[1]?).map liftLiteral |>.getD
      (padding clauseIndex source .secondPadding)
  let third :=
    (source[2]?).map liftLiteral |>.getD
      (padding clauseIndex source .thirdPadding)
  let forced :=
    if source.length = 0 then
      [.firstPadding, .secondPadding, .thirdPadding]
    else if source.length = 1 then
      [.secondPadding, .thirdPadding]
    else if source.length = 2 then
      [.thirdPadding]
    else
      []
  disjunctionGadget clauseIndex source first second third ++
    forcedPaddingClauses clauseIndex source forced

theorem computableClauseClauses_eq {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :
    computableClauseClauses clauseIndex source =
      clauseClauses clauseIndex source := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · rcases rest with _ | ⟨third, rest⟩
      · rfl
      · rfl

theorem computableClauseClauses_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input : Nat × PeriodicClause Variable =>
      computableClauseClauses input.1 input.2 := by
  let Input := Nat × PeriodicClause Variable
  have source : Primrec fun input : Input => input.2 := Primrec.snd
  have length : Primrec fun input : Input => input.2.length :=
    Primrec.list_length.comp source
  have select (index : Nat) (kind : OneInThreeAux) :
      Primrec fun input : Input =>
        (input.2[index]?).map liftLiteral |>.getD
          (padding input.1 input.2 kind) := by
    have selected : Primrec fun input : Input => input.2[index]? :=
      Primrec.list_getElem?.comp source (Primrec.const index)
    have lifted : Primrec fun input : Input =>
        (input.2[index]?).map liftLiteral :=
      Primrec.option_map selected
        (liftLiteral_primrec.comp Primrec.snd).to₂
    have fallback : Primrec fun input : Input =>
        padding input.1 input.2 kind :=
      padding_primrec.comp
        (Primrec.pair Primrec.id (Primrec.const kind))
    exact Primrec.option_getD.comp lifted fallback
  have first := select 0 .firstPadding
  have second := select 1 .secondPadding
  have third := select 2 .thirdPadding
  have core : Primrec fun input : Input =>
      disjunctionGadget input.1 input.2
        ((input.2[0]?).map liftLiteral |>.getD
          (padding input.1 input.2 .firstPadding))
        ((input.2[1]?).map liftLiteral |>.getD
          (padding input.1 input.2 .secondPadding))
        ((input.2[2]?).map liftLiteral |>.getD
          (padding input.1 input.2 .thirdPadding)) :=
    disjunctionGadget_primrec.comp
      (Primrec.pair
        (Primrec.pair Primrec.id first)
        (Primrec.pair second third))
  have lengthEq (value : Nat) :
      PrimrecPred fun input : Input => input.2.length = value :=
    Primrec.eq.comp length (Primrec.const value)
  have forcedKinds : Primrec fun input : Input =>
      if input.2.length = 0 then
        [OneInThreeAux.firstPadding, OneInThreeAux.secondPadding,
          OneInThreeAux.thirdPadding]
      else if input.2.length = 1 then
        [OneInThreeAux.secondPadding, OneInThreeAux.thirdPadding]
      else if input.2.length = 2 then
        [OneInThreeAux.thirdPadding]
      else
        [] :=
    Primrec.ite (lengthEq 0)
      (Primrec.const ([OneInThreeAux.firstPadding,
        OneInThreeAux.secondPadding,
        OneInThreeAux.thirdPadding] : List OneInThreeAux))
      (Primrec.ite (lengthEq 1)
        (Primrec.const ([OneInThreeAux.secondPadding,
          OneInThreeAux.thirdPadding] : List OneInThreeAux))
        (Primrec.ite (lengthEq 2)
          (Primrec.const
            ([OneInThreeAux.thirdPadding] : List OneInThreeAux))
          (Primrec.const ([] : List OneInThreeAux))))
  have forced : Primrec fun input : Input =>
      forcedPaddingClauses input.1 input.2
        (if input.2.length = 0 then
          [.firstPadding, .secondPadding, .thirdPadding]
        else if input.2.length = 1 then
          [.secondPadding, .thirdPadding]
        else if input.2.length = 2 then
          [.thirdPadding]
        else
          []) :=
    forcedPaddingClauses_primrec.comp
      (Primrec.pair Primrec.id forcedKinds)
  exact Primrec.list_append.comp core forced

/-- The clause gadget is primitive recursive. -/
theorem clauseClauses_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input : Nat × PeriodicClause Variable =>
      clauseClauses input.1 input.2 :=
  computableClauseClauses_primrec.of_eq fun input =>
    computableClauseClauses_eq input.1 input.2

end PeriodicOneInThree
end LeanTrominoes
