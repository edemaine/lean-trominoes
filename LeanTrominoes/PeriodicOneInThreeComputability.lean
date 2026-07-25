import LeanTrominoes.PeriodicOneInThreeOccurrences
import LeanTrominoes.PeriodicThreeSATThreeComputability
import Mathlib.Computability.Partrec

/-!
# Computability of the periodic 1-in-3SAT reduction

The clause-local gadget is primitive recursive under the canonical encodings.
This file then composes it with the verified Wang-to-periodic-3SAT-3 reduction
to obtain a computable hardness endpoint for local periodic 1-in-3SAT-3.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThree

open Encodable

noncomputable instance : Primcodable OneInThreeAux :=
  Primcodable.ofEquiv (Fin (Fintype.card OneInThreeAux))
    (Fintype.equivFin OneInThreeAux)

noncomputable instance oneInThreeVariablePrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (OneInThreeVariable Variable) :=
  inferInstance

theorem negate_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (negate :
      PeriodicLiteral Variable → PeriodicLiteral Variable) := by
  have boolNot : Primrec fun value : Bool => !value :=
    Primrec.dom_finite _
  have data : Primrec fun literal : PeriodicLiteral Variable =>
      (literal.atom, literal.offset, !literal.value) :=
    Primrec.pair PeriodicThreeCNF.literal_atom_primrec
      (Primrec.pair PeriodicThreeCNF.literal_offset_primrec
        (boolNot.comp PeriodicThreeCNF.literal_value_primrec))
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq
    fun _ => rfl

theorem liftLiteral_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (liftLiteral :
      PeriodicLiteral Variable →
        PeriodicLiteral (OneInThreeVariable Variable)) := by
  have data : Primrec fun literal : PeriodicLiteral Variable =>
      ((Sum.inl literal.atom : OneInThreeVariable Variable),
        literal.offset, literal.value) :=
    Primrec.pair
      (Primrec.sumInl.comp PeriodicThreeCNF.literal_atom_primrec)
      (Primrec.pair PeriodicThreeCNF.literal_offset_primrec
        PeriodicThreeCNF.literal_value_primrec)
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq
    fun _ => rfl

theorem anchor_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (anchor : PeriodicClause Variable → Cell) :=
  PeriodicThreeCNF.anchor_primrec.of_eq fun _ => rfl

theorem auxiliary_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        ((Nat × PeriodicClause Variable) × OneInThreeAux) × Bool =>
      auxiliary input.1.1.1 input.1.1.2 input.1.2 input.2 := by
  have atom : Primrec fun input :
      ((Nat × PeriodicClause Variable) × OneInThreeAux) × Bool =>
      (Sum.inr input.1 : OneInThreeVariable Variable) :=
    Primrec.sumInr.comp Primrec.fst
  have data : Primrec fun input :
      ((Nat × PeriodicClause Variable) × OneInThreeAux) × Bool =>
      ((Sum.inr input.1 : OneInThreeVariable Variable),
        anchor input.1.1.2, input.2) :=
    Primrec.pair atom
      (Primrec.pair
        (anchor_primrec.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        Primrec.snd)
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq
    fun _ => rfl

theorem padding_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        (Nat × PeriodicClause Variable) × OneInThreeAux =>
      padding input.1.1 input.1.2 input.2 := by
  exact auxiliary_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const true))

theorem forcePaddingFalse_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input :
        (Nat × PeriodicClause Variable) × OneInThreeAux =>
      forcePaddingFalse input.1.1 input.1.2 input.2 := by
  have literal : Primrec fun input :
      (Nat × PeriodicClause Variable) × OneInThreeAux =>
      auxiliary input.1.1 input.1.2 input.2 false :=
    auxiliary_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const false))
  exact Primrec.list_cons.comp literal (Primrec.const [])

theorem disjunctionGadget_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input :
        ((Nat × PeriodicClause Variable) ×
          PeriodicLiteral (OneInThreeVariable Variable)) ×
        (PeriodicLiteral (OneInThreeVariable Variable) ×
          PeriodicLiteral (OneInThreeVariable Variable)) =>
      disjunctionGadget input.1.1.1 input.1.1.2
        input.1.2 input.2.1 input.2.2 := by
  let Input :=
    ((Nat × PeriodicClause Variable) ×
      PeriodicLiteral (OneInThreeVariable Variable)) ×
    (PeriodicLiteral (OneInThreeVariable Variable) ×
      PeriodicLiteral (OneInThreeVariable Variable))
  let tagged : Primrec fun input : Input => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  let first : Primrec fun input : Input => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  let second : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let third : Primrec fun input : Input => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  let aux (kind : OneInThreeAux) (value : Bool) :
      Primrec fun input : Input =>
        auxiliary input.1.1.1 input.1.1.2 kind value :=
    auxiliary_primrec.comp
      (Primrec.pair
        (Primrec.pair tagged (Primrec.const kind))
        (Primrec.const value))
  let firstClause : Primrec fun input : Input =>
      [input.1.2,
        auxiliary input.1.1.1 input.1.1.2 .firstChoice true,
        auxiliary input.1.1.1 input.1.1.2 .secondChoice true] :=
    Primrec.list_cons.comp first
      (Primrec.list_cons.comp (aux .firstChoice true)
        (Primrec.list_cons.comp (aux .secondChoice true)
          (Primrec.const [])))
  let negativeSecond : Primrec fun input : Input => negate input.2.1 :=
    negate_primrec.comp second
  let secondClause : Primrec fun input : Input =>
      [negate input.2.1,
        auxiliary input.1.1.1 input.1.1.2 .firstChoice true,
        auxiliary input.1.1.1 input.1.1.2 .firstSlack true] :=
    Primrec.list_cons.comp negativeSecond
      (Primrec.list_cons.comp (aux .firstChoice true)
        (Primrec.list_cons.comp (aux .firstSlack true)
          (Primrec.const [])))
  let negativeThird : Primrec fun input : Input => negate input.2.2 :=
    negate_primrec.comp third
  let thirdClause : Primrec fun input : Input =>
      [negate input.2.2,
        auxiliary input.1.1.1 input.1.1.2 .secondChoice true,
        auxiliary input.1.1.1 input.1.1.2 .secondSlack true] :=
    Primrec.list_cons.comp negativeThird
      (Primrec.list_cons.comp (aux .secondChoice true)
        (Primrec.list_cons.comp (aux .secondSlack true)
          (Primrec.const [])))
  exact Primrec.list_cons.comp firstClause
    (Primrec.list_cons.comp secondClause
      (Primrec.list_cons.comp thirdClause (Primrec.const [])))

/-- Map the unit forcing clause over a list of padding kinds. -/
def forcedPaddingClauses {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (forced : List OneInThreeAux) :
    List (PeriodicClause (OneInThreeVariable Variable)) :=
  forced.map fun kind =>
    forcePaddingFalse clauseIndex source kind

theorem forcedPaddingClauses_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input :
        (Nat × PeriodicClause Variable) × List OneInThreeAux =>
      forcedPaddingClauses input.1.1 input.1.2 input.2 := by
  have one : Primrec₂ fun
      (input : (Nat × PeriodicClause Variable) × List OneInThreeAux)
      (kind : OneInThreeAux) =>
      forcePaddingFalse input.1.1 input.1.2 kind := by
    change Primrec fun combined :
        ((Nat × PeriodicClause Variable) × List OneInThreeAux) ×
          OneInThreeAux =>
      forcePaddingFalse combined.1.1.1 combined.1.1.2 combined.2
    exact forcePaddingFalse_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_map Primrec.snd one

/-- Empty-clause branch of `clauseClauses`, exposed for the computability
proof. -/
def emptyClauseOutput {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable) :=
  disjunctionGadget clauseIndex source
      (padding clauseIndex source .firstPadding)
      (padding clauseIndex source .secondPadding)
      (padding clauseIndex source .thirdPadding) ++
    forcedPaddingClauses clauseIndex source
      [.firstPadding, .secondPadding, .thirdPadding]

/-- Singleton branch of `clauseClauses`. -/
def singletonClauseOutput {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (first : PeriodicLiteral Variable) :=
  disjunctionGadget clauseIndex source
      (liftLiteral first)
      (padding clauseIndex source .secondPadding)
      (padding clauseIndex source .thirdPadding) ++
    forcedPaddingClauses clauseIndex source
      [.secondPadding, .thirdPadding]

/-- Two-literal branch of `clauseClauses`. -/
def pairClauseOutput {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (first second : PeriodicLiteral Variable) :=
  disjunctionGadget clauseIndex source
      (liftLiteral first) (liftLiteral second)
      (padding clauseIndex source .thirdPadding) ++
    forcedPaddingClauses clauseIndex source [.thirdPadding]

/-- Three-or-more-literal branch of `clauseClauses`. -/
def tripleClauseOutput {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (first second third : PeriodicLiteral Variable) :=
  disjunctionGadget clauseIndex source
    (liftLiteral first) (liftLiteral second) (liftLiteral third)

theorem emptyClauseOutput_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input : Nat × PeriodicClause Variable =>
      emptyClauseOutput input.1 input.2 := by
  have first : Primrec fun input : Nat × PeriodicClause Variable =>
      padding input.1 input.2 .firstPadding :=
    padding_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const .firstPadding))
  have second : Primrec fun input : Nat × PeriodicClause Variable =>
      padding input.1 input.2 .secondPadding :=
    padding_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const .secondPadding))
  have third : Primrec fun input : Nat × PeriodicClause Variable =>
      padding input.1 input.2 .thirdPadding :=
    padding_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const .thirdPadding))
  have core : Primrec fun input : Nat × PeriodicClause Variable =>
      disjunctionGadget input.1 input.2
        (padding input.1 input.2 .firstPadding)
        (padding input.1 input.2 .secondPadding)
        (padding input.1 input.2 .thirdPadding) :=
    disjunctionGadget_primrec.comp
      (Primrec.pair
        (Primrec.pair Primrec.id first)
        (Primrec.pair second third))
  have forced : Primrec fun input : Nat × PeriodicClause Variable =>
      forcedPaddingClauses input.1 input.2
        [.firstPadding, .secondPadding, .thirdPadding] :=
    forcedPaddingClauses_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const
        [.firstPadding, .secondPadding, .thirdPadding]))
  exact Primrec.list_append.comp core forced

theorem singletonClauseOutput_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input :
        (Nat × PeriodicClause Variable) × PeriodicLiteral Variable =>
      singletonClauseOutput input.1.1 input.1.2 input.2 := by
  have first : Primrec fun input :
      (Nat × PeriodicClause Variable) × PeriodicLiteral Variable =>
      liftLiteral input.2 :=
    liftLiteral_primrec.comp Primrec.snd
  have second : Primrec fun input :
      (Nat × PeriodicClause Variable) × PeriodicLiteral Variable =>
      padding input.1.1 input.1.2 .secondPadding :=
    padding_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.const .secondPadding))
  have third : Primrec fun input :
      (Nat × PeriodicClause Variable) × PeriodicLiteral Variable =>
      padding input.1.1 input.1.2 .thirdPadding :=
    padding_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.const .thirdPadding))
  have core : Primrec fun input :
      (Nat × PeriodicClause Variable) × PeriodicLiteral Variable =>
      disjunctionGadget input.1.1 input.1.2
        (liftLiteral input.2)
        (padding input.1.1 input.1.2 .secondPadding)
        (padding input.1.1 input.1.2 .thirdPadding) :=
    disjunctionGadget_primrec.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst first)
        (Primrec.pair second third))
  have forced : Primrec fun input :
      (Nat × PeriodicClause Variable) × PeriodicLiteral Variable =>
      forcedPaddingClauses input.1.1 input.1.2
        [.secondPadding, .thirdPadding] :=
    forcedPaddingClauses_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.const [.secondPadding, .thirdPadding]))
  exact Primrec.list_append.comp core forced

theorem pairClauseOutput_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input :
        ((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
          PeriodicLiteral Variable =>
      pairClauseOutput input.1.1.1 input.1.1.2 input.1.2 input.2 := by
  have first : Primrec fun input :
      ((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
        PeriodicLiteral Variable =>
      liftLiteral input.1.2 :=
    liftLiteral_primrec.comp (Primrec.snd.comp Primrec.fst)
  have second : Primrec fun input :
      ((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
        PeriodicLiteral Variable =>
      liftLiteral input.2 :=
    liftLiteral_primrec.comp Primrec.snd
  have third : Primrec fun input :
      ((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
        PeriodicLiteral Variable =>
      padding input.1.1.1 input.1.1.2 .thirdPadding :=
    padding_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const .thirdPadding))
  have core : Primrec fun input :
      ((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
        PeriodicLiteral Variable =>
      disjunctionGadget input.1.1.1 input.1.1.2
        (liftLiteral input.1.2) (liftLiteral input.2)
        (padding input.1.1.1 input.1.1.2 .thirdPadding) :=
    disjunctionGadget_primrec.comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) first)
        (Primrec.pair second third))
  have forced : Primrec fun input :
      ((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
        PeriodicLiteral Variable =>
      forcedPaddingClauses input.1.1.1 input.1.1.2 [.thirdPadding] :=
    forcedPaddingClauses_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.const [.thirdPadding]))
  exact Primrec.list_append.comp core forced

theorem tripleClauseOutput_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input :
        (((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
          PeriodicLiteral Variable) × PeriodicLiteral Variable =>
      tripleClauseOutput input.1.1.1.1 input.1.1.1.2
        input.1.1.2 input.1.2 input.2 := by
  have first : Primrec fun input :
      (((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
        PeriodicLiteral Variable) × PeriodicLiteral Variable =>
      liftLiteral input.1.1.2 :=
    liftLiteral_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have second : Primrec fun input :
      (((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
        PeriodicLiteral Variable) × PeriodicLiteral Variable =>
      liftLiteral input.1.2 :=
    liftLiteral_primrec.comp (Primrec.snd.comp Primrec.fst)
  have third : Primrec fun input :
      (((Nat × PeriodicClause Variable) × PeriodicLiteral Variable) ×
        PeriodicLiteral Variable) × PeriodicLiteral Variable =>
      liftLiteral input.2 :=
    liftLiteral_primrec.comp Primrec.snd
  exact disjunctionGadget_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) first)
      (Primrec.pair second third))

end PeriodicOneInThree
end LeanTrominoes
