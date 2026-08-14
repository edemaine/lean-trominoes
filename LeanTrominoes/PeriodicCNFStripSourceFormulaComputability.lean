/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.Computability
import LeanTrominoes.PeriodicThreeCNFComputability
import LeanTrominoes.PeriodicThreeSATThreeComputability

/-!
# Computability of the guarded strip source formula

The strip reduction first recognizes its syntactic source promises and then
selects either the ordinary width/occurrence normalization or a fixed
contradictory formula.  This module verifies that the complete guarded
transformation is primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open LeanTrominoes.Computability

/-- Primitive-recursive `List.all` with a predicate depending on the input. -/
private theorem listAll_primrec
    {Input Item : Type*} [Primcodable Input] [Primcodable Item]
    (items : Input → List Item) (predicate : Input → Item → Bool)
    (itemsPrimrec : Primrec items) (predicatePrimrec : Primrec₂ predicate) :
    Primrec fun input => (items input).all (predicate input) := by
  have step : Primrec₂ fun input (state : Item × Bool) =>
      predicate input state.1 && state.2 := by
    change Primrec fun combined : Input × (Item × Bool) =>
      predicate combined.1 combined.2.1 && combined.2.2
    exact (Primrec.and.comp
      (predicatePrimrec.comp Primrec.fst
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.list_foldr itemsPrimrec (Primrec.const true) step).of_eq ?_
  intro input
  generalize valuesEquality : items input = values
  clear valuesEquality
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simpa only [List.foldr_cons, List.all_cons] using
        congrArg (fun result => predicate input head && result) induction

/-- Manhattan distance between two periodic-literal offsets is primitive
recursive. -/
theorem offsetDistance_primrec :
    Primrec₂ (@PeriodicClause.offsetDistance Nat) := by
  have intNatAbs : Primrec Int.natAbs :=
    (intCodeMagnitude_primrec.comp Primrec.encode).of_eq
      intCodeMagnitude_encode
  have firstOffset : Primrec fun input :
      PeriodicLiteral Nat × PeriodicLiteral Nat => input.1.offset :=
    PeriodicThreeCNF.literal_offset_primrec.comp Primrec.fst
  have secondOffset : Primrec fun input :
      PeriodicLiteral Nat × PeriodicLiteral Nat => input.2.offset :=
    PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd
  have horizontalDifference : Primrec fun input :
      PeriodicLiteral Nat × PeriodicLiteral Nat =>
        input.1.offset.1 - input.2.offset.1 :=
    int_subtract_primrec.comp
      (Primrec.fst.comp firstOffset)
      (Primrec.fst.comp secondOffset)
  have verticalDifference : Primrec fun input :
      PeriodicLiteral Nat × PeriodicLiteral Nat =>
        input.1.offset.2 - input.2.offset.2 :=
    int_subtract_primrec.comp
      (Primrec.snd.comp firstOffset)
      (Primrec.snd.comp secondOffset)
  exact (Primrec.nat_add.comp
    (intNatAbs.comp horizontalDifference)
    (intNatAbs.comp verticalDifference)).to₂.of_eq fun _ _ => rfl

/-- Executable locality of one clause is primitive recursive. -/
theorem clauseIsLocal_primrec : Primrec clauseIsLocal := by
  let pairLocal := fun first second : PeriodicLiteral Nat =>
    decide (PeriodicClause.offsetDistance first second ≤ 1)
  have pairLocalPrimrec : Primrec₂ pairLocal :=
    (Primrec.nat_le.comp offsetDistance_primrec
      (Primrec.const 1).to₂).decide
  have allSeconds : Primrec₂ fun
      (clause : PeriodicClause Nat) (first : PeriodicLiteral Nat) =>
        clause.all fun second => pairLocal first second := by
    change Primrec fun input :
        PeriodicClause Nat × PeriodicLiteral Nat =>
      input.1.all fun second => pairLocal input.2 second
    exact listAll_primrec
      (fun input : PeriodicClause Nat × PeriodicLiteral Nat => input.1)
      (fun input second => pairLocal input.2 second)
      Primrec.fst
      ((pairLocalPrimrec.comp (Primrec.snd.comp Primrec.fst)
        Primrec.snd).to₂)
  exact (listAll_primrec
    (fun clause : PeriodicClause Nat => clause)
    (fun clause first => clause.all fun second => pairLocal first second)
    Primrec.id allSeconds).of_eq fun _ => rfl

/-- Executable locality of the whole source formula is primitive recursive. -/
theorem formulaIsLocal_primrec : Primrec formulaIsLocal := by
  have clausePredicate : Primrec₂ fun
      (_source : PeriodicCNF Nat) (clause : PeriodicClause Nat) =>
        clauseIsLocal clause :=
    clauseIsLocal_primrec.comp₂ Primrec₂.right
  exact (listAll_primrec
    (fun source : PeriodicCNF Nat => source.clauses)
    (fun _source clause => clauseIsLocal clause)
    PeriodicCNF.equivData_primrec clausePredicate).of_eq fun _ => rfl

/-- The recursive nonempty-clause guard is primitive recursive. -/
theorem allClausesNonempty_primrec : Primrec allClausesNonempty := by
  have isEmpty : Primrec fun clause : PeriodicClause Nat => clause.isEmpty :=
    ((Primrec.eq.comp Primrec.list_length
      (Primrec.const 0)).decide).of_eq fun clause => by
        cases clause <;> rfl
  have step : Primrec₂ fun
      (_clauses : List (PeriodicClause Nat))
      (state : PeriodicClause Nat × Bool) =>
        !state.1.isEmpty && state.2 := by
    change Primrec fun combined :
        List (PeriodicClause Nat) × (PeriodicClause Nat × Bool) =>
      !combined.2.1.isEmpty && combined.2.2
    exact (Primrec.and.comp
      (Primrec.not.comp (isEmpty.comp
        (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id
    (Primrec.const true) step).of_eq fun clauses => by
      induction clauses with
      | nil => rfl
      | cons clause clauses induction =>
          simpa only [List.foldr_cons, id_eq, allClausesNonempty] using
            congrArg (fun result => !clause.isEmpty && result) induction

/-- Recognition of the horizontal fragment is primitive recursive. -/
theorem isOneDimensional_primrec :
    Primrec (@PeriodicCNF.isOneDimensional Nat) := by
  have vertical : Primrec fun literal : PeriodicLiteral Nat =>
      literal.offset.2 :=
    Primrec.snd.comp PeriodicThreeCNF.literal_offset_primrec
  have horizontal : Primrec fun literal : PeriodicLiteral Nat =>
      literal.offset.2 == 0 :=
    Primrec.beq.comp vertical (Primrec.const 0)
  have clauseHorizontal : Primrec fun clause : PeriodicClause Nat =>
      clause.all fun literal => literal.offset.2 == 0 := by
    have predicate : Primrec₂ fun
        (_clause : PeriodicClause Nat) (literal : PeriodicLiteral Nat) =>
          literal.offset.2 == 0 :=
      horizontal.comp₂ Primrec₂.right
    exact listAll_primrec
      (fun clause : PeriodicClause Nat => clause)
      (fun _clause literal => literal.offset.2 == 0)
      Primrec.id predicate
  have clausePredicate : Primrec₂ fun
      (_source : PeriodicCNF Nat) (clause : PeriodicClause Nat) =>
        clause.all fun literal => literal.offset.2 == 0 :=
    clauseHorizontal.comp₂ Primrec₂.right
  exact (listAll_primrec
    (fun source : PeriodicCNF Nat => source.clauses)
    (fun _source clause =>
      clause.all fun literal => literal.offset.2 == 0)
    PeriodicCNF.equivData_primrec clausePredicate).of_eq fun _ => rfl

/-- The complete syntactic source guard is primitive recursive. -/
theorem sourceAdmissible_primrec : Primrec sourceAdmissible := by
  have clauses : Primrec fun source : PeriodicCNF Nat => source.clauses :=
    PeriodicCNF.equivData_primrec
  exact (Primrec.and.comp
    (Primrec.and.comp isOneDimensional_primrec formulaIsLocal_primrec)
    (allClausesNonempty_primrec.comp clauses)).of_eq fun source => by
        simp only [sourceAdmissible]

/-- The ordinary width-three and occurrence-three normalization is primitive
recursive. -/
theorem normalizedFormula_primrec : Primrec normalizedFormula :=
  PeriodicThreeSATThree.formula_primrec.comp
    PeriodicThreeCNF.formula_primrec

/-- The fixed contradictory fallback is primitive recursive. -/
theorem fallbackFormula_primrec :
    Primrec fun _source : PeriodicCNF Nat => fallbackFormula :=
  Primrec.const fallbackFormula

/-- The complete guarded source transformation is primitive recursive. -/
theorem sourceFormula_primrec : Primrec sourceFormula := by
  refine (Primrec.cond sourceAdmissible_primrec normalizedFormula_primrec
    fallbackFormula_primrec).of_eq ?_
  intro source
  by_cases admissible : SourceAdmissible source
  · have guard : sourceAdmissible source = true :=
      (sourceAdmissible_eq_true_iff source).2 admissible
    simp [sourceFormula, admissible, guard]
  · have guard : sourceAdmissible source = false := by
      cases equality : sourceAdmissible source with
      | false => rfl
      | true =>
          exact False.elim
            (admissible ((sourceAdmissible_eq_true_iff source).1 equality))
    simp [sourceFormula, admissible, guard]

theorem sourceFormula_computable : Computable sourceFormula :=
  sourceFormula_primrec.to_comp

end PeriodicCNFStripReduction
end LeanTrominoes
