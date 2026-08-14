/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositioned
import LeanTrominoes.PositionedPeriodicCNFComputability

/-!
# Computability of positioned polarity normalization

The logical replacement is already primitive recursive.  This module lifts
it to positioned clauses, parameterized only by the pointwise query for each
new complement-clause position.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicOneInThreePolarityNormalization

/-- Normalizing every literal of one indexed clause is primitive recursive. -/
theorem normalizeClause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × PeriodicClause Variable =>
      normalizeClause input.1 input.2 := by
  have tagged : Primrec fun input : Nat × PeriodicClause Variable =>
      input.2.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp Primrec.snd
  have one : Primrec₂ fun (input : Nat × PeriodicClause Variable)
      (taggedLiteral : PeriodicLiteral Variable × Nat) =>
      normalizeLiteral input.1 taggedLiteral.2 taggedLiteral.1 := by
    change Primrec fun combined :
        (Nat × PeriodicClause Variable) ×
          (PeriodicLiteral Variable × Nat) =>
      normalizeLiteral combined.1.1 combined.2.2 combined.2.1
    exact normalizeLiteral_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
  exact (Primrec.list_map tagged one).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalization

namespace PeriodicOneInThreePolarityNormalizationPositioned

open PeriodicOneInThreePolarityNormalization

/-- One positioned replacement block is primitive recursive from its source
clause and the pointwise complement-clause position query. -/
theorem clauseBlock_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (complementPosition : Input → FreshOccurrence Variable → Cell)
    (complementPositionPrimrec :
      Primrec fun input : Input × FreshOccurrence Variable =>
        complementPosition input.1 input.2) :
    Primrec fun input : (Input × Nat) × PositionedPeriodicClause Variable =>
      clauseBlock
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input.1.1 }
        input.1.2 input.2 := by
  let BlockInput :=
    (Input × Nat) × PositionedPeriodicClause Variable
  have normalized : Primrec fun input : BlockInput =>
      normalizedClause input.1.2 input.2 := by
    have literals : Primrec fun input : BlockInput =>
        normalizeClause input.1.2 input.2.literals :=
      PeriodicOneInThreePolarityNormalization.normalizeClause_primrec.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (PositionedPeriodicClause.literals_primrec.comp Primrec.snd))
    exact (PositionedPeriodicClause.mk_primrec.comp
      (Primrec.pair
        (PositionedPeriodicClause.position_primrec.comp Primrec.snd)
        literals)).of_eq fun _ => rfl
  have tagged : Primrec fun input : BlockInput =>
      input.2.literals.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)
  have one : Primrec₂ fun (input : BlockInput)
      (taggedLiteral : PeriodicLiteral Variable × Nat) =>
      if taggedLiteral.1.value = normalizedPolarity taggedLiteral.2 then
        none
      else
        some (positionedComplementClause
          { freshVariable := fun _ => (0, 0)
            complementClause := complementPosition input.1.1 }
          input.1.2 taggedLiteral.2 taggedLiteral.1) := by
    change Primrec fun combined : BlockInput ×
        (PeriodicLiteral Variable × Nat) =>
      if combined.2.1.value = normalizedPolarity combined.2.2 then
        none
      else
        some (positionedComplementClause
          { freshVariable := fun _ => (0, 0)
            complementClause := complementPosition combined.1.1.1 }
          combined.1.1.2 combined.2.2 combined.2.1)
    have compatible : PrimrecPred fun combined : BlockInput ×
        (PeriodicLiteral Variable × Nat) =>
        combined.2.1.value = normalizedPolarity combined.2.2 :=
      Primrec.eq.comp
        (PeriodicThreeCNF.literal_value_primrec.comp
          (Primrec.fst.comp Primrec.snd))
        (normalizedPolarity_primrec.comp
          (Primrec.snd.comp Primrec.snd))
    have position : Primrec fun combined : BlockInput ×
        (PeriodicLiteral Variable × Nat) =>
        complementPosition combined.1.1.1
          ((combined.1.1.2, combined.2.2), combined.2.1) :=
      complementPositionPrimrec.comp
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair
            (Primrec.pair
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.snd.comp Primrec.snd))
            (Primrec.fst.comp Primrec.snd)))
    have literals : Primrec fun combined : BlockInput ×
        (PeriodicLiteral Variable × Nat) =>
        complementClause combined.1.1.2 combined.2.2 combined.2.1 :=
      complementClause_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.snd))
    have clause : Primrec fun combined : BlockInput ×
        (PeriodicLiteral Variable × Nat) =>
        positionedComplementClause
          { freshVariable := fun _ => (0, 0)
            complementClause := complementPosition combined.1.1.1 }
          combined.1.1.2 combined.2.2 combined.2.1 :=
      (PositionedPeriodicClause.mk_primrec.comp
        (Primrec.pair position literals)).of_eq fun _ => rfl
    exact Primrec.ite compatible (Primrec.const none)
      (Primrec.option_some.comp clause)
  have complements : Primrec fun input : BlockInput =>
      positionedComplementClausesFrom
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input.1.1 }
        input.1.2 0 input.2.literals := by
    simpa [positionedComplementClausesFrom] using
      Primrec.listFilterMap tagged one
  exact (Primrec.list_cons.comp normalized complements).of_eq fun _ => rfl

/-- The complete positioned normalization is primitive recursive whenever
the source formula and complement-clause position query are. -/
theorem formula_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (complementPosition : Input → FreshOccurrence Variable → Cell)
    (sourcePrimrec : Primrec source)
    (complementPositionPrimrec :
      Primrec fun input : Input × FreshOccurrence Variable =>
        complementPosition input.1 input.2) :
    Primrec fun input : Input =>
      formula
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input }
        (source input) := by
  have tagged : Primrec fun input : Input =>
      (source input).clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicCNF.clauses_primrec.comp sourcePrimrec)
  have one : Primrec₂ fun (input : Input)
      (taggedClause : PositionedPeriodicClause Variable × Nat) =>
      clauseBlock
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input }
        taggedClause.2 taggedClause.1 := by
    change Primrec fun combined : Input ×
        (PositionedPeriodicClause Variable × Nat) =>
      clauseBlock
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition combined.1 }
        combined.2.2 combined.2.1
    exact (clauseBlock_primrec complementPosition
      complementPositionPrimrec).comp
        (Primrec.pair
          (Primrec.pair Primrec.fst
            (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.snd))
  have clauses : Primrec fun input : Input =>
      (source input).clauses.zipIdx.flatMap fun taggedClause =>
        clauseBlock
          { freshVariable := fun _ => (0, 0)
            complementClause := complementPosition input }
          taggedClause.2 taggedClause.1 :=
    Primrec.list_flatMap tagged one
  exact (PositionedPeriodicCNF.mk_primrec.comp clauses).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationPositioned
end LeanTrominoes
