/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedMetadataComputability

/-!
# Computability of positioned polarity metadata lists

This module computes the source/origin metadata in exact parallel with every
generated positioned clause.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationPositioned

open PeriodicOneInThreePolarityNormalization

private theorem complementClauseMetadataFrom_eq_filterMap
    {Variable : Type*}
    (positions : Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    complementClauseMetadataFrom positions sourceClause sourceClauseIndex
        literalStart source =
      (source.zipIdx literalStart).filterMap fun taggedLiteral =>
        if taggedLiteral.1.value = normalizedPolarity taggedLiteral.2 then
          none
        else
          some (ClauseMetadata.mk sourceClause sourceClauseIndex
            (positionedComplementClause positions sourceClauseIndex
              taggedLiteral.2 taggedLiteral.1)
            (.complement taggedLiteral.2 taggedLiteral.1)) := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart <;>
        simp [complementClauseMetadataFrom, compatible,
          induction (literalStart + 1)]

/-- One indexed source clause's complete metadata block is primitive
recursive from the complement-clause position query. -/
theorem clauseMetadataFor_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (complementPosition : Input → FreshOccurrence Variable → Cell)
    (complementPositionPrimrec :
      Primrec fun input : Input × FreshOccurrence Variable =>
        complementPosition input.1 input.2) :
    Primrec fun input : (Input × Nat) × PositionedPeriodicClause Variable =>
      clauseMetadataFor
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input.1.1 }
        input.1.2 input.2 := by
  let BlockInput :=
    (Input × Nat) × PositionedPeriodicClause Variable
  have normalizedClauseValue : Primrec fun input : BlockInput =>
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
  have normalizedMetadata : Primrec fun input : BlockInput =>
      ClauseMetadata.mk input.2 input.1.2
        (normalizedClause input.1.2 input.2) ClauseOrigin.normalized :=
    ClauseMetadata.mk_primrec.comp
      (Primrec.pair
        (Primrec.pair Primrec.snd
          (Primrec.snd.comp Primrec.fst))
        (Primrec.pair normalizedClauseValue
          (ClauseOrigin.normalized_primrec.comp
            (Primrec.const ()))))
  have tagged : Primrec fun input : BlockInput =>
      input.2.literals.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)
  have one : Primrec₂ fun (input : BlockInput)
      (taggedLiteral : PeriodicLiteral Variable × Nat) =>
      if taggedLiteral.1.value = normalizedPolarity taggedLiteral.2 then
        none
      else
        some
          (ClauseMetadata.mk input.2 input.1.2
            (positionedComplementClause
              { freshVariable := fun _ => (0, 0)
                complementClause := complementPosition input.1.1 }
              input.1.2 taggedLiteral.2 taggedLiteral.1)
            (.complement taggedLiteral.2 taggedLiteral.1)) := by
    change Primrec fun combined : BlockInput ×
        (PeriodicLiteral Variable × Nat) =>
      if combined.2.1.value = normalizedPolarity combined.2.2 then
        none
      else
        some
          (ClauseMetadata.mk combined.1.2 combined.1.1.2
            (positionedComplementClause
              { freshVariable := fun _ => (0, 0)
                complementClause := complementPosition combined.1.1.1 }
              combined.1.1.2 combined.2.2 combined.2.1)
            (.complement combined.2.2 combined.2.1))
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
    have origin : Primrec fun combined : BlockInput ×
        (PeriodicLiteral Variable × Nat) =>
        ClauseOrigin.complement combined.2.2 combined.2.1 :=
      ClauseOrigin.complement_primrec.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.snd)
          (Primrec.fst.comp Primrec.snd))
    have metadata : Primrec fun combined : BlockInput ×
        (PeriodicLiteral Variable × Nat) =>
        ClauseMetadata.mk combined.1.2 combined.1.1.2
          (positionedComplementClause
            { freshVariable := fun _ => (0, 0)
              complementClause := complementPosition combined.1.1.1 }
            combined.1.1.2 combined.2.2 combined.2.1)
          (.complement combined.2.2 combined.2.1) :=
      ClauseMetadata.mk_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.snd.comp Primrec.fst)
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair clause origin))
    exact Primrec.ite compatible (Primrec.const none)
      (Primrec.option_some.comp metadata)
  have complements : Primrec fun input : BlockInput =>
      complementClauseMetadataFrom
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input.1.1 }
        input.2 input.1.2 0 input.2.literals := by
    exact (Primrec.listFilterMap tagged one).of_eq fun input =>
      (complementClauseMetadataFrom_eq_filterMap
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input.1.1 }
        input.2 input.1.2 0 input.2.literals).symm
  exact (Primrec.list_cons.comp normalizedMetadata complements).of_eq
    fun _ => rfl

/-- The complete flattened clause-metadata list is primitive recursive. -/
theorem formulaClauseMetadata_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (complementPosition : Input → FreshOccurrence Variable → Cell)
    (sourcePrimrec : Primrec source)
    (complementPositionPrimrec :
      Primrec fun input : Input × FreshOccurrence Variable =>
        complementPosition input.1 input.2) :
    Primrec fun input =>
      formulaClauseMetadata
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input }
        (source input) := by
  have tagged : Primrec fun input : Input =>
      (source input).clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicCNF.clauses_primrec.comp sourcePrimrec)
  have one : Primrec₂ fun (input : Input)
      (taggedClause : PositionedPeriodicClause Variable × Nat) =>
      clauseMetadataFor
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input }
        taggedClause.2 taggedClause.1 := by
    change Primrec fun combined : Input ×
        (PositionedPeriodicClause Variable × Nat) =>
      clauseMetadataFor
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition combined.1 }
        combined.2.2 combined.2.1
    exact (clauseMetadataFor_primrec complementPosition
      complementPositionPrimrec).comp
        (Primrec.pair
          (Primrec.pair Primrec.fst
            (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.snd))
  exact (Primrec.list_flatMap tagged one).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationPositioned
end LeanTrominoes
