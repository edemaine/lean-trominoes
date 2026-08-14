/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedIndex

/-!
# Computability encodings for positioned polarity metadata

The flattened positioned formula retains finite source and origin metadata
for each generated clause.  This module supplies canonical encodings and
primitive-recursive constructors and projections for that runtime data.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationPositioned

namespace ClauseOrigin

def equivData {Variable : Type*} : ClauseOrigin Variable ≃
    Unit ⊕ (Nat × PeriodicLiteral Variable) where
  toFun
    | .normalized => Sum.inl ()
    | .complement index literal => Sum.inr (index, literal)
  invFun
    | Sum.inl _ => .normalized
    | Sum.inr data => .complement data.1 data.2
  left_inv origin := by cases origin <;> rfl
  right_inv data := by
    cases data with
    | inl value => cases value; rfl
    | inr value => cases value; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (ClauseOrigin Variable) :=
  Primcodable.ofEquiv
    (Unit ⊕ (Nat × PeriodicLiteral Variable)) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem normalized_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun _value : Unit => (ClauseOrigin.normalized :
      ClauseOrigin Variable) :=
  (equivData_symm_primrec.comp
    (Primrec.sumInl.comp Primrec.id)).of_eq fun _ => rfl

theorem complement_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × PeriodicLiteral Variable =>
      ClauseOrigin.complement input.1 input.2 :=
  (equivData_symm_primrec.comp
    (Primrec.sumInr.comp Primrec.id)).of_eq fun _ => rfl

end ClauseOrigin

namespace ClauseMetadata

def equivData {Variable : Type*} : ClauseMetadata Variable ≃
    (PositionedPeriodicClause Variable × Nat) ×
      (PositionedPeriodicClause (PolarityNormalizedVariable Variable) ×
        ClauseOrigin Variable) where
  toFun metadata :=
    ((metadata.sourceClause, metadata.sourceClauseIndex),
      (metadata.clause, metadata.origin))
  invFun data :=
    ⟨data.1.1, data.1.2, data.2.1, data.2.2⟩
  left_inv metadata := by cases metadata; rfl
  right_inv data := by rcases data with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (ClauseMetadata Variable) :=
  Primcodable.ofEquiv
    ((PositionedPeriodicClause Variable × Nat) ×
      (PositionedPeriodicClause (PolarityNormalizedVariable Variable) ×
        ClauseOrigin Variable)) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem sourceClause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (ClauseMetadata.sourceClause : ClauseMetadata Variable →
      PositionedPeriodicClause Variable) :=
  (Primrec.fst.comp (Primrec.fst.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem sourceClauseIndex_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (ClauseMetadata.sourceClauseIndex :
      ClauseMetadata Variable → Nat) :=
  (Primrec.snd.comp (Primrec.fst.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (ClauseMetadata.clause : ClauseMetadata Variable →
      PositionedPeriodicClause
        (PolarityNormalizedVariable Variable)) :=
  (Primrec.fst.comp (Primrec.snd.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem origin_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (ClauseMetadata.origin : ClauseMetadata Variable →
      ClauseOrigin Variable) :=
  (Primrec.snd.comp (Primrec.snd.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (PositionedPeriodicClause Variable × Nat) ×
          (PositionedPeriodicClause
              (PolarityNormalizedVariable Variable) ×
            ClauseOrigin Variable) =>
      ClauseMetadata.mk data.1.1 data.1.2 data.2.1 data.2.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end ClauseMetadata
end PeriodicOneInThreePolarityNormalizationPositioned
end LeanTrominoes
