/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computability
import LeanTrominoes.EmbeddedCNFIncidenceDrawing

/-! # Canonical primitive-recursive encoding of embedded clauses -/

noncomputable section

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedClause

def equivData {Variable : Type*} : EmbeddedClause Variable ≃
    Cell × List (Variable × Bool) where
  toFun clause := (clause.position, clause.literals)
  invFun data := ⟨data.1, data.2⟩
  left_inv clause := by cases clause; rfl
  right_inv data := by cases data; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (EmbeddedClause Variable) :=
  Primcodable.ofEquiv
    (Cell × List (Variable × Bool)) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem position_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (EmbeddedClause.position :
      EmbeddedClause Variable → Cell) :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem literals_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (EmbeddedClause.literals :
      EmbeddedClause Variable → List (Variable × Bool)) :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : Cell × List (Variable × Bool) =>
      EmbeddedClause.mk data.1 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end EmbeddedClause
end PlanarThreeSAT
end LeanTrominoes
