/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFComputability
import LeanTrominoes.PositionedPeriodicCNFScaling

/-! # Computability of positioned periodic-CNF scaling -/

noncomputable section

namespace LeanTrominoes

namespace PositionedPeriodicClause

/-- Scaling one positioned clause by a fixed natural factor is primitive
recursive. -/
theorem scale_primrec
    {Variable : Type*} [Primcodable Variable]
    (factor : Nat) :
    Primrec (PositionedPeriodicClause.scale factor :
      PositionedPeriodicClause Variable → _) := by
  have position : Primrec fun clause : PositionedPeriodicClause Variable =>
      Cell.scale factor clause.position :=
    Computability.cell_scale_primrec.comp
      (Primrec.const (factor : Int))
      PositionedPeriodicClause.position_primrec
  exact (PositionedPeriodicClause.mk_primrec.comp
    (Primrec.pair position
      PositionedPeriodicClause.literals_primrec)).of_eq fun _ => rfl

end PositionedPeriodicClause

namespace PositionedPeriodicCNF

/-- Scaling every clause position in a finite positioned formula by a fixed
natural factor is primitive recursive. -/
theorem scale_primrec
    {Variable : Type*} [Primcodable Variable]
    (factor : Nat) :
    Primrec (PositionedPeriodicCNF.scale factor :
      PositionedPeriodicCNF Variable → _) := by
  have scaledClauses : Primrec fun source : PositionedPeriodicCNF Variable =>
      source.clauses.map (PositionedPeriodicClause.scale factor) :=
    Primrec.list_map PositionedPeriodicCNF.clauses_primrec
      ((PositionedPeriodicClause.scale_primrec factor).comp Primrec.snd).to₂
  exact (PositionedPeriodicCNF.mk_primrec.comp scaledClauses).of_eq
    fun _ => rfl

end PositionedPeriodicCNF
end LeanTrominoes
