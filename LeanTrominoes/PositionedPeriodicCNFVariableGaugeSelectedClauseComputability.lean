/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFComputability

/-! # Variable-gauge route clause-lookup computability -/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

def selectedRouteClause? {Input Variable : Type*}
    (source : Input → PositionedPeriodicCNF Variable)
    (input : (Input × Nat) × Nat) :
    Option (PositionedPeriodicClause Variable) :=
  (source input.1.1).clauses[input.1.2]?

theorem selectedRouteClause?_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePrimrec : Primrec source) :
    Primrec (selectedRouteClause? source) := by
  exact Primrec.list_getElem?.comp
    (PositionedPeriodicCNF.clauses_primrec.comp
      (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.snd.comp Primrec.fst)

end PositionedPeriodicCNF
end LeanTrominoes
