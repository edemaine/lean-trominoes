/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityStraightClause

/-! # Primitive-recursive indexed straight incidence-route lookup -/

noncomputable section

namespace LeanTrominoes
namespace PlanarThreeSAT

set_option maxHeartbeats 1000000

theorem straightIncidenceRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (formula : Input → List (EmbeddedClause Variable))
    (variablePosition : Input → Variable → Cell)
    (formulaPrimrec : Primrec formula)
    (variablePositionPrimrec : Primrec fun input : Input × Variable =>
      variablePosition input.1 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      straightIncidenceRoutes (formula input.1.1)
        (variablePosition input.1.1) input.1.2 input.2 := by
  have clauseOption : Primrec fun input : (Input × Nat) × Nat =>
      (formula input.1.1)[input.1.2]? :=
    Primrec.list_getElem?.comp
      (formulaPrimrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have noClause : Primrec fun _input : (Input × Nat) × Nat =>
      ([] : List Cell) :=
    Primrec.const []
  exact (Primrec.option_casesOn clauseOption noClause
    (straightIncidenceRoutesSomeClause_primrec
      variablePosition variablePositionPrimrec)).of_eq fun input => by
        simp only [straightIncidenceRoutes]
        cases (formula input.1.1)[input.1.2]? <;> rfl

end PlanarThreeSAT
end LeanTrominoes
