/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityStraightLiteral

/-! # Primitive-recursive straight-route lookup inside one embedded clause -/

noncomputable section

namespace LeanTrominoes
namespace PlanarThreeSAT

set_option maxHeartbeats 1000000

theorem straightIncidenceRoutesSomeClause_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (variablePosition : Input → Variable → Cell)
    (variablePositionPrimrec : Primrec fun input : Input × Variable =>
      variablePosition input.1 input.2) :
    Primrec₂ fun (input : (Input × Nat) × Nat)
        (clause : EmbeddedClause Variable) =>
      match clause.literals[input.2]? with
      | none => []
      | some literal =>
          straightIncidenceRoute clause.position
            (variablePosition input.1.1 literal.1) := by
  change Primrec fun combined :
      (((Input × Nat) × Nat) × EmbeddedClause Variable) =>
    match combined.2.literals[combined.1.2]? with
    | none => []
    | some literal =>
        straightIncidenceRoute combined.2.position
          (variablePosition combined.1.1.1 literal.1)
  have literalOption : Primrec fun combined :
      (((Input × Nat) × Nat) × EmbeddedClause Variable) =>
      combined.2.literals[combined.1.2]? :=
    Primrec.list_getElem?.comp
      (EmbeddedClause.literals_primrec.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  have noLiteral : Primrec fun _combined :
      (((Input × Nat) × Nat) × EmbeddedClause Variable) =>
      ([] : List Cell) :=
    Primrec.const []
  exact (Primrec.option_casesOn literalOption noLiteral
    (straightIncidenceRoutesSomeLiteral_primrec
      variablePosition variablePositionPrimrec)).of_eq
    fun combined => by cases combined.2.literals[combined.1.2]? <;> rfl

end PlanarThreeSAT
end LeanTrominoes
