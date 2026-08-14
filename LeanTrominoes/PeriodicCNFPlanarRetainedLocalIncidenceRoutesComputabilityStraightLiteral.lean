/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityStraightRoute
import LeanTrominoes.EmbeddedClauseComputability

/-! # Primitive-recursive straight route for one selected literal -/

noncomputable section

namespace LeanTrominoes
namespace PlanarThreeSAT

theorem straightIncidenceRoutesSomeLiteral_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (variablePosition : Input → Variable → Cell)
    (variablePositionPrimrec : Primrec fun input : Input × Variable =>
      variablePosition input.1 input.2) :
    Primrec₂ fun
        (combined :
          (((Input × Nat) × Nat) × EmbeddedClause Variable))
        (literal : Variable × Bool) =>
      straightIncidenceRoute combined.2.position
        (variablePosition combined.1.1.1 literal.1) := by
  have source : Primrec fun input :
      ((((Input × Nat) × Nat) × EmbeddedClause Variable) ×
        (Variable × Bool)) =>
      input.1.2.position :=
    EmbeddedClause.position_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  have target : Primrec fun input :
      ((((Input × Nat) × Nat) × EmbeddedClause Variable) ×
        (Variable × Bool)) =>
      variablePosition input.1.1.1.1 input.2.1 :=
    variablePositionPrimrec.comp
      (Primrec.pair
        (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.fst.comp Primrec.snd))
  exact straightIncidenceRoute_primrec.comp source target

end PlanarThreeSAT
end LeanTrominoes
