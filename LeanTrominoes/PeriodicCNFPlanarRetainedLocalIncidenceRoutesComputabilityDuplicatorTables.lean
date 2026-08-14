/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityGeometry
import LeanTrominoes.PeriodicCNFPlanarRetainedClauseMetadataComputability
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing
import LeanTrominoes.PeriodicThreeDMNormalizationEncoding

/-! # Primitive-recursive retained duplicator and routed-clause tables -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PlanarThreeSAT

theorem duplicatorArmFormula_primrec :
    Primrec duplicatorArmFormula :=
  Primrec.dom_finite duplicatorArmFormula

theorem duplicatorArmVariablePosition_primrec :
    Primrec fun input : DuplicatorArm × DuplicatorArmVariable =>
      DuplicatorArmVariable.position input.1 input.2 :=
  Primrec.dom_finite fun input : DuplicatorArm × DuplicatorArmVariable =>
    DuplicatorArmVariable.position input.1 input.2

theorem duplicatorArmStraightRoutes_primrec :
    Primrec fun input : (DuplicatorArm × Nat) × Nat =>
      (duplicatorArmStraightIncidenceDrawing input.1.1).routes
        input.1.2 input.2 := by
  exact (straightIncidenceRoutes_primrec duplicatorArmFormula
    DuplicatorArmVariable.position duplicatorArmFormula_primrec
    duplicatorArmVariablePosition_primrec).of_eq fun _ => rfl

/-- Specialization of the duplicator-arm route lookup to the retained
variable-route input layout. -/
theorem duplicatorArmStraightVariableInput_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input :
        (((PeriodicCNF Variable ×
          PeriodicOrthocrossing.VariableRouteSite Variable) ×
          DuplicatorArm) × Nat) × Nat =>
      (duplicatorArmStraightIncidenceDrawing input.1.1.2).routes
        input.1.2 input.2 :=
  duplicatorArmStraightRoutes_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)

theorem routedClausePortFormula_primrec :
    Primrec routedClausePortFormula := by
  have clause : Primrec fun literals : List (DuplicatorArm × Bool) =>
      EmbeddedClause.mk (10, 10) literals :=
    EmbeddedClause.mk_primrec.comp
      (Primrec.pair (Primrec.const ((10, 10) : Cell)) Primrec.id)
  exact (Primrec.list_cons.comp clause (Primrec.const [])).of_eq
    fun _ => rfl

theorem duplicatorArmPortPosition_primrec :
    Primrec DuplicatorArm.portPosition :=
  Primrec.dom_finite DuplicatorArm.portPosition


end PlanarThreeSAT
end LeanTrominoes
