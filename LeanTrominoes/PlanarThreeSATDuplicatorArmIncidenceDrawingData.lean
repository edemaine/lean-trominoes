/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PlanarThreeSATDuplicatorArm

/-! # Incidence-drawing data for one active duplicator arm -/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- The two implication clauses of one active duplicator arm. -/
def duplicatorArmFormula
    (arm : DuplicatorArm) :
    List (EmbeddedClause DuplicatorArmVariable) :=
  equalityInstance .port .center
    (duplicatorArmEqualityPositions arm)

/-- Direct incidences for one active duplicator arm. -/
def duplicatorArmStraightIncidenceDrawing
    (arm : DuplicatorArm) :
    EmbeddedCNFIncidenceDrawing DuplicatorArmVariable :=
  straightIncidenceDrawing
    (duplicatorArmFormula arm)
    (DuplicatorArmVariable.position arm)

end PlanarThreeSAT
end LeanTrominoes
