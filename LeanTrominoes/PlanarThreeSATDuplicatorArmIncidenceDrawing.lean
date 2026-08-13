/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATDuplicatorArm
import LeanTrominoes.PlanarThreeSATIncidencePlanarity

/-!
# Incidence drawings for one active duplicator arm

The routed variable gadget instantiates only the active arms of Figure 8(a).
This module extracts the corresponding two-clause equality drawing for one
left, middle, or right arm.  Its coordinates are adapted to the three target
fanout terminals of the orthocrossing construction.

The direct clause-to-variable segments are continuously planar and retain
the eight-direction compass terminal rays needed by occurrence splitting.
They need not be orthogonal before that split.
-/

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

/-- Every direct arm incidence has its advertised clause and variable
endpoints. -/
theorem duplicatorArmStraightIncidenceDrawing_routesMatch
    (arm : DuplicatorArm) :
    (duplicatorArmStraightIncidenceDrawing arm).RoutesMatch := by
  exact straightIncidenceDrawing_routesMatch
    (duplicatorArmFormula arm)
    (DuplicatorArmVariable.position arm)

/-- Every left, top, or right active-arm drawing is continuously planar. -/
theorem duplicatorArmStraightIncidenceDrawing_isPlanar
    (arm : DuplicatorArm) :
    (duplicatorArmStraightIncidenceDrawing arm).IsPlanar := by
  cases arm <;> native_decide

/-- Every incidence of one active arm has a compass-valid terminal ray. -/
theorem duplicatorArmFormula_embeddedTerminalPortsValid
    (arm : DuplicatorArm) :
    EmbeddedTerminalPortsValid
      (duplicatorArmFormula arm)
      (DuplicatorArmVariable.position arm) := by
  cases arm <;> native_decide

/-- Reuse the four Figure 8(a) logical roles for the complete routed
equality-star template. -/
def DuplicatorArm.variable : DuplicatorArm → DuplicatorVariable
  | .left => .left
  | .middle => .top
  | .right => .right

/-- Physical placement of all four variables in the routed equality star. -/
def routedDuplicatorVariablePosition :
    DuplicatorVariable → Cell
  | .center => duplicatorArmCenterPosition
  | .left => DuplicatorArm.left.portPosition
  | .top => DuplicatorArm.middle.portPosition
  | .right => DuplicatorArm.right.portPosition

/-- All three two-clause arms of the routed equality star. -/
def routedDuplicatorFormula :
    List (EmbeddedClause DuplicatorVariable) :=
  [DuplicatorArm.left, .middle, .right].flatMap fun arm =>
    equalityInstance arm.variable .center
      (duplicatorArmEqualityPositions arm)

/-- The direct incidence drawing of the complete routed equality star. -/
def routedDuplicatorStraightIncidenceDrawing :
    EmbeddedCNFIncidenceDrawing DuplicatorVariable :=
  straightIncidenceDrawing
    routedDuplicatorFormula routedDuplicatorVariablePosition

/-- The complete three-arm layout is continuously planar, including
separation between incidences belonging to different arms. -/
theorem routedDuplicatorStraightIncidenceDrawing_isPlanar :
    routedDuplicatorStraightIncidenceDrawing.IsPlanar := by
  native_decide

/-- Every incidence in the complete three-arm layout has a compass-valid
terminal ray. -/
theorem routedDuplicatorFormula_embeddedTerminalPortsValid :
    EmbeddedTerminalPortsValid
      routedDuplicatorFormula
      routedDuplicatorVariablePosition := by
  native_decide

end PlanarThreeSAT
end LeanTrominoes
