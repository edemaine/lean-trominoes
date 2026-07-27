import LeanTrominoes.PlanarThreeSATIncidencePlanarity

/-!
# Incidence drawings for one active duplicator arm

The routed variable gadget instantiates only the active arms of Figure 8(a).
This module extracts the corresponding two-clause equality drawing for one
left, top, or right arm.  The third and all later natural-number indices use
the right-arm geometry, matching `routedVariableEqualityPositions`.

The direct clause-to-variable segments are continuously planar and retain
the eight-direction compass terminal rays needed by occurrence splitting.
They need not be orthogonal before that split.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- The endpoint and center roles present in one active duplicator arm. -/
inductive DuplicatorArmVariable
  | port
  | center
  deriving DecidableEq, Repr, Fintype

/-- The Figure 8(a) port selected by an active-arm index. -/
def duplicatorArmPort : Nat → DuplicatorVariable
  | 0 => .left
  | 1 => .top
  | _ => .right

/-- Fixed-template position of each variable in one active arm. -/
def DuplicatorArmVariable.position
    (armIndex : Nat) : DuplicatorArmVariable → Cell
  | .port =>
      DuplicatorVariable.position
        (duplicatorArmPort armIndex)
  | .center => DuplicatorVariable.position .center

/-- The two Figure 8(a) clause positions belonging to one arm. -/
def duplicatorArmEqualityPositions :
    Nat → EqualityPositions
  | 0 => ⟨(3, 4), (3, 3)⟩
  | 1 => ⟨(4, 3), (5, 3)⟩
  | _ => ⟨(5, 4), (5, 5)⟩

/-- The two implication clauses of one active duplicator arm. -/
def duplicatorArmFormula
    (armIndex : Nat) :
    List (EmbeddedClause DuplicatorArmVariable) :=
  equalityInstance .port .center
    (duplicatorArmEqualityPositions armIndex)

/-- Direct incidences for one active duplicator arm. -/
def duplicatorArmStraightIncidenceDrawing
    (armIndex : Nat) :
    EmbeddedCNFIncidenceDrawing DuplicatorArmVariable :=
  straightIncidenceDrawing
    (duplicatorArmFormula armIndex)
    (DuplicatorArmVariable.position armIndex)

/-- Every direct arm incidence has its advertised clause and variable
endpoints. -/
theorem duplicatorArmStraightIncidenceDrawing_routesMatch
    (armIndex : Nat) :
    (duplicatorArmStraightIncidenceDrawing armIndex).RoutesMatch := by
  exact straightIncidenceDrawing_routesMatch
    (duplicatorArmFormula armIndex)
    (DuplicatorArmVariable.position armIndex)

/-- Every left, top, or right active-arm drawing is continuously planar. -/
theorem duplicatorArmStraightIncidenceDrawing_isPlanar
    (armIndex : Nat) :
    (duplicatorArmStraightIncidenceDrawing armIndex).IsPlanar := by
  cases armIndex with
  | zero => native_decide
  | succ armIndex =>
      cases armIndex with
      | zero => native_decide
      | succ armIndex =>
          change
            (duplicatorArmStraightIncidenceDrawing 2).IsPlanar
          native_decide

/-- Every incidence of one active arm has a compass-valid terminal ray. -/
theorem duplicatorArmFormula_embeddedTerminalPortsValid
    (armIndex : Nat) :
    EmbeddedTerminalPortsValid
      (duplicatorArmFormula armIndex)
      (DuplicatorArmVariable.position armIndex) := by
  cases armIndex with
  | zero => native_decide
  | succ armIndex =>
      cases armIndex with
      | zero => native_decide
      | succ armIndex =>
          change
            EmbeddedTerminalPortsValid
              (duplicatorArmFormula 2)
              (DuplicatorArmVariable.position 2)
          native_decide

end PlanarThreeSAT
end LeanTrominoes
