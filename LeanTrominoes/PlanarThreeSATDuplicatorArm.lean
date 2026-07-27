import LeanTrominoes.PlanarThreeSATWires

/-!
# Routed duplicator-arm coordinates

The periodic orthocrossing construction reaches a variable macrocell through
three target fanout ports.  These definitions adapt Figure 8(a)'s logical
three-way equality star to those exact local coordinates.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- The three geometric arms at a routed variable site.  The middle route
fanout enters from below in the drawing coordinate system. -/
inductive DuplicatorArm
  | left
  | middle
  | right
  deriving DecidableEq, Repr, Fintype

/-- The endpoint and center roles present in one active duplicator arm. -/
inductive DuplicatorArmVariable
  | port
  | center
  deriving DecidableEq, Repr, Fintype

/-- Local target-terminal coordinate of each routed-variable arm. -/
def DuplicatorArm.portPosition : DuplicatorArm → Cell
  | .left => (1, 6)
  | .middle => (6, 11)
  | .right => (11, 6)

/-- The common center of the routed-variable equality star. -/
def duplicatorArmCenterPosition : Cell := (6, 7)

/-- Fixed-template position of each variable in one active arm. -/
def DuplicatorArmVariable.position
    (arm : DuplicatorArm) : DuplicatorArmVariable → Cell
  | .port => arm.portPosition
  | .center => duplicatorArmCenterPosition

/-- The two compass-valid clause positions belonging to one routed arm. -/
def duplicatorArmEqualityPositions :
    DuplicatorArm → EqualityPositions
  | .left => ⟨(2, 7), (5, 6)⟩
  | .middle => ⟨(4, 9), (6, 8)⟩
  | .right => ⟨(6, 6), (8, 9)⟩

end PlanarThreeSAT
end LeanTrominoes
