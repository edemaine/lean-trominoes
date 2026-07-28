import LeanTrominoes.PeriodicOrthocrossingCarrierLensGeometry
import LeanTrominoes.PeriodicCNFPlanarSATGeometry

/-!
# Macrocell arithmetic for planar-SAT vertex positions

Every variable of the routed planar-SAT construction is placed at a local
integer coordinate inside a `20 × 20` macrocell.  This file records the
arithmetic uniqueness of that representation and classifies the local
coordinates used by carrier ports.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A refined point with a half-open local coordinate has a unique
macrocell center and local coordinate. -/
theorem planarSATMacrocellPosition_eq
    {firstCenter secondCenter firstLocal secondLocal : Cell}
    (firstBounds :
      0 ≤ firstLocal.1 ∧ firstLocal.1 < planarMacroScale ∧
        0 ≤ firstLocal.2 ∧ firstLocal.2 < planarMacroScale)
    (secondBounds :
      0 ≤ secondLocal.1 ∧ secondLocal.1 < planarMacroScale ∧
        0 ≤ secondLocal.2 ∧ secondLocal.2 < planarMacroScale)
    (equal :
      Cell.add (Cell.scale planarMacroScale firstCenter) firstLocal =
        Cell.add
          (Cell.scale planarMacroScale secondCenter) secondLocal) :
    firstCenter = secondCenter ∧ firstLocal = secondLocal := by
  have horizontal :=
    periodic_coordinate_unique
      (period := planarMacroScale)
      (first := firstLocal.1) (second := secondLocal.1)
      (firstShift := firstCenter.1)
      (secondShift := secondCenter.1)
      (by norm_num [planarMacroScale])
      ⟨firstBounds.1, firstBounds.2.1⟩
      ⟨secondBounds.1, secondBounds.2.1⟩
      (by
        simpa [Cell.add, Cell.scale, add_comm] using
          congrArg Prod.fst equal)
  have vertical :=
    periodic_coordinate_unique
      (period := planarMacroScale)
      (first := firstLocal.2) (second := secondLocal.2)
      (firstShift := firstCenter.2)
      (secondShift := secondCenter.2)
      (by norm_num [planarMacroScale])
      ⟨firstBounds.2.2.1, firstBounds.2.2.2⟩
      ⟨secondBounds.2.2.1, secondBounds.2.2.2⟩
      (by
        simpa [Cell.add, Cell.scale, add_comm] using
          congrArg Prod.snd equal)
  exact
    ⟨Prod.ext horizontal.2 vertical.2,
      Prod.ext horizontal.1 vertical.1⟩

/-- Every carrier node's total local coordinate lies in the half-open
planar-SAT macrocell. -/
theorem CarrierNode.localPosition_in_macrocell
    (node : CarrierNode) :
    0 ≤ node.localPosition.1 ∧
      node.localPosition.1 < planarMacroScale ∧
      0 ≤ node.localPosition.2 ∧
      node.localPosition.2 < planarMacroScale := by
  cases node with
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      cases side <;>
        norm_num [CarrierNode.localPosition,
          CrossingSide.localPosition,
          CrossoverVariable.position, planarMacroScale]
  | terminal terminal =>
      have bounded :=
        segmentTerminalLocalPosition_in_macrocell
          terminal.indexed.segment terminal.endpoint
      exact
        ⟨le_of_lt bounded.1, bounded.2.1,
          le_of_lt bounded.2.2.1, bounded.2.2.2⟩

/-- Every fixed crossover-variable coordinate lies in the half-open
planar-SAT macrocell. -/
theorem CrossoverVariable.position_in_macrocell
    (role : CrossoverVariable) :
    0 ≤ (CrossoverVariable.position role).1 ∧
      (CrossoverVariable.position role).1 < planarMacroScale ∧
      0 ≤ (CrossoverVariable.position role).2 ∧
      (CrossoverVariable.position role).2 < planarMacroScale := by
  cases role <;>
    norm_num [CrossoverVariable.position, planarMacroScale]

/-- The routed-variable center coordinate lies in the half-open
planar-SAT macrocell. -/
theorem duplicatorArmCenterPosition_in_macrocell :
    0 ≤ duplicatorArmCenterPosition.1 ∧
      duplicatorArmCenterPosition.1 < planarMacroScale ∧
      0 ≤ duplicatorArmCenterPosition.2 ∧
      duplicatorArmCenterPosition.2 < planarMacroScale := by
  norm_num [duplicatorArmCenterPosition, planarMacroScale]

/-- The fixed crossover coordinate table is injective. -/
theorem CrossoverVariable.position_injective :
    Function.Injective CrossoverVariable.position := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [CrossoverVariable.position]

/-- Internal crossover roles have distinct fixed coordinates. -/
theorem crossoverInternalVariable_position_injective :
    Function.Injective
      (CrossoverVariable.position ∘ crossoverInternalVariable) := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [crossoverInternalVariable,
      CrossoverVariable.position]

/-- The four genuine directional coordinates used by carrier ports. -/
def IsCarrierPortLocalPosition (position : Cell) : Prop :=
  position = (1, 6) ∨ position = (11, 6) ∨
    position = (6, 1) ∨ position = (6, 11)

instance (position : Cell) :
    Decidable (IsCarrierPortLocalPosition position) := by
  unfold IsCarrierPortLocalPosition
  infer_instance

/-- Every crossover boundary uses one of the four carrier-port
coordinates. -/
theorem CrossingSide.isCarrierPortLocalPosition
    (side : CrossingSide) :
    IsCarrierPortLocalPosition side.localPosition := by
  cases side <;>
    simp [IsCarrierPortLocalPosition,
      CrossingSide.localPosition, CrossoverVariable.position]

/-- Every endpoint of a genuine axis-aligned segment uses one of the four
carrier-port coordinates. -/
theorem segmentTerminalLocalPosition_isCarrierPort
    (segment : GridSegment) (endpoint : SegmentEnd)
    (axisAligned : segment.IsAxisAligned) :
    IsCarrierPortLocalPosition
      (segmentTerminalLocalPosition segment endpoint) := by
  rcases axisAligned with horizontal | vertical
  · rcases horizontal with ⟨sameY, differentX⟩
    unfold segmentTerminalLocalPosition
    split_ifs <;> cases endpoint <;>
      simp_all [IsCarrierPortLocalPosition] <;> omega
  · rcases vertical with ⟨sameX, differentY⟩
    unfold segmentTerminalLocalPosition
    split_ifs <;> cases endpoint <;>
      simp_all [IsCarrierPortLocalPosition] <;> omega

/-- A genuine carrier port never occupies the routed-variable center. -/
theorem IsCarrierPortLocalPosition.ne_duplicatorArmCenterPosition
    {position : Cell}
    (carrierPort : IsCarrierPortLocalPosition position) :
    position ≠ duplicatorArmCenterPosition := by
  rcases carrierPort with
    rfl | rfl | rfl | rfl <;>
      norm_num [duplicatorArmCenterPosition]

/-- A genuine carrier port never occupies an internal crossover-variable
coordinate. -/
theorem IsCarrierPortLocalPosition.ne_crossoverInternalPosition
    {position : Cell}
    (carrierPort : IsCarrierPortLocalPosition position)
    (internal : CrossoverInternal) :
    position ≠
      CrossoverVariable.position
        (crossoverInternalVariable internal) := by
  rcases carrierPort with
    rfl | rfl | rfl | rfl <;>
      cases internal <;>
        norm_num [crossoverInternalVariable,
          CrossoverVariable.position]

/-- No internal crossover variable occupies the routed-variable center. -/
theorem crossoverInternalPosition_ne_duplicatorArmCenterPosition
    (internal : CrossoverInternal) :
    CrossoverVariable.position
        (crossoverInternalVariable internal) ≠
      duplicatorArmCenterPosition := by
  cases internal <;>
    norm_num [crossoverInternalVariable,
      CrossoverVariable.position, duplicatorArmCenterPosition]

end PeriodicOrthocrossing
end LeanTrominoes
