import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentGeometry
import LeanTrominoes.PeriodicThreeDMNormalizationRasterizationCorrectness

/-!
# Separation of normalized 3DM vertex cells

Every degree-three vertex center lies in one fixed residue class modulo the
three-round normalization scale, while a cardinal neighbor differs by one in
one coordinate.  This module turns that coarse-lattice observation into the
`VerticesSeparated` certificate required by the tromino gadget reduction.

The argument deliberately does not assume global route collision freedom.
Vertex assignments precede route assignments in the compiled lookup, and
every route assignment is a nonvertex cell, so any compiled vertex cell must
come from a normalized vertex center.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Rasterized route cells are never degree-three vertex cells. -/
@[simp]
theorem routingCellType_isVertex
    (first second : Side) (color : WireColor) :
    (routingCellType first second color).isVertex = false := by
  cases first <;> cases second <;>
    simp [routingCellType, OrthogonalCellType.isVertex]

@[simp]
theorem routingCellTypeAt_isVertex
    (before current after : Cell) (color : WireColor) :
    (routingCellTypeAt before current after color).isVertex = false := by
  simp [routingCellTypeAt]

/-- Every assignment emitted from a route has a nonvertex cell type. -/
theorem routeInteriorAssignments_isVertex_false
    (period : Nat) (color : WireColor) :
    ∀ {route : List Cell} {assignment : NormalizedCellAssignment},
      assignment ∈ routeInteriorAssignments period color route →
        assignment.2.isVertex = false
  | [], _, member => by simp [routeInteriorAssignments] at member
  | [_], _, member => by simp [routeInteriorAssignments] at member
  | [_, _], _, member => by simp [routeInteriorAssignments] at member
  | before :: current :: after :: rest, assignment, member => by
      simp only [routeInteriorAssignments, List.mem_cons] at member
      rcases member with equal | tailMember
      · subst assignment
        simp
      · exact routeInteriorAssignments_isVertex_false period color tailMember

/-- Every assignment in the flattened route-assignment suffix is a
nonvertex cell. -/
theorem PlanarPresentation.finalRouteAssignment_isVertex_false
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {assignment : NormalizedCellAssignment}
    (member : assignment ∈ presentation.finalRouteAssignments) :
    assignment.2.isVertex = false := by
  simp only [PlanarPresentation.finalRouteAssignments,
    List.mem_flatMap] at member
  rcases member with ⟨edge, _, assignmentMember⟩
  exact routeInteriorAssignments_isVertex_false _ _ assignmentMember

/-- A lookup result classified as a vertex must have come from the vertex
prefix, hence its location is the rasterization of a listed normalized
vertex center. -/
theorem PlanarPresentation.exists_vertex_of_finalCellTypeAt_isVertex
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {location : Cell}
    (isVertex : (presentation.finalCellTypeAt location).isVertex = true) :
    ∃ vertex ∈ problem.contractedGraph.vertices,
      location = rasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition vertex) := by
  unfold PlanarPresentation.finalCellTypeAt at isVertex
  generalize lookupEqual : presentation.finalCellAssignments.lookup location = result
    at isVertex
  cases result with
  | none => simp [OrthogonalCellType.isVertex] at isVertex
  | some cellType =>
      simp only [Option.getD_some] at isVertex
      have assignmentMember : (location, cellType) ∈
          presentation.finalCellAssignments :=
        List.mem_of_lookup_eq_some lookupEqual
      simp only [PlanarPresentation.finalCellAssignments,
        List.mem_append] at assignmentMember
      rcases assignmentMember with vertexMember | routeMember
      · simp only [PlanarPresentation.finalVertexAssignments,
          List.mem_map] at vertexMember
        rcases vertexMember with ⟨vertex, vertexListed, assignmentEqual⟩
        exact ⟨vertex, vertexListed,
          (congrArg Prod.fst assignmentEqual).symm⟩
      · have routeNonvertex :=
          presentation.finalRouteAssignment_isVertex_false routeMember
        rw [routeNonvertex] at isVertex
        contradiction

/-- Expanding the three affine normalization rounds gives scale `12³` and
translation `3 · (12² + 12 + 1) = 471`. -/
theorem PlanarPresentation.finalNormalizationPosition_eq_scaleCube
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) :
    presentation.finalNormalizationPosition vertex =
      Cell.add (Cell.scale 1728
        (presentation.normalizationPosition0 vertex)) (471, 471) := by
  rcases positionEqual : presentation.normalizationPosition0 vertex with
    ⟨horizontal, vertical⟩
  simp only [PlanarPresentation.finalNormalizationPosition,
    PlanarPresentation.normalizationPosition2,
    PlanarPresentation.normalizationPosition1,
    normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add,
    positionEqual, Prod.mk.injEq]
  constructor <;> ring

/-- Three affine normalization rounds put every vertex coordinate in the
same residue class modulo `12³`. -/
theorem PlanarPresentation.finalNormalizationPosition_mod_scaleCube
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) :
    ((presentation.finalNormalizationPosition vertex).1 % 1728,
      (presentation.finalNormalizationPosition vertex).2 % 1728) =
      (471, 471) := by
  rw [presentation.finalNormalizationPosition_eq_scaleCube]
  rcases presentation.normalizationPosition0 vertex with ⟨horizontal, vertical⟩
  simp [Cell.add, Cell.scale, Int.add_emod]

/-- No final normalized vertex center is one genuine unit step away from
another modulo the final drawing period. -/
theorem PlanarPresentation.rasterized_finalNormalizationPositions_not_unitStep
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (first second : PeriodicThreeDMVertex) (direction : AxisDirection)
    (genuine : direction.IsGenuine) :
    rasterLocation presentation.finalNormalizationPeriod
        (presentation.finalNormalizationPosition second) ≠
      rasterLocation presentation.finalNormalizationPeriod
        (Cell.add (presentation.finalNormalizationPosition first)
          direction.step) := by
  intro equal
  rcases (rasterLocation_eq_iff_exists_periodTranslation _ _ _).mp equal with
    ⟨translate, geometricEqual⟩
  rw [presentation.finalNormalizationPosition_eq_scaleCube,
    presentation.finalNormalizationPosition_eq_scaleCube] at geometricEqual
  rcases firstPositionEqual : presentation.normalizationPosition0 first with
    ⟨firstX, firstY⟩
  rcases secondPositionEqual : presentation.normalizationPosition0 second with
    ⟨secondX, secondY⟩
  rcases translate with ⟨translateX, translateY⟩
  cases direction with
  | invalid => simp [AxisDirection.IsGenuine] at genuine
  | east =>
    have horizontalEqual := congrArg Prod.fst geometricEqual
    simp only [firstPositionEqual, secondPositionEqual, AxisDirection.step,
      Cell.add, Cell.scale, PlanarPresentation.finalNormalizationPeriod,
      vertexNormalizationScaleNat] at horizontalEqual
    have horizontalMod :=
      congrArg (fun value : Int => value % 1728) horizontalEqual
    norm_num [Int.add_emod, Int.mul_emod] at horizontalMod
  | north =>
    have verticalEqual := congrArg Prod.snd geometricEqual
    simp only [firstPositionEqual, secondPositionEqual, AxisDirection.step,
      Cell.add, Cell.scale, PlanarPresentation.finalNormalizationPeriod,
      vertexNormalizationScaleNat] at verticalEqual
    have verticalMod :=
      congrArg (fun value : Int => value % 1728) verticalEqual
    norm_num [Int.add_emod, Int.mul_emod] at verticalMod
  | west =>
    have horizontalEqual := congrArg Prod.fst geometricEqual
    simp only [firstPositionEqual, secondPositionEqual, AxisDirection.step,
      Cell.add, Cell.scale, PlanarPresentation.finalNormalizationPeriod,
      vertexNormalizationScaleNat] at horizontalEqual
    have horizontalMod :=
      congrArg (fun value : Int => value % 1728) horizontalEqual
    norm_num [Int.add_emod, Int.mul_emod] at horizontalMod
  | south =>
    have verticalEqual := congrArg Prod.snd geometricEqual
    simp only [firstPositionEqual, secondPositionEqual, AxisDirection.step,
      Cell.add, Cell.scale, PlanarPresentation.finalNormalizationPeriod,
      vertexNormalizationScaleNat] at verticalEqual
    have verticalMod :=
      congrArg (fun value : Int => value % 1728) verticalEqual
    norm_num [Int.add_emod, Int.mul_emod] at verticalMod

/-- Choose the genuine geometric direction corresponding to a drawing-cell
side. -/
def axisDirectionOfSide : Side → AxisDirection
  | .north => .north
  | .east => .east
  | .south => .south
  | .west => .west

@[simp]
theorem axisDirectionOfSide_isGenuine (side : Side) :
    (axisDirectionOfSide side).IsGenuine := by
  cases side <;> simp [axisDirectionOfSide, AxisDirection.IsGenuine]

@[simp]
theorem Side.ofAxisDirection_axisDirectionOfSide (side : Side) :
    Side.ofAxisDirection (axisDirectionOfSide side) = side := by
  cases side <;> rfl

/-- The compiled normalized orthogonal drawing has at least one routing cell
between every pair of degree-three vertex cells. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_verticesSeparated
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.normalizedOrthogonalDrawing.VerticesSeparated := by
  apply presentation.normalizedOrthogonalDrawing_verticesSeparated_of_lookup
  intro position side currentIsVertex
  rcases presentation.exists_vertex_of_finalCellTypeAt_isVertex currentIsVertex with
    ⟨currentVertex, currentMember, currentEqual⟩
  by_contra neighborNotFalse
  have neighborIsVertex :
      (presentation.finalCellTypeAt
        (((presentation.normalizedOrthogonalDrawing.neighbor position side).1.val : Int),
          ((presentation.normalizedOrthogonalDrawing.neighbor position side).2.val : Int))).isVertex =
        true := by
    cases value : (presentation.finalCellTypeAt
      (((presentation.normalizedOrthogonalDrawing.neighbor position side).1.val : Int),
        ((presentation.normalizedOrthogonalDrawing.neighbor position side).2.val : Int))).isVertex <;>
      simp_all
  rcases presentation.exists_vertex_of_finalCellTypeAt_isVertex neighborIsVertex with
    ⟨neighborVertex, neighborMember, neighborEqual⟩
  have currentValues := presentation.normalizedPositionAt_values
    (presentation.finalNormalizationPosition currentVertex)
  have currentValueEqual := currentEqual.trans currentValues.symm
  have currentFiniteEqual :
      position = presentation.normalizedPositionAt
        (presentation.finalNormalizationPosition currentVertex) := by
    have horizontalEqual := congrArg Prod.fst currentValueEqual
    have verticalEqual := congrArg Prod.snd currentValueEqual
    have horizontalEqual' :
        (position.1.val : Int) =
          ((presentation.normalizedPositionAt
            (presentation.finalNormalizationPosition currentVertex)).1.val : Int) := by
      simpa using horizontalEqual
    have verticalEqual' :
        (position.2.val : Int) =
          ((presentation.normalizedPositionAt
            (presentation.finalNormalizationPosition currentVertex)).2.val : Int) := by
      simpa using verticalEqual
    apply Prod.ext
    · apply Fin.ext
      exact_mod_cast horizontalEqual'
    · apply Fin.ext
      exact_mod_cast verticalEqual'
  have neighborFiniteEqual :
      presentation.normalizedOrthogonalDrawing.neighbor position side =
        presentation.normalizedPositionAt
          (Cell.add (presentation.finalNormalizationPosition currentVertex)
            (axisDirectionOfSide side).step) := by
    rw [currentFiniteEqual]
    symm
    simpa using presentation.normalizedPositionAt_add_step
      (presentation.finalNormalizationPosition currentVertex)
      (axisDirectionOfSide_isGenuine side)
  have neighborValues := congrArg
    (fun finitePosition : presentation.normalizedOrthogonalDrawing.Position =>
      (((finitePosition.1.val : Int), (finitePosition.2.val : Int))))
    neighborFiniteEqual
  rw [presentation.normalizedPositionAt_values] at neighborValues
  have rasterEqual := neighborEqual.symm.trans neighborValues
  exact presentation.rasterized_finalNormalizationPositions_not_unitStep
    currentVertex neighborVertex (axisDirectionOfSide side)
      (axisDirectionOfSide_isGenuine side) rasterEqual

end PeriodicThreeDM
end LeanTrominoes
