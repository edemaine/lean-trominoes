/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentGeometry

/-! # Uniform blank margins in the normalized hard-source drawing

The last factor-twelve normalization round confines its local templates to
residues 0 through 6. Magnified axis steps have one coordinate congruent to 3.
Thus the opposite five-by-five residue square is unused, independently of
the input drawing and its route lengths.
-/

namespace LeanTrominoes.PeriodicThreeDM

open DegreeThreeVertexNormalization

/-- The residue corridors occupied by the final normalization round. -/
def InNormalizationCorridor (p : Cell) : Prop := p.1 % 12 ≤ 6 ∨ p.2 % 12 ≤ 6

private theorem subdivide_in_corridor (points : List Cell)
    (centers : ∀ p ∈ points, p.1 % 12 = 3 ∧ p.2 % 12 = 3) :
    ∀ p ∈ AxisDirection.unitSubdividePolyline points, InNormalizationCorridor p := by
  induction points using List.twoStepInduction with
  | nil => simp
  | singleton a =>
    intro p hp
    simp only [AxisDirection.unitSubdividePolyline, List.mem_singleton] at hp
    subst p
    have ha := centers a (by simp)
    unfold InNormalizationCorridor
    omega
  | cons_cons a b rest _ ih =>
    intro p hp
    rw [AxisDirection.unitSubdividePolyline] at hp
    rcases mem_joinAtEndpoint hp with first | tail
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp first
      have ha := centers a (by simp)
      unfold InNormalizationCorridor
      cases AxisDirection.between a b <;>
        dsimp [Cell.add, Cell.scale, AxisDirection.step] <;> omega
    · exact ih b (fun q hq => centers q (List.mem_cons_of_mem a hq)) p tail

theorem magnifiedUnitRoute_in_corridor (points : List Cell) :
    ∀ p ∈ magnifiedUnitRoute points, InNormalizationCorridor p := by
  apply subdivide_in_corridor
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  simp [normalizeVertexPosition, vertexNormalizationScale, center, Cell.add, Cell.scale,
    Int.add_emod]

private theorem template_in_corridor (position : Cell) (points : List Cell)
    (bounded : RouteInSquare points) :
    ∀ p ∈ normalizationTemplateAt position points, InNormalizationCorridor p := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have bounds := bounded q hq
  dsimp [InNormalizationCorridor, vertexNormalizationScale, Cell.add, Cell.scale]
  simp only [Int.add_emod, Int.mul_emod_right, Int.zero_add, Int.emod_emod]
  omega

theorem normalizeRouteWithTemplates_in_corridor (source target : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell)
    (sourceBounded : RouteInSquare sourceTemplate) (targetBounded : RouteInSquare targetTemplate) :
    ∀ p ∈ normalizeRouteWithTemplates source target sourceTemplate targetTemplate oldRoute,
      InNormalizationCorridor p := by
  intro p hp
  rcases mem_joinAtEndpoint hp with hs | rest
  · exact template_in_corridor source sourceTemplate sourceBounded p hs
  · rcases mem_joinAtEndpoint rest with middle | ht
    · exact magnifiedUnitRoute_in_corridor oldRoute p
        (List.mem_of_mem_drop (List.mem_of_mem_take middle))
    · exact template_in_corridor target targetTemplate targetBounded p (List.mem_reverse.mp ht)

private theorem rotation_template_bounded (active : Bool) (port : CanonicalVertexPort) :
    RouteInSquare (rotationRoundPortAndRoute active port).2 := by
  cases active <;> cases port <;> decide +kernel

/-- Every final route point avoids the open residue square `(6,12)²`. -/
theorem PlanarPresentation.finalNormalizationRoute_in_corridor
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) (edge : ContractedEdge) :
    ∀ p ∈ presentation.finalNormalizationRoute edge, InNormalizationCorridor p := by
  apply normalizeRouteWithTemplates_in_corridor
  · exact rotation_template_bounded _ _
  · exact rotation_template_bounded _ _

theorem PlanarPresentation.finalNormalizationPosition_in_corridor
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) :
    InNormalizationCorridor (presentation.finalNormalizationPosition vertex) := by
  simp [PlanarPresentation.finalNormalizationPosition, InNormalizationCorridor,
    normalizeVertexPosition, vertexNormalizationScale, center, Cell.add, Cell.scale, Int.add_emod]

theorem PlanarPresentation.finalGeometricAssignmentPoints_in_corridor
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    ∀ p ∈ presentation.finalGeometricAssignmentPoints, InNormalizationCorridor p := by
  intro p hp
  rw [PlanarPresentation.finalGeometricAssignmentPoints, List.mem_append] at hp
  rcases hp with vertex | route
  · rw [presentation.finalNormalizedVertexPositions_eq_map] at vertex
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp vertex
    exact presentation.finalNormalizationPosition_in_corridor v
  · obtain ⟨edge, _, hp⟩ := List.mem_flatMap.mp route
    exact presentation.finalNormalizationRoute_in_corridor edge p
      (List.mem_of_mem_tail (List.mem_of_mem_dropLast hp))

/-- The final period preserves residues modulo twelve. -/
theorem PlanarPresentation.twelve_dvd_finalNormalizationPeriod
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    (12 : Int) ∣ (presentation.finalNormalizationPeriod : Int) := by
  refine ⟨144 * (presentation.contractedDrawing.gridSize : Int), ?_⟩
  simp [PlanarPresentation.finalNormalizationPeriod, vertexNormalizationScaleNat]
  ring

/-- The unused five-by-five residue square, after the rasterizer's vertical
reflection. The conclusion concerns the actual drawing lookup. -/
theorem PlanarPresentation.finalCellTypeAt_blank_of_residues
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) (location : Cell)
    (hx : 7 ≤ location.1 % 12) (hy : 1 ≤ location.2 % 12) (hy' : location.2 % 12 ≤ 5) :
    presentation.finalCellTypeAt location = .blank := by
  have divisor := presentation.twelve_dvd_finalNormalizationPeriod
  unfold PlanarPresentation.finalCellTypeAt
  cases lookup : presentation.finalCellAssignments.lookup location with
  | none => rfl
  | some cellType =>
    have member : location ∈ presentation.finalAssignmentLocations :=
      List.mem_map.mpr ⟨(location, cellType), List.mem_of_lookup_eq_some lookup, rfl⟩
    rw [presentation.finalAssignmentLocations_eq_map] at member
    obtain ⟨p, hp, eq⟩ := List.mem_map.mp member
    have corridor := presentation.finalGeometricAssignmentPoints_in_corridor p hp
    have ex : location.1 % 12 = p.1 % 12 := by
      rw [← eq]
      exact Int.emod_emod_of_dvd _ divisor
    have ey : location.2 % 12 = (-p.2) % 12 := by
      rw [← eq]
      exact Int.emod_emod_of_dvd _ divisor
    unfold InNormalizationCorridor at corridor
    omega

/-- The same blank square occurs throughout the infinite periodic lift. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_getAt_blank_of_residues
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) (location : Cell)
    (hx : 7 ≤ location.1 % 12) (hy : 1 ≤ location.2 % 12) (hy' : location.2 % 12 ≤ 5) :
    presentation.normalizedOrthogonalDrawing.getAt location = .blank := by
  unfold Gadget.PeriodicOrthogonalDrawing.getAt
  rw [presentation.normalizedOrthogonalDrawing_get]
  have px : (presentation.normalizedOrthogonalDrawing.horizontalPeriodPred : Int) + 1 =
      presentation.finalNormalizationPeriod := by
    exact_mod_cast presentation.normalizedOrthogonalDrawing_periods.1
  have py : (presentation.normalizedOrthogonalDrawing.verticalPeriodPred : Int) + 1 =
      presentation.finalNormalizationPeriod := by
    exact_mod_cast presentation.normalizedOrthogonalDrawing_periods.2
  apply presentation.finalCellTypeAt_blank_of_residues
  all_goals
    simp only [Gadget.PeriodicOrthogonalDrawing.positionAt,
      Gadget.PeriodicOrthogonalDrawing.residue_val_int, px, py,
      Int.emod_emod_of_dvd _ presentation.twelve_dvd_finalNormalizationPeriod]
    assumption

end LeanTrominoes.PeriodicThreeDM
