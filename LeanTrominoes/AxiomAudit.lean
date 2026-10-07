/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.FiniteTrominoRegionNPComplete
import LeanTrominoes.FiniteTrominoCompletionNPComplete
import LeanTrominoes.CompletionCompleteness
import LeanTrominoes.CompletionStripHardness
import LeanTrominoes.TwoConnectedPolycubesSpaceProof
import LeanTrominoes.TwoConnectedPolycubesSlabsProof
import LeanTrominoes.Theorem52Proof
import LeanTrominoes.Theorem55Proof
import LeanTrominoes.Theorem55StripProof
import LeanTrominoes.ThreeTranslationProof
import LeanTrominoes.ThreeTranslationPolycubesProof
import LeanTrominoes.FinitePolyominoCompletionCoRE
import LeanTrominoes.FixedWangSeedPlaneHardness
import LeanTrominoes.FixedThreeSATThreeSeedCompleteness
import LeanTrominoes.FixedPlanarSATSeedCompleteness
import LeanTrominoes.FixedRetainedExactOneSeedCompleteness
import LeanTrominoes.FixedPlanarThreeDMSeedCompleteness
import LeanTrominoes.FixedNormalizedOrientationSeedCompleteness
import LeanTrominoes.GadgetIPreferredSelection
import LeanTrominoes.GadgetICanonicalSeedComputability
import LeanTrominoes.FixedPolyominoSeedQuarterSoundness
import LeanTrominoes.FixedPolyominoSeedCompleteness
import LeanTrominoes.PeriodicCNFPlanarRetainedPolaritySeed
import LeanTrominoes.BumpySeedRefinement
import LeanTrominoes.PeriodicCNFDimensions
import LeanTrominoes.PeriodicThreeDMLocalPlaneCompleteness
import LeanTrominoes.FiniteOrientationNPComplete
import LeanTrominoes.TrichromaticGraphOrientationCompleteness
import LeanTrominoes.TrichromaticOrientationForcedSinkDrawing
import LeanTrominoes.OrthogonalDrawingRefinementBounds
import LeanTrominoes.GridSegmentRealSlabOrder
import LeanTrominoes.PeriodicGridDrawingStraightCopyWindow
import LeanTrominoes.PeriodicGridDrawingVerticalCrossings
import LeanTrominoes.PeriodicGridDrawingVerticalCrossingEnumeration
import LeanTrominoes.FiniteCrossingRanks
import LeanTrominoes.PeriodicGridDrawingStraightAnchorGeometry
import LeanTrominoes.OrthogonalSlabRouteBounds
import LeanTrominoes.OrthogonalSlabRouteWord
import LeanTrominoes.OrthogonalSlabPeriodicOverlap
import LeanTrominoes.OrthogonalBoundaryMatchingCorrect
import LeanTrominoes.OrthogonalBoundaryCellSeparation
import LeanTrominoes.RealRectangleBoundaryNoninterlacing
import LeanTrominoes.PeriodicGridDrawingPeriodicHorizontalCrossingTable
import LeanTrominoes.FiniteHeightPaddedRedistribution
import LeanTrominoes.PeriodicGridDrawingPaddedCrossingBars
import LeanTrominoes.PeriodicGridDrawingPaddedSlabPorts
import LeanTrominoes.FiniteRationalPerturbation
import LeanTrominoes.PeriodicGridDrawingShiftedSeamBounds
import LeanTrominoes.RectangleBoundaryMatchingTransport
import LeanTrominoes.OrthogonalBoundarySlabSeparation
import LeanTrominoes.PeriodicGridDrawingVirtualHorizontalPortOrder
import LeanTrominoes.PeriodicGridDrawingColumnPortTransport
import LeanTrominoes.PeriodicGridDrawingAnchorBoundaryOrder
import LeanTrominoes.PeriodicGridDrawingPeriodicColumnRefinement
import LeanTrominoes.PeriodicGridDrawingPeriodicCrossingBars
import LeanTrominoes.PeriodicGraphDrawingCardinality
import LeanTrominoes.GridSegmentCollinearRectangleSeparation
import LeanTrominoes.DegreeThreeVertexNormalizationSelectedPort
import LeanTrominoes.GeneralVertexNormalization
import LeanTrominoes.PeriodicOrthocrossingGeneralLocal
import LeanTrominoes.PeriodicOrthocrossingGeneralCoreOccurrenceCrossings
import LeanTrominoes.PeriodicOrthocrossingGeneralFanContacts
import LeanTrominoes.PeriodicOrthocrossingGeneralFanCoreContacts
import LeanTrominoes.PeriodicOrthocrossingGeneralRouteFanCoreSeparation
import LeanTrominoes.PeriodicOrthocrossingGeneralCrossingCertificates
import LeanTrominoes.GridPolylineRealOpenSimple
import LeanTrominoes.GridPolylineRealAlgebra
import LeanTrominoes.KeyedComplementRecoveredWindowTilings
import LeanTrominoes.KeyedComplementGadgetPins
import Lean.Util.CollectAxioms

/-!
# Axiom regression checks for the main completeness theorems

All finite certificates are checked by Lean's kernel. These checks reject
any assumption beyond the three standard Lean axioms, including native
execution certificates and unfinished proofs.
-/

open Lean Elab Command in
run_cmd do
  for name in [``LeanTrominoes.Tromino.FiniteCoordinateColumns.region_npComplete,
      ``LeanTrominoes.Tromino.FiniteCoordinateColumns.completion_npComplete,
      ``LeanTrominoes.PeriodicTrominoPrefill.planeProblem_coREComplete,
      ``LeanTrominoes.PeriodicStripTrominoPrefill.problem_PSPACEComplete,
      ``LeanTrominoes.TwoConnectedPolycubes.spaceProved,
      ``LeanTrominoes.TwoConnectedPolycubes.slabsProved,
      ``LeanTrominoes.ThreeTranslationPolyominoes.proved,
      ``LeanTrominoes.ThreeTranslationPolycubes.proved,
      ``LeanTrominoes.Theorem52.proved,
      ``LeanTrominoes.Theorem55.planeProved,
      ``LeanTrominoes.Theorem55.stripProved,
      ``LeanTrominoes.FinitePolyominoCompletion.coRE,
      ``LeanTrominoes.FixedMachineWangSeed.PlaneExtension.universalPlanePalette_coREHard,
      ``LeanTrominoes.FixedThreeSATThreeSeed.coREComplete,
      ``LeanTrominoes.FixedPlanarSATSeed.coREComplete,
      ``LeanTrominoes.FixedPlanarSATSeed.fixedCertificate,
      ``LeanTrominoes.FixedRetainedExactOneSeed.coREComplete,
      ``LeanTrominoes.FixedRetainedExactOneSeed.fixedDrawing_planar,
      ``LeanTrominoes.FixedRetainedExactOneSeed.fixedDrawing_compatible,
      ``LeanTrominoes.FixedPlanarThreeDMSeed.coREComplete,
      ``LeanTrominoes.FixedPlanarThreeDMSeed.fixedPresentation,
      ``LeanTrominoes.FixedNormalizedOrientationSeed.coREComplete,
      ``LeanTrominoes.FixedNormalizedOrientationSeed.fixedDrawing_wellFormed,
      ``LeanTrominoes.FixedNormalizedOrientationSeed.fixedDrawing_verticesSeparated,
      ``LeanTrominoes.Gadget.PreferredISelection.assignment_compatible,
      ``LeanTrominoes.Gadget.PreferredISelection.pattern_eq_of_active_eq,
      ``LeanTrominoes.Gadget.CanonicalISelection.seeded_tiling_iff,
      ``LeanTrominoes.Gadget.CanonicalISelection.refinedSeedPlacements_primrec,
      ``LeanTrominoes.FixedWangNormalizedSeedDecoder.uniform_window,
      ``LeanTrominoes.FixedPolyominoSeed.quarter_satisfies,
      ``LeanTrominoes.FixedPolyominoSeed.coREComplete,
      ``LeanTrominoes.FixedPolyominoSeed.corollary57,
      ``LeanTrominoes.FixedPolyominoSeed.reduction_computable,
      ``LeanTrominoes.FixedMachineWangSeed.PlaneExtension.quarter_of_seeded_quarter,
      ``LeanTrominoes.KeyedPeriodicComplement.PartialGadgetReadout.readout_eq_of_deep_pins,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.encodedSeedFactor,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.totalSeedReduction_correct,
      ``LeanTrominoes.PeriodicOrthocrossing.retainedPolaritySeedFactor,
      ``LeanTrominoes.PeriodicCNF.SignedDecoder.local_clause,
      ``LeanTrominoes.PlusRefinement.seeded_refinement_iff,
      ``LeanTrominoes.PeriodicCNFDimensions.satisfiable_coREComplete,
      ``LeanTrominoes.PeriodicThreeDM.localPlaneProblem_coREComplete,
      ``LeanTrominoes.Gadget.FiniteOrientation.npComplete,
      ``LeanTrominoes.TrichromaticGraphOrientation.problem_coREComplete,
      ``LeanTrominoes.TrichromaticGraphOrientation.ForcedSink.internal_orientation_forces_boundary,
      ``LeanTrominoes.TrichromaticGraphOrientation.ForcedSink.drawing_planar,
      ``LeanTrominoes.TrichromaticGraphOrientation.ForcedSink.drawing_orthogonal,
      ``LeanTrominoes.OrthogonalSlabRouting.real_tracks_disjoint,
      ``LeanTrominoes.OrthogonalDrawingRefinement.gridSize_cubic,
      ``LeanTrominoes.GridSegment.vertex_rectangle_avoids_nonincident_segment,
      ``LeanTrominoes.PeriodicGridDrawing.compatible_edge_count_bound,
      ``LeanTrominoes.DegreeThreeVertexNormalization.selectedBoundarySide_west,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.portX_injective,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.drawing_isCompatible,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.drawing_isOrthogonal,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.drawing_isRealLocal,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.drawing_gridSize_linear,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.degreeFourFan_meet_only_at_center,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.core_isRealSimple,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.core_contacts_distinct_occurrences_are_proper,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.fan_periodic_contacts_center,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.fan_isRealSimple,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.fan_top_contact,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.fan_core_contacts_only_at_joint,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.route_realContains_parts,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.source_fan_core_contacts_same_occurrence,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.target_fan_core_contacts_same_occurrence,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.drawing_isRealOrthocrossing,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.drawing_realVerticesAvoidRoutes,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.route_isRealSimple,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.local_orthocrossing_drawing,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.local_orthogonal_orthocrossing_drawing,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.drawing_crossings_integral,
      ``LeanTrominoes.PeriodicOrthocrossing.GeneralPorts.route_occurrences_no_triple,
      ``LeanTrominoes.DegreeThreeVertexNormalization.selectedTemplate_isRealOpenSimple,
      ``LeanTrominoes.DegreeThreeVertexNormalization.selectedCanonicalPort_chosen,
      ``LeanTrominoes.GeneralVertexNormalization.portDirection_genuine,
      ``LeanTrominoes.GeneralVertexNormalization.fanAssignment_last,
      ``LeanTrominoes.GeneralVertexNormalization.fanAssignment_chosen_west,
      ``LeanTrominoes.GeneralVertexNormalization.distinctPortSides_of_planar_orthogonal,
      ``LeanTrominoes.GeneralVertexNormalization.normalizedRoute_simple,
      ``LeanTrominoes.GeneralVertexNormalization.normalizedDrawing_isRealPlanarDrawing,
      ``LeanTrominoes.GeneralVertexNormalization.normalizedDrawing_isRealLocal,
      ``LeanTrominoes.GeneralVertexNormalization.normalizedDrawing_chosen_west,
      ``LeanTrominoes.GeneralVertexNormalization.lemma23,
      ``LeanTrominoes.GridSegment.real_slab_order_preserved,
      ``LeanTrominoes.GridSegment.real_slab_order_strict,
      ``LeanTrominoes.GridSegment.real_local_segment_copy_window,
      ``LeanTrominoes.PeriodicGridDrawing.straight_realEdgeRoute_copy_window,
      ``LeanTrominoes.GridSegment.rationalLineHeight_realContains,
      ``LeanTrominoes.PeriodicGridDrawing.vertical_crossing_heights_ne,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCrossingHeights_card_bound,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCrossingCopies_complete,
      ``LeanTrominoes.OrthogonalDrawingRefinement.crossingRank_strictMonoOn,
      ``LeanTrominoes.OrthogonalDrawingRefinement.ranked_crossingCoordinate_outside_rectangles,
      ``LeanTrominoes.GridSegment.realContains_straightRay_halfStep,
      ``LeanTrominoes.PeriodicGridDrawing.distinctPortRayKeys_of_planar_straight,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rectangleTemplate_isRealOpenSimple,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rectangleTemplate_contacts_center,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rectangleTemplate_boundary_contact,
      ``LeanTrominoes.OrthogonalDrawingRefinement.AnchorProfile.initialDirections_clockwise,
      ``LeanTrominoes.OrthogonalDrawingRefinement.incidenceAnchorIndex_injective,
      ``LeanTrominoes.OrthogonalDrawingRefinement.incidenceTemplates_contact,
      ``LeanTrominoes.OrthogonalDrawingRefinement.orderedIncidences_strict,
      ``LeanTrominoes.OrthogonalDrawingRefinement.incidenceTemplate_firstDirection_injective,
      ``LeanTrominoes.OrthogonalDrawingRefinement.incidenceTemplateAt_avoids_nonincident_segment,
      ``LeanTrominoes.OrthogonalDrawingRefinement.refinementFactor_isolates_rectangles,
      ``LeanTrominoes.OrthogonalSlabRouting.route_isRealOpenSimple,
      ``LeanTrominoes.OrthogonalSlabRouting.routes_disjoint,
      ``LeanTrominoes.OrthogonalSlabRouting.route_left_boundary,
      ``LeanTrominoes.OrthogonalSlabRouting.route_right_boundary,
      ``LeanTrominoes.OrthogonalSlabRouting.consecutive_routes_contact_joint,
      ``LeanTrominoes.GridPolyline.isRealOpenSimple_join,
      ``LeanTrominoes.OrthogonalSlabRouting.SlabRoute.compose_valid,
      ``LeanTrominoes.OrthogonalSlabRouting.SlabRoute.compose_image,
      ``LeanTrominoes.OrthogonalSlabRouting.periodic_vertical_track_overlap,
      ``LeanTrominoes.OrthogonalBoundaryRouting.route_isRealOpenSimple,
      ``LeanTrominoes.OrthogonalBoundaryRouting.inner_boundaries_disjoint,
      ``LeanTrominoes.OrthogonalBoundaryRouting.normal_innerArc_real_contact_between,
      ``LeanTrominoes.OrthogonalBoundaryRouting.distinctNestingDepth_injective,
      ``LeanTrominoes.OrthogonalBoundaryRouting.distinctNestingDepth_le_card,
      ``LeanTrominoes.OrthogonalBoundaryRouting.distinctNestingDepth_strict,
      ``LeanTrominoes.OrthogonalBoundaryRouting.matchingRoute_orthogonal,
      ``LeanTrominoes.OrthogonalBoundaryRouting.matchingRoute_isRealOpenSimple,
      ``LeanTrominoes.OrthogonalBoundaryRouting.matchingRoutes_disjoint,
      ``LeanTrominoes.OrthogonalBoundaryRouting.route_boundary_contact_ports,
      ``LeanTrominoes.OrthogonalBoundaryRouting.distinct_cells_contact_first_endpoint,
      ``LeanTrominoes.GridSegment.RealContains.interpolate_interior,
      ``LeanTrominoes.GridSegment.real_interior_contact_of_opposite_sides,
      ``LeanTrominoes.RealRectangleBoundary.orientedArea_positive_between,
      ``LeanTrominoes.RealRectangleBoundary.alternating_chords_interior_contact,
      ``LeanTrominoes.RealRectangleBoundary.noninterlacing_of_disjoint_interiors,
      ``LeanTrominoes.PeriodicGridDrawing.horizontalCrossingAbscissae_card_bound,
      ``LeanTrominoes.PeriodicGridDrawing.horizontalCrossingCopies_complete,
      ``LeanTrominoes.PeriodicGridDrawing.horizontal_crossing_abscissae_ne,
      ``LeanTrominoes.PeriodicGridDrawing.periodic_horizontal_crossing_residue_mem,
      ``LeanTrominoes.OrthogonalDrawingRefinement.paddedGridSize_cubic,
      ``LeanTrominoes.OrthogonalDrawingRefinement.paddedRedistributedHeight_strictMonoOn,
      ``LeanTrominoes.OrthogonalDrawingRefinement.paddedRedistributedHeight_bounds,
      ``LeanTrominoes.GridPolyline.IsRealOpenSimple.scale,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_isRealOpenSimple,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_orthogonal,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_contacts_center,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_contacts_same_position,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedCrossingBars_disjoint,
      ``LeanTrominoes.OrthogonalDrawingRefinement.periodicRedistributedHeight_vertex_clearance,
      ``LeanTrominoes.PeriodicGridDrawing.paddedPeriodicColumnHeight_translate,
      ``LeanTrominoes.PeriodicGridDrawing.paddedPeriodicColumnHeight_row_clearance,
      ``LeanTrominoes.PeriodicGridDrawing.paddedPeriodicColumnHeight_preserves_order,
      ``LeanTrominoes.PeriodicGridDrawing.paddedPeriodicColumnHeight_avoids_lifted_vertex,
      ``LeanTrominoes.PeriodicGridDrawing.paddedCrossingBar_avoids_lifted_rectangle,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rationalSlab_translate,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rationalSlab_order,
      ``LeanTrominoes.OrthogonalDrawingRefinement.seamCoordinate_strictMonoOn,
      ``LeanTrominoes.GridSegment.local_horizontal_seam_abscissa_bounds,
      ``LeanTrominoes.PeriodicGridDrawing.horizontalCrossingCopies_abscissa_injective,
      ``LeanTrominoes.PeriodicGridDrawing.periodic_seam_crossing_residue_mem,
      ``LeanTrominoes.PeriodicGridDrawing.periodicSeamCoordinate_translate,
      ``LeanTrominoes.PeriodicGridDrawing.periodicSeamCoordinate_preserves_order,
      ``LeanTrominoes.PeriodicGridDrawing.periodicSeamCoordinate_slab_clearance,
      ``LeanTrominoes.PeriodicGridDrawing.row_seam_integral_column_bias,
      ``LeanTrominoes.PeriodicGridDrawing.row_seam_port_column_locality,
      ``LeanTrominoes.PeriodicGridDrawing.row_seam_ports_preserve_order,
      ``LeanTrominoes.PeriodicGridDrawing.paddedSlab_room,
      ``LeanTrominoes.PeriodicGridDrawing.paddedVerticalSlabPort_inside,
      ``LeanTrominoes.PeriodicGridDrawing.paddedHorizontalSlabPort_inside,
      ``LeanTrominoes.PeriodicGridDrawing.paddedVerticalSlabPort_point,
      ``LeanTrominoes.PeriodicGridDrawing.paddedHorizontalSlabPort_point,
      ``LeanTrominoes.RationalPerturbation.margin_positive,
      ``LeanTrominoes.RationalPerturbation.evaluate_order,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rationalSlab_perturbation,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rationalSlab_perturbation_strict_bounds,
      ``LeanTrominoes.RationalPerturbation.slabPerturbation_positive,
      ``LeanTrominoes.RationalPerturbation.slabPerturbation_preserves_order,
      ``LeanTrominoes.RationalPerturbation.slabPerturbation_realizes_bias,
      ``LeanTrominoes.GridSegment.shifted_horizontal_seam_slab,
      ``LeanTrominoes.GridSegment.shifted_horizontal_seam_realInteriorContains,
      ``LeanTrominoes.PeriodicGridDrawing.shiftedSeamAbscissa_slab,
      ``LeanTrominoes.PeriodicGridDrawing.shiftedSeamAbscissae_preserve_order,
      ``LeanTrominoes.PeriodicGridDrawing.row_shifted_seam_slab,
      ``LeanTrominoes.PeriodicGridDrawing.row_shifted_seam_realInteriorContains,
      ``LeanTrominoes.PeriodicGridDrawing.shiftedSeamAbscissa_strict_slab_bounds,
      ``LeanTrominoes.PeriodicGridDrawing.shiftedSeamAbscissa_in_cell,
      ``LeanTrominoes.RealRectangleBoundary.shifted_noninterlacing_of_disjoint_interiors,
      ``LeanTrominoes.RectangleBoundaryMatchingTransport.preserves_before,
      ``LeanTrominoes.RectangleBoundaryMatchingTransport.routed_straight_chords_disjoint,
      ``LeanTrominoes.OrthogonalBoundaryRouting.distinct_slabs_contact_first_endpoint,
      ``LeanTrominoes.PeriodicGridDrawing.columnCutMargin_positive,
      ``LeanTrominoes.PeriodicGridDrawing.shiftedSeamAbscissa_inside_shrunken_slab,
      ``LeanTrominoes.PeriodicGridDrawing.virtualHorizontalPort_inside,
      ``LeanTrominoes.PeriodicGridDrawing.virtualHorizontalPort_realInteriorContains,
      ``LeanTrominoes.PeriodicGridDrawing.virtualHorizontalPort_before,
      ``LeanTrominoes.RationalPerturbation.evaluate_lt_iff,
      ``LeanTrominoes.RationalPerturbation.evaluate_injective_on,
      ``LeanTrominoes.PeriodicGridDrawing.shifted_row_bounds_for_column_crossing,
      ``LeanTrominoes.PeriodicGridDrawing.columnPerturbation_preserves_order,
      ``LeanTrominoes.PeriodicGridDrawing.virtualVerticalPort_inside,
      ``LeanTrominoes.PeriodicGridDrawing.virtualVerticalPort_point,
      ``LeanTrominoes.PeriodicGridDrawing.virtualIncidencePort_inside,
      ``LeanTrominoes.PeriodicGridDrawing.virtualIncidencePort_realInteriorContains,
      ``LeanTrominoes.PeriodicGridDrawing.virtualVerticalPort_before,
      ``LeanTrominoes.PeriodicGridDrawing.crossing_fan_coordinate_order,
      ``LeanTrominoes.PeriodicGridDrawing.fan_crossing_coordinate_order,
      ``LeanTrominoes.PeriodicGridDrawing.virtualIncidencePort_coordinate_order,
      ``LeanTrominoes.PeriodicGridDrawing.columnPort_coordinate_order,
      ``LeanTrominoes.PeriodicGridDrawing.columnPort_virtual_inside,
      ``LeanTrominoes.PeriodicGridDrawing.columnPort_integral_inside,
      ``LeanTrominoes.PeriodicGridDrawing.paddedFanSlabPort_point,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_last_anchor,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCrossingCopies_height_injective,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCrossingHeights_card_eq,
      ``LeanTrominoes.OrthogonalDrawingRefinement.height_brackets_same_or_separated,
      ``LeanTrominoes.OrthogonalDrawingRefinement.redistributedHeight_strictMonoOn,
      ``LeanTrominoes.PeriodicGridDrawing.redistributedCrossingHeights_strictMonoOn,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCrossingHeight_ne_vertex,
      ``LeanTrominoes.PeriodicGridDrawing.redistributedCrossingBar_avoids_rectangle,
      ``LeanTrominoes.OrthogonalDrawingRefinement.sorted_groups_eq_anchorGroups,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rayGroups_eq_anchorGroups,
      ``LeanTrominoes.OrthogonalDrawingRefinement.incidenceTemplate_last_some,
      ``LeanTrominoes.OrthogonalDrawingRefinement.right_portBoundaryAnchor_order,
      ``LeanTrominoes.OrthogonalDrawingRefinement.left_portBoundaryAnchor_order,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rationalResidue_translate,
      ``LeanTrominoes.GridSegment.rationalLineHeight_translate,
      ``LeanTrominoes.OrthogonalDrawingRefinement.periodicRedistributedHeight_preserves_order,
      ``LeanTrominoes.PeriodicGridDrawing.periodic_crossing_residue_mem,
      ``LeanTrominoes.PeriodicGridDrawing.periodicColumnHeight_translate,
      ``LeanTrominoes.PeriodicGridDrawing.periodicColumnHeight_in_row,
      ``LeanTrominoes.PeriodicGridDrawing.periodicColumnHeight_preserves_order,
      ``LeanTrominoes.PeriodicGridDrawing.periodicColumnHeight_avoids_lifted_vertex,
      ``LeanTrominoes.PeriodicGridDrawing.periodicCrossingBar_avoids_lifted_rectangle,
      ``LeanTrominoes.DegreeThreeVertexNormalization.selectedTemplate_real_contacts_center,
      ``LeanTrominoes.DegreeThreeVertexNormalization.selectedTemplateAt_contacts_same_position,
      ``LeanTrominoes.DegreeThreeVertexNormalization.selectedTemplateAt_trimmedRoute_contact,
      ``LeanTrominoes.GridPolyline.IsRealSimple.scale,
      ``LeanTrominoes.GridPolyline.IsRealSimple.translate,
      ``LeanTrominoes.GridPolyline.clippedScaledRoute_isRealOpenSimple,
      ``LeanTrominoes.GridPolyline.clippedScaledRoute_neighborhood_contact,
      ``LeanTrominoes.GridSegment.scaled_neighborhood_contact_implies_incident,
      ``LeanTrominoes.GridPolyline.IsRealOpenSimple.head_contact_index,
      ``LeanTrominoes.GridPolyline.IsRealOpenSimple.last_contact_index,
      ``LeanTrominoes.KeyedPeriodicComplement.recoveredCoarse_windowTiling,
      ``LeanTrominoes.KeyedPeriodicComplement.PartialGadgetReadout.vertex_sound,
      ``LeanTrominoes.KeyedPeriodicComplement.PartialGadgetReadout.readout_eq_of_pins] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do
      throwError "{name} depends on unexpected axioms: {extra}"
