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
import LeanTrominoes.PeriodicGridDrawingRectangleInputRoutes
import LeanTrominoes.PeriodicGridDrawingRectangleInteriorCoverage
import LeanTrominoes.GridPolylineRouteWord
import LeanTrominoes.GridPolylineRouteWordTranslation
import LeanTrominoes.GridPolylineIntervalAssembly
import LeanTrominoes.PeriodicGridDrawingEdgeRouteAssembly
import LeanTrominoes.PeriodicGridDrawingEdgePieceBoundaryPorts
import LeanTrominoes.PeriodicGridDrawingRectanglePortParameterPoints
import LeanTrominoes.PeriodicGridDrawingRectanglePieceJoins
import LeanTrominoes.PeriodicGridDrawingRectangleVerticalPortPositions
import LeanTrominoes.PeriodicGridDrawingLiftedCrossingPortPoints
import LeanTrominoes.PeriodicGridDrawingCutPieceParameterPoints
import LeanTrominoes.PeriodicGridDrawingEdgeRouteOrthogonal
import LeanTrominoes.PeriodicGridDrawingEdgePieceContactEndpoints
import LeanTrominoes.PeriodicGridDrawingNonverticalEdgeRouteSimple
import LeanTrominoes.PeriodicGridDrawingStraightRefinementVertexAvoidance
import LeanTrominoes.RationalAffineContactOrder
import LeanTrominoes.PeriodicGridDrawingRectangleClipIntervals
import LeanTrominoes.PeriodicGridDrawingRectangleParameterIntervals
import LeanTrominoes.PeriodicGridDrawingRectangleRouteSeparation
import LeanTrominoes.PeriodicGridDrawingRectangleTwoSidedContacts
import LeanTrominoes.PeriodicGridDrawingPaddedIncidenceIsolation
import LeanTrominoes.PeriodicGridDrawingPaddedCrossingSeparation
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
      ``LeanTrominoes.PeriodicGridDrawing.perturbedColumnHeight_translate,
      ``LeanTrominoes.PeriodicGridDrawing.periodic_perturbedColumnHeight_row_bounds,
      ``LeanTrominoes.PeriodicGridDrawing.periodicVirtualVerticalPort_inside,
      ``LeanTrominoes.PeriodicGridDrawing.periodic_columnPort_coordinate_order,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_preserves_before,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_integral_inside,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_parent_realInteriorContains,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_input_noninterlacing,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_virtual_before_iff,
      ``LeanTrominoes.PeriodicGridDrawing.mem_rectanglePortCandidates,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentPorts_cover,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentPorts_length_le_two,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleChordFamily_card_bound,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleChordFamily_noninterlacing,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleInputRoute_isRealOpenSimple,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleInputRoute_orthogonal,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleInputRoutes_disjoint,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleInputRoute_boundary_contact,
      ``LeanTrominoes.GridSegment.realContains_spans_unit_column,
      ``LeanTrominoes.GridSegment.realContains_affine_height,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_parent_cut_realInteriorContains,
      ``LeanTrominoes.PeriodicGridDrawing.translated_incidence_cell_zero,
      ``LeanTrominoes.PeriodicGridDrawing.column_crossing_retained_of_virtual_row,
      ``LeanTrominoes.PeriodicGridDrawing.endpoint_occurrence_cut_retained,
      ``LeanTrominoes.PeriodicGridDrawing.vertical_cut_retained,
      ``LeanTrominoes.PeriodicGridDrawing.straight_lifted_endpoints_avoid_row_seam,
      ``LeanTrominoes.PeriodicGridDrawing.horizontal_cut_table_coverage,
      ``LeanTrominoes.PeriodicGridDrawing.horizontal_cut_retained,
      ``LeanTrominoes.PeriodicGridDrawing.virtual_column_cut_height_avoids_row_seams,
      ``LeanTrominoes.RationalAffineBoundary.two_distinct_contacts,
      ``LeanTrominoes.RationalAffineBoundary.contact_exists_of_real_interior,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_rational_contact,
      ``LeanTrominoes.PeriodicGridDrawing.rational_rectangle_contact_retained,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_parent_two_contacts,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentPorts_length_eq_two_of_port,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChord_exists_of_port,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_parent_mem_nineEdgeCopies,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleChordFamily_covers_port,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_exists_of_interior_contact,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleChordFamily_covers_interior_contact,
      ``LeanTrominoes.GridPolyline.joinWord_valid,
      ``LeanTrominoes.GridPolyline.joinWord_translate,
      ``LeanTrominoes.GridPolyline.assembleIntervals_valid,
      ``LeanTrominoes.RationalIntervalPartition.ordered_cover_chain,
      ``LeanTrominoes.RationalIntervalPartition.sortIntervals_cover_chain,
      ``LeanTrominoes.RationalAffineBoundary.contacts_are_two_endpoints,
      ``LeanTrominoes.RationalAffineBoundary.closed_clip_x_interval,
      ``LeanTrominoes.RealRectangleBoundary.Port.eq_of_point_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChord_x_distinct,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChord_clip_interval,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChord_clip_realInteriorContains,
      ``LeanTrominoes.GridSegment.rationalXParameter_in_unit_interval,
      ``LeanTrominoes.GridSegment.rationalXParameter_injective,
      ``LeanTrominoes.GridSegment.rationalXParameter_translate,
      ``LeanTrominoes.GridPolyline.IsRealOpenSimple.reverse,
      ``LeanTrominoes.GridPolyline.joinWord_endpoints,
      ``LeanTrominoes.GridSegment.rationalXParameter_between_iff,
      ``LeanTrominoes.GridSegment.rationalXParameter_between_open_iff,
      ``LeanTrominoes.GridSegment.rationalPointAtParameter_translate,
      ``LeanTrominoes.GridSegment.rationalPointAtParameter_realContains,
      ``LeanTrominoes.GridSegment.rationalPointAtParameter_height,
      ``LeanTrominoes.RationalAffineBoundary.open_clip_strict_inside,
      ``LeanTrominoes.PeriodicGridDrawing.orientedRectangleInputRoute_valid,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChordInterval_contains_iff,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChordInterval_open_bounds,
      ``LeanTrominoes.PeriodicGridDrawing.crossingEdgePiece_mem,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece_mem,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgePieces_interval_bounds,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgePieces_cover,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgePieces_interiors_disjoint,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgePieces_sorted_partition,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgeRoute_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgeRoute_valid_of_joins,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_boundary_ports,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_endpoint_original_points,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_parameter_point,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_prototype_parameter_point,
      ``LeanTrominoes.RationalIntegerStripCover.closed_slab_column_unique,
      ``LeanTrominoes.RationalIntegerStripCover.closed_row_contact_cases,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_ports_join_across_row,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePieces_join,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_vertical_of_left_contact,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_vertical_of_right_contact,
      ``LeanTrominoes.PeriodicGridDrawing.paddedCrossingRoute_lifted_boundary_port,
      ``LeanTrominoes.PeriodicGridDrawing.crossingEdgePiece_endpoint_original_x,
      ``LeanTrominoes.PeriodicGridDrawing.sourceEdgePiece_finish_original_x,
      ``LeanTrominoes.PeriodicGridDrawing.targetEdgePiece_start_original_x,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_at_cut_boundary,
      ``LeanTrominoes.PeriodicGridDrawing.incidence_parent_prototype_line,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_crossing_of_proper_cut,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_incidence_of_endpoint_cut,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_endpoint_data,
      ``LeanTrominoes.PeriodicGridDrawing.crossing_rectangle_piece_endpoint_join,
      ``LeanTrominoes.PeriodicGridDrawing.fan_rectangle_piece_endpoint_join,
      ``LeanTrominoes.PeriodicGridDrawing.cutPieces_cannot_join,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgePieces_join,
      ``LeanTrominoes.GridPolyline.joinWord_orthogonal_image,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgeRoute_valid_of_separated,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgeRoute_orthogonal_image,
      ``LeanTrominoes.GridPolyline.realIsEndpoint_reverse,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_raw_image_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.crossingEdgePiece_avoids_endpoint_fans,
      ``LeanTrominoes.PeriodicGridDrawing.source_target_pieces_disjoint,
      ``LeanTrominoes.PeriodicGridDrawing.cutPieces_contact_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePieces_distinct_contact_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_crossing_contact_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_fan_contact_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgePieces_distinct_contact_endpoints,
      ``LeanTrominoes.OrthogonalBoundaryRouting.Port.point_bounds_faces,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleIntegralPort_point_bounds_faces,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_at_new_cut_boundary,
      ``LeanTrominoes.PeriodicGridDrawing.rectanglePort_new_cut_recovers_parameter,
      ``LeanTrominoes.PeriodicGridDrawing.crossingEdgePiece_endpoint_data,
      ``LeanTrominoes.PeriodicGridDrawing.crossing_rectangle_endpoint_parameters_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_before_crossing_contact,
      ``LeanTrominoes.GridPolyline.ordered_endpoint_contact,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_fan_outer_contact,
      ``LeanTrominoes.PeriodicGridDrawing.endpointPort_nonvertical_anchor_x,
      ``LeanTrominoes.PeriodicGridDrawing.fanEdgePiece_outer_endpoint_data,
      ``LeanTrominoes.PeriodicGridDrawing.fan_rectangle_endpoint_parameters_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_fan_contact_parameter,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_distinct_integral_ports_old_y_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_rectangle_endpoint_parameters_eq,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgePieces_ordered_contact,
      ``LeanTrominoes.GridPolyline.separatedWord_of_parameter_order,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgePieces_separated_word,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgeRoute_valid,
      ``LeanTrominoes.PeriodicGridDrawing.verticalEdgeRoute_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.verticalEdgeRoute_isRealOpenSimple,
      ``LeanTrominoes.PeriodicGridDrawing.verticalEdgeRoute_orthogonal,
      ``LeanTrominoes.GridPolyline.RealIsEndpoint.map,
      ``LeanTrominoes.GridPolyline.RealIsEndpoint.translate,
      ``LeanTrominoes.GridPolyline.RealIsEndpoint.scale,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_contains_scaled_grid_point,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedCrossingBar_contains_scaled_grid_point,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementRoute_valid,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementRoute_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_gridSize_cubic,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_compatible,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_routes_simple,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_orthogonal,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_avoids_scaled_grid_point,
      ``LeanTrominoes.PeriodicGridDrawing.crossingEdgePiece_avoids_scaled_vertex,
      ``LeanTrominoes.PeriodicGridDrawing.nonverticalEdgeRoute_vertex_avoidance,
      ``LeanTrominoes.PeriodicGridDrawing.verticalEdgeRoute_vertex_avoidance,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementRoute_vertex_avoidance,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_vertices_avoid_routes,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_isRealDrawing,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChord_parameter_bounds,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChordInterval_bounds,
      ``LeanTrominoes.OrthogonalBoundaryRouting.strip_slab_contact_vertical_boundary,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedCrossingBars_contact_same_column,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_vertical_boundary_contact_endpoint,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleRouteOffset_eq_translate,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleInputRoute_isRealOpenSimple,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleInputRoutes_distinct_cells_contact_endpoint,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleInputRoutes_same_cell_disjoint,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_horizontal_ports_join,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_horizontal_parent_keys_join,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_incidence_port_is_fan_endpoint,
      ``LeanTrominoes.PeriodicGridDrawing.paddedIncidenceRoute_isRealOpenSimple,
      ``LeanTrominoes.PeriodicGridDrawing.liftedPaddedIncidenceRoute_eq_translate,
      ``LeanTrominoes.PeriodicGridDrawing.liftedPaddedIncidenceRoute_in_cell,
      ``LeanTrominoes.PeriodicGridDrawing.liftedPaddedIncidenceRoutes_contact,
      ``LeanTrominoes.PeriodicGridDrawing.paddedCrossingBar_avoids_incidence_route,
      ``LeanTrominoes.PeriodicGridDrawing.paddedCrossingRoute_head_joins_rectangle,
      ``LeanTrominoes.PeriodicGridDrawing.paddedCrossingRoute_last_joins_rectangle,
      ``LeanTrominoes.PeriodicGridDrawing.paddedCrossingRoute_add_cell,
      ``LeanTrominoes.PeriodicGridDrawing.paddedCrossingRoutes_contact_identifies_occurrence,
      ``LeanTrominoes.PeriodicGridDrawing.crossing_bar_rectangle_contact_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.vertex_fan_rectangle_contact_endpoints,
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
