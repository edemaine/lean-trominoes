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
import LeanTrominoes.GridSegmentVerticalCore
import LeanTrominoes.OrthogonalBoundaryPortPointInjection
import LeanTrominoes.OrthogonalEnlargedCrossingColumnContacts
import LeanTrominoes.OrthogonalVertexEnlargedHorizontalBoundaryContacts
import LeanTrominoes.OrthogonalVertexHorizontalBoundaryLast
import LeanTrominoes.OrthogonalVertexVerticalAnchors
import LeanTrominoes.OrthogonalVertexVerticalSegmentCounterexample
import LeanTrominoes.OrthogonalVerticalCoreFanContacts
import LeanTrominoes.PeriodicGridDrawingEndpointFanSeparation
import LeanTrominoes.PeriodicGridDrawingPaddedPeriodicVertexOrder
import LeanTrominoes.PeriodicGridDrawingRectanglePieceOccurrenceSeparation
import LeanTrominoes.PeriodicGridDrawingRectanglePortContactColumns
import LeanTrominoes.PeriodicGridDrawingRectanglePortContactParents
import LeanTrominoes.PeriodicGridDrawingRectangleRouteContactParents
import LeanTrominoes.PeriodicGridDrawingVerticalCoreRouteGeometry
import LeanTrominoes.PeriodicGridDrawingVerticalCrossingOldSeparation
import LeanTrominoes.PeriodicGridDrawingVerticalCrossingSeparation
import LeanTrominoes.PeriodicGridDrawingVerticalFanRoute
import LeanTrominoes.PeriodicGridDrawingVerticalFanRouteSimple
import LeanTrominoes.PeriodicGridDrawingVerticalFanVertexAvoidance
import LeanTrominoes.PeriodicGridDrawingVerticalPortAnchors
import LeanTrominoes.PeriodicGridDrawingVerticalRectangleSeparation
import LeanTrominoes.PeriodicHeightVertexOrder
import LeanTrominoes.GridSegmentScaledIntegerNeighborhood
import LeanTrominoes.GridSegmentVerticalCoreInterior
import LeanTrominoes.PeriodicGridDrawingEndpointFanOccurrences
import LeanTrominoes.PeriodicGridDrawingEndpointOccurrenceInjection
import LeanTrominoes.PeriodicGridDrawingRectangleBarOccurrenceSeparation
import LeanTrominoes.PeriodicGridDrawingRectangleFanOccurrenceSeparation
import LeanTrominoes.PeriodicGridDrawingRectanglePortPhysicalPieces
import LeanTrominoes.PeriodicGridDrawingRectangleStripContactKeys
import LeanTrominoes.PeriodicGridDrawingRefinementPhysicalImages
import LeanTrominoes.PeriodicGridDrawingRefinementPhysicalSeparation
import LeanTrominoes.PeriodicGridDrawingRefinementPieceTranslations
import LeanTrominoes.PeriodicGridDrawingStraightRefinementPlanarity
import LeanTrominoes.PeriodicGridDrawingVerticalCoreExternalSeparation
import LeanTrominoes.PeriodicGridDrawingVerticalCoreFanOccurrenceSeparation
import LeanTrominoes.PeriodicGridDrawingVerticalCoreOccurrenceSeparation
import LeanTrominoes.PeriodicGridDrawingVerticalFanContactVertices
import LeanTrominoes.GridSegmentLocalCellContact
import LeanTrominoes.PeriodicGridDrawingCrossingBarLocality
import LeanTrominoes.PeriodicGridDrawingRectanglePieceLocalCells
import LeanTrominoes.PeriodicGridDrawingRectanglePieceLocality
import LeanTrominoes.PeriodicGridDrawingRefinedLocalBoxes
import LeanTrominoes.PeriodicGridDrawingScaledStraightLocality
import LeanTrominoes.PeriodicGridDrawingStraightLocalCoordinateBoxes
import LeanTrominoes.PeriodicGridDrawingStraightRefinementLocality
import LeanTrominoes.PeriodicGridDrawingStraightRefinementTheorem
import Lean.Util.CollectAxioms
import LeanTrominoes.PeriodicGridDrawingIndexing
import LeanTrominoes.PeriodicPlanarThreeDMContractedLocality
import LeanTrominoes.PeriodicPlanarThreeDMIncidenceOffsets
import LeanTrominoes.PeriodicPlanarThreeDMTerminalOffsets
import LeanTrominoes.PeriodicThreeDMContractionLocality
import LeanTrominoes.TrichromaticGraphOrientationLineDecision
import LeanTrominoes.TrichromaticGraphOrientationLocalCoRE
import LeanTrominoes.TrichromaticGraphOrientationLocalCompleteness
import LeanTrominoes.TrichromaticGraphOrientationPlanarHardness
import LeanTrominoes.TrichromaticGraphOrientationFlatEncoding
import LeanTrominoes.TrichromaticGraphOrientationLineWindow
import LeanTrominoes.TrichromaticGraphOrientationPackedWindow
import LeanTrominoes.TrichromaticGraphOrientationCoreGuard
import LeanTrominoes.TrichromaticGraphOrientationFieldBudgetPolynomial
import LeanTrominoes.TrichromaticGraphOrientationFieldCycleAdapters
import LeanTrominoes.TrichromaticGraphOrientationFieldCyclePair
import LeanTrominoes.TrichromaticGraphOrientationFieldCycleSearch
import LeanTrominoes.TrichromaticGraphOrientationFieldEvaluator
import LeanTrominoes.TrichromaticGraphOrientationFieldIncidences
import LeanTrominoes.TrichromaticGraphOrientationFieldQueries
import LeanTrominoes.TrichromaticGraphOrientationFieldReach
import LeanTrominoes.TrichromaticGraphOrientationFieldSavitchInput
import LeanTrominoes.TrichromaticGraphOrientationFieldSavitchLeaf
import LeanTrominoes.TrichromaticGraphOrientationFieldSavitchRun
import LeanTrominoes.TrichromaticGraphOrientationFieldSearch
import LeanTrominoes.TrichromaticGraphOrientationFieldTransition
import LeanTrominoes.TrichromaticGraphOrientationIncidenceCounts
import LeanTrominoes.TrichromaticGraphOrientationIncidenceIndices
import LeanTrominoes.TrichromaticGraphOrientationLineMembership
import LeanTrominoes.TrichromaticGraphOrientationSelectedIndices
import LeanTrominoes.TrichromaticGraphOrientationVertexGuard
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceTargetFilter
import LeanTrominoes.ProgramGraphOrientationElements
import LeanTrominoes.ProgramGraphOrientationEndpointFields
import LeanTrominoes.ProgramGraphOrientationFiniteEncoding
import LeanTrominoes.ProgramGraphOrientationSourceFields
import LeanTrominoes.ProgramGraphOrientationVertexFields
import LeanTrominoes.TrichromaticGraphOrientationFieldsCompiler
import LeanTrominoes.TrichromaticGraphOrientationFinite
import LeanTrominoes.TrichromaticGraphOrientationFiniteHardness
import LeanTrominoes.TrichromaticGraphOrientationLineHardness
import LeanTrominoes.TrichromaticGraphOrientationLineReduction
import LeanTrominoes.TrichromaticGraphOrientationNativeEncoding
import LeanTrominoes.TrichromaticGraphOrientationNativeEndpointFields
import LeanTrominoes.TrichromaticGraphOrientationNativeOffsetFields
import LeanTrominoes.TrichromaticGraphOrientationNativeSourceFields
import LeanTrominoes.TrichromaticGraphOrientationNativeVertexFields
import LeanTrominoes.UnaryColumnBoundedSignedDifference
import LeanTrominoes.UnaryColumnChoiceCompiler
import LeanTrominoes.UnaryColumnDenseLookupCompiler
import LeanTrominoes.UnaryColumnFilterCompiler
import LeanTrominoes.UnaryColumnFiveCompiler
import LeanTrominoes.UnaryColumnOrdinalCompiler

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
      ``LeanTrominoes.GridSegment.cell_index_bounds_of_overlap,
      ``LeanTrominoes.GridSegment.cell_eq_endpoint_of_local_coordinate_bounds,
      ``LeanTrominoes.GridSegment.local_coordinate_shifted_open_box,
      ``LeanTrominoes.GridSegment.scaled_local_coordinate_endpoint_box,
      ``LeanTrominoes.PeriodicGridDrawing.paddedCrossingRoute_isRealLocal,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChord_local_cell,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleInputRoute_in_refined_cell,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_isRealLocal,
      ``LeanTrominoes.PeriodicGridDrawing.refined_real_local_of_coordinate_box,
      ``LeanTrominoes.PeriodicGridDrawing.scaled_straight_segment_isRealLocal,
      ``LeanTrominoes.PeriodicGridDrawing.straightSegment_rational_local_coordinate_bounds,
      ``LeanTrominoes.PeriodicGridDrawing.liftedPaddedIncidenceRoute_in_refined_cell,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_isRealLocal,
      ``LeanTrominoes.PeriodicGridDrawing.straight_refinement,
      ``LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence.targetControls_cons_two,
      ``LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence.targetControls_cons_three,
      ``LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence.targetControls_eq_blocks,
      ``LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence.selected_targets_eq_contracted,
      ``LeanTrominoes.PeriodicCNFStripReduction.programThreeDMOneColorCodes,
      ``LeanTrominoes.PeriodicCNFStripReduction.programThreeDMElement_mem,
      ``LeanTrominoes.PeriodicCNFStripReduction.programThreeDMWellFormed,
      ``LeanTrominoes.PeriodicCNFStripReduction.programThreeDMIncidenceElement_mem,
      ``LeanTrominoes.PeriodicCNFStripReduction.programThreeDMDegree,
      ``LeanTrominoes.PeriodicCNFStripReduction.programTriplePositions_length,
      ``LeanTrominoes.PeriodicCNFStripReduction.programThreeDM_zeroOffsets,
      ``LeanTrominoes.PeriodicCNFStripReduction.programOrientationGraph_zeroOffsets,
      ``LeanTrominoes.PeriodicCNFStripReduction.programOrientationGraph_finite_correct,
      ``LeanTrominoes.PeriodicCNFStripReduction.programElementKeys_nodup,
      ``LeanTrominoes.PeriodicCNFStripReduction.programElement_eq_of_key_eq,
      ``LeanTrominoes.PeriodicCNFStripReduction.programVertices_eq,
      ``LeanTrominoes.PeriodicCNFStripReduction.programVertexKey_injective_on,
      ``LeanTrominoes.TrichromaticGraphOrientation.ends_offset_eq_zero,
      ``LeanTrominoes.TrichromaticGraphOrientation.incoming_offset_eq_zero,
      ``LeanTrominoes.TrichromaticGraphOrientation.freeze_orientation,
      ``LeanTrominoes.TrichromaticGraphOrientation.finiteHasOrientation_iff,
      ``LeanTrominoes.TrichromaticGraphOrientation.finiteProblem_iff,
      ``LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding.input_zeroOffsets,
      ``LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding.finiteProblem_iff,
      ``LeanTrominoes.TrichromaticGraphOrientation.finiteReduction_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.finiteManyOne,
      ``LeanTrominoes.TrichromaticGraphOrientation.finiteProblem_npHard,
      ``LeanTrominoes.TrichromaticGraphOrientation.localLineReduction_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.localLineManyOne,
      ``LeanTrominoes.TrichromaticGraphOrientation.localLineProblem_PSPACEHard,
      ``LeanTrominoes.TrichromaticGraphOrientation.localLineProblem_PSPACEComplete,
      ``LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding.input_isOneDimensional,
      ``LeanTrominoes.PeriodicCNFStripReduction.problem_incidenceOffsetsComparable,
      ``LeanTrominoes.PeriodicCNFStripReduction.nativeThreeDM_incidenceOffsetsComparable,
      ``LeanTrominoes.PeriodicCNFStripReduction.nativeOrientationGraph_isLocal,
      ``LeanTrominoes.PeriodicCNFStripReduction.nativeOrientationGraph_isOneDimensional,
      ``LeanTrominoes.PeriodicCNFStripReduction.nativeOrientationGraph_correct,
      ``LeanTrominoes.PeriodicCNFStripReduction.incidenceElement_of_mem,
      ``LeanTrominoes.PeriodicCNFStripReduction.contractedEdge_endpoints_mem,
      ``LeanTrominoes.PeriodicCNFStripReduction.incidence_offset_reference_of_mem,
      ``LeanTrominoes.PeriodicCNFStripReduction.nativeElementKeys_nodup,
      ``LeanTrominoes.PeriodicCNFStripReduction.nativeElement_eq_of_key_eq,
      ``LeanTrominoes.PeriodicCNFStripReduction.nativeVertices_eq,
      ``LeanTrominoes.PeriodicCNFStripReduction.nativeVertexKey_injective_on,
      ``LeanTrominoes.UnaryColumn.encode_small_int,
      ``LeanTrominoes.TrichromaticGraphOrientation.CoreGuard.recordCheck_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.CoreGuard.core_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.CoreGuard.core_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.cycleBudgetPolynomial_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.cycleBudget_mono,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pairReachInput_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pairTransitionInput_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pairReachInput_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pairTransitionInput_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pair_space_le,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pairGuard_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pairGuard_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pairTransition_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pairReach_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pair_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.pair_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.prependField_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.outer_space_le,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.cycle_space_le,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.counter_length_le,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.outer_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.cycle_eval_guarded,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.cyclePredicate_eq,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.cycle_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.outer_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.cycle_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.fields_space,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.suffixCode_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.suffixCode_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.edges_bound,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.suffix_space,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.bits_bound,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.decide_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.decide_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.header_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.owner_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.indexValue_eq,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.inward_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.selected_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldQueries.vertexCount_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldQueries.edgeCount_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldQueries.entry_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldQueries.entry_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.answer_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.reach_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.request_space_le,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.reach_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.restoreInput_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.restoreInput_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.decision_code_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.decision_code_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.baseExpr_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.baseExpr_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.base_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.base_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.countdown_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.result_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.bits_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.bits_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.count_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.searchInput_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.search_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.searchInput_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldSavitch.search_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.kind_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.inward_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.coherent_typed,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.exactOne_typed,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.valid_typed,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.overlap_typed,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.transition_typed,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.check_true,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.transition_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.decision_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.decision_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.FieldPredicate.cycle_iff,
      ``LeanTrominoes.TrichromaticGraphOrientation.mem_incidentIndices,
      ``LeanTrominoes.TrichromaticGraphOrientation.mem_colorIndices,
      ``LeanTrominoes.TrichromaticGraphOrientation.degree_eq_card,
      ``LeanTrominoes.TrichromaticGraphOrientation.colorCount_eq_card,
      ``LeanTrominoes.TrichromaticGraphOrientation.degree_three_iff,
      ``LeanTrominoes.TrichromaticGraphOrientation.color_one_iff,
      ``LeanTrominoes.TrichromaticGraphOrientation.monochromatic_iff,
      ``LeanTrominoes.TrichromaticGraphOrientation.ends_eq_incidenceIndices,
      ``LeanTrominoes.TrichromaticGraphOrientation.incidenceAt_atom,
      ``LeanTrominoes.TrichromaticGraphOrientation.incidenceAt_polarity,
      ``LeanTrominoes.TrichromaticGraphOrientation.incidenceAt_injective,
      ``LeanTrominoes.TrichromaticGraphOrientation.NativeLine.metadata_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.NativeLine.decision_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.NativeLine.decision_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.NativeLine.metadataCode_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.NativeLine.metadata_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.NativeLine.result_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.NativeLine.code_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.NativeLine.code_fits,
      ``LeanTrominoes.TrichromaticGraphOrientation.localLineProblem_inPSPACE,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.mem_selectedIndices,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.selected_card,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.exactlyOne_iff_unique,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.coherent_iff_indices,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.ownerMatch_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.colorAt_eval,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.colored_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.witnesses_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.degree_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.colorOne_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.colorAll_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.trichromatic_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.monochromatic_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.guard_truth,
      ``LeanTrominoes.TrichromaticGraphOrientation.VertexGuard.guard_noPower,
      ``LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding.fields_length,
      ``LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding.decodeEdge_append,
      ``LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding.decodeEdges_append,
      ``LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding.decodeFields_fields,
      ``LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding.edgeFields_length,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.incoming_atom_lt,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.incoming_horizontal,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.position_eq,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.vertex_constraint_congr,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.hasOrientation_iff,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.hasOrientation_iff_cycle,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.card_window,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.decodeWord_encodeWindow,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.encodeWindow_lt,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.hasOrientation_iff_packed_cycle,
      ``LeanTrominoes.TrichromaticGraphOrientation.LineWindow.stateBits_le_input_length,
      ``LeanTrominoes.PeriodicGraph.indexed_wellFormed,
      ``LeanTrominoes.PeriodicGraph.indexed_isLocal,
      ``LeanTrominoes.PeriodicGridDrawing.vertexPosition_indexed,
      ``LeanTrominoes.PeriodicGridDrawing.isCompatible_indexed,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.encodedProblem_incidenceOffsetsComparable,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.encodedProblem_contractedGraph_isLocal,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_incidenceOffsetsComparable,
      ``LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem_incidenceOffsetsComparable,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.encodedReference_offset_zero_of_local,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.encodedReferences_offsets_comparable,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.encoded_incidence_reference,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.encoded_incidence_offsets_comparable,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.terminalGroup_injective_below_three,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.occurrenceReverseOffset_eq_of_terminal_eq,
      ``LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.occurrenceReverseOffset_eq_of_elementIndex_eq,
      ``LeanTrominoes.PeriodicThreeDM.contractedGraph_isLocal,
      ``LeanTrominoes.TrichromaticGraphOrientation.incoming_offset,
      ``LeanTrominoes.TrichromaticGraphOrientation.vertexClauses_offsets,
      ``LeanTrominoes.TrichromaticGraphOrientation.formula_edgeLocal,
      ``LeanTrominoes.TrichromaticGraphOrientation.formula_horizontal,
      ``LeanTrominoes.TrichromaticGraphOrientation.localFormula_satisfiable,
      ``LeanTrominoes.TrichromaticGraphOrientation.lineCheck_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.isLocal_primrec,
      ``LeanTrominoes.TrichromaticGraphOrientation.localProblem_coRE,
      ``LeanTrominoes.PeriodicWangPlanarThreeDMReduction.problem_incidenceOffsetsComparable,
      ``LeanTrominoes.PeriodicWangPlanarThreeDMReduction.problem_contractedGraph_isLocal,
      ``LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding.input_isLocal,
      ``LeanTrominoes.TrichromaticGraphOrientation.wangReduction_isLocal,
      ``LeanTrominoes.TrichromaticGraphOrientation.wangReduction_local_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.localProblem_coREHard,
      ``LeanTrominoes.TrichromaticGraphOrientation.localProblem_coREComplete,
      ``LeanTrominoes.TrichromaticGraphOrientation.wangReduction_localPlanar_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.localPlanarProblem_coREHard,
      ``LeanTrominoes.TrichromaticGraphOrientation.underlyingGraph_contracted,
      ``LeanTrominoes.TrichromaticGraphOrientation.wangReduction_hasPlanarPresentation,
      ``LeanTrominoes.TrichromaticGraphOrientation.wangReduction_planar_correct,
      ``LeanTrominoes.TrichromaticGraphOrientation.planarProblem_coREHard,
      ``LeanTrominoes.GridSegment.scaled_integer_near_eq,
      ``LeanTrominoes.GridSegment.between_of_scaled_neighborhood,
      ``LeanTrominoes.GridSegment.scaled_vertical_neighborhood_contact_implies_incident,
      ``LeanTrominoes.GridSegment.verticalCore_inverse_image_interior,
      ``LeanTrominoes.PeriodicGridDrawing.endpointFan_occurrence_injective,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece_endpoint_fan_contact_occurrence_eq,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCore_endpoint_fan_contact_occurrence_eq,
      ``LeanTrominoes.PeriodicGridDrawing.endpointPort_occurrence_injective,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleParentRoute_bar_contact_parent_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece_bar_contact_occurrence_eq,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleParentRoute_fan_contact_parent_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece_fan_contact_occurrence_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_crossing_port_on_bar,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_incidence_port_on_fan,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_crossing_port_lifted_crosses,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleParentRoute_strip_contact_key,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementRoute_physical_image,
      ``LeanTrominoes.PeriodicGridDrawing.refinementPhysicalContains_fan_or_nonfan,
      ``LeanTrominoes.PeriodicGridDrawing.liftedStraightSegment_isVertical_of_zero,
      ``LeanTrominoes.PeriodicGridDrawing.refinement_nonfan_fan_disjoint,
      ``LeanTrominoes.PeriodicGridDrawing.refinement_nonfan_nonfan_disjoint,
      ``LeanTrominoes.PeriodicGridDrawing.refinementPhysicalContains_contact_scaled_vertex,
      ``LeanTrominoes.GridSegment.verticalCore_translate,
      ``LeanTrominoes.PeriodicGridDrawing.liftedPaddedIncidenceRoute_add_cell,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCoreRoute_lifted_image,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_routes_meet_only_at_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.straightRefinementDrawing_isRealPlanarDrawing,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCore_lifted_fan_contact_identifies_endpoint,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCore_lifted_avoids_rectangle_piece,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCoreRoute_fan_contact_identifies_endpoint,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCore_occurrences_disjoint,
      ``LeanTrominoes.PeriodicGridDrawing.scaled_vertical_segment_fan_contact_vertex,
      ``LeanTrominoes.GridSegment.verticalCore_avoids_scaled_endpoint,
      ``LeanTrominoes.OrthogonalDrawingRefinement.verticalCore_fan_contact_core_endpoint,
      ``LeanTrominoes.GridSegment.verticalCore_isVertical,
      ``LeanTrominoes.GridSegment.verticalCore_order,
      ``LeanTrominoes.GridSegment.verticalCore_endpoints_contained,
      ``LeanTrominoes.GridSegment.verticalCore_realContains_parent,
      ``LeanTrominoes.OrthogonalBoundaryRouting.Port.eq_of_point_eq,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedCrossingBar_contact_scaled_column,
      ``LeanTrominoes.OrthogonalDrawingRefinement.rectangleTemplate_horizontal_boundary_contact,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_horizontal_boundary_contact_endpoint,
      ``LeanTrominoes.OrthogonalDrawingRefinement.enlargedRectangleTemplate_horizontal_boundary_contact_last,
      ``LeanTrominoes.OrthogonalDrawingRefinement.AnchorProfile.down_anchor,
      ``LeanTrominoes.OrthogonalDrawingRefinement.AnchorProfile.up_anchor,
      ``LeanTrominoes.OrthogonalDrawingRefinement.east_fan_meets_vertical_segment_interior,
      ``LeanTrominoes.OrthogonalDrawingRefinement.verticalCore_fan_boundary,
      ``LeanTrominoes.OrthogonalDrawingRefinement.verticalCore_fan_contact_last,
      ``LeanTrominoes.PeriodicGridDrawing.endpoint_fans_disjoint,
      ``LeanTrominoes.PeriodicGridDrawing.paddedPeriodicColumnHeight_below_lifted_vertex,
      ``LeanTrominoes.PeriodicGridDrawing.paddedPeriodicColumnHeight_above_lifted_vertex,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleInputRoute_add_cell,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece?_translated_raw_image,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleEdgePiece_occurrences_contact_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_integral_ports_contact_columns,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_integral_ports_same_cell_parent_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangle_integral_ports_contact_parent_eq,
      ``LeanTrominoes.PeriodicGridDrawing.rectangleParentChord_integral_parent_injective,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleParentRoute_endpoint_key,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleParentRoutes_contact_parent_eq,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCoreRoute_eq_segment,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCoreRoute_valid,
      ``LeanTrominoes.PeriodicGridDrawing.verticalFanRouteWord_connected,
      ``LeanTrominoes.PeriodicGridDrawing.straight_vertical_avoids_crossing_point,
      ``LeanTrominoes.PeriodicGridDrawing.scaled_vertical_segment_avoids_crossing_bar,
      ``LeanTrominoes.PeriodicGridDrawing.verticalFanRouteWord_long,
      ``LeanTrominoes.PeriodicGridDrawing.verticalFanEdgeRoute_endpoints,
      ``LeanTrominoes.PeriodicGridDrawing.verticalCoreRoute_coordinates,
      ``LeanTrominoes.PeriodicGridDrawing.verticalFanRouteWord_separated,
      ``LeanTrominoes.PeriodicGridDrawing.verticalFanEdgeRoute_valid,
      ``LeanTrominoes.PeriodicGridDrawing.verticalFanEdgeRoute_vertex_avoidance,
      ``LeanTrominoes.PeriodicGridDrawing.portBoundaryAnchor_of_up,
      ``LeanTrominoes.PeriodicGridDrawing.portBoundaryAnchor_of_down,
      ``LeanTrominoes.PeriodicGridDrawing.vertical_endpoint_anchors,
      ``LeanTrominoes.PeriodicGridDrawing.verticalEdgeRoute_contains_x,
      ``LeanTrominoes.PeriodicGridDrawing.liftedRectangleInputRoute_avoids_scaled_column,
      ``LeanTrominoes.PeriodicGridDrawing.verticalEdgeRoute_avoids_rectangle,
      ``LeanTrominoes.OrthogonalDrawingRefinement.periodicRedistributedHeight_below_vertex,
      ``LeanTrominoes.OrthogonalDrawingRefinement.periodicRedistributedHeight_above_vertex,
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
