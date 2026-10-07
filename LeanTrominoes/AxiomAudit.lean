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
