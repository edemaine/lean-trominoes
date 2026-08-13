/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariablePositionInjectivity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicization

/-!
# Canonical positions of retained periodic planar-SAT variables

Periodicization removes the displayed lattice translate from terminal and
atom names and normalizes crossover sites to their canonical orbit
representatives.  This file gives every resulting protovariable its
translation-zero finite representative.  The representative has exactly the
canonical periodic position, so finite retained-position injectivity can be
reused at the periodic level.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The finite translation-zero representative of a periodic routed-SAT
protovariable. -/
def periodicPlanarSATVariableZeroLift
    {Variable : Type*} :
    PeriodicPlanarSATVariable Variable → PlanarSATVariable Variable
  | .terminal indexed endpoint =>
      .inl (.carrier (.terminal ⟨indexed, (0, 0), endpoint⟩))
  | .boundary boundary =>
      .inl (.carrier (.boundary boundary))
  | .atom atom =>
      .inl (.atom (atom, (0, 0)))
  | .crossoverInternal internal =>
      .inr internal

/-- Geometric membership conditions sufficient for a periodic
protovariable's translation-zero representative to occur in the retained
finite geometry. -/
def RetainedDrawingPeriodicPlanarSATVariableValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicPlanarSATVariable Variable → Prop
  | .terminal indexed _ =>
      indexed ∈
        (drawing (PeriodicCNF.incidenceGraph formula)).indexedSegments
  | .boundary boundary =>
      boundary ∈
        drawingCrossingBoundaries
          (PeriodicCNF.incidenceGraph formula)
  | .atom atom =>
      (atom, (0, 0)) ∈ drawingVariableRouteSites formula
  | .crossoverInternal (crossing, _) =>
      crossing ∈
        orientedCrossings (PeriodicCNF.incidenceGraph formula)

/-- Negating the offset of a local edge gives one of the nine neighboring
translations enumerated by the finite routed block. -/
theorem edgeNegativeOffset_isNeighbor_of_span_le_one
    {Vertex : Type*}
    (edge : PeriodicEdge Vertex)
    (hLocal : edge.span ≤ 1) :
    IsNeighborTranslation
      (-edge.offset.1, -edge.offset.2) := by
  rcases offset_eq_of_span_le_one edge hLocal with
    offsetEq | offsetEq | offsetEq | offsetEq | offsetEq <;>
      simp [offsetEq, IsNeighborTranslation]

/-- If a lifted variable site occurs anywhere in the neighboring routed
block, the same atom also occurs at its canonical translation-zero site. -/
theorem drawingVariableRouteSite_zero_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {site : VariableRouteSite Variable}
    (siteMem : site ∈ drawingVariableRouteSites formula) :
    (site.1, (0, 0)) ∈ drawingVariableRouteSites formula := by
  rw [drawingVariableRouteSites, List.mem_dedup] at siteMem ⊢
  rcases List.mem_map.mp siteMem with
    ⟨occurrence, occurrenceMem, siteEq⟩
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, occurrenceMem⟩
  rcases List.mem_map.mp occurrenceMem with
    ⟨translate, _translateMem, occurrenceEq⟩
  subst occurrence
  have taggedEdgeMem :=
    PeriodicCNF.tagged_incidence_edge_mem
      formula taggedIncidenceMem
  have edgeLocal :
      taggedIncidence.1.edge.span ≤ 1 :=
    isLocal taggedIncidence.1.edge
      (List.fst_mem_of_mem_zipIdx taggedEdgeMem)
  let canonicalTranslate : Cell :=
    (-taggedIncidence.1.edge.offset.1,
      -taggedIncidence.1.edge.offset.2)
  let canonicalOccurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, canonicalTranslate⟩
  have canonicalOccurrenceMem :
      canonicalOccurrence ∈ drawingCNFRouteOccurrences formula := by
    apply List.mem_flatMap.mpr
    refine ⟨taggedIncidence, taggedIncidenceMem, ?_⟩
    apply List.mem_map.mpr
    refine ⟨canonicalTranslate, ?_, rfl⟩
    apply (mem_neighborTranslations_iff canonicalTranslate).mpr
    exact edgeNegativeOffset_isNeighbor_of_span_le_one
      taggedIncidence.1.edge edgeLocal
  apply List.mem_map.mpr
  refine ⟨canonicalOccurrence, canonicalOccurrenceMem, ?_⟩
  rw [← siteEq]
  simp [canonicalOccurrence, canonicalTranslate,
    CNFRouteOccurrence.variableOccurrence,
    CNFRouteOccurrence.edge, Cell.add]

/-- Normalizing a valid finite retained variable produces a periodically
valid protovariable. -/
theorem retainedDrawingPlanarSATVariableValid_normalize
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (valid : RetainedDrawingPlanarSATVariableValid formula atom) :
    RetainedDrawingPeriodicPlanarSATVariableValid formula
      (normalizePlanarSATVariable formula atom).1 := by
  let graph := PeriodicCNF.incidenceGraph formula
  rcases atom with (⟨carrier⟩ | ⟨site⟩) |
    ⟨crossing, internal⟩
  · cases carrier with
    | terminal terminal =>
        exact retainedCarrierNode_indexed_mem graph valid
    | boundary boundary =>
        have boundaryMem :
            boundary ∈ retainedCrossingBoundaries graph := by
          unfold RetainedDrawingPlanarSATVariableValid at valid
          unfold retainedDrawingCarrierNodes at valid
          simpa using valid
        exact retainedCrossingBoundary_periodNormalize_mem
          graph boundaryMem
  · exact drawingVariableRouteSite_zero_mem
      formula isLocal valid
  · exact periodNormalize_mem_orientedCrossings
      wellFormed degree isLocal valid

/-- Every protovariable occurrence in the periodicized retained formula
satisfies the canonical geometric validity conditions. -/
theorem retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {atom : PeriodicPlanarSATVariable Variable}
    (atomMem :
      atom ∈
        (retainedDrawingPeriodicPlanarSATFormula
          formula).variableOccurrences) :
    RetainedDrawingPeriodicPlanarSATVariableValid formula atom := by
  unfold PeriodicCNF.variableOccurrences at atomMem
  rcases List.mem_flatMap.mp atomMem with
    ⟨periodicClause, periodicClauseMem, atomMem⟩
  rcases List.mem_map.mp periodicClauseMem with
    ⟨finiteClause, finiteClauseMem, periodicClauseEq⟩
  subst periodicClause
  rcases List.mem_map.mp atomMem with
    ⟨periodicLiteral, periodicLiteralMem, atomEq⟩
  rcases List.mem_map.mp periodicLiteralMem with
    ⟨finiteLiteral, finiteLiteralMem, periodicLiteralEq⟩
  subst periodicLiteral
  have finiteAtomMem :
      finiteLiteral.1 ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).variableVertices := by
    rw [EmbeddedCNFIncidenceDrawing.variableVertices,
      retainedDrawingPlanarSATLocalIncidenceDrawing_formula,
      List.mem_dedup]
    apply List.mem_flatMap.mpr
    refine ⟨finiteClause, finiteClauseMem, ?_⟩
    exact List.mem_map.mpr
      ⟨finiteLiteral, finiteLiteralMem, rfl⟩
  have finiteValid :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_variableVertices_valid
      formula wellFormed degree isLocal finiteLiteral.1 finiteAtomMem
  rw [← atomEq]
  simpa [retainedDrawingPeriodicPlanarSATFormula,
    periodicizePlanarSATClause, periodicizePlanarSATLiteral] using
    retainedDrawingPlanarSATVariableValid_normalize
      formula wellFormed degree isLocal finiteLiteral.1 finiteValid

/-- Renaming a positioned formula maps its erased variable-occurrence list
in the same order. -/
@[simp]
theorem PositionedPeriodicCNF.variableOccurrences_erase_rename
    {Source Target : Type*}
    (source : PositionedPeriodicCNF Source)
    (variableMap : Source → Target) :
    (source.rename variableMap).erase.variableOccurrences =
      source.erase.variableOccurrences.map variableMap := by
  simp [PositionedPeriodicCNF.rename,
    PositionedPeriodicCNF.erase,
    PeriodicCNF.variableOccurrences,
    List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

/-- Every wrapped protovariable retained after anchor normalization and
clause-orbit deduplication is backed by a valid canonical routed-SAT
protovariable. -/
theorem
    retainedDeduplicatedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {atom : WrappedPeriodicPlanarSATVariable Variable}
    (atomMem :
      atom ∈
        (retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.variableOccurrences) :
    RetainedDrawingPeriodicPlanarSATVariableValid
      formula atom.original := by
  let normalizedSource :=
    retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  have normalizedMem :
      atom ∈ normalizedSource.erase.variableOccurrences := by
    have deduplicatedMem :
        atom ∈ normalizedSource.erase.deduplicate.variableOccurrences := by
      simpa [normalizedSource,
        retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula,
        PositionedPeriodicCNF.erase_deduplicateByLiterals] using atomMem
    exact
      (PeriodicCNF.deduplicate_variableOccurrences_sublist
        normalizedSource.erase).subset deduplicatedMem
  have wrappedMem :
      atom ∈
        (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.variableOccurrences := by
    simpa [normalizedSource,
      retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using normalizedMem
  have unwrappedMem :
      atom.original ∈
        (retainedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.variableOccurrences := by
    rw [retainedWrappedDrawingPositionedPeriodicPlanarSATFormula,
      PositionedPeriodicCNF.variableOccurrences_erase_rename] at wrappedMem
    rcases List.mem_map.mp wrappedMem with
      ⟨original, originalMem, atomEq⟩
    exact
      (congrArg WrappedPeriodicVariable.original atomEq).symm ▸
        originalMem
  rw [retainedDrawingPositionedPeriodicPlanarSATFormula_erase]
    at unwrappedMem
  exact
    retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_valid
      formula wellFormed degree isLocal unwrappedMem

/-- The zero lift has exactly the canonical periodic protovariable
position. -/
@[simp]
theorem drawingPlanarSATVariablePosition_zeroLift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    drawingPlanarSATVariablePosition formula
        (periodicPlanarSATVariableZeroLift atom) =
      drawingPeriodicPlanarSATVariablePosition formula atom := by
  cases atom <;>
    rfl

/-- Distinct periodic protovariable names have distinct zero lifts. -/
theorem periodicPlanarSATVariableZeroLift_injective
    {Variable : Type*} :
    Function.Injective
      (@periodicPlanarSATVariableZeroLift Variable) := by
  intro first second equal
  cases first <;> cases second <;>
    simp [periodicPlanarSATVariableZeroLift] at equal ⊢
  all_goals exact equal

/-- Every periodically valid protovariable has a valid retained finite zero
lift. -/
theorem retainedDrawingPeriodicPlanarSATVariableValid_zeroLift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid formula atom) :
    RetainedDrawingPlanarSATVariableValid formula
      (periodicPlanarSATVariableZeroLift atom) := by
  let graph := PeriodicCNF.incidenceGraph formula
  cases atom with
  | terminal indexed endpoint =>
      change
        CarrierNode.terminal ⟨indexed, (0, 0), endpoint⟩ ∈
          retainedDrawingCarrierNodes graph
      unfold retainedDrawingCarrierNodes
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨⟨indexed, (0, 0), endpoint⟩, ?_, rfl⟩
      apply
        mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
      · exact valid
      · exact ⟨by simp, by simp⟩
  | boundary boundary =>
      change
        CarrierNode.boundary boundary ∈
          retainedDrawingCarrierNodes graph
      unfold retainedDrawingCarrierNodes
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact
        ⟨boundary,
          drawingCrossingBoundaries_subset_retainedCrossingBoundaries
            graph valid,
          rfl⟩
  | atom atom =>
      exact valid
  | crossoverInternal internal =>
      exact orientedCrossings_subset_orientedCrossingHalo
        graph valid

/-- Canonical positions are injective on the retained periodic
protovariables. -/
theorem drawingPeriodicPlanarSATVariablePosition_injective_of_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {first second : PeriodicPlanarSATVariable Variable}
    (firstValid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula first)
    (secondValid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula second)
    (positionEq :
      drawingPeriodicPlanarSATVariablePosition formula first =
        drawingPeriodicPlanarSATVariablePosition formula second) :
    first = second := by
  apply periodicPlanarSATVariableZeroLift_injective
  apply drawingPlanarSATVariable_eq_of_valid_of_position_eq
    formula wellFormed degree isLocal
  · exact retainedDrawingPeriodicPlanarSATVariableValid_zeroLift
      formula first firstValid
  · exact retainedDrawingPeriodicPlanarSATVariableValid_zeroLift
      formula second secondValid
  · simpa using positionEq

/-- The variable-position prefix of the final deduplicated periodic
incidence drawing has no repeated positions. -/
theorem
    retainedDeduplicatedWrappedDrawingPeriodicPlanarSAT_variablePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    ((retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.incidenceVariableVertices.map fun vertex =>
      match vertex with
      | .variable atom =>
          (wrappedDrawingPeriodicPlanarSATPlacement formula).position atom
      | .clause _ => (0, 0)).Nodup := by
  rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
  apply
    (List.nodup_dedup
      (retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.variableOccurrences).map_on
  intro first firstMem second secondMem positionEq
  have originalEq : first.original = second.original := by
    apply drawingPeriodicPlanarSATVariablePosition_injective_of_valid
      formula wellFormed degree isLocal
    · exact
        retainedDeduplicatedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
          formula wellFormed degree isLocal
          ((List.mem_dedup).mp firstMem)
    · exact
        retainedDeduplicatedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
          formula wellFormed degree isLocal
          ((List.mem_dedup).mp secondMem)
    · simpa [Function.comp_def,
        wrappedDrawingPeriodicPlanarSATPlacement,
        drawingPeriodicPlanarSATPlacement] using positionEq
  cases first
  cases second
  simpa using originalEq

end LeanTrominoes.PeriodicOrthocrossing
