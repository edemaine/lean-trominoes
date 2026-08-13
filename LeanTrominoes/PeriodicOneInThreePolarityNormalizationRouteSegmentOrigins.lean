/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteContinuousPlanarity
import LeanTrominoes.PeriodicThreeDMContractionContinuousPlanarity

/-!
# Segment provenance for polarity-normalized route splitting

Every segment of a raw normalized route is inherited from exactly one
segment of a refined source incidence.  Compatible incidences retain the
whole source route.  Incompatible incidences partition it into source
segment `0`, reversed source segment `1`, and the suffix beginning at source
segment `2`.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalization

/-- The four ways in which an output route can inherit source segments. -/
inductive RawRouteFragment where
  | whole
  | prefix
  | middle
  | suffix
  deriving DecidableEq, Repr

/-- Provenance of one raw output segment in the refined source drawing. -/
structure RawSegmentOrigin where
  original : IndexedGridSegment
  latticeShift : Cell
  reversed : Bool
  sourceClauseIndex : Nat
  sourceLiteralIndex : Nat
  outputClauseIndex : Nat
  outputLiteralIndex : Nat
  fragment : RawRouteFragment
  deriving DecidableEq, Repr

/-- Realize a source segment after the whole-period translation and optional
route reversal recorded by its raw-splitting provenance. -/
def RawSegmentOrigin.realize
    (drawing : PeriodicGridDrawing)
    (origin : RawSegmentOrigin) : GridSegment :=
  let translated := origin.original.segment.translate
    (drawing.periodTranslation origin.latticeShift)
  if origin.reversed then translated.reverse else translated

/-- Lattice shift used to put a complement-clause route into its canonical
fundamental representative. -/
def complementLatticeShift {Variable : Type*}
    (literal : PeriodicLiteral Variable) : Cell :=
  Cell.sub (0, 0) literal.offset

/-- The physical complement-clause shift is exactly a whole-period shift in
the refined source drawing. -/
theorem complementCanonicalShift_eq_periodTranslation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (literal : PeriodicLiteral Variable) :
    complementCanonicalShift sourcePlacement literal =
      (PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        (refinedRouteFamily presentation).routes).periodTranslation
          (complementLatticeShift literal) := by
  unfold complementCanonicalShift complementLatticeShift
    PeriodicGridDrawing.periodTranslation
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize]
  · rcases literal.offset with ⟨literalX, literalY⟩
    simp [refinedPlacement, PeriodicVariablePlacement.scale,
      PeriodicVariablePlacement.translation,
      Cell.sub, Cell.scale]
  · change 0 < refinementFactor * sourcePlacement.period
    exact Nat.mul_pos refinementFactor_positive presentation.periodPositive

/-- The segment list of a two-point prefix is the first source segment. -/
theorem gridPolylineSegments_take_two
    {route : List Cell} (length : 2 ≤ route.length) :
    gridPolylineSegments (route.take 2) =
      (gridPolylineSegments route).take 1 := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          simp [gridPolylineSegments]

/-- Dropping two route points drops exactly the first two source segments. -/
theorem gridPolylineSegments_drop_two
    (route : List Cell) :
    gridPolylineSegments (route.drop 2) =
      (gridPolylineSegments route).drop 2 := by
  cases route with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              simp [gridPolylineSegments]

/-- With four available points, the reversed reserved middle pair realizes
the reversal of source segment index `1`. -/
theorem reverse_middle_segment
    (route : List Cell) (length : 4 ≤ route.length) :
    gridPolylineSegments [route.getD 2 (0, 0), route.getD 1 (0, 0)] =
      [((gridPolylineSegments route).getD 1
        (GridSegment.mk (0, 0) (0, 0))).reverse] := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest =>
              simp [gridPolylineSegments, GridSegment.reverse]

/-- Build forward provenance for every segment of one refined source route. -/
def sourceSegmentOrigins
    (routeIndex sourceClauseIndex sourceLiteralIndex : Nat)
    (route : List Cell) : List RawSegmentOrigin :=
  (gridPolylineSegments route).zipIdx.map fun segment =>
    { original := ⟨routeIndex, segment.2, segment.1⟩
      latticeShift := (0, 0)
      reversed := false
      sourceClauseIndex := sourceClauseIndex
      sourceLiteralIndex := sourceLiteralIndex
      outputClauseIndex := 0
      outputLiteralIndex := 0
      fragment := .whole }

/-- Override output metadata and the geometric transform of a source-origin
block without changing its original segment occurrences. -/
def retagOrigins
    (outputClauseIndex outputLiteralIndex : Nat)
    (fragment : RawRouteFragment)
    (latticeShift : Cell) (reversed : Bool) :
    List RawSegmentOrigin → List RawSegmentOrigin :=
  List.map fun origin =>
    { origin with
      latticeShift := latticeShift
      reversed := reversed
      outputClauseIndex := outputClauseIndex
      outputLiteralIndex := outputLiteralIndex
      fragment := fragment }

/-- Original source occurrences are unaffected by retagging. -/
@[simp]
theorem retagOrigins_map_original
    (outputClauseIndex outputLiteralIndex : Nat)
    (fragment : RawRouteFragment)
    (latticeShift : Cell) (reversed : Bool)
    (origins : List RawSegmentOrigin) :
    (retagOrigins outputClauseIndex outputLiteralIndex fragment
      latticeShift reversed origins).map RawSegmentOrigin.original =
        origins.map RawSegmentOrigin.original := by
  simp [retagOrigins, List.map_map, Function.comp_def]

/-- Forward source origins realize exactly their source segment list. -/
theorem sourceSegmentOrigins_realize
    (drawing : PeriodicGridDrawing)
    (routeIndex sourceClauseIndex sourceLiteralIndex : Nat)
    (route : List Cell) :
    (sourceSegmentOrigins routeIndex sourceClauseIndex sourceLiteralIndex
      route).map (RawSegmentOrigin.realize drawing) =
        gridPolylineSegments route := by
  simp [sourceSegmentOrigins, RawSegmentOrigin.realize,
    List.map_map, Function.comp_def,
    PeriodicGridDrawing.periodTranslation,
    GridSegment.translate, Cell.scale, Cell.add]

/-- Forgetting source-origin metadata leaves the source segment list. -/
@[simp]
theorem sourceSegmentOrigins_map_segment
    (routeIndex sourceClauseIndex sourceLiteralIndex : Nat)
    (route : List Cell) :
    (sourceSegmentOrigins routeIndex sourceClauseIndex sourceLiteralIndex
      route).map (fun origin => origin.original.segment) =
        gridPolylineSegments route := by
  simp [sourceSegmentOrigins, List.map_map, Function.comp_def]

/-- Retagging applies one common geometric transform to the realized source
segments while preserving all list selections already made. -/
theorem retagOrigins_realize
    (drawing : PeriodicGridDrawing)
    (outputClauseIndex outputLiteralIndex : Nat)
    (fragment : RawRouteFragment)
    (latticeShift : Cell) (reversed : Bool)
    (origins : List RawSegmentOrigin) :
    (retagOrigins outputClauseIndex outputLiteralIndex fragment
      latticeShift reversed origins).map
        (RawSegmentOrigin.realize drawing) =
      (origins.map (fun origin => origin.original.segment)).map fun segment =>
        let translated := segment.translate
          (drawing.periodTranslation latticeShift)
        if reversed then translated.reverse else translated := by
  simp [retagOrigins, RawSegmentOrigin.realize,
    List.map_map, Function.comp_def]

/-- Retagging a forward source-origin list applies exactly the advertised
translation and optional segment reversal, pointwise and in the same list
order. -/
theorem retag_sourceSegmentOrigins_realize
    (drawing : PeriodicGridDrawing)
    (routeIndex sourceClauseIndex sourceLiteralIndex : Nat)
    (route : List Cell)
    (outputClauseIndex outputLiteralIndex : Nat)
    (fragment : RawRouteFragment)
    (latticeShift : Cell) (reversed : Bool) :
    (retagOrigins outputClauseIndex outputLiteralIndex fragment
      latticeShift reversed
      (sourceSegmentOrigins routeIndex sourceClauseIndex
        sourceLiteralIndex route)).map
        (RawSegmentOrigin.realize drawing) =
      (gridPolylineSegments route).map fun segment =>
        let translated := segment.translate
          (drawing.periodTranslation latticeShift)
        if reversed then translated.reverse else translated := by
  simp [retagOrigins, sourceSegmentOrigins,
    RawSegmentOrigin.realize, List.map_map, Function.comp_def]
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0 (gridPolylineSegments route),
      List.map_map, Function.comp_def]

/-- Flat refined-source route index of one metadata-selected source
incidence.  Invalid arguments are harmless because origin tables are used
only after the corresponding membership proof has been recovered. -/
def refinedIncidenceIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex sourceLiteralIndex : Nat)
    (sourceLiteral : PeriodicLiteral Variable) : Nat :=
  (PeriodicCNF.incidencesWithMetadata
    (refinedSource source sourcePlacement).erase).idxOf
      (CNFIncidence.mk sourceClauseIndex sourceClause.literals
        sourceLiteralIndex sourceLiteral)

/-- Provenance list parallel to one raw route selected by generated-clause
metadata. -/
def rawSegmentOriginsForMetadata
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (outputClauseIndex outputLiteralIndex : Nat) :
    List RawSegmentOrigin :=
  match metadata.origin with
  | .normalized =>
      match metadata.sourceClause.literals[outputLiteralIndex]? with
      | none => []
      | some sourceLiteral =>
          let base := sourceSegmentOrigins
            (refinedIncidenceIndex source sourcePlacement
              metadata.sourceClause metadata.sourceClauseIndex
              outputLiteralIndex sourceLiteral)
            metadata.sourceClauseIndex outputLiteralIndex
            (refinedRoute sourceRoutes metadata.sourceClauseIndex
              outputLiteralIndex)
          if sourceLiteral.value = normalizedPolarity outputLiteralIndex then
            retagOrigins outputClauseIndex outputLiteralIndex .whole
              (0, 0) false base
          else
            retagOrigins outputClauseIndex outputLiteralIndex .prefix
              (0, 0) false (base.take 1)
  | .complement sourceLiteralIndex sourceLiteral =>
      let base := sourceSegmentOrigins
        (refinedIncidenceIndex source sourcePlacement
          metadata.sourceClause metadata.sourceClauseIndex
          sourceLiteralIndex sourceLiteral)
        metadata.sourceClauseIndex sourceLiteralIndex
        (refinedRoute sourceRoutes metadata.sourceClauseIndex
          sourceLiteralIndex)
      let shift := complementLatticeShift sourceLiteral
      if outputLiteralIndex = 0 then
        retagOrigins outputClauseIndex outputLiteralIndex .middle
          shift true ((base.drop 1).take 1)
      else if outputLiteralIndex = 1 then
        retagOrigins outputClauseIndex outputLiteralIndex .suffix
          shift false (base.drop 2)
      else
        []

/-- Total raw-origin lookup parallel to the total raw route lookup. -/
def rawSegmentOrigins
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (outputClauseIndex outputLiteralIndex : Nat) :
    List RawSegmentOrigin :=
  match (clauseMetadata source sourcePlacement sourceRoutes)[outputClauseIndex]?
      with
  | none => []
  | some metadata =>
      rawSegmentOriginsForMetadata source sourcePlacement sourceRoutes
        metadata outputClauseIndex outputLiteralIndex

/-- A successful metadata lookup exposes the selected raw origin block. -/
theorem rawSegmentOrigins_of_metadata_lookup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (outputClauseIndex outputLiteralIndex : Nat)
    (metadataLookup :
      (clauseMetadata source sourcePlacement sourceRoutes)[outputClauseIndex]? =
        some metadata) :
    rawSegmentOrigins source sourcePlacement sourceRoutes
        outputClauseIndex outputLiteralIndex =
      rawSegmentOriginsForMetadata source sourcePlacement sourceRoutes
        metadata outputClauseIndex outputLiteralIndex := by
  simp [rawSegmentOrigins, metadataLookup]

/-- On every genuine raw output incidence, provenance realizes exactly the
segment list of the selected raw route. -/
theorem rawSegmentOrigins_realize_of_output_members
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {outputClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {outputClauseIndex : Nat}
    (outputClauseMember :
      (outputClause, outputClauseIndex) ∈
        (rawFormula source sourcePlacement presentation.routes).clauses.zipIdx)
    {outputLiteral : PeriodicLiteral (PolarityNormalizedVariable Variable)}
    {outputLiteralIndex : Nat}
    (outputLiteralMember :
      (outputLiteral, outputLiteralIndex) ∈ outputClause.literals.zipIdx) :
    (rawSegmentOrigins source sourcePlacement presentation.routes
      outputClauseIndex outputLiteralIndex).map
        (RawSegmentOrigin.realize
          (PositionedPeriodicCNF.incidenceDrawing
            (refinedSource source sourcePlacement)
            (refinedPlacement sourcePlacement)
            (refinedRouteFamily presentation).routes)) =
      gridPolylineSegments
        (rawIncidenceRoutes source sourcePlacement presentation.routes
          outputClauseIndex outputLiteralIndex) := by
  rcases exists_raw_source_of_output_members presentation
      outputClauseMember outputLiteralMember with
    ⟨metadata, sourceLiteral, sourceLiteralIndex, metadataLookup,
      sourceClauseMember, sourceLiteralMember, originData⟩
  rw [rawSegmentOrigins_of_metadata_lookup
    source sourcePlacement presentation.routes metadata
    outputClauseIndex outputLiteralIndex metadataLookup]
  rw [rawIncidenceRoutes_of_metadata_lookup
    source sourcePlacement presentation.routes metadata
    outputClauseIndex outputLiteralIndex metadataLookup]
  rcases originData with normalized | complement
  · rcases normalized with ⟨originEq, sourceIndexEq⟩
    subst sourceLiteralIndex
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember
    by_cases compatible :
        sourceLiteral.value = normalizedPolarity outputLiteralIndex
    · rw [rawRouteForMetadata_normalized_compatible
        sourcePlacement presentation.routes metadata sourceLiteral
        outputLiteralIndex originEq sourceLiteralLookup compatible]
      simp [rawSegmentOriginsForMetadata, originEq, sourceLiteralLookup,
        compatible, retagOrigins_realize,
        PeriodicGridDrawing.periodTranslation, GridSegment.translate,
        Cell.scale, Cell.add]
    · rw [rawRouteForMetadata_normalized_incompatible
        sourcePlacement presentation.routes metadata sourceLiteral
        outputLiteralIndex originEq sourceLiteralLookup compatible]
      rw [gridPolylineSegments_take_two]
      · simp [rawSegmentOriginsForMetadata, originEq, sourceLiteralLookup,
          compatible, retagOrigins_realize,
          PeriodicGridDrawing.periodTranslation, GridSegment.translate,
          Cell.scale, Cell.add]
      · exact le_trans (by decide : 2 ≤ 4)
          (refinedRoute_length_ge_four_of_members presentation
            sourceClauseMember sourceLiteralMember)
  · rcases complement with ⟨originEq, outputIndexCases⟩
    have routeLength := refinedRoute_length_ge_four_of_members
      presentation sourceClauseMember sourceLiteralMember
    rcases outputIndexCases with outputIndexEq | outputIndexEq
    · subst outputLiteralIndex
      rw [rawRouteForMetadata_complement_fresh
        sourcePlacement presentation.routes metadata sourceLiteral
        sourceLiteralIndex originEq]
      simp only [rawSegmentOriginsForMetadata, originEq, if_pos,
        retagOrigins_realize, List.map_take, List.map_drop,
        sourceSegmentOrigins_map_segment]
      rw [gridPolylineSegments_translatePolyline,
        complementCanonicalShift_eq_periodTranslation presentation]
      unfold routePoint
      cases routeEq : refinedRoute presentation.routes
          metadata.sourceClauseIndex sourceLiteralIndex with
      | nil => simp [routeEq] at routeLength
      | cons first rest =>
          cases rest with
          | nil => simp [routeEq] at routeLength
          | cons second rest =>
              cases rest with
              | nil => simp [routeEq] at routeLength
              | cons third rest =>
                  simp [gridPolylineSegments, GridSegment.reverse,
                    GridSegment.translate]
    · subst outputLiteralIndex
      rw [rawRouteForMetadata_complement_original
        sourcePlacement presentation.routes metadata sourceLiteral
        sourceLiteralIndex originEq]
      simp only [rawSegmentOriginsForMetadata, originEq]
      rw [if_neg (by omega : (1 : Nat) ≠ 0)]
      simp only [if_true]
      rw [retagOrigins_realize]
      simp only [List.map_drop, sourceSegmentOrigins_map_segment]
      rw [gridPolylineSegments_translatePolyline,
        complementCanonicalShift_eq_periodTranslation presentation,
        gridPolylineSegments_drop_two]
      simp

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
