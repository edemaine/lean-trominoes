import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
import LeanTrominoes.PositionedPeriodicCNFPresentationCanonicalRoutes
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds

/-!
# Endpoint and orthogonality correctness for polarity-normalized routes

This file verifies the local geometric contract of the three-way incidence
subdivision.  A continuously planar source presentation is first
anchor-normalized, refined threefold, and unit-subdivided.  The resulting
pointwise route family supplies exact source endpoints and orthogonality for
the normalized main prefixes, reverse middle edges, and complement suffixes.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Canonical source routes after anchor normalization, threefold scaling,
and unit subdivision. -/
def refinedRouteFamily {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement) :=
  let normalized := presentation.anchorNormalize
  let normalizedFamily :=
    normalized.toPlanarIncidencePresentation.canonicalOrthogonalRoutes
  (normalizedFamily.scale refinementFactor_positive).unitSubdivide

/-- The abstract refined family selects exactly `refinedRoute`. -/
@[simp]
theorem refinedRouteFamily_routes {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (clauseIndex literalIndex : Nat) :
    (refinedRouteFamily presentation).routes clauseIndex literalIndex =
      refinedRoute presentation.routes clauseIndex literalIndex := by
  rfl

/-- Every clause retained by the refined source still has anchor zero. -/
theorem refinedSource_clauseAnchor_eq_zero {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx) :
    PeriodicCNF.clauseAnchor clause.literals = (0, 0) := by
  unfold refinedSource at clauseMember
  rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
      at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEq⟩
  have clauseEq :
      taggedClause.1.scale refinementFactor = clause := by
    simpa only [Prod.map, id_eq] using congrArg Prod.fst taggedClauseEq
  subst clause
  rw [PositionedPeriodicCNF.anchorNormalize, List.zipIdx_map]
      at taggedClauseMember
  rcases List.mem_map.mp taggedClauseMember with
    ⟨sourceTagged, _sourceTaggedMember, sourceTaggedEq⟩
  have literalsEq :
      sourceTagged.1.literals.anchorNormalize =
        taggedClause.1.literals := by
    simpa only [Prod.map, id_eq] using
      congrArg (fun tagged => tagged.1.literals) sourceTaggedEq
  rw [PositionedPeriodicClause.scale_literals, ← literalsEq]
  exact PeriodicClause.clauseAnchor_anchorNormalize _

/-- A refined source incidence retains the same two presentation indices as
one incidence of the unnormalized source. -/
theorem exists_sourceTagged_of_refined_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ tagged,
      tagged ∈
          (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx ∧
        tagged.1.clauseIndex = clauseIndex ∧
        tagged.1.literalIndex = literalIndex := by
  rcases PositionedPeriodicCNF.exists_taggedIncidence_of_members
      (refinedSource source sourcePlacement)
      clauseMember literalMember with
    ⟨incidenceIndex, refinedTaggedMember⟩
  rw [refinedSource,
    PositionedPeriodicCNF.erase_scale,
    PositionedPeriodicCNF.erase_anchorNormalize,
    PeriodicCNF.incidencesWithMetadata_anchorNormalize,
    List.zipIdx_map] at refinedTaggedMember
  rcases List.mem_map.mp refinedTaggedMember with
    ⟨tagged, taggedMember, taggedEq⟩
  refine ⟨tagged, taggedMember, ?_, ?_⟩
  · simpa using congrArg (fun value => value.1.clauseIndex) taggedEq
  · simpa using congrArg (fun value => value.1.literalIndex) taggedEq

/-- Every genuine source route behind a refined incidence has at least two
points. -/
theorem sourceRoute_length_ge_two_of_refined_members
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤ (presentation.routes clauseIndex literalIndex).length := by
  rcases exists_sourceTagged_of_refined_members source sourcePlacement
      clauseMember literalMember with
    ⟨tagged, taggedMember, clauseIndexEq, literalIndexEq⟩
  have segmentsNonempty :=
    presentation.toPlanarIncidencePresentation
      |>.route_segments_ne_nil_of_tagged taggedMember
  have segmentsPositive :
      0 <
        (gridPolylineSegments
          (presentation.routes tagged.1.clauseIndex
            tagged.1.literalIndex)).length :=
    List.length_pos_iff.mpr segmentsNonempty
  rw [gridPolylineSegments_length] at segmentsPositive
  rw [clauseIndexEq, literalIndexEq] at segmentsPositive
  omega

/-- Every source route behind a refined incidence is orthogonal. -/
theorem sourceRoute_orthogonal_of_refined_members
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (presentation.routes clauseIndex literalIndex) := by
  rcases exists_sourceTagged_of_refined_members source sourcePlacement
      clauseMember literalMember with
    ⟨tagged, taggedMember, clauseIndexEq, literalIndexEq⟩
  have orthogonal :=
    presentation.toPlanarIncidencePresentation
      |>.route_orthogonal_of_tagged taggedMember
  rwa [clauseIndexEq, literalIndexEq] at orthogonal

/-- A genuine refined source incidence has the two reserved subdivision
vertices and hence at least four listed points. -/
theorem refinedRoute_length_ge_four_of_members
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    4 ≤ (refinedRoute presentation.routes clauseIndex literalIndex).length :=
  refinedRoute_length_ge_four presentation.routes clauseIndex literalIndex
    (sourceRoute_length_ge_two_of_refined_members presentation
      clauseMember literalMember)
    (sourceRoute_orthogonal_of_refined_members presentation
      clauseMember literalMember)

@[simp]
theorem rawPlacement_period {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    (rawPlacement sourcePlacement sourceRoutes).period =
      (refinedPlacement sourcePlacement).period := by
  rfl

@[simp]
theorem rawPlacement_original_position {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (rawPlacement sourcePlacement sourceRoutes).position (Sum.inl atom) =
      (refinedPlacement sourcePlacement).position atom := by
  rfl

@[simp]
theorem rawPlacement_fresh_position {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (fresh : FreshOccurrence Variable) :
    (rawPlacement sourcePlacement sourceRoutes).position (Sum.inr fresh) =
      Cell.sub (routePoint sourceRoutes fresh 1)
        ((refinedPlacement sourcePlacement).translation fresh.2.offset) := by
  rfl

/-- Before gauging, both literals of a complement clause retain the source
offset, so its canonical anchor is that offset. -/
@[simp]
theorem clauseAnchor_complementClause {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (sourceLiteral : PeriodicLiteral Variable) :
    PeriodicCNF.clauseAnchor
        (PeriodicOneInThreePolarityNormalization.complementClause
          clauseIndex literalIndex sourceLiteral) =
      sourceLiteral.offset := by
  rfl

/-- The first two points of a four-point route retain its first point. -/
theorem take_two_head?_eq
    (route : List Cell) (length : 4 ≤ route.length) :
    (route.take 2).head? = route.head? := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest => simp

/-- The first two-point prefix ends at index one.  This local form is placed
before the endpoint lemmas that consume it. -/
theorem take_two_getLast?_eq_getD_one_early
    (route : List Cell) (length : 4 ≤ route.length) :
    (route.take 2).getLast? = some (route.getD 1 (0, 0)) := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest => simp

/-- The suffix after two points starts at index two. -/
theorem drop_two_head?_eq_getD_two_early
    (route : List Cell) (length : 4 ≤ route.length) :
    (route.drop 2).head? = some (route.getD 2 (0, 0)) := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest => simp

/-- The suffix after two points retains the source route's final point. -/
theorem drop_two_getLast?_eq_early
    (route : List Cell) (length : 4 ≤ route.length) :
    (route.drop 2).getLast? = route.getLast? := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest => simp

/-- Endpoint correctness for a compatible normalized main incidence. -/
theorem rawRouteForMetadata_normalized_compatible_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceClauseMember :
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (sourceLiteral : PeriodicLiteral Variable)
    (literalIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, literalIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (originEq : metadata.origin = .normalized)
    (compatible :
      sourceLiteral.value =
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          literalIndex) :
    let outputClause :=
      PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
        metadata.sourceClauseIndex metadata.sourceClause
    let outputLiteral :=
      PeriodicOneInThreePolarityNormalization.normalizeLiteral
        metadata.sourceClauseIndex literalIndex sourceLiteral
    (rawRouteForMetadata sourcePlacement presentation.routes
        metadata literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (rawPlacement sourcePlacement presentation.routes)
            outputClause) ∧
      (rawRouteForMetadata sourcePlacement presentation.routes
        metadata literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (rawPlacement sourcePlacement presentation.routes)
            outputClause outputLiteral) := by
  dsimp only
  have sourceAnchor := refinedSource_clauseAnchor_eq_zero
    source sourcePlacement sourceClauseMember
  have sourceEndpoints :=
    (refinedRouteFamily presentation).endpoints
      metadata.sourceClause metadata.sourceClauseIndex sourceClauseMember
      sourceLiteral literalIndex sourceLiteralMember
  rw [refinedRouteFamily_routes] at sourceEndpoints
  rw [rawRouteForMetadata_normalized_compatible
    sourcePlacement presentation.routes metadata sourceLiteral literalIndex
    originEq
    ((List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember)
    compatible]
  constructor
  · simpa [PositionedPeriodicCNF.canonicalClausePosition,
      PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
      rawPlacement, PeriodicVariablePlacement.translation,
      sourceAnchor] using sourceEndpoints.1
  · simpa [PositionedPeriodicCNF.canonicalLiteralPosition,
      PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
      PeriodicOneInThreePolarityNormalization.normalizeLiteral,
      compatible,
      PeriodicOneInThreePolarityNormalization.liftLiteral,
      rawPlacement, PeriodicVariablePlacement.translation,
      sourceAnchor] using sourceEndpoints.2

/-- Endpoint correctness for the clause-side prefix of an incompatible
normalized main incidence. -/
theorem rawRouteForMetadata_normalized_incompatible_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceClauseMember :
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (sourceLiteral : PeriodicLiteral Variable)
    (literalIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, literalIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (originEq : metadata.origin = .normalized)
    (incompatible :
      sourceLiteral.value ≠
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          literalIndex) :
    let outputClause :=
      PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
        metadata.sourceClauseIndex metadata.sourceClause
    let outputLiteral :=
      PeriodicOneInThreePolarityNormalization.normalizeLiteral
        metadata.sourceClauseIndex literalIndex sourceLiteral
    (rawRouteForMetadata sourcePlacement presentation.routes
        metadata literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (rawPlacement sourcePlacement presentation.routes)
            outputClause) ∧
      (rawRouteForMetadata sourcePlacement presentation.routes
        metadata literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (rawPlacement sourcePlacement presentation.routes)
            outputClause outputLiteral) := by
  dsimp only
  have sourceAnchor := refinedSource_clauseAnchor_eq_zero
    source sourcePlacement sourceClauseMember
  have sourceEndpoints :=
    (refinedRouteFamily presentation).endpoints
      metadata.sourceClause metadata.sourceClauseIndex sourceClauseMember
      sourceLiteral literalIndex sourceLiteralMember
  rw [refinedRouteFamily_routes] at sourceEndpoints
  have routeLength := refinedRoute_length_ge_four_of_members
    presentation sourceClauseMember sourceLiteralMember
  rw [rawRouteForMetadata_normalized_incompatible
    sourcePlacement presentation.routes metadata sourceLiteral literalIndex
    originEq
    ((List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember)
    incompatible]
  constructor
  · rw [take_two_head?_eq _ routeLength]
    simpa [PositionedPeriodicCNF.canonicalClausePosition,
      PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
      rawPlacement, PeriodicVariablePlacement.translation,
      sourceAnchor] using sourceEndpoints.1
  · rw [take_two_getLast?_eq_getD_one_early _ routeLength]
    rcases sourceLiteral with
      ⟨sourceAtom, ⟨sourceOffsetX, sourceOffsetY⟩, sourceValue⟩
    simp [PositionedPeriodicCNF.canonicalLiteralPosition,
      PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
      PeriodicOneInThreePolarityNormalization.normalizeLiteral,
      incompatible,
      PeriodicOneInThreePolarityNormalization.complementLiteral,
      rawPlacement, rawPositions, routePoint,
      PeriodicVariablePlacement.translation,
      sourceAnchor, Cell.add, Cell.sub]

/-- Endpoint correctness for the reverse middle edge from a binary
complement clause to its fresh variable. -/
theorem rawRouteForMetadata_complement_fresh_endpoints
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    let outputClause :=
      PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
        (rawPositions sourcePlacement sourceRoutes)
        metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral
    let outputLiteral :=
      PeriodicOneInThreePolarityNormalization.complementFalseLiteral
        metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral
    (rawRouteForMetadata sourcePlacement sourceRoutes metadata 0).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (rawPlacement sourcePlacement sourceRoutes) outputClause) ∧
      (rawRouteForMetadata sourcePlacement sourceRoutes metadata 0).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (rawPlacement sourcePlacement sourceRoutes)
            outputClause outputLiteral) := by
  dsimp only
  rw [rawRouteForMetadata_complement_fresh
    sourcePlacement sourceRoutes metadata sourceLiteral
    sourceLiteralIndex originEq]
  rcases sourceLiteral with
    ⟨sourceAtom, ⟨sourceOffsetX, sourceOffsetY⟩, sourceValue⟩
  generalize pointOneEq : routePoint sourceRoutes
      ((metadata.sourceClauseIndex, sourceLiteralIndex),
        { atom := sourceAtom
          offset := (sourceOffsetX, sourceOffsetY)
          value := sourceValue }) 1 = pointOne
  rcases pointOne with ⟨pointOneX, pointOneY⟩
  generalize pointTwoEq : routePoint sourceRoutes
      ((metadata.sourceClauseIndex, sourceLiteralIndex),
        { atom := sourceAtom
          offset := (sourceOffsetX, sourceOffsetY)
          value := sourceValue }) 2 = pointTwo
  rcases pointTwo with ⟨pointTwoX, pointTwoY⟩
  simp [PeriodicOrthocrossing.translatePolyline,
    complementCanonicalShift,
    PositionedPeriodicCNF.canonicalClausePosition,
    PositionedPeriodicCNF.canonicalLiteralPosition,
    PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
    PeriodicOneInThreePolarityNormalization.complementFalseLiteral,
    clauseAnchor_complementClause,
    rawPlacement, rawPositions,
    PeriodicVariablePlacement.translation,
    Cell.add, Cell.sub, Cell.scale,
    sub_eq_add_neg, add_comm, pointOneEq, pointTwoEq]

/-- Endpoint correctness for the binary-clause suffix leading to the
embedded original variable. -/
theorem rawRouteForMetadata_complement_original_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceClauseMember :
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    let outputClause :=
      PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
        (rawPositions sourcePlacement presentation.routes)
        metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral
    let outputLiteral :=
      PeriodicOneInThreePolarityNormalization.originalFalseLiteral
        sourceLiteral
    (rawRouteForMetadata sourcePlacement presentation.routes metadata 1).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (rawPlacement sourcePlacement presentation.routes) outputClause) ∧
      (rawRouteForMetadata sourcePlacement presentation.routes metadata 1).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (rawPlacement sourcePlacement presentation.routes)
            outputClause outputLiteral) := by
  dsimp only
  have sourceAnchor := refinedSource_clauseAnchor_eq_zero
    source sourcePlacement sourceClauseMember
  have sourceEndpoints :=
    (refinedRouteFamily presentation).endpoints
      metadata.sourceClause metadata.sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
  rw [refinedRouteFamily_routes] at sourceEndpoints
  have routeLength := refinedRoute_length_ge_four_of_members
    presentation sourceClauseMember sourceLiteralMember
  rw [rawRouteForMetadata_complement_original
    sourcePlacement presentation.routes metadata sourceLiteral
    sourceLiteralIndex originEq]
  constructor
  · simp only [PeriodicOrthocrossing.translatePolyline,
      List.head?_map,
      drop_two_head?_eq_getD_two_early _ routeLength,
      Option.map_some]
    rcases sourceLiteral with
      ⟨sourceAtom, ⟨sourceOffsetX, sourceOffsetY⟩, sourceValue⟩
    simp [complementCanonicalShift,
      PositionedPeriodicCNF.canonicalClausePosition,
      PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
      clauseAnchor_complementClause,
      rawPlacement, rawPositions, routePoint,
      PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale,
      sub_eq_add_neg, add_comm]
  · simp only [PeriodicOrthocrossing.translatePolyline,
      List.getLast?_map,
      drop_two_getLast?_eq_early _ routeLength,
      sourceEndpoints.2, Option.map_some]
    rcases sourceLiteral with
      ⟨sourceAtom, ⟨sourceOffsetX, sourceOffsetY⟩, sourceValue⟩
    rcases (refinedPlacement sourcePlacement).position sourceAtom with
      ⟨positionX, positionY⟩
    simp [complementCanonicalShift,
      PositionedPeriodicCNF.canonicalLiteralPosition,
      PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
      PeriodicOneInThreePolarityNormalization.originalFalseLiteral,
      clauseAnchor_complementClause,
      rawPlacement,
      PeriodicVariablePlacement.translation,
      sourceAnchor, Cell.add, Cell.sub, Cell.scale,
      sub_eq_add_neg, add_comm]

/-- Reversing an axis-aligned segment preserves axis alignment. -/
theorem axisAligned_reverse {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (GridSegment.mk second first).IsAxisAligned := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases aligned with horizontal | vertical
  · left
    exact ⟨horizontal.1.symm, Ne.symm horizontal.2⟩
  · right
    exact ⟨vertical.1.symm, Ne.symm vertical.2⟩

/-- Points two and one of a four-point orthogonal route form an orthogonal
reverse middle edge. -/
theorem reverse_middle_orthogonal
    (route : List Cell)
    (length : 4 ≤ route.length)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route) :
    PeriodicOrthocrossing.OrthogonalPolyline
      [route.getD 2 (0, 0), route.getD 1 (0, 0)] := by
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          cases rest with
          | nil => simp at length
          | cons third rest =>
              have secondThird :
                  (GridSegment.mk second third).IsAxisAligned :=
                (List.isChain_cons_cons.mp
                  (List.isChain_cons_cons.mp orthogonal).2).1
              simpa [PeriodicOrthocrossing.OrthogonalPolyline] using
                axisAligned_reverse secondThird

/-- A normalized main-clause route remains orthogonal, whether it keeps the
whole refined route or only its clause-side prefix. -/
theorem rawRouteForMetadata_normalized_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceClauseMember :
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (originEq : metadata.origin = .normalized) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rawRouteForMetadata sourcePlacement presentation.routes
        metadata sourceLiteralIndex) := by
  have refinedOrthogonal :=
    (refinedRouteFamily presentation).orthogonal
      metadata.sourceClause metadata.sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
  rw [refinedRouteFamily_routes] at refinedOrthogonal
  by_cases compatible :
      sourceLiteral.value =
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          sourceLiteralIndex
  · rw [rawRouteForMetadata_normalized_compatible
      sourcePlacement presentation.routes metadata sourceLiteral
      sourceLiteralIndex originEq
      ((List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember)
      compatible]
    exact refinedOrthogonal
  · rw [rawRouteForMetadata_normalized_incompatible
      sourcePlacement presentation.routes metadata sourceLiteral
      sourceLiteralIndex originEq
      ((List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember)
      compatible]
    exact List.IsChain.take refinedOrthogonal 2

/-- The fresh-variable route of a complement clause is the translated
reverse middle edge of an orthogonal refined route. -/
theorem rawRouteForMetadata_complement_fresh_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceClauseMember :
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rawRouteForMetadata sourcePlacement presentation.routes metadata 0) := by
  have refinedOrthogonal :=
    (refinedRouteFamily presentation).orthogonal
      metadata.sourceClause metadata.sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
  rw [refinedRouteFamily_routes] at refinedOrthogonal
  have routeLength := refinedRoute_length_ge_four_of_members
    presentation sourceClauseMember sourceLiteralMember
  rw [rawRouteForMetadata_complement_fresh
    sourcePlacement presentation.routes metadata sourceLiteral
    sourceLiteralIndex originEq]
  apply PeriodicOrthocrossing.OrthogonalPolyline.translate
  simpa [routePoint] using
    reverse_middle_orthogonal
      (refinedRoute presentation.routes metadata.sourceClauseIndex
        sourceLiteralIndex)
      routeLength refinedOrthogonal

/-- The original-variable route of a complement clause is the translated
suffix of an orthogonal refined route. -/
theorem rawRouteForMetadata_complement_original_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceClauseMember :
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rawRouteForMetadata sourcePlacement presentation.routes metadata 1) := by
  have refinedOrthogonal :=
    (refinedRouteFamily presentation).orthogonal
      metadata.sourceClause metadata.sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
  rw [refinedRouteFamily_routes] at refinedOrthogonal
  rw [rawRouteForMetadata_complement_original
    sourcePlacement presentation.routes metadata sourceLiteral
    sourceLiteralIndex originEq]
  have suffixOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        ((refinedRoute presentation.routes metadata.sourceClauseIndex
          sourceLiteralIndex).drop 2) :=
    List.IsChain.drop refinedOrthogonal 2
  exact suffixOrthogonal.translate _

/-- The assembled raw route table has the canonical endpoints of the
ungauged positioned polarity normalization. -/
theorem rawIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    ∀ outputClause outputClauseIndex,
      (outputClause, outputClauseIndex) ∈
          (rawFormula source sourcePlacement presentation.routes).clauses.zipIdx →
      ∀ outputLiteral outputLiteralIndex,
        (outputLiteral, outputLiteralIndex) ∈
            outputClause.literals.zipIdx →
        (rawIncidenceRoutes source sourcePlacement presentation.routes
            outputClauseIndex outputLiteralIndex).head? =
            some
              (PositionedPeriodicCNF.canonicalClausePosition
                (rawPlacement sourcePlacement presentation.routes)
                outputClause) ∧
          (rawIncidenceRoutes source sourcePlacement presentation.routes
            outputClauseIndex outputLiteralIndex).getLast? =
            some
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (rawPlacement sourcePlacement presentation.routes)
                outputClause outputLiteral) := by
  intro outputClause outputClauseIndex outputClauseMember
    outputLiteral outputLiteralIndex outputLiteralMember
  have formulaClauseMember :
      (outputClause, outputClauseIndex) ∈
        (PeriodicOneInThreePolarityNormalizationPositioned.formula
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)).clauses.zipIdx := by
    simpa [rawFormula] using outputClauseMember
  rcases
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_lookup
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement) formulaClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEq⟩
  have rawMetadataLookup :
      (clauseMetadata source sourcePlacement presentation.routes)[outputClauseIndex]? =
        some metadata := by
    simpa [clauseMetadata] using metadataLookup
  rw [rawIncidenceRoutes_of_metadata_lookup
    source sourcePlacement presentation.routes metadata
    outputClauseIndex outputLiteralIndex rawMetadataLookup]
  have metadataIndexLt :
      outputClauseIndex <
        (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement))[outputClauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have sourceClauseMember :=
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_source_mem
      (rawPositions sourcePlacement presentation.routes)
      (refinedSource source sourcePlacement) metadataMember
  cases originEq : metadata.origin with
  | normalized =>
      have normalizedClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have normalizedLiteralMember :
          (outputLiteral, outputLiteralIndex) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
              metadata.sourceClauseIndex metadata.sourceClause).literals.zipIdx := by
        rw [← normalizedClauseEq, metadataClauseEq]
        exact outputLiteralMember
      have normalizedLiteralLookup :
          (PeriodicOneInThreePolarityNormalization.normalizeClause
            metadata.sourceClauseIndex metadata.sourceClause.literals)[outputLiteralIndex]? =
              some outputLiteral := by
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause]
          using (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
      rw [PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?]
          at normalizedLiteralLookup
      rcases Option.map_eq_some_iff.mp normalizedLiteralLookup with
        ⟨sourceLiteral, sourceLiteralLookup, outputLiteralEq⟩
      have sourceLiteralMember :
          (sourceLiteral, outputLiteralIndex) ∈
            metadata.sourceClause.literals.zipIdx :=
        (List.mem_zipIdx_iff_getElem?).mpr sourceLiteralLookup
      rw [← metadataClauseEq, normalizedClauseEq]
      rw [← outputLiteralEq]
      by_cases compatible :
          sourceLiteral.value =
            PeriodicOneInThreePolarityNormalization.normalizedPolarity
              outputLiteralIndex
      · exact rawRouteForMetadata_normalized_compatible_endpoints
          presentation metadata sourceClauseMember sourceLiteral
          outputLiteralIndex sourceLiteralMember originEq compatible
      · exact rawRouteForMetadata_normalized_incompatible_endpoints
          presentation metadata sourceClauseMember sourceLiteral
          outputLiteralIndex sourceLiteralMember originEq compatible
  | complement sourceLiteralIndex sourceLiteral =>
      have complementValid :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have complementClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have complementLiteralMember :
          (outputLiteral, outputLiteralIndex) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
              (rawPositions sourcePlacement presentation.routes)
              metadata.sourceClauseIndex sourceLiteralIndex
              sourceLiteral).literals.zipIdx := by
        rw [← complementClauseEq, metadataClauseEq]
        exact outputLiteralMember
      have outputLiteralIndexLt : outputLiteralIndex < 2 := by
        have := List.snd_lt_of_mem_zipIdx complementLiteralMember
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause] using this
      have outputIndexCases :
          outputLiteralIndex = 0 ∨ outputLiteralIndex = 1 := by
        omega
      rcases outputIndexCases with outputIndexEq | outputIndexEq
      · subst outputLiteralIndex
        have outputLiteralLookup :=
          (List.mem_zipIdx_iff_getElem?).mp complementLiteralMember
        have outputLiteralEq :
            PeriodicOneInThreePolarityNormalization.complementFalseLiteral
                metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral =
              outputLiteral := by
          simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
            PeriodicOneInThreePolarityNormalization.complementClause] using
              outputLiteralLookup
        rw [← metadataClauseEq, complementClauseEq]
        rw [← outputLiteralEq]
        exact rawRouteForMetadata_complement_fresh_endpoints
          sourcePlacement presentation.routes metadata sourceLiteral
          sourceLiteralIndex originEq
      · subst outputLiteralIndex
        have outputLiteralLookup :=
          (List.mem_zipIdx_iff_getElem?).mp complementLiteralMember
        have outputLiteralEq :
            PeriodicOneInThreePolarityNormalization.originalFalseLiteral
                sourceLiteral = outputLiteral := by
          simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
            PeriodicOneInThreePolarityNormalization.complementClause] using
              outputLiteralLookup
        rw [← metadataClauseEq, complementClauseEq]
        rw [← outputLiteralEq]
        exact rawRouteForMetadata_complement_original_endpoints
          presentation metadata complementValid.1 sourceLiteral
          sourceLiteralIndex complementValid.2.1 originEq

/-- The assembled raw route table is orthogonal on every generated
incidence. -/
theorem rawIncidenceRoutes_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    ∀ outputClause outputClauseIndex,
      (outputClause, outputClauseIndex) ∈
          (rawFormula source sourcePlacement presentation.routes).clauses.zipIdx →
      ∀ outputLiteral outputLiteralIndex,
        (outputLiteral, outputLiteralIndex) ∈
            outputClause.literals.zipIdx →
        PeriodicOrthocrossing.OrthogonalPolyline
          (rawIncidenceRoutes source sourcePlacement presentation.routes
            outputClauseIndex outputLiteralIndex) := by
  intro outputClause outputClauseIndex outputClauseMember
    outputLiteral outputLiteralIndex outputLiteralMember
  have formulaClauseMember :
      (outputClause, outputClauseIndex) ∈
        (PeriodicOneInThreePolarityNormalizationPositioned.formula
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)).clauses.zipIdx := by
    simpa [rawFormula] using outputClauseMember
  rcases
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_lookup
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement) formulaClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEq⟩
  have rawMetadataLookup :
      (clauseMetadata source sourcePlacement presentation.routes)[outputClauseIndex]? =
        some metadata := by
    simpa [clauseMetadata] using metadataLookup
  rw [rawIncidenceRoutes_of_metadata_lookup
    source sourcePlacement presentation.routes metadata
    outputClauseIndex outputLiteralIndex rawMetadataLookup]
  have metadataIndexLt :
      outputClauseIndex <
        (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement)).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement))[outputClauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have sourceClauseMember :=
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_source_mem
      (rawPositions sourcePlacement presentation.routes)
      (refinedSource source sourcePlacement) metadataMember
  cases originEq : metadata.origin with
  | normalized =>
      have normalizedClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have normalizedLiteralMember :
          (outputLiteral, outputLiteralIndex) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause
              metadata.sourceClauseIndex metadata.sourceClause).literals.zipIdx := by
        rw [← normalizedClauseEq, metadataClauseEq]
        exact outputLiteralMember
      have normalizedLiteralLookup :
          (PeriodicOneInThreePolarityNormalization.normalizeClause
            metadata.sourceClauseIndex metadata.sourceClause.literals)[outputLiteralIndex]? =
              some outputLiteral := by
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause]
          using (List.mem_zipIdx_iff_getElem?).mp normalizedLiteralMember
      rw [PeriodicOneInThreePolarityNormalization.normalizeClause_getElem?]
          at normalizedLiteralLookup
      rcases Option.map_eq_some_iff.mp normalizedLiteralLookup with
        ⟨sourceLiteral, sourceLiteralLookup, _outputLiteralEq⟩
      have sourceLiteralMember :
          (sourceLiteral, outputLiteralIndex) ∈
            metadata.sourceClause.literals.zipIdx :=
        (List.mem_zipIdx_iff_getElem?).mpr sourceLiteralLookup
      exact rawRouteForMetadata_normalized_orthogonal
        presentation metadata sourceClauseMember sourceLiteral
        outputLiteralIndex sourceLiteralMember originEq
  | complement sourceLiteralIndex sourceLiteral =>
      have complementValid :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have complementClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) metadataMember originEq
      have complementLiteralMember :
          (outputLiteral, outputLiteralIndex) ∈
            (PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause
              (rawPositions sourcePlacement presentation.routes)
              metadata.sourceClauseIndex sourceLiteralIndex
              sourceLiteral).literals.zipIdx := by
        rw [← complementClauseEq, metadataClauseEq]
        exact outputLiteralMember
      have outputLiteralIndexLt : outputLiteralIndex < 2 := by
        have := List.snd_lt_of_mem_zipIdx complementLiteralMember
        simpa [PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause] using this
      have outputIndexCases :
          outputLiteralIndex = 0 ∨ outputLiteralIndex = 1 := by
        omega
      rcases outputIndexCases with outputIndexEq | outputIndexEq
      · subst outputLiteralIndex
        exact rawRouteForMetadata_complement_fresh_orthogonal
          presentation metadata complementValid.1 sourceLiteral
          sourceLiteralIndex complementValid.2.1 originEq
      · subst outputLiteralIndex
        exact rawRouteForMetadata_complement_original_orthogonal
          presentation metadata complementValid.1 sourceLiteral
          sourceLiteralIndex complementValid.2.1 originEq

/-- The raw split routes form one canonical orthogonal route family for the
ungauged positioned polarity normalization. -/
def rawRouteFamily
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes) where
  routes := rawIncidenceRoutes source sourcePlacement presentation.routes
  endpoints := rawIncidenceRoutes_endpoints presentation
  orthogonal := rawIncidenceRoutes_orthogonal presentation

/-- Threefold refinement preserves positivity of the physical period used by
the raw normalized drawing. -/
theorem rawPlacement_periodPositive
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    0 < (rawPlacement sourcePlacement presentation.routes).period := by
  rw [rawPlacement_period]
  change 0 < refinementFactor * sourcePlacement.period
  exact Nat.mul_pos refinementFactor_positive presentation.periodPositive

/-- Before the fresh-variable gauge, the assembled split routes match all
incidence-graph endpoints. -/
theorem rawIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      (rawIncidenceRoutes source sourcePlacement presentation.routes))
        |>.RoutesMatch
          (rawFormula source sourcePlacement presentation.routes).erase.incidenceGraph := by
  exact (rawRouteFamily presentation).routesMatch
    (rawPlacement_periodPositive presentation)

/-- Before the fresh-variable gauge, every assembled split route is
orthogonal. -/
theorem rawIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      (rawIncidenceRoutes source sourcePlacement presentation.routes))
        |>.IsOrthogonal := by
  exact (rawRouteFamily presentation).isOrthogonal

/-- Gauge transport gives the final normalized drawing the exact endpoints
of its gauged incidence graph. -/
theorem incidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.RoutesMatch
          (formula source sourcePlacement presentation.routes).erase.incidenceGraph := by
  simpa [formula, placement, incidenceRoutes] using
    PositionedPeriodicCNF.incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_routesMatch
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      freshGauge
      (rawIncidenceRoutes source sourcePlacement presentation.routes)
      (rawPlacement_periodPositive presentation)
      (rawIncidenceDrawing_routesMatch presentation)

/-- Gauge transport preserves orthogonality of every route in the final
normalized incidence drawing. -/
theorem incidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.IsOrthogonal := by
  simpa [formula, placement, incidenceRoutes] using
    PositionedPeriodicCNF.incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_isOrthogonal
      (rawFormula source sourcePlacement presentation.routes)
      (rawPlacement sourcePlacement presentation.routes)
      freshGauge
      (rawIncidenceRoutes source sourcePlacement presentation.routes)
      (rawIncidenceDrawing_isOrthogonal presentation)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
