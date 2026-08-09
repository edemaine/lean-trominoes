import LeanTrominoes.OrthogonalPolylineUnitSubdivisionScaling
import LeanTrominoes.PeriodicOneInThreeAnchorNormalization
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedIndex
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing
import LeanTrominoes.PositionedPeriodicCNFScaling
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeOneInThree
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeRouteOrders

/-!
# Route subdivision data for positioned polarity normalization

The source drawing is first anchor-normalized and refined by a factor of
three.  Unit subdivision then supplies two lattice points immediately after
each clause endpoint.  They become, respectively, the fresh complement
variable and the binary complement clause.

The logical normalization initially stores a fresh literal at the source
literal's offset.  A per-fresh-variable gauge moves that offset to zero while
moving its physical prototype position onto the selected route point.  Thus
the gauged incidence path follows the old route in the order

`source clause -- fresh variable -- complement clause -- original variable`.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Short name for the occurrence tags used by this route layer. -/
abbrev FreshOccurrence (Variable : Type*) :=
  PeriodicOneInThreePolarityNormalizationPositioned.FreshOccurrence Variable

/-- Threefold refinement leaves room for two new unit-spaced vertices on
the first segment of every genuine incidence route. -/
def refinementFactor : Nat := 3

theorem refinementFactor_positive : 0 < refinementFactor := by
  decide

/-- Anchor-normalized, uniformly refined positioned source. -/
def refinedSource {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF Variable :=
  (source.anchorNormalize placement).scale refinementFactor

/-- Uniformly refined source placement. -/
def refinedPlacement {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement Variable :=
  placement.scale refinementFactor

/-- Unit subdivision of one uniformly refined source incidence route. -/
def refinedRoute
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) : List Cell :=
  AxisDirection.unitSubdividePolyline
    (scalePolyline refinementFactor
      (routes clauseIndex literalIndex))

/-- One selected point of the refined route, with an irrelevant default for
indices outside the finite source presentation. -/
def routePoint {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fresh : FreshOccurrence Variable)
    (pointIndex : Nat) : Cell :=
  (refinedRoute routes fresh.1.1 fresh.1.2).getD
    pointIndex (0, 0)

/-- Raw positions before the fresh-variable gauge is applied.  Subtracting
the literal translation makes the raw occurrence endpoint equal `routePoint
1`; the gauge below subsequently moves the stored prototype itself there. -/
def rawPositions {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable where
  freshVariable := fun fresh =>
    Cell.sub (routePoint routes fresh 1)
      ((refinedPlacement placement).translation fresh.2.offset)
  complementClause := fun fresh =>
    routePoint routes fresh 2

/-- Gauge only fresh complement variables, subtracting their retained source
literal offset. -/
def freshGauge {Variable : Type*} :
    PolarityNormalizedVariable Variable → Cell
  | Sum.inl _ => (0, 0)
  | Sum.inr fresh => Cell.sub (0, 0) fresh.2.offset

/-- Positioned normalized formula after moving every fresh variable to its
selected route point, before applying the fresh-variable gauge. -/
def rawFormula {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF (PolarityNormalizedVariable Variable) :=
  PeriodicOneInThreePolarityNormalizationPositioned.formula
    (rawPositions placement routes)
    (refinedSource source placement)

/-- Placement parallel to `rawFormula`, before gauging fresh variables. -/
def rawPlacement {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PeriodicVariablePlacement (PolarityNormalizedVariable Variable) :=
  PeriodicOneInThreePolarityNormalizationPositioned.placement
    (refinedPlacement sourcePlacement)
    (rawPositions sourcePlacement routes)

/-- Positioned normalized formula after moving every fresh variable to its
selected route point. -/
def formula {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF (PolarityNormalizedVariable Variable) :=
  (rawFormula source placement routes).variableGauge freshGauge

/-- Placement parallel to `formula`. -/
def placement {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PeriodicVariablePlacement (PolarityNormalizedVariable Variable) :=
  (rawPlacement sourcePlacement routes).variableGauge freshGauge

/-- Translate a displayed source occurrence back to the canonical cell of
its binary complement clause.  Both literals of the raw binary clause have
the same source offset, so this is precisely the clause-anchor correction. -/
def complementCanonicalShift {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceLiteral : PeriodicLiteral Variable) : Cell :=
  Cell.sub (0, 0)
    ((refinedPlacement sourcePlacement).translation sourceLiteral.offset)

/-- Clause-origin metadata parallel to `rawFormula`. -/
def clauseMetadata {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :=
  PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
    (rawPositions sourcePlacement sourceRoutes)
    (refinedSource source sourcePlacement)

/-- Forgetting route-splitting metadata recovers the complete ungauged
positioned formula. -/
@[simp]
theorem clauseMetadata_clauses {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    (clauseMetadata source sourcePlacement sourceRoutes).map
        PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata.clause =
      (rawFormula source sourcePlacement sourceRoutes).clauses := by
  simp [clauseMetadata, rawFormula]

/-- Select the canonical raw route for one metadata-classified output
incidence.  Compatible main incidences keep the whole refined source route.
An incompatible incidence is split into its first edge, reversed middle
edge, and remaining suffix.  The two complement-clause routes receive the
common source-offset translation required by that clause's canonical
anchor. -/
def rawRouteForMetadata {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (literalIndex : Nat) : List Cell :=
  match metadata.origin with
  | .normalized =>
      match metadata.sourceClause.literals[literalIndex]? with
      | none => []
      | some sourceLiteral =>
          if sourceLiteral.value =
              PeriodicOneInThreePolarityNormalization.normalizedPolarity
                literalIndex then
            refinedRoute sourceRoutes metadata.sourceClauseIndex literalIndex
          else
            (refinedRoute sourceRoutes metadata.sourceClauseIndex
              literalIndex).take 2
  | .complement sourceLiteralIndex sourceLiteral =>
      if literalIndex = 0 then
        PeriodicOrthocrossing.translatePolyline
          (complementCanonicalShift sourcePlacement sourceLiteral)
          ((refinedRoute sourceRoutes metadata.sourceClauseIndex
            sourceLiteralIndex).drop 2)
      else if literalIndex = 1 then
        PeriodicOrthocrossing.translatePolyline
          (complementCanonicalShift sourcePlacement sourceLiteral)
          [routePoint sourceRoutes
              ((metadata.sourceClauseIndex, sourceLiteralIndex),
                sourceLiteral) 2,
            routePoint sourceRoutes
              ((metadata.sourceClauseIndex, sourceLiteralIndex),
                sourceLiteral) 1]
      else
        []

/-- Raw incidence routes parallel to the ungauged positioned normalization.
The flattened clause lookup is total outside the finite formula. -/
def rawIncidenceRoutes {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match (clauseMetadata source sourcePlacement sourceRoutes)[clauseIndex]? with
    | none => []
    | some metadata =>
        rawRouteForMetadata sourcePlacement sourceRoutes metadata literalIndex

/-- Final route family after transporting every split raw route through the
fresh-variable gauge. -/
def incidenceRoutes {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes
    (rawFormula source sourcePlacement sourceRoutes)
    (rawPlacement sourcePlacement sourceRoutes)
    freshGauge
    (rawIncidenceRoutes source sourcePlacement sourceRoutes)

/-- A successful output-clause metadata lookup exposes the selected raw
route definitionally. -/
theorem rawIncidenceRoutes_of_metadata_lookup {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (clauseIndex literalIndex : Nat)
    (metadataLookup :
      (clauseMetadata source sourcePlacement sourceRoutes)[clauseIndex]? =
        some metadata) :
    rawIncidenceRoutes source sourcePlacement sourceRoutes
        clauseIndex literalIndex =
      rawRouteForMetadata sourcePlacement sourceRoutes metadata
        literalIndex := by
  simp [rawIncidenceRoutes, metadataLookup]

/-- A compatible main incidence retains its entire refined source route. -/
theorem rawRouteForMetadata_normalized_compatible {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (literalIndex : Nat)
    (originEq : metadata.origin = .normalized)
    (literalLookup :
      metadata.sourceClause.literals[literalIndex]? = some sourceLiteral)
    (compatible :
      sourceLiteral.value =
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          literalIndex) :
    rawRouteForMetadata sourcePlacement sourceRoutes metadata literalIndex =
      refinedRoute sourceRoutes metadata.sourceClauseIndex literalIndex := by
  simp [rawRouteForMetadata, originEq, literalLookup, compatible]

/-- An incompatible main incidence keeps exactly the clause-side first
edge of its refined source route. -/
theorem rawRouteForMetadata_normalized_incompatible {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (literalIndex : Nat)
    (originEq : metadata.origin = .normalized)
    (literalLookup :
      metadata.sourceClause.literals[literalIndex]? = some sourceLiteral)
    (incompatible :
      sourceLiteral.value ≠
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          literalIndex) :
    rawRouteForMetadata sourcePlacement sourceRoutes metadata literalIndex =
      (refinedRoute sourceRoutes metadata.sourceClauseIndex
        literalIndex).take 2 := by
  simp [rawRouteForMetadata, originEq, literalLookup, incompatible]

/-- The first binary-clause incidence is the translated suffix leading to
the original variable. -/
theorem rawRouteForMetadata_complement_original {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    rawRouteForMetadata sourcePlacement sourceRoutes metadata 0 =
      PeriodicOrthocrossing.translatePolyline
        (complementCanonicalShift sourcePlacement sourceLiteral)
        ((refinedRoute sourceRoutes metadata.sourceClauseIndex
          sourceLiteralIndex).drop 2) := by
  simp [rawRouteForMetadata, originEq]

/-- The second binary-clause incidence is the translated reverse middle
edge leading to the fresh complement variable. -/
theorem rawRouteForMetadata_complement_fresh {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    rawRouteForMetadata sourcePlacement sourceRoutes metadata 1 =
      PeriodicOrthocrossing.translatePolyline
        (complementCanonicalShift sourcePlacement sourceLiteral)
        [routePoint sourceRoutes
            ((metadata.sourceClauseIndex, sourceLiteralIndex), sourceLiteral) 2,
          routePoint sourceRoutes
            ((metadata.sourceClauseIndex, sourceLiteralIndex), sourceLiteral) 1] := by
  simp [rawRouteForMetadata, originEq]

/-- At a genuine raw output clause, final routes are exactly the split raw
routes translated by the canonical fresh-variable gauge shift. -/
theorem incidenceRoutes_of_raw_clause_mem {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    {rawClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {clauseIndex literalIndex : Nat}
    (clauseMember :
      (rawClause, clauseIndex) ∈
        (rawFormula source sourcePlacement sourceRoutes).clauses.zipIdx) :
    incidenceRoutes source sourcePlacement sourceRoutes
        clauseIndex literalIndex =
      PeriodicOrthocrossing.translatePolyline
        ((rawPlacement sourcePlacement sourceRoutes).translation
          (PositionedPeriodicCNF.variableGaugeCanonicalRouteShift
            freshGauge rawClause))
        (rawIncidenceRoutes source sourcePlacement sourceRoutes
          clauseIndex literalIndex) := by
  exact
    PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      (rawFormula source sourcePlacement sourceRoutes)
      (rawPlacement sourcePlacement sourceRoutes)
      freshGauge
      (rawIncidenceRoutes source sourcePlacement sourceRoutes)
      clauseMember

/-- Threefold scaling multiplies the Manhattan length of an axis segment by
three. -/
@[simp]
theorem segmentLength_scale_three (first second : Cell) :
    AxisDirection.segmentLength
        (Cell.scale refinementFactor first)
        (Cell.scale refinementFactor second) =
      refinementFactor * AxisDirection.segmentLength first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [refinementFactor, AxisDirection.segmentLength, Cell.scale]
  have horizontal :
      3 * secondX - 3 * firstX = 3 * (secondX - firstX) := by
    ring
  have vertical :
      3 * secondY - 3 * firstY = 3 * (secondY - firstY) := by
    ring
  norm_num
  rw [horizontal, vertical, Int.natAbs_mul, Int.natAbs_mul]
  simp
  omega

/-- Every genuine orthogonal source route yields at least the four points
needed for its two inserted subdivision vertices. -/
theorem refinedRoute_length_ge_four
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (length : 2 ≤ (routes clauseIndex literalIndex).length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (routes clauseIndex literalIndex)) :
    4 ≤ (refinedRoute routes clauseIndex literalIndex).length := by
  unfold refinedRoute
  generalize routeEq : routes clauseIndex literalIndex = route at length orthogonal ⊢
  cases route with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second tail =>
          have aligned :
              (GridSegment.mk first second).IsAxisAligned :=
            (List.isChain_cons_cons.mp orthogonal).1
          have positive :
              0 < AxisDirection.segmentLength first second :=
            AxisDirection.segmentLength_positive_of_axisAligned aligned
          have scaledLength :
              AxisDirection.segmentLength
                  (Cell.scale 3 first) (Cell.scale 3 second) =
                3 * AxisDirection.segmentLength first second := by
            simpa [refinementFactor] using
              segmentLength_scale_three first second
          simp only [scalePolyline_cons]
          change 4 ≤
            (AxisDirection.unitSubdividePolyline
              (Cell.scale 3 first :: Cell.scale 3 second ::
                scalePolyline 3 tail)).length
          rw [AxisDirection.unitSubdividePolyline]
          simp [LeanTrominoes.joinAtEndpoint, scaledLength]
          omega

/-- Original variables retain their uniformly scaled source positions after
the fresh-only gauge. -/
@[simp]
theorem placement_original_position {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (placement sourcePlacement routes).position (Sum.inl atom) =
      (refinedPlacement sourcePlacement).position atom := by
  simp [placement, rawPlacement, freshGauge,
    PeriodicVariablePlacement.variableGauge,
    PeriodicOneInThreePolarityNormalizationPositioned.placement,
    PeriodicVariablePlacement.translation, Cell.scale, Cell.sub]

/-- After gauging, a fresh complement prototype is exactly the first selected
interior point of its refined source route. -/
@[simp]
theorem placement_fresh_position {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fresh : FreshOccurrence Variable) :
    (placement sourcePlacement routes).position (Sum.inr fresh) =
      routePoint routes fresh 1 := by
  generalize pointEq : routePoint routes fresh 1 = point
  rcases point with ⟨pointX, pointY⟩
  simp [placement, rawPlacement, rawPositions, freshGauge,
    PeriodicOneInThreePolarityNormalizationPositioned.placement,
    PeriodicVariablePlacement.variableGauge,
    PeriodicVariablePlacement.translation,
    Cell.sub, Cell.scale, pointEq]

/-- Fresh literals whose raw offset is the retained source offset acquire
zero offset under the route-subdivision gauge. -/
theorem freshLiteral_variableGauge_offset_zero {Variable : Type*}
    (fresh : FreshOccurrence Variable)
    (value : Bool) :
    (PeriodicLiteral.variableGauge freshGauge
      (PeriodicLiteral.mk (Sum.inr fresh) fresh.2.offset value)).offset =
        (0, 0) := by
  rcases fresh with ⟨indices, literal⟩
  rcases literal with ⟨atom, ⟨offsetX, offsetY⟩, sourceValue⟩
  simp [PeriodicLiteral.variableGauge, freshGauge,
    Cell.add, Cell.sub]

/-- Erasing positions exposes exactly the logical polarity normalization of
the refined anchor-normalized source, followed by the fresh-variable gauge. -/
@[simp]
theorem erase_formula {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (formula source sourcePlacement routes).erase =
      (PeriodicOneInThreePolarityNormalization.formula
        (refinedSource source sourcePlacement).erase).variableGauge
          freshGauge := by
  simp [formula, rawFormula,
    PositionedPeriodicCNF.erase_variableGauge]

/-- Route-subdivision polarity normalization preserves exact-one
satisfiability all the way back to the unrefined positioned source. -/
theorem satisfiable_iff {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PeriodicOneInThree.Satisfiable
        (formula source sourcePlacement routes).erase ↔
      PeriodicOneInThree.Satisfiable source.erase := by
  rw [erase_formula,
    PeriodicOneInThree.variableGauge_satisfiable_iff,
    PeriodicOneInThreePolarityNormalization.satisfiable_iff]
  simpa [refinedSource] using
    PeriodicOneInThree.anchorNormalize_satisfiable_iff source.erase

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
