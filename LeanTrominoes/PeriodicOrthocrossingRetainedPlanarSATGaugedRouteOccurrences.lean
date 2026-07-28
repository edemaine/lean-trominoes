import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteBounds
import LeanTrominoes.PositionedPeriodicCNFRouteOccurrenceNormalization

/-!
# Physical representatives of gauged retained route occurrences

The final retained periodic drawing is obtained from the finite retained
incidence drawing by variable gauging, clause-anchor normalization, and
first-representative clause deduplication.  This module reverses that
bookkeeping for one route occurrence.

Every translated final route is identified with a translated route of one
genuine incidence in the continuously planar finite retained drawing.  The
physical translation is exactly the requested periodic shift minus the
pre-normalization clause anchor.  This is the main quotient-to-finite route
interface used by periodic planarity.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- The gauged periodic clause attached to retained metadata immediately
before clause-anchor normalization. -/
def metadataGaugedPositionedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable Variable) :=
  ⟨metadata.clause.position,
    (wrapPeriodicPlanarSATClause
      (periodicizePlanarSATClause formula
        metadata.clause)).variableGauge
          (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
            formula)⟩

/-- The finite retained incidence named by metadata and a literal at the
same two presentation indices. -/
def metadataPhysicalIncidence
    {Variable : Type*}
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataIndex : Nat)
    (literal : PlanarSATVariable Variable × Bool)
    (literalIndex : Nat) :
    EmbeddedCNFIncidence (PlanarSATVariable Variable) :=
  ⟨metadata.clause, metadataIndex, literal, literalIndex⟩

/-- One translated occurrence of a route in the final periodic quotient. -/
def finalGaugedRouteOccurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (shift : Cell) : List Cell :=
  translatePolyline
    ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).translation shift)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula clauseIndex literalIndex)

/-- The corresponding anchor-adjusted occurrence of a physical finite
retained route. -/
def metadataPhysicalRouteOccurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataIndex : Nat)
    (literal : PlanarSATVariable Variable × Bool)
    (literalIndex : Nat)
    (shift : Cell) : List Cell :=
  translatePolyline
    ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).translation
      (Cell.sub shift
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula metadata).literals)))
    ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
      (metadataPhysicalIncidence
        metadata metadataIndex literal literalIndex))

/-- Metadata and literal lookups name a genuine incidence of the finite
retained drawing. -/
theorem metadataPhysicalIncidence_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataIndex : Nat)
    (literal : PlanarSATVariable Variable × Bool)
    (literalIndex : Nat)
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata
        formula)[metadataIndex]? = some metadata)
    (literalMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx) :
    metadataPhysicalIncidence
        metadata metadataIndex literal literalIndex ∈
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).incidences := by
  apply
    (mem_embeddedCNFIncidences_iff
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).formula
      (metadataPhysicalIncidence
        metadata metadataIndex literal literalIndex)).mpr
  change
    (metadata.clause, metadataIndex) ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).formula.zipIdx ∧
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx
  constructor
  · rw [
      retainedDrawingPlanarSATLocalIncidenceDrawing_formula,
      ← retainedDrawingPlanarSATClauseMetadata_clauses,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(metadata, metadataIndex),
        (List.mem_zipIdx_iff_getElem?).mpr metadataLookup,
        rfl⟩
  · exact literalMember

/-- Finite-drawing representative of one translated route in the final
periodic quotient. -/
structure FinalGaugedRouteOccurrenceWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (shift : Cell) where
  metadata : DrawingPlanarSATClauseMetadata Variable
  metadataIndex : Nat
  metadataLookup :
    (retainedDrawingPlanarSATClauseMetadata
      formula)[metadataIndex]? = some metadata
  literal : PlanarSATVariable Variable × Bool
  literalMember :
    (literal, literalIndex) ∈ metadata.clause.literals.zipIdx
  incidenceMember :
    metadataPhysicalIncidence
        metadata metadataIndex literal literalIndex ∈
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).incidences
  routeEq :
    finalGaugedRouteOccurrence
        formula clauseIndex literalIndex shift =
      metadataPhysicalRouteOccurrence
        formula metadata metadataIndex literal literalIndex shift

/-- Every genuine final route occurrence comes from one genuine incidence
of the finite retained drawing.  Its physical lattice shift is the final
shift minus the anchor of that incidence's gauged periodic clause. -/
theorem
    exists_retainedPhysicalIncidence_of_finalRouteOccurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (taggedClause :
      PositionedPeriodicClause
          (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (taggedClauseMember :
      taggedClause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    (taggedLiteral :
      PeriodicLiteral
          (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (taggedLiteralMember :
      taggedLiteral ∈ taggedClause.1.literals.zipIdx)
    (shift : Cell) :
    Nonempty
      (FinalGaugedRouteOccurrenceWitness
        formula taggedClause.2 taggedLiteral.2 shift) := by
  let retainedClause := taggedClause.1
  let clauseIndex := taggedClause.2
  let literalIndex := taggedLiteral.2
  have retainedClauseMember :
      retainedClause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses :=
    List.fst_mem_of_mem_zipIdx taggedClauseMember
  have retainedClauseLookup :
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[clauseIndex]? =
          some retainedClause :=
    (List.mem_zipIdx_iff_getElem?).mp taggedClauseMember
  let source :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  have retainedClauseMember' :
      retainedClause ∈ source.deduplicateByLiterals.clauses := by
    simpa only [source,
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using retainedClauseMember
  rcases
      exists_representativeClause_of_mem_deduplicateByLiterals
        source retainedClause retainedClauseMember' with
    ⟨sourceClause, sourceClauseLookup,
      sourceClauseLiterals⟩
  have sourceClausesEq :
      source.clauses =
        (retainedDrawingPlanarSATClauseMetadata formula).map
          (fun metadata =>
            (⟨clauseResidue formula metadata.clause,
              metadataGaugedNormalizedClause formula metadata⟩ :
              PositionedPeriodicClause
                (WrappedPeriodicPlanarSATVariable Variable))) := by
    simpa [source] using
      anchorNormalized_clauses_eq_metadata
        formula wellFormed degree isLocal clausesNonempty
  rw [sourceClausesEq, List.getElem?_map] at sourceClauseLookup
  rcases Option.map_eq_some_iff.mp sourceClauseLookup with
    ⟨metadata, metadataLookup, sourceClauseEq⟩
  let metadataIndex :=
    source.representativeClauseIndex retainedClause.literals
  have metadataLookup' :
      (retainedDrawingPlanarSATClauseMetadata
        formula)[metadataIndex]? = some metadata := by
    simpa only [metadataIndex] using metadataLookup
  have literalIndexLt :
      literalIndex < metadata.clause.literals.length := by
    have retainedLiteralIndexLt :=
      List.snd_lt_of_mem_zipIdx taggedLiteralMember
    change
      taggedLiteral.2 < metadata.clause.literals.length
    change
      taggedLiteral.2 < retainedClause.literals.length
      at retainedLiteralIndexLt
    rw [← sourceClauseLiterals,
      ← sourceClauseEq] at retainedLiteralIndexLt
    simpa [metadataGaugedNormalizedClause,
      wrapPeriodicPlanarSATClause,
      periodicizePlanarSATClause] using retainedLiteralIndexLt
  let literal := metadata.clause.literals[literalIndex]
  have literalMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx :=
    (List.mem_zipIdx_iff_getElem?).mpr
      (by simp [literal, literalIndexLt])
  let incidence : EmbeddedCNFIncidence
      (PlanarSATVariable Variable) :=
    metadataPhysicalIncidence
      metadata metadataIndex literal literalIndex
  have incidenceMember :
      incidence ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).incidences := by
    exact
      metadataPhysicalIncidence_mem
        formula metadata metadataIndex literal literalIndex
        metadataLookup' literalMember
  have anchorZero :
      PeriodicCNF.clauseAnchor retainedClause.literals = (0, 0) := by
    apply clauseAnchor_eq_zero_of_mem_deduplicate_anchorNormalize
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      retainedClause
    simpa only [
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
      retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using retainedClauseMember
  have outerRouteEq :
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex literalIndex =
        PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
          (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
          metadataIndex literalIndex := by
    apply
      PositionedPeriodicCNF.deduplicatedIncidenceRoutes_eq_sourceRoute_of_anchor_zero
        source
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
          (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          (retainedDrawingPlanarSATLocalIncidenceRoutes formula))
        retainedClauseLookup anchorZero literalIndex
  have gaugedClauseLookup :
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[metadataIndex]? =
          some (metadataGaugedPositionedClause formula metadata) := by
    rw [gauged_clauses_eq_metadata formula,
      List.getElem?_map, metadataLookup]
    rfl
  have translatedInner :=
    PositionedPeriodicCNF.translatePolyline_anchorNormalizedIncidenceRoutes
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
      gaugedClauseLookup literalIndex shift
  have localRouteEq :
      retainedDrawingPlanarSATLocalIncidenceRoutes
          formula metadataIndex literalIndex =
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).routeAt incidence := by
    simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      incidence, metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt]
  refine ⟨{
    metadata := metadata
    metadataIndex := metadataIndex
    metadataLookup := metadataLookup'
    literal := literal
    literalMember := literalMember
    incidenceMember := incidenceMember
    routeEq := ?_
  }⟩
  unfold finalGaugedRouteOccurrence
    metadataPhysicalRouteOccurrence
  change
    translatePolyline
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation shift)
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex literalIndex) =
      _
  rw [outerRouteEq]
  exact translatedInner.trans
    (congrArg
      (translatePolyline
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation
          (Cell.sub shift
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause
                formula metadata).literals))))
      localRouteEq)

end PeriodicOrthocrossing
end LeanTrominoes
