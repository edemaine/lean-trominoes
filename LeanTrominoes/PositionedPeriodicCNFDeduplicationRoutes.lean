import LeanTrominoes.PositionedPeriodicCNFDeduplication
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalization
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Incidence routes through positioned clause deduplication

Clause-orbit deduplication retains the first positioned representative of
each periodic literal list.  Geometric routes, however, are naturally
indexed by the original finite embedded formula.

This file reconnects those indices.  A retained clause selects its first
source index, reuses the source route at the same literal index, and
subtracts the retained clause anchor from every route point.  The resulting
route has exactly the canonical clause and translated-variable endpoints
required by the periodic incidence graph.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A raw route family meets the displayed positioned clause and literal
occurrence before the clause anchor is normalized. -/
def PhysicalIncidenceRoutesMatch
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : Prop :=
  ∀ positionedClause clauseIndex,
    (positionedClause, clauseIndex) ∈ source.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈
            positionedClause.literals.zipIdx →
          (routes clauseIndex literalIndex).head? =
              some positionedClause.position ∧
            (routes clauseIndex literalIndex).getLast? =
              some (placement.literalPosition literal)

/-- Renaming positioned variables preserves raw physical route endpoints
when the target placement assigns every renamed variable the same point. -/
theorem PhysicalIncidenceRoutesMatch.rename
    {Source Target : Type*}
    (source : PositionedPeriodicCNF Source)
    (sourcePlacement : PeriodicVariablePlacement Source)
    (targetPlacement : PeriodicVariablePlacement Target)
    (routes : IncidenceRoutes)
    (variableMap : Source → Target)
    (routesMatch :
      source.PhysicalIncidenceRoutesMatch
        sourcePlacement routes)
    (positionsMatch :
      ∀ atom,
        targetPlacement.position (variableMap atom) =
          sourcePlacement.position atom)
    (periodsMatch :
      targetPlacement.period = sourcePlacement.period) :
    (source.rename variableMap).PhysicalIncidenceRoutesMatch
      targetPlacement routes := by
  intro targetClause clauseIndex targetClauseMember
    targetLiteral literalIndex targetLiteralMember
  change
    (targetClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨clause.position, clause.literals.map fun literal =>
          ⟨variableMap literal.atom,
            literal.offset, literal.value⟩⟩).zipIdx
    at targetClauseMember
  rw [List.zipIdx_map] at targetClauseMember
  rcases List.mem_map.mp targetClauseMember with
    ⟨taggedSourceClause, taggedSourceClauseMember,
      targetClauseEqual⟩
  have sourceClauseMember :
      (taggedSourceClause.1, taggedSourceClause.2) ∈
        source.clauses.zipIdx :=
    taggedSourceClauseMember
  have clauseIndexEqual :
      taggedSourceClause.2 = clauseIndex :=
    congrArg Prod.snd targetClauseEqual
  have targetClauseValueEqual :
      targetClause =
        ⟨taggedSourceClause.1.position,
          taggedSourceClause.1.literals.map fun literal =>
            ⟨variableMap literal.atom,
              literal.offset, literal.value⟩⟩ := by
    exact (congrArg Prod.fst targetClauseEqual).symm
  subst clauseIndex
  subst targetClause
  change
    (targetLiteral, literalIndex) ∈
      (taggedSourceClause.1.literals.map fun literal =>
        ⟨variableMap literal.atom,
          literal.offset, literal.value⟩).zipIdx
    at targetLiteralMember
  rw [List.zipIdx_map] at targetLiteralMember
  rcases List.mem_map.mp targetLiteralMember with
    ⟨taggedSourceLiteral, taggedSourceLiteralMember,
      targetLiteralEqual⟩
  have literalIndexEqual :
      taggedSourceLiteral.2 = literalIndex :=
    congrArg Prod.snd targetLiteralEqual
  have targetLiteralValueEqual :
      targetLiteral =
        ⟨variableMap taggedSourceLiteral.1.atom,
          taggedSourceLiteral.1.offset,
          taggedSourceLiteral.1.value⟩ := by
    exact (congrArg Prod.fst targetLiteralEqual).symm
  subst literalIndex
  subst targetLiteral
  have endpoints :=
    routesMatch taggedSourceClause.1 taggedSourceClause.2
      sourceClauseMember taggedSourceLiteral.1
      taggedSourceLiteral.2 taggedSourceLiteralMember
  refine ⟨endpoints.1, ?_⟩
  rw [endpoints.2]
  apply congrArg some
  simp [PeriodicVariablePlacement.literalPosition,
    PeriodicVariablePlacement.translation,
    positionsMatch, periodsMatch]

/-- Translate a displayed physical route into the canonical clause-anchor
gauge of the periodic incidence graph. -/
def normalizeIncidenceRoute
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (route : List Cell) : List Cell :=
  route.map fun point =>
    Cell.sub point
      (placement.translation
        (PeriodicCNF.clauseAnchor clause.literals))

/-- Normalization sends a displayed clause endpoint to its canonical
prototype position. -/
theorem normalizeIncidenceRoute_head?
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (route : List Cell)
    (routeHead : route.head? = some clause.position) :
    (normalizeIncidenceRoute placement clause route).head? =
      some (canonicalClausePosition placement clause) := by
  simp [normalizeIncidenceRoute, routeHead,
    canonicalClausePosition]

/-- Normalization subtracts the common clause anchor from a literal
occurrence's periodic offset. -/
theorem normalizeIncidenceRoute_getLast?
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (route : List Cell)
    (routeLast :
      route.getLast? =
        some (placement.literalPosition literal)) :
    (normalizeIncidenceRoute placement clause route).getLast? =
      some
        (Cell.add
          (placement.position literal.atom)
          (placement.translation
            (Cell.sub literal.offset
              (PeriodicCNF.clauseAnchor clause.literals)))) := by
  simp only [normalizeIncidenceRoute,
    List.getLast?_map, routeLast, Option.map_some]
  apply congrArg some
  apply Prod.ext <;>
  simp [PeriodicVariablePlacement.literalPosition,
    PeriodicVariablePlacement.translation,
    Cell.add, Cell.sub, Cell.scale] <;>
  ring

/-- Translating a displayed route into the periodic clause-anchor gauge
preserves axis alignment of every segment. -/
theorem normalizeIncidenceRoute_orthogonal
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (route : List Cell)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (normalizeIncidenceRoute placement clause route) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline at orthogonal ⊢
  unfold normalizeIncidenceRoute
  apply List.isChain_map_of_isChain
    (fun point =>
      Cell.sub point
        (placement.translation
          (PeriodicCNF.clauseAnchor clause.literals)))
  · intro first second aligned
    let offset :=
      placement.translation
        (PeriodicCNF.clauseAnchor clause.literals)
    have translated :=
      (GridSegment.isAxisAligned_translate
        (GridSegment.mk first second)
        (Cell.scale (-1) offset)).mpr aligned
    simpa [GridSegment.translate, Cell.add,
      Cell.sub, Cell.scale, offset, sub_eq_add_neg,
      add_comm] using translated
  · exact orthogonal

/-- Normalize every raw physical route by the anchor of the source clause at
the same index.  This is the route family naturally indexed by the
anchor-normalized positioned formula. -/
def anchorNormalizedIncidenceRoutes
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        normalizeIncidenceRoute placement clause
          (routes clauseIndex literalIndex)

/-- Normalizing both a positioned formula and its raw route family preserves
the physical endpoint condition. -/
theorem anchorNormalizedIncidenceRoutes_physicalRoutesMatch
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (routesMatch :
      source.PhysicalIncidenceRoutesMatch placement routes) :
    (source.anchorNormalize placement).PhysicalIncidenceRoutesMatch
      placement
      (source.anchorNormalizedIncidenceRoutes placement routes) := by
  intro normalizedClause clauseIndex normalizedClauseMember
    normalizedLiteral literalIndex normalizedLiteralMember
  change
    (normalizedClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨canonicalClausePosition placement clause,
          clause.literals.anchorNormalize⟩).zipIdx
    at normalizedClauseMember
  rw [List.zipIdx_map] at normalizedClauseMember
  rcases List.mem_map.mp normalizedClauseMember with
    ⟨taggedClause, taggedClauseMember, normalizedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd normalizedClauseEqual
  have normalizedClauseValueEqual :
      normalizedClause =
        ⟨canonicalClausePosition placement taggedClause.1,
          taggedClause.1.literals.anchorNormalize⟩ := by
    exact (congrArg Prod.fst normalizedClauseEqual).symm
  subst clauseIndex
  subst normalizedClause
  change
    (normalizedLiteral, literalIndex) ∈
      (taggedClause.1.literals.map
        (PeriodicLiteral.anchorNormalize
          (PeriodicCNF.clauseAnchor
            taggedClause.1.literals))).zipIdx
    at normalizedLiteralMember
  rw [List.zipIdx_map] at normalizedLiteralMember
  rcases List.mem_map.mp normalizedLiteralMember with
    ⟨taggedLiteral, taggedLiteralMember,
      normalizedLiteralEqual⟩
  have literalIndexEqual :
      taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd normalizedLiteralEqual
  have normalizedLiteralValueEqual :
      normalizedLiteral =
        taggedLiteral.1.anchorNormalize
          (PeriodicCNF.clauseAnchor
            taggedClause.1.literals) := by
    exact (congrArg Prod.fst normalizedLiteralEqual).symm
  subst literalIndex
  subst normalizedLiteral
  have sourceClauseLookup :
      source.clauses[taggedClause.2]? =
        some taggedClause.1 :=
    (List.mem_zipIdx_iff_getElem?).mp taggedClauseMember
  have rawEndpoints :=
    routesMatch taggedClause.1 taggedClause.2
      taggedClauseMember taggedLiteral.1 taggedLiteral.2
      taggedLiteralMember
  constructor
  · simpa [anchorNormalizedIncidenceRoutes,
      sourceClauseLookup] using
        normalizeIncidenceRoute_head?
          placement taggedClause.1
          (routes taggedClause.2 taggedLiteral.2)
          rawEndpoints.1
  · simpa [anchorNormalizedIncidenceRoutes,
      sourceClauseLookup,
      PeriodicVariablePlacement.literalPosition] using
        normalizeIncidenceRoute_getLast?
          placement taggedClause.1 taggedLiteral.1
          (routes taggedClause.2 taggedLiteral.2)
          rawEndpoints.2

/-- The first source clause carrying a given erased literal list. -/
def representativeClauseIndex
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clause : PeriodicClause Variable) : Nat :=
  source.erase.clauses.idxOf clause

/-- Every retained literal list retrieves an original positioned
representative at its declared first-source index. -/
theorem exists_representativeClause
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clause : PeriodicClause Variable)
    (clauseMember : clause ∈ source.erase.clauses) :
    ∃ positionedClause : PositionedPeriodicClause Variable,
      source.clauses[
          source.representativeClauseIndex clause]? =
        some positionedClause ∧
      positionedClause.literals = clause ∧
      positionedClause.position =
        source.representativeClausePosition clause := by
  have indexLt :
      source.representativeClauseIndex clause <
        source.clauses.length := by
    rw [representativeClauseIndex]
    have erasedIndexLt :
        source.erase.clauses.idxOf clause <
          source.erase.clauses.length :=
      List.idxOf_lt_length_iff.mpr clauseMember
    simpa [erase] using erasedIndexLt
  let positionedClause :=
    source.clauses[
      source.representativeClauseIndex clause]
  have positionedLookup :
      source.clauses[
          source.representativeClauseIndex clause]? =
        some positionedClause := by
    exact List.getElem?_eq_getElem indexLt
  have erasedLookup :
      source.erase.clauses[
          source.representativeClauseIndex clause]? =
        some clause := by
    exact List.getElem?_idxOf clauseMember
  have literalsEqual :
      positionedClause.literals = clause := by
    simpa [erase, positionedClause,
      List.getElem?_eq_getElem indexLt] using erasedLookup
  refine
    ⟨positionedClause, positionedLookup, literalsEqual, ?_⟩
  change positionedClause.position =
    (source.clauses[
        source.representativeClauseIndex clause]?.map
      PositionedPeriodicClause.position).getD (0, 0)
  rw [positionedLookup]
  rfl

/-- If a source clause position determines its erased literal list, then
retaining the first representative of each literal list also retains
pairwise-distinct clause positions. -/
theorem deduplicateByLiterals_clausePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePositionDeterminesLiterals :
      ∀ first ∈ source.clauses, ∀ second ∈ source.clauses,
        first.position = second.position →
          first.literals = second.literals) :
    (source.deduplicateByLiterals.clauses.map
      PositionedPeriodicClause.position).Nodup := by
  rw [deduplicateByLiterals, List.map_map]
  apply source.erase.clauses.nodup_dedup.map_on
  intro first firstMember second secondMember positionEqual
  have firstSourceMember : first ∈ source.erase.clauses :=
    by simpa using firstMember
  have secondSourceMember : second ∈ source.erase.clauses :=
    by simpa using secondMember
  rcases exists_representativeClause source first firstSourceMember with
    ⟨firstClause, firstLookup, firstLiterals, firstPosition⟩
  rcases exists_representativeClause source second secondSourceMember with
    ⟨secondClause, secondLookup, secondLiterals, secondPosition⟩
  have firstClauseMember : firstClause ∈ source.clauses := by
    exact List.mem_iff_getElem.mpr
      ⟨source.representativeClauseIndex first,
        (List.getElem?_eq_some_iff.mp firstLookup).1,
        (List.getElem?_eq_some_iff.mp firstLookup).2⟩
  have secondClauseMember : secondClause ∈ source.clauses := by
    exact List.mem_iff_getElem.mpr
      ⟨source.representativeClauseIndex second,
        (List.getElem?_eq_some_iff.mp secondLookup).1,
        (List.getElem?_eq_some_iff.mp secondLookup).2⟩
  have clausesEqual :=
    sourcePositionDeterminesLiterals
      firstClause firstClauseMember secondClause secondClauseMember
      (firstPosition.trans (positionEqual.trans secondPosition.symm))
  exact firstLiterals.symm.trans
    (clausesEqual.trans secondLiterals)

/-- A retained positioned clause has the representative position prescribed
by its erased literal list. -/
theorem eq_representative_of_mem_deduplicateByLiterals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clause : PositionedPeriodicClause Variable)
    (clauseMember :
      clause ∈ source.deduplicateByLiterals.clauses) :
    clause =
      ⟨source.representativeClausePosition clause.literals,
        clause.literals⟩ := by
  simp only [deduplicateByLiterals, List.mem_map] at clauseMember
  rcases clauseMember with
    ⟨literals, literalsMember, clauseEqual⟩
  rw [← clauseEqual]

/-- Reindex a raw source route family through clause-orbit deduplication and
put every retained route in the canonical clause-anchor gauge. -/
def deduplicatedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match source.deduplicateByLiterals.clauses[clauseIndex]? with
    | none => []
    | some clause =>
        normalizeIncidenceRoute placement clause
          (routes
            (source.representativeClauseIndex clause.literals)
            literalIndex)

/-- Every genuine retained incidence route has the exact canonical source
and translated-target endpoints of its periodic incidence edge. -/
theorem deduplicatedIncidenceRoutes_endpoints_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (routesMatch :
      source.PhysicalIncidenceRoutesMatch placement routes)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata
          source.deduplicateByLiterals.erase).zipIdx) :
    (source.deduplicatedIncidenceRoutes placement routes
        tagged.1.clauseIndex tagged.1.literalIndex).head? =
        some
          (incidenceVertexPositionAt
            source.deduplicateByLiterals placement
            (.clause tagged.1.clauseIndex)) ∧
      (source.deduplicatedIncidenceRoutes placement routes
        tagged.1.clauseIndex tagged.1.literalIndex).getLast? =
        some
          (Cell.add
            (placement.position tagged.1.literal.atom)
            (placement.translation tagged.1.edge.offset)) := by
  rcases
      incidenceMetadata_of_tagged
        source.deduplicateByLiterals taggedMember with
    ⟨retainedClause, literal,
      retainedClauseMember, literalMember, taggedEqual⟩
  have retainedClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp retainedClauseMember
  have retainedClauseMem :
      retainedClause ∈
        source.deduplicateByLiterals.clauses :=
    List.fst_mem_of_mem_zipIdx retainedClauseMember
  have retainedLiteralsMem :
      retainedClause.literals ∈ source.erase.clauses := by
    have deduplicatedMember :
        retainedClause.literals ∈
          source.deduplicateByLiterals.erase.clauses := by
      change
        retainedClause.literals ∈
          (source.deduplicateByLiterals.clauses.map
            PositionedPeriodicClause.literals)
      exact List.mem_map.mpr
        ⟨retainedClause, retainedClauseMem, rfl⟩
    exact
      (clause_mem_erase_deduplicateByLiterals_iff
        source retainedClause.literals).mp deduplicatedMember
  rcases
      exists_representativeClause source retainedClause.literals
        retainedLiteralsMem with
    ⟨sourceClause, sourceClauseLookup,
      sourceClauseLiterals, sourceClausePosition⟩
  have retainedClauseRepresentative :=
    eq_representative_of_mem_deduplicateByLiterals
      source retainedClause retainedClauseMem
  have positionsEqual :
      sourceClause.position = retainedClause.position := by
    rw [sourceClausePosition]
    exact congrArg PositionedPeriodicClause.position
      retainedClauseRepresentative.symm
  have sourceLiteralLookup :
      sourceClause.literals[tagged.1.literalIndex]? =
        some literal := by
    rw [sourceClauseLiterals]
    exact
      (List.mem_zipIdx_iff_getElem?).mp literalMember
  have sourceLiteralMember :
      (literal, tagged.1.literalIndex) ∈
        sourceClause.literals.zipIdx := by
    exact
      (List.mem_zipIdx_iff_getElem?).mpr sourceLiteralLookup
  have sourceClauseMember :
      (sourceClause,
        source.representativeClauseIndex
          retainedClause.literals) ∈ source.clauses.zipIdx := by
    exact
      (List.mem_zipIdx_iff_getElem?).mpr sourceClauseLookup
  have rawEndpoints :=
    routesMatch sourceClause
      (source.representativeClauseIndex
        retainedClause.literals)
      sourceClauseMember literal tagged.1.literalIndex
      sourceLiteralMember
  have rawHead :
      (routes
        (source.representativeClauseIndex
          retainedClause.literals)
        tagged.1.literalIndex).head? =
          some retainedClause.position := by
    simpa [positionsEqual] using rawEndpoints.1
  have normalizedHead :=
    normalizeIncidenceRoute_head?
      placement retainedClause
      (routes
        (source.representativeClauseIndex
          retainedClause.literals)
        tagged.1.literalIndex)
      rawHead
  have normalizedLast :=
    normalizeIncidenceRoute_getLast?
      placement retainedClause literal
      (routes
        (source.representativeClauseIndex
          retainedClause.literals)
        tagged.1.literalIndex)
      rawEndpoints.2
  rw [taggedEqual]
  constructor
  · simpa [deduplicatedIncidenceRoutes,
      retainedClauseLookup,
      incidenceVertexPositionAt,
      (List.mem_zipIdx_iff_getElem?).mp retainedClauseMember] using
        normalizedHead
  · simpa [deduplicatedIncidenceRoutes,
      retainedClauseLookup, CNFIncidence.edge,
      PeriodicCNF.incidenceEdge] using
        normalizedLast

/-- The reindexed and normalized retained routes satisfy the complete
periodic incidence-graph endpoint condition. -/
theorem deduplicatedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (routesMatch :
      source.PhysicalIncidenceRoutesMatch placement routes)
    (periodPositive : 0 < placement.period) :
    (incidenceDrawing source.deduplicateByLiterals placement
      (source.deduplicatedIncidenceRoutes
        placement routes)).RoutesMatch
      source.deduplicateByLiterals.erase.incidenceGraph := by
  intro taggedEdge taggedEdgeMember
  have metadataEdgeMember := taggedEdgeMember
  rw [← PeriodicCNF.incidencesWithMetadata_edges
    source.deduplicateByLiterals.erase,
    List.zipIdx_map] at metadataEdgeMember
  rcases List.mem_map.mp metadataEdgeMember with
    ⟨taggedIncidence, taggedIncidenceMember,
      taggedIncidenceEqual⟩
  have endpoints :=
    deduplicatedIncidenceRoutes_endpoints_of_tagged
      source placement routes routesMatch
      taggedIncidenceMember
  have graphWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed
      source.deduplicateByLiterals.erase
  have edgeMember :
      taggedIncidence.1.edge ∈
        source.deduplicateByLiterals.erase.incidenceGraph.edges :=
    List.fst_mem_of_mem_zipIdx
      (PeriodicCNF.tagged_incidence_edge_mem
        source.deduplicateByLiterals.erase
        taggedIncidenceMember)
  have endpointMembers :=
    graphWellFormed.2 taggedIncidence.1.edge edgeMember
  have sourcePosition :=
    incidenceDrawing_vertexPosition_of_mem
      source.deduplicateByLiterals placement
      (source.deduplicatedIncidenceRoutes placement routes)
      endpointMembers.1
  have targetPosition :=
    incidenceDrawing_vertexPosition_of_mem
      source.deduplicateByLiterals placement
      (source.deduplicatedIncidenceRoutes placement routes)
      endpointMembers.2
  have routeLookup :=
    incidenceDrawing_edgeRoute_of_tagged
      source.deduplicateByLiterals placement
      (source.deduplicatedIncidenceRoutes placement routes)
      taggedIncidenceMember
  rw [← taggedIncidenceEqual]
  simp only [Prod.map, id_eq]
  rw [routeLookup]
  constructor
  · rw [sourcePosition]
    rw [CNFIncidence.edge_source]
    exact endpoints.1
  · rw [targetPosition]
    rw [CNFIncidence.edge_target]
    simp only [incidenceVertexPositionAt,
      PeriodicGridDrawing.periodTranslation]
    rw [incidenceDrawing_gridSize
      source.deduplicateByLiterals placement
      (source.deduplicatedIncidenceRoutes placement routes)
      periodPositive]
    simpa [
      PeriodicVariablePlacement.translation] using
        endpoints.2

/-- Once the finite vertex positions are distinct and lie in the open
fundamental square, the transported route family supplies all remaining
compatibility fields automatically. -/
theorem deduplicatedIncidenceDrawing_isCompatible
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (routesMatch :
      source.PhysicalIncidenceRoutesMatch placement routes)
    (periodPositive : 0 < placement.period)
    (positionsNodup :
      (incidenceVertexPositions
        source.deduplicateByLiterals placement).Nodup)
    (positionsInSquare :
      ∀ position ∈
          incidenceVertexPositions
            source.deduplicateByLiterals placement,
        (incidenceDrawing source.deduplicateByLiterals placement
          (source.deduplicatedIncidenceRoutes
            placement routes)).PositionInFundamentalSquare
          position) :
    (incidenceDrawing source.deduplicateByLiterals placement
      (source.deduplicatedIncidenceRoutes
        placement routes)).IsCompatible
      source.deduplicateByLiterals.erase.incidenceGraph := by
  refine
    ⟨PeriodicCNF.incidenceGraph_isWellFormed
        source.deduplicateByLiterals.erase,
      incidenceVertexPositions_length
        source.deduplicateByLiterals placement,
      incidenceEdgeRoutes_length
        source.deduplicateByLiterals
        (source.deduplicatedIncidenceRoutes placement routes),
      positionsNodup, positionsInSquare, ?_⟩
  exact deduplicatedIncidenceDrawing_routesMatch
    source placement routes routesMatch periodPositive

end PositionedPeriodicCNF
end LeanTrominoes
