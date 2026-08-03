import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedLocalRoutes
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Anchor-normalized local unit-elimination routes

The finite unit-elimination drawings are expressed in displayed physical
coordinates, while a periodic incidence drawing stores routes in each
generated clause's canonical anchor gauge.  This file normalizes the selected
local routes and records their exact endpoints.

For newly introduced auxiliaries the normalized local endpoint is already
the final variable endpoint.  For inherited source variables it is the local
boundary point at which the preceding route layer must be spliced.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

open PlanarThreeSAT

/-- The endpoint advertised by the selected finite unit-elimination drawing,
put in the canonical anchor gauge of its generated periodic clause. -/
def normalizedLocalEndpoint
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) : Cell :=
  match (formulaClauseMetadata source)[clauseIndex]? with
  | none => (0, 0)
  | some metadata =>
      match metadata.clause.literals[literalIndex]? with
      | none => (0, 0)
      | some literal =>
          Cell.sub
            ((PlanarOneInThreeNoUnits.instantiatedDrawing
              metadata.sourceClauseIndex
              metadata.sourceClause).variablePosition literal.atom)
            ((placement source sourcePlacement).translation
              (PeriodicCNF.clauseAnchor
                metadata.clause.literals))

/-- Normalize every metadata-selected local unit-elimination route by its
generated clause's logical anchor. -/
def normalizedLocalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match (formulaClauseMetadata source)[clauseIndex]? with
    | none => []
    | some metadata =>
        PositionedPeriodicCNF.normalizeIncidenceRoute
          (placement source sourcePlacement)
          metadata.clause
          (localRoutes source clauseIndex literalIndex)

/-- Every genuine raw local route meets its displayed generated clause and
the exact variable endpoint selected by the corresponding finite drawing. -/
theorem localRoutes_endpoints_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    ∃ metadata : ClauseMetadata Variable,
      (formulaClauseMetadata source)[clauseIndex]? =
          some metadata ∧
        metadata.clause = clause ∧
        (localRoutes source clauseIndex literalIndex).head? =
          some clause.position ∧
        (localRoutes source clauseIndex literalIndex).getLast? =
          some
            ((PlanarOneInThreeNoUnits.instantiatedDrawing
              metadata.sourceClauseIndex
              metadata.sourceClause).variablePosition literal.atom) := by
  rcases formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause metadataSourceMember
  let drawing :=
    PlanarOneInThreeNoUnits.instantiatedDrawing
      metadata.sourceClauseIndex metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        (clauseGadget metadata.sourceClauseIndex
          metadata.sourceClause).map
            PlanarOneInThreeNoUnits.embedPositionedClause :=
    PlanarOneInThreeNoUnits.instantiatedDrawing_formula
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈
        drawing.formula.zipIdx := by
    rw [drawingFormula, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(metadata.clause, metadata.localClauseIndex),
        localClauseMember, rfl⟩
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex),
        metadataLiteralMember, rfl⟩
  have drawingValid :
      drawing.IsValid :=
    PlanarOneInThreeNoUnits.instantiatedDrawing_isValid
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth metadataDistinct
  have localEndpoints :=
    EmbeddedCNFIncidenceDrawing.physicalRoutesMatch
      drawing drawingValid.1
      (PlanarOneInThreeNoUnits.embedPositionedClause
        metadata.clause)
      metadata.localClauseIndex embeddedClauseMember
      (literal.atom, literal.value)
      literalIndex embeddedLiteralMember
  refine
    ⟨metadata, metadataLookup, clauseEqual, ?_, ?_⟩
  · simpa [localRoutes, metadataLookup, drawing,
      PlanarOneInThreeNoUnits.embedPositionedClause,
      clauseEqual]
      using localEndpoints.1
  · simpa [localRoutes, metadataLookup, drawing]
      using localEndpoints.2

/-- Every genuine normalized local unit-elimination route has the exact
canonical generated-clause endpoint and selected normalized local endpoint. -/
theorem normalizedLocalRoutes_endpoints_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement source sourcePlacement) clause) ∧
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex).getLast? =
        some
          (normalizedLocalEndpoint source sourcePlacement
            clauseIndex literalIndex) := by
  rcases localRoutes_endpoints_of_members
      source sourceWidth sourceDistinct
      clauseMember literalMember with
    ⟨metadata, metadataLookup, clauseEqual,
      localHead, localLast⟩
  subst clause
  constructor
  · simpa [normalizedLocalRoutes, metadataLookup] using
      PositionedPeriodicCNF.normalizeIncidenceRoute_head?
        (placement source sourcePlacement)
        metadata.clause
        (localRoutes source clauseIndex literalIndex)
        localHead
  · have literalLookup :
        metadata.clause.literals[literalIndex]? =
          some literal :=
      (List.mem_zipIdx_iff_getElem?).mp literalMember
    simp [normalizedLocalRoutes, normalizedLocalEndpoint,
      metadataLookup,
      PositionedPeriodicCNF.normalizeIncidenceRoute,
      localLast, literalLookup]

/-- Anchor normalization preserves orthogonality of every genuine selected
unit-elimination route. -/
theorem normalizedLocalRoutes_orthogonal_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex) := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  subst clause
  simpa [normalizedLocalRoutes, metadataLookup] using
    PositionedPeriodicCNF.normalizeIncidenceRoute_orthogonal
      (placement source sourcePlacement)
      metadata.clause
      (localRoutes source clauseIndex literalIndex)
      (localRoutes_orthogonal_of_members
        source sourceWidth sourceDistinct
        clauseMember literalMember)

/-- Anchor normalization is a common translation and therefore preserves
continuous route simplicity. -/
theorem normalizedLocalRoutes_isSimple_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex) := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  subst clause
  let anchor :=
    (placement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  have translatedSimple :=
    EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      (localRoutes_isSimple_of_members
        source sourceWidth sourceDistinct
        clauseMember literalMember)
      (Cell.scale (-1) anchor)
  have normalizedRouteEqual :
      PositionedPeriodicCNF.normalizeIncidenceRoute
          (placement source sourcePlacement)
          metadata.clause
          (localRoutes source clauseIndex literalIndex) =
        (localRoutes source clauseIndex literalIndex).map
          (Cell.add (Cell.scale (-1) anchor)) := by
    unfold PositionedPeriodicCNF.normalizeIncidenceRoute
    apply List.map_congr_left
    intro point pointMember
    apply Prod.ext <;>
      simp [Cell.sub, Cell.add, Cell.scale, anchor,
        sub_eq_add_neg, add_comm]
  simpa [normalizedLocalRoutes, metadataLookup,
    normalizedRouteEqual] using translatedSimple

/-- Distinct incidences in one source-clause block remain completely
separated after their common periodic-anchor normalization. -/
theorem normalizedLocalRoutes_avoidEachOther_of_members_of_same_source
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {firstClause secondClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (formula source).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (formula source).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    {firstMetadata secondMetadata : ClauseMetadata Variable}
    (firstLookup :
      (formulaClauseMetadata source)[firstClauseIndex]? =
        some firstMetadata)
    (secondLookup :
      (formulaClauseMetadata source)[secondClauseIndex]? =
        some secondMetadata)
    (sameSource :
      firstMetadata.sourceClauseIndex =
        secondMetadata.sourceClauseIndex)
    (localIncidencesDistinct :
      firstMetadata.localClauseIndex ≠
          secondMetadata.localClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      (normalizedLocalRoutes source sourcePlacement
        secondClauseIndex secondLiteralIndex) := by
  rcases formulaClauseMetadata_lookup_valid
      source firstClauseMember with
    ⟨actualFirst, actualFirstLookup, firstClauseEqual,
      firstSourceMember, firstLocalMember⟩
  have actualFirstEqual : actualFirst = firstMetadata := by
    apply Option.some.inj
    exact actualFirstLookup.symm.trans firstLookup
  subst actualFirst
  rcases formulaClauseMetadata_lookup_valid
      source secondClauseMember with
    ⟨actualSecond, actualSecondLookup, secondClauseEqual,
      secondSourceMember, secondLocalMember⟩
  have actualSecondEqual : actualSecond = secondMetadata := by
    apply Option.some.inj
    exact actualSecondLookup.symm.trans secondLookup
  subst actualSecond
  have taggedSourcesEqual :
      (firstMetadata.sourceClause,
          firstMetadata.sourceClauseIndex) =
        (secondMetadata.sourceClause,
          secondMetadata.sourceClauseIndex) :=
    PeriodicOrthocrossing.tagged_eq_of_mem_zipIdx_of_snd_eq
      firstSourceMember secondSourceMember sameSource
  have sourceClausesEqual :
      firstMetadata.sourceClause =
        secondMetadata.sourceClause :=
    congrArg Prod.fst taggedSourcesEqual
  have firstGeneratedMember :
      firstMetadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          firstMetadata.sourceClauseIndex
          firstMetadata.sourceClause.literals := by
    rw [← clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨firstMetadata.clause,
        List.fst_mem_of_mem_zipIdx firstLocalMember, rfl⟩
  have secondGeneratedMember :
      secondMetadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          secondMetadata.sourceClauseIndex
          secondMetadata.sourceClause.literals := by
    rw [← clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨secondMetadata.clause,
        List.fst_mem_of_mem_zipIdx secondLocalMember, rfl⟩
  have firstAnchor :=
    PeriodicOneInThreeNoUnits.clauseAnchor_eq_of_mem_clauseClauses
      firstMetadata.sourceClauseIndex
      firstMetadata.sourceClause.literals
      firstMetadata.clause.literals firstGeneratedMember
  have secondAnchor :=
    PeriodicOneInThreeNoUnits.clauseAnchor_eq_of_mem_clauseClauses
      secondMetadata.sourceClauseIndex
      secondMetadata.sourceClause.literals
      secondMetadata.clause.literals secondGeneratedMember
  have anchorsEqual :
      PeriodicCNF.clauseAnchor firstMetadata.clause.literals =
        PeriodicCNF.clauseAnchor secondMetadata.clause.literals := by
    rw [sourceClausesEqual] at firstAnchor
    simpa [PeriodicCNF.clauseAnchor,
      PeriodicOneInThree.anchor] using
      firstAnchor.trans secondAnchor.symm
  have rawSeparated :=
    localRoutes_avoidEachOther_of_members_of_same_source
      source sourceWidth sourceDistinct
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstLookup secondLookup sameSource
      localIncidencesDistinct
  let anchor :=
    (placement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor
        firstMetadata.clause.literals)
  have translatedSeparated :=
    EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_translate
      rawSeparated (Cell.scale (-1) anchor)
  have firstNormalizedEqual :
      PositionedPeriodicCNF.normalizeIncidenceRoute
          (placement source sourcePlacement)
          firstMetadata.clause
          (localRoutes source firstClauseIndex
            firstLiteralIndex) =
        (localRoutes source firstClauseIndex
          firstLiteralIndex).map
            (Cell.add (Cell.scale (-1) anchor)) := by
    unfold PositionedPeriodicCNF.normalizeIncidenceRoute
    apply List.map_congr_left
    intro point pointMember
    apply Prod.ext <;>
      simp [anchor, Cell.sub, Cell.add, Cell.scale,
        sub_eq_add_neg, add_comm]
  have secondNormalizedEqual :
      PositionedPeriodicCNF.normalizeIncidenceRoute
          (placement source sourcePlacement)
          secondMetadata.clause
          (localRoutes source secondClauseIndex
            secondLiteralIndex) =
        (localRoutes source secondClauseIndex
          secondLiteralIndex).map
            (Cell.add (Cell.scale (-1) anchor)) := by
    unfold PositionedPeriodicCNF.normalizeIncidenceRoute
    apply List.map_congr_left
    intro point pointMember
    apply Prod.ext <;>
      simp [anchor, anchorsEqual, Cell.sub, Cell.add,
        Cell.scale, sub_eq_add_neg, add_comm]
  simpa [normalizedLocalRoutes, firstLookup, secondLookup,
    firstNormalizedEqual, secondNormalizedEqual] using
      translatedSeparated

/-- Same-source-block separation after normalization, with distinctness
expressed in the global generated-formula incidence coordinates. -/
theorem normalizedLocalRoutes_avoidEachOther_of_members_of_same_source_of_global_distinct
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {firstClause secondClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (formula source).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (formula source).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    {firstMetadata secondMetadata : ClauseMetadata Variable}
    (firstLookup :
      (formulaClauseMetadata source)[firstClauseIndex]? =
        some firstMetadata)
    (secondLookup :
      (formulaClauseMetadata source)[secondClauseIndex]? =
        some secondMetadata)
    (sameSource :
      firstMetadata.sourceClauseIndex =
        secondMetadata.sourceClauseIndex)
    (globalIncidencesDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      (normalizedLocalRoutes source sourcePlacement
        secondClauseIndex secondLiteralIndex) := by
  apply
    normalizedLocalRoutes_avoidEachOther_of_members_of_same_source
      source sourcePlacement sourceWidth sourceDistinct
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstLookup secondLookup sameSource
  exact localIncidencesDistinct_of_global
    source firstLookup secondLookup sameSource
      globalIncidencesDistinct

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
