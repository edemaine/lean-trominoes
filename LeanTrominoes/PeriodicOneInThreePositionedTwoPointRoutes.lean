import LeanTrominoes.PlanarOneInThreeFigureNineTwoPointRoutes
import LeanTrominoes.PeriodicOneInThreePositionedAuxiliaryRouteIsolation
import LeanTrominoes.PeriodicOneInThreePositionedInheritedSplicedRouteIsolation
import LeanTrominoes.PeriodicOneInThreePositionedRouteTerminalDirections
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedConnectorIsolation

/-!
# Vertical two-point routes after Figure 9 splicing

The finite Figure 9 invariant says that two-point auxiliary routes are
vertical.  This module transports that fact through anchor normalization and
then through global route splicing.  An inherited source-variable route is
handled separately: the nontrivial inherited suffix makes it too long to be
a two-point route.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

open PlanarThreeSAT

/-- A normalized local two-point route incident to a Figure 9 auxiliary is
vertical. -/
theorem normalizedLocalRoutes_twoPoint_vertical_of_auxiliary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (auxiliary :
      (Nat × PeriodicClause Variable) × OneInThreeAux)
    (literalAuxiliary : literal.atom = .inr auxiliary)
    {head exit : Cell}
    (routePair :
      normalizedLocalRoutes source sourcePlacement
        clauseIndex literalIndex = [head, exit]) :
    exit.1 = head.1 := by
  rcases formulaClauseMetadata_lookup_valid source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember : metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth : metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  let drawing :=
    PlanarOneInThreePositioned.instantiatedDrawing
      metadata.sourceClauseIndex metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        (clauseGadget metadata.sourceClauseIndex
          metadata.sourceClause).map
            PlanarOneInThreeNoUnits.embedPositionedClause :=
    PlanarOneInThreePositioned.instantiatedDrawing_formula
      metadata.sourceClauseIndex metadata.sourceClause metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
        metadata.localClauseIndex) ∈ drawing.formula.zipIdx := by
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
      ⟨(literal, literalIndex), metadataLiteralMember, rfl⟩
  let anchor :=
    (placement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  let route := localRoutes source clauseIndex literalIndex
  have normalizedPair :
      route.map (fun point => Cell.sub point anchor) = [head, exit] := by
    simpa [normalizedLocalRoutes, metadataLookup,
      PositionedPeriodicCNF.normalizeIncidenceRoute, route, anchor]
      using routePair
  have routeLength : route.length = 2 := by
    have mappedLength := congrArg List.length normalizedPair
    simpa using mappedLength
  cases routeEquation : route with
  | nil => simp [routeEquation] at routeLength
  | cons first rest =>
      cases rest with
      | nil => simp [routeEquation] at routeLength
      | cons second tail =>
          have tailEmpty : tail = [] := by
            simpa [routeEquation] using routeLength
          subst tail
          have localPair :
              drawing.routes metadata.localClauseIndex literalIndex =
                [first, second] := by
            simpa [drawing, route, localRoutes, metadataLookup]
              using routeEquation
          have auxiliarySelected :
              PlanarOneInThree.OneInThreeVariable.IsAuxiliary
                literal.atom := by
            simp [literalAuxiliary,
              PlanarOneInThree.OneInThreeVariable.IsAuxiliary]
          have localVertical : second.1 = first.1 :=
            EmbeddedCNFIncidenceDrawing.twoPointRoute_verticalOn_of_members
              drawing
              PlanarOneInThree.OneInThreeVariable.IsAuxiliary
              (PlanarOneInThreePositioned.instantiatedDrawing_twoPointAuxiliaryRoutesVertical
                metadata.sourceClauseIndex metadata.sourceClause
                metadataWidth)
              embeddedClauseMember embeddedLiteralMember
              auxiliarySelected localPair
          have normalizedCoordinates :
              [Cell.sub first anchor, Cell.sub second anchor] =
                [head, exit] := by
            simpa [routeEquation] using normalizedPair
          have firstNormalized : Cell.sub first anchor = head := by
            simpa using congrArg List.head? normalizedCoordinates
          have secondNormalized : Cell.sub second anchor = exit := by
            have tails := congrArg List.tail normalizedCoordinates
            simpa using congrArg List.head? tails
          rw [← firstNormalized, ← secondNormalized]
          simpa [Cell.sub] using localVertical

/-- In a spliced Figure 9 route family whose inherited source suffixes each
contain an edge, every two-point route is vertical. -/
theorem splicedRoutes_twoPoint_vertical
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    (inheritedLength :
      ∀ {clause clauseIndex literal literalIndex sourceAtom},
        (clause, clauseIndex) ∈ (formula source).clauses.zipIdx →
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        literal.atom = .inl sourceAtom →
        2 ≤ (inherited.routes clauseIndex literalIndex).length)
    {clause :
      PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {head exit : Cell}
    (routePair :
      splicedRoutes source sourcePlacement inherited
        clauseIndex literalIndex = [head, exit]) :
    exit.1 = head.1 := by
  rcases atomEquation : literal.atom with sourceAtom | auxiliary
  · have long :=
      splicedRoutes_length_ge_three_inherited
        source sourcePlacement sourceWidth sourceDistinct inherited
        clauseMember literalMember sourceAtom atomEquation
        (inheritedLength clauseMember literalMember atomEquation)
    rw [routePair] at long
    simp at long
  · rw [splicedRoutes_eq_normalizedLocalRoutes_of_auxiliary
      source sourcePlacement inherited clauseMember literalMember
      auxiliary atomEquation] at routePair
    exact normalizedLocalRoutes_twoPoint_vertical_of_auxiliary
      source sourcePlacement sourceWidth clauseMember literalMember
      auxiliary atomEquation routePair

/-- Every genuine inherited Figure 9 suffix contains at least its connector
edge. -/
theorem inheritedRouteSuffixes_length_ge_two_of_original
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    {clause : PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    2 ≤
      ((inheritedRouteSuffixes source sourcePlacement
        sourceWidth sourceDistinct sourceRoutes
        sourceEndpoints sourceOrthogonal).routes
          clauseIndex literalIndex).length := by
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  simpa [inheritedRouteSuffixes,
    inheritedRouteSuffixesRoutes, dataLookup] using
    inheritedRouteSuffix_length_ge_two
      (placement source sourcePlacement) sourcePlacement
      data.sourceClause data.generatedClause
      data.sourceLiteralIndex
      (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)

/-- A complete Figure 9 route built from the canonical inherited family is
vertical whenever it has only two points. -/
theorem inheritedSplicedRoutes_twoPoint_vertical
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    {clause : PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {head exit : Cell}
    (routePair :
      splicedRoutes source sourcePlacement
          (inheritedRouteSuffixes source sourcePlacement
            sourceWidth sourceDistinct sourceRoutes
            sourceEndpoints sourceOrthogonal)
          clauseIndex literalIndex = [head, exit]) :
    exit.1 = head.1 := by
  apply splicedRoutes_twoPoint_vertical
    source sourcePlacement sourceWidth sourceDistinct
    (inheritedRouteSuffixes source sourcePlacement
      sourceWidth sourceDistinct sourceRoutes
      sourceEndpoints sourceOrthogonal)
  · intro inheritedClause inheritedClauseIndex inheritedLiteral
      inheritedLiteralIndex inheritedAtom
      inheritedClauseMember inheritedLiteralMember inheritedSource
    exact inheritedRouteSuffixes_length_ge_two_of_original
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal
      inheritedClauseMember inheritedLiteralMember
      inheritedAtom inheritedSource
  · exact clauseMember
  · exact literalMember
  · exact routePair

/-- The exceptional case required by unit elimination: if a complete Figure
9 route's final variable endpoint is already its first exit, that one segment
is vertical. -/
theorem inheritedSplicedRoutes_verticalIfLastIsExit
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    (sourceLength :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          2 ≤ (sourceRoutes sourceClauseIndex sourceLiteralIndex).length)
    (sourceSimple :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          LocalIncidenceDrawing.RouteIsSimple
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    {clause : PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (exit : Cell)
    (routeExit :
      (splicedRoutes source sourcePlacement
        (inheritedRouteSuffixes source sourcePlacement
          sourceWidth sourceDistinct sourceRoutes
          sourceEndpoints sourceOrthogonal)
        clauseIndex literalIndex).tail.head? = some exit)
    (finalIsExit :
      PositionedPeriodicCNF.canonicalLiteralPosition
        (placement source sourcePlacement) clause literal = exit) :
    exit.1 =
      (PositionedPeriodicCNF.canonicalClausePosition
        (placement source sourcePlacement) clause).1 := by
  let inherited :=
    inheritedRouteSuffixes source sourcePlacement
      sourceWidth sourceDistinct sourceRoutes
      sourceEndpoints sourceOrthogonal
  let route :=
    splicedRoutes source sourcePlacement inherited
      clauseIndex literalIndex
  have valid := splicedRoutes_valid_of_members
    source sourcePlacement sourceWidth sourceDistinct inherited
    clauseMember literalMember
  have routeLast : route.getLast? = some exit := by
    rw [valid.2.1, finalIsExit]
  have fresh := splicedRoutes_lastNotInDropLast
    source sourcePlacement sourceWidth sourceDistinct
    sourceRoutes sourceEndpoints sourceOrthogonal
    sourceLength sourceSimple clauseMember literalMember
  have routePair :
      route =
        [PositionedPeriodicCNF.canonicalClausePosition
          (placement source sourcePlacement) clause, exit] :=
    PeriodicOneInThreeNoUnitsPositioned.eq_pair_of_last_eq_firstExit
      valid.1 routeExit routeLast valid.2.2 fresh
  exact inheritedSplicedRoutes_twoPoint_vertical
    source sourcePlacement sourceWidth sourceDistinct
    sourceRoutes sourceEndpoints sourceOrthogonal
    clauseMember literalMember routePair

end PeriodicOneInThreePositioned
end LeanTrominoes
