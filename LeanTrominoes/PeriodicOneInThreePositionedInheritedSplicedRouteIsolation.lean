import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteFamilyIsolation
import LeanTrominoes.PeriodicOneInThreePositionedAuxiliaryRouteIsolation
import LeanTrominoes.PositionedPeriodicCNFLocalRouteSplicingEndpointDirections

/-!
# Endpoint isolation for complete inherited Figure 9 routes

An inherited local Figure 9 route is one short segment from its generated
clause to one of the three boundary ports.  None of these segments meets the
scale-twelve source lattice.  After anchor normalization, this separates the
local prefix from the final endpoint of every inherited suffix, so the two
pieces can be joined without losing final-endpoint isolation.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- Local Figure 9 clause port attached to each inherited source literal. -/
def sourceLocalClausePosition : Nat → Cell
  | 0 => (6, 2)
  | 1 => (3, 5)
  | _ => (9, 5)

theorem localRoutes_eq_inherited_segment
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (literalAtom : literal.atom = .inl sourceLiteral.atom) :
    localRoutes source clauseIndex literalIndex =
      [Cell.add
          (Cell.scale PlanarOneInThree.gadgetScale
            metadata.sourceClause.position)
          (sourceLocalClausePosition sourceLiteralIndex),
        Cell.add
          (Cell.scale PlanarOneInThree.gadgetScale
            metadata.sourceClause.position)
          (PlanarOneInThreePositioned.sourceLocalPosition
            sourceLiteralIndex)] := by
  have metadataIndexLt :
      clauseIndex < (formulaClauseMetadata source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (formulaClauseMetadata source)[clauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember : metadata ∈ formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  rcases metadata with
    ⟨metadataSourceClause, metadataSourceClauseIndex,
      metadataClause, metadataLocalClauseIndex⟩
  rw [show localRoutes source clauseIndex literalIndex =
      (PlanarOneInThreePositioned.instantiatedDrawing
        metadataSourceClauseIndex metadataSourceClause).routes
          metadataLocalClauseIndex literalIndex by
    simp [localRoutes, metadataLookup]]
  have valid := formulaClauseMetadata_valid source metadataMember
  have sourceMember : metadataSourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx valid.1
  have width : metadataSourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadataSourceClause.literals
    exact List.mem_map.mpr ⟨metadataSourceClause, sourceMember, rfl⟩
  have distinct : metadataSourceClause.AtomsNodup :=
    sourceDistinct metadataSourceClause sourceMember
  rcases metadataSourceClause with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · simp at sourceLiteralMember
  · rcases rest with _ | ⟨second, rest⟩
    · simp [clauseGadget, PeriodicOneInThree.clauseClauses,
        PeriodicOneInThree.disjunctionGadget,
        PeriodicOneInThree.forcePaddingFalse,
        PeriodicOneInThree.padding,
        PeriodicOneInThree.auxiliary,
        PeriodicOneInThree.liftLiteral,
        PlanarOneInThree.generatedClausePosition]
        at valid literalMember sourceLiteralMember ⊢
      rcases valid.2 with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp at literalMember
        rcases literalMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> simp_all [PlanarOneInThreePositioned.instantiatedDrawing,
          PlanarOneInThreePositioned.instantiatedOneDrawing,
          PlanarOneInThreePositioned.rescopeDrawing,
          PlanarOneInThreePositioned.rescopeEquiv,
          PlanarOneInThree.instantiatedOneDrawing,
          PlanarOneInThree.figureNineOneDrawingFor,
          PlanarOneInThree.figureNineOneRoute,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
          sourceLocalClausePosition,
          PlanarOneInThreePositioned.sourceLocalPosition,
          PlanarOneInThree.gadgetScale, Cell.add, Cell.scale]
      · simp at literalMember
        rcases literalMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> simp_all
      · simp at literalMember
        rcases literalMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> simp_all
      · simp at literalMember
        simp_all
      · simp at literalMember
        simp_all
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond : first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup] using distinct
        simp [clauseGadget, PeriodicOneInThree.clauseClauses,
            PeriodicOneInThree.disjunctionGadget,
            PeriodicOneInThree.forcePaddingFalse,
            PeriodicOneInThree.padding,
            PeriodicOneInThree.auxiliary,
            PeriodicOneInThree.liftLiteral,
            PlanarOneInThree.generatedClausePosition]
            at valid literalMember sourceLiteralMember ⊢
        rcases valid.2 with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp at literalMember
          rcases literalMember with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          <;> rcases sourceLiteralMember with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          <;> simp_all [PlanarOneInThreePositioned.instantiatedDrawing,
            PlanarOneInThreePositioned.instantiatedTwoDrawing,
            PlanarOneInThreePositioned.rescopeDrawing,
            PlanarOneInThreePositioned.rescopeEquiv,
            PlanarOneInThree.instantiatedTwoDrawing,
            PlanarOneInThree.figureNineTwoDrawingFor,
            PlanarOneInThree.figureNineTwoRoute,
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
            sourceLocalClausePosition,
            PlanarOneInThreePositioned.sourceLocalPosition,
            PlanarOneInThree.gadgetScale, Cell.add, Cell.scale]
        · simp at literalMember
          rcases literalMember with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          <;> rcases sourceLiteralMember with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          <;> simp_all [PlanarOneInThreePositioned.instantiatedDrawing,
            PlanarOneInThreePositioned.instantiatedTwoDrawing,
            PlanarOneInThreePositioned.rescopeDrawing,
            PlanarOneInThreePositioned.rescopeEquiv,
            PlanarOneInThree.instantiatedTwoDrawing,
            PlanarOneInThree.figureNineTwoDrawingFor,
            PlanarOneInThree.figureNineTwoRoute,
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
            sourceLocalClausePosition,
            PlanarOneInThreePositioned.sourceLocalPosition,
            PlanarOneInThree.gadgetScale, Cell.add, Cell.scale,
            Ne.symm firstNeSecond]
        · simp at literalMember
          rcases literalMember with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          <;> simp_all
        · simp at literalMember
          simp_all
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        have pairwise :
            (first.atom ≠ second.atom ∧
              first.atom ≠ third.atom) ∧
            second.atom ≠ third.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup] using distinct
        simp [clauseGadget, PeriodicOneInThree.clauseClauses,
            PeriodicOneInThree.disjunctionGadget,
            PeriodicOneInThree.auxiliary,
            PeriodicOneInThree.liftLiteral,
            PlanarOneInThree.generatedClausePosition]
            at valid literalMember sourceLiteralMember ⊢
        rcases valid.2 with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        all_goals
          simp at literalMember
          rcases literalMember with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          <;> rcases sourceLiteralMember with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          <;> simp_all [PlanarOneInThreePositioned.instantiatedDrawing,
            PlanarOneInThreePositioned.instantiatedThreeDrawing,
            PlanarOneInThreePositioned.rescopeDrawing,
            PlanarOneInThreePositioned.rescopeEquiv,
            PlanarOneInThree.instantiatedThreeDrawing,
            PlanarOneInThree.figureNineDrawingFor,
            PlanarOneInThree.figureNineRoute,
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
            sourceLocalClausePosition,
            PlanarOneInThreePositioned.sourceLocalPosition,
            PlanarOneInThree.gadgetScale, Cell.add, Cell.scale,
            Ne.symm pairwise.1.1, Ne.symm pairwise.1.2,
            Ne.symm pairwise.2]

/-- No point of an inherited local Figure 9 segment lies on the source
clause's scale-twelve lattice. -/
theorem scaledGridPoint_not_mem_localRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (literalAtom : literal.atom = .inl sourceLiteral.atom)
    (point : Cell) :
    Cell.add
        (Cell.scale PlanarOneInThree.gadgetScale
          metadata.sourceClause.position)
        (Cell.scale PlanarOneInThree.gadgetScale point) ∉
      AxisDirection.unitSubdividePolyline
        (localRoutes source clauseIndex literalIndex) := by
  rw [localRoutes_eq_inherited_segment
    source sourceWidth sourceDistinct metadataLookup
    literalMember sourceLiteralMember literalAtom]
  have metadataIndexLt :
      clauseIndex < (formulaClauseMetadata source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (formulaClauseMetadata source)[clauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember : metadata ∈ formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have sourceMember : metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx
      (formulaClauseMetadata_valid source metadataMember).1
  have metadataWidth : metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, sourceMember, rfl⟩
  have sourceLiteralIndexLt : sourceLiteralIndex < 3 := by
    have := (List.mem_zipIdx' sourceLiteralMember).1
    omega
  intro member
  rcases point with ⟨x, y⟩
  rcases sourceLiteralIndex with _ | sourceLiteralIndex
  · norm_num [sourceLocalClausePosition,
      PlanarOneInThreePositioned.sourceLocalPosition,
      PlanarOneInThree.gadgetScale,
      AxisDirection.unitSubdividePolyline,
      AxisDirection.unitSegmentPoints,
      AxisDirection.segmentLength,
      AxisDirection.between, AxisDirection.step,
      Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
      List.range_succ] at member ⊢
    rcases member with member | member | member <;> omega
  · rcases sourceLiteralIndex with _ | sourceLiteralIndex
    · norm_num [sourceLocalClausePosition,
        PlanarOneInThreePositioned.sourceLocalPosition,
        PlanarOneInThree.gadgetScale,
        AxisDirection.unitSubdividePolyline,
        AxisDirection.unitSegmentPoints,
        AxisDirection.segmentLength,
        AxisDirection.between, AxisDirection.step,
        Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
        List.range_succ] at member ⊢
      rcases member with member | member | member | member <;> omega
    · have indexZero : sourceLiteralIndex = 0 := by omega
      subst sourceLiteralIndex
      norm_num [sourceLocalClausePosition,
        PlanarOneInThreePositioned.sourceLocalPosition,
        PlanarOneInThree.gadgetScale,
        AxisDirection.unitSubdividePolyline,
        AxisDirection.unitSegmentPoints,
        AxisDirection.segmentLength,
        AxisDirection.between, AxisDirection.step,
        Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
        List.range_succ] at member ⊢
      rcases member with member | member | member | member <;> omega

/-- The final point of any refined inherited source route is absent from
the normalized local Figure 9 prefix. -/
theorem inheritedSourceEndpoint_not_mem_normalizedLocalRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (literalAtom : literal.atom = .inl sourceLiteral.atom)
    (sourceLast : Cell) :
    Cell.add
        (inheritedSourceRouteShift
          (placement source sourcePlacement) sourcePlacement
          metadata.sourceClause metadata.clause)
        (Cell.scale PlanarOneInThree.gadgetScale sourceLast) ∉
      AxisDirection.unitSubdividePolyline
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex) := by
  let outputPlacement := placement source sourcePlacement
  let anchor :=
    outputPlacement.translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  let sourceFirst :=
    PositionedPeriodicCNF.canonicalClausePosition
      sourcePlacement metadata.sourceClause
  let difference := Cell.sub sourceLast sourceFirst
  have normalizedRouteEqual :
      normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex =
        (localRoutes source clauseIndex literalIndex).map
          (Cell.add (Cell.scale (-1) anchor)) := by
    simp only [normalizedLocalRoutes, metadataLookup]
    unfold PositionedPeriodicCNF.normalizeIncidenceRoute
    apply List.map_congr_left
    intro point pointMember
    apply Prod.ext <;>
      simp [Cell.sub, Cell.add, Cell.scale, anchor,
        outputPlacement, sub_eq_add_neg, add_comm]
  have finalEqual :
      Cell.add
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement
            metadata.sourceClause metadata.clause)
          (Cell.scale PlanarOneInThree.gadgetScale sourceLast) =
        Cell.add (Cell.scale (-1) anchor)
          (Cell.add
            (Cell.scale PlanarOneInThree.gadgetScale
              metadata.sourceClause.position)
            (Cell.scale PlanarOneInThree.gadgetScale difference)) := by
    apply Prod.ext <;>
      simp [inheritedSourceRouteShift,
        normalizedSourceClausePosition,
        PositionedPeriodicCNF.canonicalClausePosition,
        outputPlacement, sourceFirst, difference,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  intro member
  rw [normalizedRouteEqual,
    AxisDirection.unitSubdividePolyline_map_add] at member
  rw [finalEqual] at member
  rcases List.mem_map.mp member with
    ⟨point, pointMember, pointEqual⟩
  have pointPhysical :
      point =
        Cell.add
          (Cell.scale PlanarOneInThree.gadgetScale
            metadata.sourceClause.position)
          (Cell.scale PlanarOneInThree.gadgetScale difference) :=
    Cell.add_left_injective (Cell.scale (-1) anchor) pointEqual
  subst point
  exact scaledGridPoint_not_mem_localRoute
    source sourceWidth sourceDistinct metadataLookup
    literalMember sourceLiteralMember literalAtom difference pointMember

/-- The final canonical endpoint of an inherited Figure 9 incidence is
absent from its normalized local prefix. -/
theorem canonicalLiteralPosition_not_mem_normalizedLocalRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
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
    PositionedPeriodicCNF.canonicalLiteralPosition
        (placement source sourcePlacement) clause literal ∉
      AxisDirection.unitSubdividePolyline
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex) := by
  rcases normalizedLocalEndpoint_inherited
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨metadata, sourceLiteral, sourceLiteralIndex,
      metadataLookup, metadataClause, sourceClauseMember,
      sourceLiteralMember, sourceLiteralAtom,
      literalOffset, localEndpoint⟩
  subst clause
  have metadataLiteralMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx := by
    simpa using literalMember
  have literalAtom : literal.atom = .inl sourceLiteral.atom := by
    rw [literalSource, sourceLiteralAtom]
  let sourceLast :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      sourcePlacement metadata.sourceClause sourceLiteral
  have endpointEqual :
      Cell.add
          (inheritedSourceRouteShift
            (placement source sourcePlacement) sourcePlacement
            metadata.sourceClause metadata.clause)
          (Cell.scale PlanarOneInThree.gadgetScale sourceLast) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (placement source sourcePlacement) metadata.clause literal := by
    have endpoint := inheritedSourceRoute_getLast?
      source sourcePlacement metadata.sourceClause metadata.clause
      sourceLiteral literal [sourceLast] (by simp [sourceLast])
      literalAtom literalOffset
    simpa [inheritedSourceRoute,
      PeriodicOrthocrossing.translatePolyline,
      scalePolyline] using endpoint
  rw [← endpointEqual]
  exact inheritedSourceEndpoint_not_mem_normalizedLocalRoute
    source sourcePlacement sourceWidth sourceDistinct metadataLookup
    metadataLiteralMember sourceLiteralMember literalAtom sourceLast

/-- A nondegenerate source route gives a nondegenerate inherited Figure 9
suffix. -/
theorem inheritedRouteSuffix_length_ge_two
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceLiteralIndex : Nat)
    (sourceRoute : List Cell) :
    2 ≤
      (inheritedRouteSuffix outputPlacement sourcePlacement
        sourceClause generatedClause sourceLiteralIndex
        sourceRoute).length := by
  simp only [inheritedRouteSuffix, LeanTrominoes.joinAtEndpoint,
    List.length_append, List.length_tail,
    inheritedSourceRoute, PeriodicOrthocrossing.translatePolyline,
    List.length_map, scalePolyline,
    PositionedPeriodicCNF.orthogonalDetour,
    List.length_cons, List.length_nil]
  omega

/-- Every genuine inherited Figure 9 route retains final-endpoint isolation
after its local prefix and inherited suffix are spliced. -/
theorem splicedRoutes_lastNotInDropLast_of_inherited
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
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (splicedRoutes source sourcePlacement
          (inheritedRouteSuffixes source sourcePlacement
            sourceWidth sourceDistinct sourceRoutes
            sourceEndpoints sourceOrthogonal)
          clauseIndex literalIndex)) := by
  let inherited :=
    inheritedRouteSuffixes source sourcePlacement
      sourceWidth sourceDistinct sourceRoutes
      sourceEndpoints sourceOrthogonal
  let suffix :=
    inheritedRouteSuffixesRoutes
      source sourcePlacement sourceRoutes clauseIndex literalIndex
  have completeRoutesEqual :
      (completeRouteSuffixes source sourcePlacement inherited).routes
          clauseIndex literalIndex = suffix := by
    change
      PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes
          inherited clauseIndex literalIndex = suffix
    calc
      _ = inherited.routes clauseIndex literalIndex :=
        PositionedPeriodicCNF.completeSumIncidenceRouteSuffixesRoutes_eq_inherited
          inherited clauseMember literalMember sourceAtom literalSource
      _ = suffix := by rfl
  have localEndpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  have localNonempty :
      normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex ≠ [] := by
    intro empty
    simp [empty] at localEndpoints
  have localOrthogonal :=
    normalizedLocalRoutes_orthogonal_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  have suffixValid :=
    inheritedRouteSuffixesRoutes_valid
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal
      clauseMember literalMember sourceAtom literalSource
  have suffixFresh :=
    inheritedRouteSuffixesRoutes_lastNotInDropLast
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal
      sourceLength sourceSimple clauseMember literalMember
      sourceAtom literalSource
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  have suffixLength : 2 ≤ suffix.length := by
    simpa [suffix, inheritedRouteSuffixesRoutes, dataLookup] using
      inheritedRouteSuffix_length_ge_two
        (placement source sourcePlacement) sourcePlacement
        data.sourceClause data.generatedClause
        data.sourceLiteralIndex
        (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
  have finalNotInLocal :=
    canonicalLiteralPosition_not_mem_normalizedLocalRoute
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource
  have joined :=
    AxisDirection.LastNotInDropLast.unitSubdividePolyline_joinAtEndpoint
      suffixFresh localNonempty suffixLength
      localOrthogonal suffixValid.2.2
      localEndpoints.2 suffixValid.1 suffixValid.2.1
      finalNotInLocal
  simpa [splicedRoutes,
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes,
    completeRoutesEqual, inherited, suffix] using joined

/-- Every genuine complete Figure 9 route, whether inherited or auxiliary,
has an isolated final endpoint after unit subdivision. -/
theorem splicedRoutes_lastNotInDropLast
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (splicedRoutes source sourcePlacement
          (inheritedRouteSuffixes source sourcePlacement
            sourceWidth sourceDistinct sourceRoutes
            sourceEndpoints sourceOrthogonal)
          clauseIndex literalIndex)) := by
  rcases atomEqual : literal.atom with sourceAtom | auxiliary
  · exact splicedRoutes_lastNotInDropLast_of_inherited
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal
      sourceLength sourceSimple clauseMember literalMember
      sourceAtom atomEqual
  · exact
      (splicedRoutes_endpointIsolation_of_auxiliary
        source sourcePlacement sourceWidth sourceDistinct
        (inheritedRouteSuffixes source sourcePlacement
          sourceWidth sourceDistinct sourceRoutes
          sourceEndpoints sourceOrthogonal)
        clauseMember literalMember auxiliary atomEqual).2

end PeriodicOneInThreePositioned
end LeanTrominoes
