import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedAuxiliaryRouteIsolation
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamilyIsolation
import LeanTrominoes.PeriodicOneInThreePositionedInheritedSplicedRouteIsolation

/-!
# Endpoint isolation for complete unit-elimination routes

The inherited suffix has already been proved final-endpoint isolated.  This
module supplies the remaining local-prefix separation and joins the two
pieces, then combines inherited and auxiliary incidences into a uniform
endpoint-isolation theorem.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- Local generated-clause endpoint of a source-variable route, selected by
the arity of the source clause. -/
def sourceLocalClausePosition (sourceArity : Nat) : Cell :=
  if sourceArity = 1 then (3, 2) else (3, 3)

/-- Every inherited local unit-elimination route is the single displayed
segment from its generated clause to its source boundary port. -/
theorem localRoutes_eq_inherited_segment
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
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
          (Cell.scale gadgetScale metadata.sourceClause.position)
          (sourceLocalClausePosition
            metadata.sourceClause.literals.length),
        Cell.add
          (Cell.scale gadgetScale metadata.sourceClause.position)
          (PlanarOneInThreeNoUnits.sourceLocalPosition
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
      (PlanarOneInThreeNoUnits.instantiatedDrawing
        metadataSourceClauseIndex metadataSourceClause).routes
          metadataLocalClauseIndex literalIndex by
    simp [localRoutes, metadataLookup]]
  have valid := formulaClauseMetadata_valid source metadataMember
  have sourceMember : metadataSourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx valid.1
  have width : metadataSourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadataSourceClause.literals
    exact List.mem_map.mpr
      ⟨metadataSourceClause, sourceMember, rfl⟩
  have distinct : metadataSourceClause.AtomsNodup :=
    sourceDistinct metadataSourceClause sourceMember
  rcases metadataSourceClause with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · simp at sourceLiteralMember
  · rcases rest with _ | ⟨second, rest⟩
    · dsimp [clauseGadget,
        PeriodicOneInThreeNoUnits.clauseClauses,
        PeriodicOneInThreeNoUnits.liftLiteral,
        PeriodicOneInThreeNoUnits.auxiliary,
        PeriodicOneInThree.negate,
        generatedClausePosition] at valid
      simp at valid
      rcases valid.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · dsimp at literalMember sourceLiteralMember ⊢
        simp at literalMember sourceLiteralMember
        rcases literalMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> simp_all [PlanarOneInThreeNoUnits.instantiatedDrawing,
          PlanarOneInThreeNoUnits.instantiatedUnitDrawing,
          PlanarOneInThreeNoUnits.unitDrawingFor,
          PlanarOneInThreeNoUnits.unitRoute,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
          sourceLocalClausePosition,
          PlanarOneInThreeNoUnits.sourceLocalPosition,
          gadgetScale, Cell.add, Cell.scale]
      · dsimp at literalMember sourceLiteralMember ⊢
        simp at literalMember sourceLiteralMember
        rcases literalMember with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> simp_all
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond : first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup] using distinct
        dsimp [clauseGadget,
            PeriodicOneInThreeNoUnits.clauseClauses,
            PeriodicOneInThreeNoUnits.liftLiteral,
            generatedClausePosition] at valid
        simp at valid
        rcases valid.2 with ⟨rfl, rfl⟩
        dsimp at literalMember sourceLiteralMember ⊢
        simp at literalMember sourceLiteralMember
        rcases literalMember with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> rcases sourceLiteralMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> simp_all [PlanarOneInThreeNoUnits.instantiatedDrawing,
          PlanarOneInThreeNoUnits.instantiatedTwoDrawing,
          PlanarOneInThreeNoUnits.twoDrawingFor,
          PlanarOneInThreeNoUnits.twoRoute,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
          sourceLocalClausePosition,
          PlanarOneInThreeNoUnits.sourceLocalPosition,
          gadgetScale, Cell.add, Cell.scale,
          Ne.symm firstNeSecond]
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
        dsimp [clauseGadget,
            PeriodicOneInThreeNoUnits.clauseClauses,
            PeriodicOneInThreeNoUnits.liftLiteral,
            generatedClausePosition] at valid
        simp at valid
        rcases valid.2 with ⟨rfl, rfl⟩
        dsimp at literalMember sourceLiteralMember ⊢
        simp at literalMember sourceLiteralMember
        rcases literalMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> rcases sourceLiteralMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        <;> simp_all [PlanarOneInThreeNoUnits.instantiatedDrawing,
          PlanarOneInThreeNoUnits.instantiatedThreeDrawing,
          PlanarOneInThreeNoUnits.threeDrawingFor,
          PlanarOneInThreeNoUnits.threeRoute,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.rename,
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate,
          sourceLocalClausePosition,
          PlanarOneInThreeNoUnits.sourceLocalPosition,
          gadgetScale, Cell.add, Cell.scale,
          Ne.symm pairwise.1.1, Ne.symm pairwise.1.2,
          Ne.symm pairwise.2]

/-- No point of an inherited local unit-elimination segment lies on the
source clause's scale-six lattice. -/
theorem scaledGridPoint_not_mem_localRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
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
        (Cell.scale gadgetScale metadata.sourceClause.position)
        (Cell.scale gadgetScale point) ∉
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
  have sourceArityPositive : 0 < metadata.sourceClause.literals.length :=
    Nat.zero_lt_of_lt
      ((List.mem_zipIdx' sourceLiteralMember).1)
  intro member
  rcases point with ⟨x, y⟩
  interval_cases sourceLiteralIndex <;>
    interval_cases hArity : metadata.sourceClause.literals.length <;>
    norm_num [sourceLocalClausePosition,
      PlanarOneInThreeNoUnits.sourceLocalPosition,
      gadgetScale,
      AxisDirection.unitSubdividePolyline,
      AxisDirection.unitSegmentPoints,
      AxisDirection.segmentLength,
      AxisDirection.between, AxisDirection.step,
      Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
      List.range_succ] at member ⊢ <;>
    omega

/-- The final point of any refined inherited source route is absent from
the normalized local unit-elimination prefix. -/
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
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
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
        (Cell.scale gadgetScale sourceLast) ∉
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
          (Cell.scale gadgetScale sourceLast) =
        Cell.add (Cell.scale (-1) anchor)
          (Cell.add
            (Cell.scale gadgetScale metadata.sourceClause.position)
            (Cell.scale gadgetScale difference)) := by
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
          (Cell.scale gadgetScale metadata.sourceClause.position)
          (Cell.scale gadgetScale difference) :=
    Cell.add_left_injective (Cell.scale (-1) anchor) pointEqual
  subst point
  exact scaledGridPoint_not_mem_localRoute
    source sourceWidth sourceDistinct metadataLookup
    literalMember sourceLiteralMember literalAtom difference pointMember

/-- The final canonical endpoint of an inherited unit-elimination incidence
is absent from its normalized local prefix. -/
theorem canonicalLiteralPosition_not_mem_normalizedLocalRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
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
          (Cell.scale gadgetScale sourceLast) =
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

/-- The local generated-clause point is absent from the boundary-port detour
to a refined source first exit.  Only the middle port needs a hypothesis: its
source exit must lie weakly left of the source clause point. -/
theorem sourceLocalClausePosition_not_mem_sourceExitConnector
    (sourceArity sourceLiteralIndex : Nat)
    (arityPositive : 0 < sourceArity)
    (arityAtMostThree : sourceArity ≤ 3)
    (sourceLiteralIndexLt : sourceLiteralIndex < sourceArity)
    (relativeExit : Cell)
    (middleWeakLeft : sourceLiteralIndex = 1 → relativeExit.1 ≤ 0) :
    sourceLocalClausePosition sourceArity ∉
      AxisDirection.unitSubdividePolyline
        (PositionedPeriodicCNF.orthogonalDetour
          (PlanarOneInThreeNoUnits.sourceLocalPosition sourceLiteralIndex)
          (Cell.scale gadgetScale relativeExit)) := by
  intro member
  have connectorOrthogonal :=
    PositionedPeriodicCNF.orthogonalDetour_orthogonal
      (PlanarOneInThreeNoUnits.sourceLocalPosition sourceLiteralIndex)
      (Cell.scale gadgetScale relativeExit)
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        connectorOrthogonal member with
    originalMember | ⟨segment, segmentMember, interior⟩
  · rcases relativeExit with ⟨exitX, exitY⟩
    interval_cases sourceArity <;>
      interval_cases sourceLiteralIndex <;>
      simp [sourceLocalClausePosition,
        PlanarOneInThreeNoUnits.sourceLocalPosition,
        PositionedPeriodicCNF.orthogonalDetour,
        PositionedPeriodicCNF.freshDetourCoordinate,
        gadgetScale, Cell.scale] at originalMember <;>
      omega
  · rcases relativeExit with ⟨exitX, exitY⟩
    interval_cases sourceArity <;>
      interval_cases sourceLiteralIndex <;>
      simp [sourceLocalClausePosition,
        PlanarOneInThreeNoUnits.sourceLocalPosition,
        PositionedPeriodicCNF.orthogonalDetour,
        PositionedPeriodicCNF.freshDetourCoordinate,
        gadgetScale, Cell.scale,
        gridPolylineSegments] at segmentMember
    all_goals
      rcases segmentMember with rfl | rfl | rfl | rfl
      all_goals
        (simp [GridSegment.InteriorContains,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          GridSegment.StrictlyBetween,
          sourceLocalClausePosition,
          PlanarOneInThreeNoUnits.sourceLocalPosition,
          PositionedPeriodicCNF.freshDetourCoordinate,
          gadgetScale, Cell.scale] at interior <;>
        omega)

/-- The canonical generated-clause endpoint of an inherited local route is
the normalized source-clause point plus its arity-selected local position. -/
theorem canonicalClausePosition_eq_normalizedSourceClausePosition_add_local
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (literalAtom : literal.atom = .inl sourceLiteral.atom) :
    PositionedPeriodicCNF.canonicalClausePosition
        (placement source sourcePlacement) metadata.clause =
      Cell.add
        (normalizedSourceClausePosition
          (placement source sourcePlacement)
          metadata.sourceClause metadata.clause)
        (sourceLocalClausePosition
          metadata.sourceClause.literals.length) := by
  have clauseLookup :
      (formula source).clauses[clauseIndex]? = some metadata.clause := by
    rw [← formulaClauseMetadata_clauses]
    rw [List.getElem?_map, metadataLookup]
    rfl
  have clauseMember :
      (metadata.clause, clauseIndex) ∈
        (formula source).clauses.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr clauseLookup
  have endpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  have routeEqual :=
    localRoutes_eq_inherited_segment
      source sourceWidth sourceDistinct metadataLookup
      literalMember sourceLiteralMember literalAtom
  let anchor :=
    (placement source sourcePlacement).translation
      (PeriodicCNF.clauseAnchor metadata.clause.literals)
  have segmentHead :
      (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex).head? =
        some
          (Cell.sub
            (Cell.add
              (Cell.scale gadgetScale metadata.sourceClause.position)
              (sourceLocalClausePosition
                metadata.sourceClause.literals.length))
            anchor) := by
    simp [normalizedLocalRoutes, metadataLookup,
      PositionedPeriodicCNF.normalizeIncidenceRoute,
      routeEqual, anchor]
  have headEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          (placement source sourcePlacement) metadata.clause =
        Cell.sub
          (Cell.add
            (Cell.scale gadgetScale metadata.sourceClause.position)
            (sourceLocalClausePosition
              metadata.sourceClause.literals.length))
          anchor :=
    Option.some.inj (endpoints.1.symm.trans segmentHead)
  rw [headEqual]
  apply Prod.ext <;>
    simp [normalizedSourceClausePosition, anchor,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- Every point of a refined inherited source route lies on a horizontal or
vertical line of its translated scale-six source lattice. -/
theorem inheritedSourceRoute_unitSubdivision_mem_gridLine
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceRoute : List Cell)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute)
    {point : Cell}
    (pointMember :
      point ∈
        AxisDirection.unitSubdividePolyline
          (inheritedSourceRoute outputPlacement sourcePlacement
            sourceClause generatedClause sourceRoute)) :
    let shift :=
      inheritedSourceRouteShift outputPlacement sourcePlacement
        sourceClause generatedClause
    (∃ x, point.1 = shift.1 + gadgetScale * x) ∨
      (∃ y, point.2 = shift.2 + gadgetScale * y) := by
  let shift :=
    inheritedSourceRouteShift outputPlacement sourcePlacement
      sourceClause generatedClause
  apply
    PeriodicOneInThreePositioned.unitSubdividePolyline_mem_shiftedGridLine
      gadgetScale shift
  · exact inheritedSourceRoute_orthogonal
      outputPlacement sourcePlacement sourceClause generatedClause
      sourceRoute sourceOrthogonal
  · intro listed listedMember
    unfold inheritedSourceRoute
      PeriodicOrthocrossing.translatePolyline at listedMember
    rcases List.mem_map.mp listedMember with
      ⟨scaled, scaledMember, rfl⟩
    rcases List.mem_map.mp scaledMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    exact
      ⟨⟨sourcePoint.1, by
          simp [shift, Cell.add, Cell.scale]⟩,
        ⟨sourcePoint.2, by
          simp [shift, Cell.add, Cell.scale]⟩⟩
  · exact pointMember

/-- If the middle source route exits weakly left, the generated clause
endpoint is absent from the complete unit-elimination suffix. -/
theorem canonicalClausePosition_not_mem_inheritedRouteSuffix
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (literalAtom : literal.atom = .inl sourceLiteral.atom)
    (sourceRoute : List Cell)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement metadata.sourceClause))
    (sourceExit : Cell)
    (sourceTailHead : sourceRoute.tail.head? = some sourceExit)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute)
    (middleWeakLeft :
      sourceLiteralIndex = 1 →
        sourceExit.1 ≤
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement metadata.sourceClause).1) :
    PositionedPeriodicCNF.canonicalClausePosition
        (placement source sourcePlacement) metadata.clause ∉
      AxisDirection.unitSubdividePolyline
        (inheritedRouteSuffix
          (placement source sourcePlacement) sourcePlacement
          metadata.sourceClause metadata.clause
          sourceLiteralIndex sourceRoute) := by
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
  have sourceLiteralIndexLt :
      sourceLiteralIndex < metadata.sourceClause.literals.length :=
    (List.mem_zipIdx' sourceLiteralMember).1
  have metadataPositive : 0 < metadata.sourceClause.literals.length :=
    Nat.zero_lt_of_lt sourceLiteralIndexLt
  let outputPlacement := placement source sourcePlacement
  let shift :=
    inheritedSourceRouteShift outputPlacement sourcePlacement
      metadata.sourceClause metadata.clause
  let sourceFirst :=
    PositionedPeriodicCNF.canonicalClausePosition
      sourcePlacement metadata.sourceClause
  let relativeExit := Cell.sub sourceExit sourceFirst
  let sourcePoint :=
    normalizedSourceClausePosition outputPlacement
      metadata.sourceClause metadata.clause
  let port :=
    normalizedSourcePort outputPlacement
      metadata.sourceClause metadata.clause sourceLiteralIndex
  let transformed :=
    inheritedSourceRoute outputPlacement sourcePlacement
      metadata.sourceClause metadata.clause sourceRoute
  let transformedExit :=
    Cell.add sourcePoint (Cell.scale gadgetScale relativeExit)
  let connector :=
    PositionedPeriodicCNF.orthogonalDetour port transformedExit
  let generatedHead :=
    PositionedPeriodicCNF.canonicalClausePosition
      outputPlacement metadata.clause
  have generatedHeadEqual :
      generatedHead =
        Cell.add sourcePoint
          (sourceLocalClausePosition
            metadata.sourceClause.literals.length) := by
    exact
      canonicalClausePosition_eq_normalizedSourceClausePosition_add_local
        source sourcePlacement sourceWidth sourceDistinct
        metadataLookup literalMember sourceLiteralMember literalAtom
  have sourcePointEqual :
      sourcePoint =
        Cell.add shift (Cell.scale gadgetScale sourceFirst) := by
    apply Prod.ext <;>
      simp [sourcePoint, shift, sourceFirst,
        inheritedSourceRouteShift,
        normalizedSourceClausePosition,
        PositionedPeriodicCNF.canonicalClausePosition,
        Cell.add, Cell.sub, Cell.scale]
  have transformedTailHead :
      transformed.tail.head? = some transformedExit := by
    have mapped := inheritedSourceRoute_tail_head?
      outputPlacement sourcePlacement metadata.sourceClause
      metadata.clause sourceRoute sourceExit sourceTailHead
    rw [show transformedExit =
        Cell.add shift (Cell.scale gadgetScale sourceExit) by
      apply Prod.ext <;>
        simp [transformedExit, sourcePoint, relativeExit,
          sourceFirst, shift, inheritedSourceRouteShift,
          normalizedSourceClausePosition,
          PositionedPeriodicCNF.canonicalClausePosition,
          Cell.add, Cell.sub, Cell.scale] <;>
        ring]
    simpa [transformed, shift] using mapped
  have firstExitEqual :
      polylineFirstExit transformed = transformedExit :=
    polylineFirstExit_eq transformedTailHead
  have relativeMiddleWeakLeft :
      sourceLiteralIndex = 1 → relativeExit.1 ≤ 0 := by
    intro middle
    have weak := middleWeakLeft middle
    have weak' : sourceExit.1 ≤ sourceFirst.1 := by
      simpa [sourceFirst] using weak
    rcases sourceExit with ⟨exitX, exitY⟩
    rcases sourceFirst with ⟨firstX, firstY⟩
    simpa [relativeExit, Cell.sub] using sub_nonpos.mpr weak'
  have connectorEqual :
      connector =
        (PositionedPeriodicCNF.orthogonalDetour
          (PlanarOneInThreeNoUnits.sourceLocalPosition
            sourceLiteralIndex)
          (Cell.scale gadgetScale relativeExit)).map
            (Cell.add sourcePoint) := by
    rw [← PositionedPeriodicCNF.orthogonalDetour_add_left]
    simp [connector, port, normalizedSourcePort,
      transformedExit, sourcePoint, Cell.add]
  have generatedHeadNotInConnector :
      generatedHead ∉
        AxisDirection.unitSubdividePolyline connector := by
    intro member
    rw [connectorEqual,
      AxisDirection.unitSubdividePolyline_map_add,
      generatedHeadEqual] at member
    rcases List.mem_map.mp member with
      ⟨point, pointMember, pointEqual⟩
    have pointLocal :
        point =
          sourceLocalClausePosition
            metadata.sourceClause.literals.length :=
      Cell.add_left_injective sourcePoint pointEqual
    subst point
    exact sourceLocalClausePosition_not_mem_sourceExitConnector
      metadata.sourceClause.literals.length sourceLiteralIndex
      metadataPositive metadataWidth sourceLiteralIndexLt
      relativeExit relativeMiddleWeakLeft pointMember
  have generatedHeadNotInTransformed :
      generatedHead ∉
        AxisDirection.unitSubdividePolyline transformed := by
    intro member
    have gridLine :=
      inheritedSourceRoute_unitSubdivision_mem_gridLine
        outputPlacement sourcePlacement metadata.sourceClause
        metadata.clause sourceRoute sourceOrthogonal member
    rw [generatedHeadEqual, sourcePointEqual] at gridLine
    interval_cases hArity : metadata.sourceClause.literals.length
    all_goals
      rcases gridLine with
        ⟨coordinate, line⟩ | ⟨coordinate, line⟩
      all_goals
        norm_num [shift, sourceLocalClausePosition,
          gadgetScale, Cell.add, Cell.scale] at line ⊢
        omega
  have generatedHeadNotInTransformedTail :
      generatedHead ∉
        AxisDirection.unitSubdividePolyline transformed.tail := by
    intro member
    have transformedOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline transformed :=
      inheritedSourceRoute_orthogonal
        outputPlacement sourcePlacement metadata.sourceClause
        metadata.clause sourceRoute sourceOrthogonal
    have gridLine :=
      PeriodicOneInThreePositioned.unitSubdividePolyline_mem_shiftedGridLine
        gadgetScale shift transformedOrthogonal.tail
        (fun listed listedMember => by
          have listedFull : listed ∈ transformed :=
            List.mem_of_mem_tail listedMember
          unfold transformed inheritedSourceRoute
            PeriodicOrthocrossing.translatePolyline at listedFull
          rcases List.mem_map.mp listedFull with
            ⟨scaled, scaledMember, rfl⟩
          rcases List.mem_map.mp scaledMember with
            ⟨sourcePoint, sourcePointMember, rfl⟩
          exact
            ⟨⟨sourcePoint.1, by
                simp [shift, Cell.add, Cell.scale]⟩,
              ⟨sourcePoint.2, by
                simp [shift, Cell.add, Cell.scale]⟩⟩)
        member
    rw [generatedHeadEqual, sourcePointEqual] at gridLine
    interval_cases hArity : metadata.sourceClause.literals.length
    all_goals
      rcases gridLine with
        ⟨coordinate, line⟩ | ⟨coordinate, line⟩
      all_goals
        norm_num [shift, sourceLocalClausePosition,
          gadgetScale, Cell.add, Cell.scale] at line ⊢
        omega
  have connectorHead : connector.head? = some port := by
    simp [connector]
  have connectorLast : connector.getLast? = some transformedExit := by
    simp [connector]
  have connectorNonempty : connector ≠ [] := by
    intro empty
    simp [empty] at connectorHead
  intro member
  change generatedHead ∈
    AxisDirection.unitSubdividePolyline
      (replacePolylineHead
        (PositionedPeriodicCNF.orthogonalDetour port
          (polylineFirstExit transformed)) transformed) at member
  rw [firstExitEqual] at member
  change generatedHead ∈
    AxisDirection.unitSubdividePolyline
      (replacePolylineHead connector transformed) at member
  rw [replacePolylineHead,
    AxisDirection.unitSubdividePolyline_joinAtEndpoint
      connectorNonempty connectorLast transformedTailHead,
    LeanTrominoes.joinAtEndpoint, List.mem_append] at member
  rcases member with connectorMember | transformedTailMember
  · exact generatedHeadNotInConnector connectorMember
  · exact generatedHeadNotInTransformedTail
      (List.mem_of_mem_tail transformedTailMember)

private theorem value_eq_of_mem_zipIdx_same_index
    {alpha : Type*} {values : List alpha}
    {first second : alpha} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second := by
  exact
    (List.mem_zipIdx' firstMember).2.trans
      (List.mem_zipIdx' secondMember).2.symm

private theorem pair_eq_of_mem_of_mem_of_fst_eq
    {First Second : Type*}
    (pairs : List (First × Second))
    (fstNodup : (pairs.map Prod.fst).Nodup)
    {first second : First × Second}
    (firstMember : first ∈ pairs)
    (secondMember : second ∈ pairs)
    (fstEq : first.1 = second.1) :
    first = second := by
  have pairsNodup : pairs.Nodup :=
    fstNodup.of_map Prod.fst
  exact
    ((List.nodup_map_iff_inj_on pairsNodup).mp fstNodup)
      first firstMember second secondMember fstEq

/-- Every selected inherited suffix avoids the canonical clause endpoint of
its generated incidence when middle source routes exit weakly left. -/
theorem inheritedRouteSuffixesRoutes_clauseEndpoint_not_mem
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
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
              some exit)
    (sourceMiddleWeakLeft :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral,
          (sourceLiteral, 1) ∈ sourceClause.literals.zipIdx →
          ∀ exit,
            (sourceRoutes sourceClauseIndex 1).tail.head? = some exit →
            exit.1 ≤
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause).1)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    PositionedPeriodicCNF.canonicalClausePosition
        (placement source sourcePlacement) clause ∉
      AxisDirection.unitSubdividePolyline
        (inheritedRouteSuffixesRoutes
          source sourcePlacement sourceRoutes
          clauseIndex literalIndex) := by
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  have generatedClauseEqual : data.generatedClause = clause :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedClauseMember clauseMember
  subst clause
  have generatedLiteralEqual : data.generatedLiteral = literal :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedLiteralMember literalMember
  subst literal
  rcases normalizedLocalEndpoint_inherited
      source sourcePlacement sourceWidth sourceDistinct
      data.generatedClauseMember data.generatedLiteralMember
      data.sourceLiteral.atom data.literalAtom with
    ⟨metadata, recoveredSourceLiteral, recoveredSourceLiteralIndex,
      metadataLookup, metadataClause, metadataSourceClauseMember,
      recoveredSourceLiteralMember, recoveredSourceLiteralAtom,
      _recoveredLiteralOffset, _recoveredLocalEndpoint⟩
  have metadataLiteralMember :
      (data.generatedLiteral, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [metadataClause] using
      data.generatedLiteralMember
  have recoveredOccurrencePair :
      ((data.generatedLiteral, clauseIndex, literalIndex),
        (recoveredSourceLiteral, metadata.sourceClauseIndex,
          recoveredSourceLiteralIndex)) ∈
        PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs
          source.erase data.sourceLiteral.atom :=
    originalOccurrencePair_of_formulaMetadataLookup
      source sourceWidth sourceDistinct data.sourceLiteral.atom
      metadataLookup metadataLiteralMember
      recoveredSourceLiteralMember data.literalAtom
      recoveredSourceLiteralAtom
  let pairs :=
    PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs
      source.erase data.sourceLiteral.atom
  have pairsFstNodup : (pairs.map Prod.fst).Nodup := by
    rw [show
      pairs.map Prod.fst =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (PeriodicOneInThreeNoUnits.formula source.erase)
          (.inl data.sourceLiteral.atom) by
      simpa [pairs] using
        PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs_fst
          source.erase data.sourceLiteral.atom]
    exact PeriodicOneInThreeToThreeDM.occurrencesOf_nodup _ _
  have recoveredOccurrencePairMember :
      ((data.generatedLiteral, clauseIndex, literalIndex),
        (recoveredSourceLiteral, metadata.sourceClauseIndex,
          recoveredSourceLiteralIndex)) ∈ pairs := by
    simpa [pairs] using recoveredOccurrencePair
  have dataOccurrencePairMember :
      ((data.generatedLiteral, clauseIndex, literalIndex),
        (data.sourceLiteral, data.sourceClauseIndex,
          data.sourceLiteralIndex)) ∈ pairs := by
    simpa [pairs] using data.originalOccurrencePair
  have occurrencePairEqual :
      ((data.generatedLiteral, clauseIndex, literalIndex),
        (recoveredSourceLiteral, metadata.sourceClauseIndex,
          recoveredSourceLiteralIndex)) =
      ((data.generatedLiteral, clauseIndex, literalIndex),
        (data.sourceLiteral, data.sourceClauseIndex,
          data.sourceLiteralIndex)) :=
    pair_eq_of_mem_of_mem_of_fst_eq pairs pairsFstNodup
      recoveredOccurrencePairMember dataOccurrencePairMember
      rfl
  have sourceOccurrenceEqual :
      (recoveredSourceLiteral, metadata.sourceClauseIndex,
        recoveredSourceLiteralIndex) =
      (data.sourceLiteral, data.sourceClauseIndex,
        data.sourceLiteralIndex) :=
    congrArg Prod.snd occurrencePairEqual
  have recoveredSourceLiteralEqual :
      recoveredSourceLiteral = data.sourceLiteral :=
    congrArg Prod.fst sourceOccurrenceEqual
  have recoveredSourceClauseIndexEqual :
      metadata.sourceClauseIndex = data.sourceClauseIndex :=
    congrArg (fun occurrence => occurrence.2.1) sourceOccurrenceEqual
  have recoveredSourceLiteralIndexEqual :
      recoveredSourceLiteralIndex = data.sourceLiteralIndex :=
    congrArg (fun occurrence => occurrence.2.2) sourceOccurrenceEqual
  have metadataSourceClauseEqual :
      metadata.sourceClause = data.sourceClause :=
    value_eq_of_mem_zipIdx_same_index
      metadataSourceClauseMember
      (by
        simpa [recoveredSourceClauseIndexEqual] using
          data.sourceClauseMember)
  have metadataSourceLiteralMember :
      (data.sourceLiteral, data.sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx := by
    simpa [recoveredSourceLiteralEqual,
      recoveredSourceLiteralIndexEqual] using
      recoveredSourceLiteralMember
  rcases sourceExits data.sourceClause data.sourceClauseIndex
      data.sourceClauseMember data.sourceLiteral
      data.sourceLiteralIndex data.sourceLiteralMember with
    ⟨sourceExit, sourceTailHead⟩
  have middleWeakLeft :
      data.sourceLiteralIndex = 1 →
        sourceExit.1 ≤
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement metadata.sourceClause).1 := by
    intro middle
    rw [metadataSourceClauseEqual]
    apply sourceMiddleWeakLeft
      data.sourceClause data.sourceClauseIndex
      data.sourceClauseMember data.sourceLiteral
    · simpa [middle] using data.sourceLiteralMember
    · simpa [middle] using sourceTailHead
  have sourceHeadAtMetadataClause :
      (sourceRoutes
          data.sourceClauseIndex data.sourceLiteralIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement metadata.sourceClause) := by
    simpa [metadataSourceClauseEqual] using
      (sourceEndpoints data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember data.sourceLiteral
        data.sourceLiteralIndex data.sourceLiteralMember).1
  have excluded :=
    canonicalClausePosition_not_mem_inheritedRouteSuffix
      source sourcePlacement sourceWidth sourceDistinct
      metadataLookup metadataLiteralMember
      metadataSourceLiteralMember data.literalAtom
      (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
      sourceHeadAtMetadataClause
      sourceExit sourceTailHead
      (sourceOrthogonal data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember data.sourceLiteral
        data.sourceLiteralIndex data.sourceLiteralMember)
      middleWeakLeft
  rw [metadataSourceClauseEqual] at excluded
  simpa [inheritedRouteSuffixesRoutes, dataLookup,
    metadataClause] using excluded

/-- Every genuine inherited unit-elimination route retains first-endpoint
isolation after its local prefix and inherited suffix are spliced. -/
theorem splicedRoutes_headNotInTail_of_inherited
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
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
              some exit)
    (sourceMiddleWeakLeft :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral,
          (sourceLiteral, 1) ∈ sourceClause.literals.zipIdx →
          ∀ exit,
            (sourceRoutes sourceClauseIndex 1).tail.head? = some exit →
            exit.1 ≤
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause).1)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        (splicedRoutes source sourcePlacement
          (inheritedRouteSuffixes source sourcePlacement
            sourceWidth sourceDistinct sourceRoutes
            sourceEndpoints sourceOrthogonal sourceExits)
          clauseIndex literalIndex)) := by
  let inherited :=
    inheritedRouteSuffixes source sourcePlacement
      sourceWidth sourceDistinct sourceRoutes
      sourceEndpoints sourceOrthogonal sourceExits
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
  have localSimple :=
    normalizedLocalRoutes_isSimple_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember
  have localFresh :=
    AxisDirection.headNotInTail_unitSubdividePolyline_of_simple
      localOrthogonal localSimple
  have suffixValid :=
    inheritedRouteSuffixesRoutes_valid
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
      clauseMember literalMember sourceAtom literalSource
  have headNotInSuffix :=
    inheritedRouteSuffixesRoutes_clauseEndpoint_not_mem
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
      sourceMiddleWeakLeft clauseMember literalMember
      sourceAtom literalSource
  have joined :=
    AxisDirection.HeadNotInTail.unitSubdividePolyline_joinAtEndpoint
      localFresh localNonempty localEndpoints.1 localEndpoints.2
      suffixValid.1 headNotInSuffix
  simpa [splicedRoutes,
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes,
    completeRoutesEqual, inherited, suffix] using joined

/-- Every inherited unit-elimination suffix contains at least its boundary
port and transformed source-clause point. -/
theorem inheritedRouteSuffix_length_ge_two
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceLiteralIndex : Nat)
    (sourceRoute : List Cell) :
    2 ≤
      (inheritedRouteSuffix outputPlacement sourcePlacement
        sourceClause generatedClause sourceLiteralIndex
        sourceRoute).length := by
  simp only [inheritedRouteSuffix, replacePolylineHead, joinAtEndpoint,
    List.length_append, List.length_tail,
    inheritedSourceRoute, PeriodicOrthocrossing.translatePolyline,
    List.length_map, scalePolyline,
    PositionedPeriodicCNF.orthogonalDetour,
    List.length_cons, List.length_nil]
  omega

/-- Every genuine complete unit-elimination route contains the first edge of
its normalized local prefix, independently of which valid suffix is used. -/
theorem splicedRoutes_length_ge_two_of_members
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
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (splicedRoutes source sourcePlacement inherited
        clauseIndex literalIndex).length := by
  have rawLocalLength :=
    localRoutes_length_ge_two_of_members
      source sourceWidth sourceDistinct clauseMember literalMember
  rcases formulaClauseMetadata_lookup source clauseMember with
    ⟨metadata, metadataLookup, _metadataClause⟩
  have localLength :
      2 ≤
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex).length := by
    simpa [normalizedLocalRoutes, metadataLookup,
      PositionedPeriodicCNF.normalizeIncidenceRoute] using
      rawLocalLength
  change
    2 ≤
      (joinAtEndpoint
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex)
        ((completeRouteSuffixes source sourcePlacement inherited).routes
          clauseIndex literalIndex)).length
  simp only [joinAtEndpoint, List.length_append]
  omega

/-- Every genuine inherited route retains final-endpoint isolation after
its local unit-elimination prefix and inherited suffix are spliced. -/
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
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
              some exit)
    (sourceIsolation :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          AxisDirection.HeadNotInTail
              (AxisDirection.unitSubdividePolyline
                (sourceRoutes sourceClauseIndex sourceLiteralIndex)) ∧
            AxisDirection.LastNotInDropLast
              (AxisDirection.unitSubdividePolyline
                (sourceRoutes sourceClauseIndex sourceLiteralIndex)))
    (sourceVerticalIfLastIsExit :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∀ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit →
            PositionedPeriodicCNF.canonicalLiteralPosition
                sourcePlacement sourceClause sourceLiteral = exit →
            exit.1 =
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause).1)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
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
            sourceEndpoints sourceOrthogonal sourceExits)
          clauseIndex literalIndex)) := by
  let inherited :=
    inheritedRouteSuffixes source sourcePlacement
      sourceWidth sourceDistinct sourceRoutes
      sourceEndpoints sourceOrthogonal sourceExits
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
      sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
      clauseMember literalMember sourceAtom literalSource
  have suffixFresh :=
    inheritedRouteSuffixesRoutes_lastNotInDropLast
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
      sourceIsolation sourceVerticalIfLastIsExit
      clauseMember literalMember sourceAtom literalSource
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

/-- Every complete unit-elimination route, inherited or auxiliary, has an
isolated final endpoint after unit subdivision. -/
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
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
              some exit)
    (sourceIsolation :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          AxisDirection.HeadNotInTail
              (AxisDirection.unitSubdividePolyline
                (sourceRoutes sourceClauseIndex sourceLiteralIndex)) ∧
            AxisDirection.LastNotInDropLast
              (AxisDirection.unitSubdividePolyline
                (sourceRoutes sourceClauseIndex sourceLiteralIndex)))
    (sourceVerticalIfLastIsExit :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∀ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit →
            PositionedPeriodicCNF.canonicalLiteralPosition
                sourcePlacement sourceClause sourceLiteral = exit →
            exit.1 =
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause).1)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (splicedRoutes source sourcePlacement
          (inheritedRouteSuffixes source sourcePlacement
            sourceWidth sourceDistinct sourceRoutes
            sourceEndpoints sourceOrthogonal sourceExits)
          clauseIndex literalIndex)) := by
  rcases atomEqual : literal.atom with sourceAtom | auxiliary
  · exact splicedRoutes_lastNotInDropLast_of_inherited
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
      sourceIsolation sourceVerticalIfLastIsExit
      clauseMember literalMember sourceAtom atomEqual
  · exact
      (splicedRoutes_endpointIsolation_of_auxiliary
        source sourcePlacement sourceWidth sourceDistinct
        (inheritedRouteSuffixes source sourcePlacement
          sourceWidth sourceDistinct sourceRoutes
          sourceEndpoints sourceOrthogonal sourceExits)
        clauseMember literalMember auxiliary atomEqual).2

/-- Every complete unit-elimination route has both endpoints isolated after
unit subdivision.  For inherited routes, first-endpoint isolation only needs
the weak-left first-exit property of the middle source incidence. -/
theorem splicedRoutes_endpointIsolation
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
    (sourceExits :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∃ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
              some exit)
    (sourceIsolation :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          AxisDirection.HeadNotInTail
              (AxisDirection.unitSubdividePolyline
                (sourceRoutes sourceClauseIndex sourceLiteralIndex)) ∧
            AxisDirection.LastNotInDropLast
              (AxisDirection.unitSubdividePolyline
                (sourceRoutes sourceClauseIndex sourceLiteralIndex)))
    (sourceVerticalIfLastIsExit :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          ∀ exit,
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit →
            PositionedPeriodicCNF.canonicalLiteralPosition
                sourcePlacement sourceClause sourceLiteral = exit →
            exit.1 =
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause).1)
    (sourceMiddleWeakLeft :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral,
          (sourceLiteral, 1) ∈ sourceClause.literals.zipIdx →
          ∀ exit,
            (sourceRoutes sourceClauseIndex 1).tail.head? = some exit →
            exit.1 ≤
              (PositionedPeriodicCNF.canonicalClausePosition
                sourcePlacement sourceClause).1)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (splicedRoutes source sourcePlacement
            (inheritedRouteSuffixes source sourcePlacement
              sourceWidth sourceDistinct sourceRoutes
              sourceEndpoints sourceOrthogonal sourceExits)
            clauseIndex literalIndex)) ∧
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline
          (splicedRoutes source sourcePlacement
            (inheritedRouteSuffixes source sourcePlacement
              sourceWidth sourceDistinct sourceRoutes
              sourceEndpoints sourceOrthogonal sourceExits)
            clauseIndex literalIndex)) := by
  rcases atomEqual : literal.atom with sourceAtom | auxiliary
  · exact
      ⟨splicedRoutes_headNotInTail_of_inherited
          source sourcePlacement sourceWidth sourceDistinct
          sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
          sourceMiddleWeakLeft clauseMember literalMember
          sourceAtom atomEqual,
        splicedRoutes_lastNotInDropLast_of_inherited
          source sourcePlacement sourceWidth sourceDistinct
          sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
          sourceIsolation sourceVerticalIfLastIsExit
          clauseMember literalMember sourceAtom atomEqual⟩
  · exact splicedRoutes_endpointIsolation_of_auxiliary
      source sourcePlacement sourceWidth sourceDistinct
      (inheritedRouteSuffixes source sourcePlacement
        sourceWidth sourceDistinct sourceRoutes
        sourceEndpoints sourceOrthogonal sourceExits)
      clauseMember literalMember auxiliary atomEqual

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
