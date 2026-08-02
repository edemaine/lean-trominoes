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

private theorem gridPolylineSegments_start_mem
    {points : List Cell} {segment : GridSegment}
    (segmentMember : segment ∈ gridPolylineSegments points) :
    segment.start ∈ points := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [gridPolylineSegments] at segmentMember
  | cons_cons first second rest _ tailInduction =>
      simp only [gridPolylineSegments, List.mem_cons] at segmentMember
      rcases segmentMember with segmentEqual | segmentMember
      · subst segment
        simp
      · exact List.mem_cons_of_mem first
          (tailInduction second segmentMember)

private theorem value_eq_of_mem_zipIdx_same_index
    {alpha : Type*} {values : List alpha}
    {first second : alpha} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second := by
  exact
    (List.mem_zipIdx' firstMember).2.trans
      (List.mem_zipIdx' secondMember).2.symm

/-- Every unit-subdivision point of an orthogonal polyline whose listed
points lie on a translated rectangular lattice lies on one of that lattice's
horizontal or vertical grid lines. -/
theorem unitSubdividePolyline_mem_shiftedGridLine
    (factor : Int) (shift : Cell)
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (listedOnGrid :
      ∀ listed ∈ points,
        (∃ x, listed.1 = shift.1 + factor * x) ∧
          (∃ y, listed.2 = shift.2 + factor * y))
    {point : Cell}
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline points) :
    (∃ x, point.1 = shift.1 + factor * x) ∨
      (∃ y, point.2 = shift.2 + factor * y) := by
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        orthogonal pointMember with
    pointListed | ⟨segment, segmentMember, pointInterior⟩
  · exact Or.inl (listedOnGrid point pointListed).1
  · have startGrid :=
      listedOnGrid segment.start
        (gridPolylineSegments_start_mem segmentMember)
    rcases pointInterior with horizontal | vertical
    · right
      rcases startGrid.2 with ⟨y, startY⟩
      exact ⟨y, horizontal.2.1.trans startY⟩
    · left
      rcases startGrid.1 with ⟨x, startX⟩
      exact ⟨x, vertical.2.1.trans startX⟩

/-- Every point of a refined inherited source route lies on a horizontal or
vertical line of its translated scale-twelve source lattice. -/
theorem inheritedSourceRoute_unitSubdivision_mem_gridLine
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
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
    (∃ x,
        point.1 = shift.1 + PlanarOneInThree.gadgetScale * x) ∨
      (∃ y,
        point.2 = shift.2 + PlanarOneInThree.gadgetScale * y) := by
  let shift :=
    inheritedSourceRouteShift outputPlacement sourcePlacement
      sourceClause generatedClause
  apply unitSubdividePolyline_mem_shiftedGridLine
    PlanarOneInThree.gadgetScale shift
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

/-- None of the three local Figure 9 clause ports occurs in the canonical
boundary connector from the corresponding source port to the source-clause
point. -/
theorem sourceLocalClausePosition_not_mem_sourceConnector
    (sourceLiteralIndex : Nat)
    (indexLt : sourceLiteralIndex < 3) :
    sourceLocalClausePosition sourceLiteralIndex ∉
      AxisDirection.unitSubdividePolyline
        (PositionedPeriodicCNF.orthogonalDetour
          (PlanarOneInThreePositioned.sourceLocalPosition
            sourceLiteralIndex)
          (0, 0)) := by
  rcases sourceLiteralIndex with _ | sourceLiteralIndex
  · norm_num [sourceLocalClausePosition,
      PlanarOneInThreePositioned.sourceLocalPosition,
      PositionedPeriodicCNF.orthogonalDetour,
      PositionedPeriodicCNF.freshDetourCoordinate,
      AxisDirection.unitSubdividePolyline,
      AxisDirection.unitSegmentPoints,
      AxisDirection.segmentLength,
      AxisDirection.between, AxisDirection.step,
      Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
      List.range_succ]
  · rcases sourceLiteralIndex with _ | sourceLiteralIndex
    · norm_num [sourceLocalClausePosition,
        PlanarOneInThreePositioned.sourceLocalPosition,
        PositionedPeriodicCNF.orthogonalDetour,
        PositionedPeriodicCNF.freshDetourCoordinate,
        AxisDirection.unitSubdividePolyline,
        AxisDirection.unitSegmentPoints,
        AxisDirection.segmentLength,
        AxisDirection.between, AxisDirection.step,
        Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
        List.range_succ]
    · have indexZero : sourceLiteralIndex = 0 := by omega
      subst sourceLiteralIndex
      norm_num [sourceLocalClausePosition,
        PlanarOneInThreePositioned.sourceLocalPosition,
        PositionedPeriodicCNF.orthogonalDetour,
        PositionedPeriodicCNF.freshDetourCoordinate,
        AxisDirection.unitSubdividePolyline,
        AxisDirection.unitSegmentPoints,
        AxisDirection.segmentLength,
        AxisDirection.between, AxisDirection.step,
        Cell.add, Cell.scale, LeanTrominoes.joinAtEndpoint,
        List.range_succ]

/-- The canonical generated-clause endpoint of an inherited local route is
the source-clause point plus its index-selected local clause port. -/
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
    PositionedPeriodicCNF.canonicalClausePosition
        (placement source sourcePlacement) metadata.clause =
      Cell.add
        (normalizedSourceClausePosition
          (placement source sourcePlacement)
          metadata.sourceClause metadata.clause)
        (sourceLocalClausePosition sourceLiteralIndex) := by
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
              (Cell.scale PlanarOneInThree.gadgetScale
                metadata.sourceClause.position)
              (sourceLocalClausePosition sourceLiteralIndex))
            anchor) := by
    simp [normalizedLocalRoutes, metadataLookup,
      PositionedPeriodicCNF.normalizeIncidenceRoute,
      routeEqual, anchor]
  have headEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          (placement source sourcePlacement) metadata.clause =
        Cell.sub
          (Cell.add
            (Cell.scale PlanarOneInThree.gadgetScale
              metadata.sourceClause.position)
            (sourceLocalClausePosition sourceLiteralIndex))
          anchor :=
    Option.some.inj (endpoints.1.symm.trans segmentHead)
  rw [headEqual]
  apply Prod.ext <;>
    simp [normalizedSourceClausePosition, anchor,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- The generated-clause endpoint of an inherited Figure 9 incidence is
absent from its complete boundary-to-variable suffix. -/
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
    (sourceRoute : List Cell)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement metadata.sourceClause))
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute) :
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
  have sourceLiteralIndexLt : sourceLiteralIndex < 3 := by
    have := (List.mem_zipIdx' sourceLiteralMember).1
    omega
  let outputPlacement := placement source sourcePlacement
  let shift :=
    inheritedSourceRouteShift outputPlacement sourcePlacement
      metadata.sourceClause metadata.clause
  let sourceFirst :=
    PositionedPeriodicCNF.canonicalClausePosition
      sourcePlacement metadata.sourceClause
  let sourcePoint :=
    normalizedSourceClausePosition outputPlacement
      metadata.sourceClause metadata.clause
  let port :=
    normalizedSourcePort outputPlacement
      metadata.sourceClause metadata.clause sourceLiteralIndex
  let connector :=
    PositionedPeriodicCNF.orthogonalDetour port sourcePoint
  let transformed :=
    inheritedSourceRoute outputPlacement sourcePlacement
      metadata.sourceClause metadata.clause sourceRoute
  let generatedHead :=
    PositionedPeriodicCNF.canonicalClausePosition
      outputPlacement metadata.clause
  have generatedHeadEqual :
      generatedHead =
        Cell.add sourcePoint
          (sourceLocalClausePosition sourceLiteralIndex) := by
    exact
      canonicalClausePosition_eq_normalizedSourceClausePosition_add_local
        source sourcePlacement sourceWidth sourceDistinct
        metadataLookup literalMember sourceLiteralMember literalAtom
  have sourcePointEqual :
      sourcePoint =
        Cell.add shift
          (Cell.scale PlanarOneInThree.gadgetScale sourceFirst) := by
    apply Prod.ext <;>
      simp [sourcePoint, shift, sourceFirst,
        inheritedSourceRouteShift,
        normalizedSourceClausePosition,
        PositionedPeriodicCNF.canonicalClausePosition,
        Cell.add, Cell.sub, Cell.scale]
  have connectorEqual :
      connector =
        (PositionedPeriodicCNF.orthogonalDetour
          (PlanarOneInThreePositioned.sourceLocalPosition
            sourceLiteralIndex)
          (0, 0)).map (Cell.add sourcePoint) := by
    rw [← PositionedPeriodicCNF.orthogonalDetour_add_left]
    simp [connector, port, normalizedSourcePort, sourcePoint, Cell.add]
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
        point = sourceLocalClausePosition sourceLiteralIndex :=
      Cell.add_left_injective sourcePoint pointEqual
    subst point
    exact sourceLocalClausePosition_not_mem_sourceConnector
      sourceLiteralIndex sourceLiteralIndexLt pointMember
  have generatedHeadNotInTransformed :
      generatedHead ∉
        AxisDirection.unitSubdividePolyline transformed := by
    intro member
    have gridLine :=
      inheritedSourceRoute_unitSubdivision_mem_gridLine
        outputPlacement sourcePlacement metadata.sourceClause
        metadata.clause sourceRoute sourceOrthogonal member
    rw [generatedHeadEqual, sourcePointEqual] at gridLine
    rcases sourceLiteralIndex with _ | sourceLiteralIndex
    · rcases gridLine with ⟨coordinate, line⟩ | ⟨coordinate, line⟩
      all_goals
        norm_num [shift, sourceLocalClausePosition,
          PlanarOneInThree.gadgetScale,
          Cell.add, Cell.scale] at line ⊢
        omega
    · rcases sourceLiteralIndex with _ | sourceLiteralIndex
      · rcases gridLine with
          ⟨coordinate, line⟩ | ⟨coordinate, line⟩
        all_goals
          norm_num [shift, sourceLocalClausePosition,
            PlanarOneInThree.gadgetScale,
            Cell.add, Cell.scale] at line ⊢
          omega
      · have indexZero : sourceLiteralIndex = 0 := by omega
        subst sourceLiteralIndex
        rcases gridLine with
          ⟨coordinate, line⟩ | ⟨coordinate, line⟩
        all_goals
          norm_num [shift, sourceLocalClausePosition,
            PlanarOneInThree.gadgetScale,
            Cell.add, Cell.scale] at line ⊢
          omega
  have connectorHead : connector.head? = some port := by
    simp [connector]
  have connectorLast : connector.getLast? = some sourcePoint := by
    simp [connector]
  have connectorNonempty : connector ≠ [] := by
    intro empty
    simp [empty] at connectorHead
  have transformedHead : transformed.head? = some sourcePoint := by
    exact inheritedSourceRoute_head?
      outputPlacement sourcePlacement metadata.sourceClause
      metadata.clause sourceRoute sourceHead
  intro member
  change generatedHead ∈
    AxisDirection.unitSubdividePolyline
      (LeanTrominoes.joinAtEndpoint connector transformed) at member
  rw [AxisDirection.unitSubdividePolyline_joinAtEndpoint
    connectorNonempty connectorLast transformedHead,
    LeanTrominoes.joinAtEndpoint, List.mem_append] at member
  rcases member with connectorMember | transformedTailMember
  · exact generatedHeadNotInConnector connectorMember
  · exact generatedHeadNotInTransformed
      (List.mem_of_mem_tail transformedTailMember)

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

/-- Every selected inherited suffix avoids the canonical clause endpoint of
its generated Figure 9 incidence. -/
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
  have metadataLiteralMember :
      (data.generatedLiteral, literalIndex) ∈
        data.metadata.clause.literals.zipIdx := by
    simpa [data.metadataGeneratedClause] using
      data.generatedLiteralMember
  have metadataSourceLiteralMember :
      (data.sourceLiteral, data.sourceLiteralIndex) ∈
        data.metadata.sourceClause.literals.zipIdx := by
    simpa [data.metadataSourceClause] using
      data.sourceLiteralMember
  have endpoints :=
    sourceEndpoints data.sourceClause data.sourceClauseIndex
      data.sourceClauseMember data.sourceLiteral
      data.sourceLiteralIndex data.sourceLiteralMember
  have sourceHead :
      (sourceRoutes data.sourceClauseIndex
          data.sourceLiteralIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement data.metadata.sourceClause) := by
    simpa [data.metadataSourceClause] using endpoints.1
  have excluded :=
    canonicalClausePosition_not_mem_inheritedRouteSuffix
      source sourcePlacement sourceWidth sourceDistinct
      data.metadataLookup metadataLiteralMember
      metadataSourceLiteralMember data.literalAtom
      (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
      sourceHead
      (sourceOrthogonal data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember data.sourceLiteral
        data.sourceLiteralIndex data.sourceLiteralMember)
  rw [data.metadataSourceClause] at excluded
  simpa [inheritedRouteSuffixesRoutes, dataLookup,
    data.metadataGeneratedClause] using excluded

/-- Every genuine inherited Figure 9 route retains first-endpoint isolation
after its local prefix and inherited suffix are spliced. -/
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
    AxisDirection.HeadNotInTail
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
      sourceRoutes sourceEndpoints sourceOrthogonal
      clauseMember literalMember sourceAtom literalSource
  have headNotInSuffix :=
    inheritedRouteSuffixesRoutes_clauseEndpoint_not_mem
      source sourcePlacement sourceWidth sourceDistinct
      sourceRoutes sourceEndpoints sourceOrthogonal
      clauseMember literalMember sourceAtom literalSource
  have joined :=
    AxisDirection.HeadNotInTail.unitSubdividePolyline_joinAtEndpoint
      localFresh localNonempty localEndpoints.1 localEndpoints.2
      suffixValid.1 headNotInSuffix
  simpa [splicedRoutes,
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes,
    completeRoutesEqual, inherited, suffix] using joined

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

/-- Every genuine complete Figure 9 route has both endpoints isolated after
unit subdivision. -/
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
    AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (splicedRoutes source sourcePlacement
            (inheritedRouteSuffixes source sourcePlacement
              sourceWidth sourceDistinct sourceRoutes
              sourceEndpoints sourceOrthogonal)
            clauseIndex literalIndex)) ∧
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline
          (splicedRoutes source sourcePlacement
            (inheritedRouteSuffixes source sourcePlacement
              sourceWidth sourceDistinct sourceRoutes
              sourceEndpoints sourceOrthogonal)
            clauseIndex literalIndex)) := by
  rcases atomEqual : literal.atom with sourceAtom | auxiliary
  · exact
      ⟨splicedRoutes_headNotInTail_of_inherited
          source sourcePlacement sourceWidth sourceDistinct
          sourceRoutes sourceEndpoints sourceOrthogonal
          clauseMember literalMember sourceAtom atomEqual,
        splicedRoutes_lastNotInDropLast_of_inherited
          source sourcePlacement sourceWidth sourceDistinct
          sourceRoutes sourceEndpoints sourceOrthogonal
          sourceLength sourceSimple clauseMember literalMember
          sourceAtom atomEqual⟩
  · exact splicedRoutes_endpointIsolation_of_auxiliary
      source sourcePlacement sourceWidth sourceDistinct
      (inheritedRouteSuffixes source sourcePlacement
        sourceWidth sourceDistinct sourceRoutes
        sourceEndpoints sourceOrthogonal)
      clauseMember literalMember auxiliary atomEqual

end PeriodicOneInThreePositioned
end LeanTrominoes
