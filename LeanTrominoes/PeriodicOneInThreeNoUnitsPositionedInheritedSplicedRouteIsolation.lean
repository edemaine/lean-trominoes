import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedAuxiliaryRouteIsolation
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteFamilyIsolation

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

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
