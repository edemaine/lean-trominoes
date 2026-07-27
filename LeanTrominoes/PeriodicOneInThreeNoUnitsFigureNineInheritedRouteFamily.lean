import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedRouteSplicing

/-!
# Complete original-source suffixes for composed routes

The two-stage incidence classifier supplies all source indices needed by the
direct splice.  This file packages those data behind a proof-backed total
selector and builds a suffix family for precisely the final incidences whose
atoms have the twice-inherited form `.inl (.inl sourceAtom)`.

First-stage and second-stage auxiliaries already terminate inside the
composed finite drawing and will receive singleton suffixes separately.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

/-- Canonical suffixes required only for variables inherited through both
Figure 9 and unit elimination. -/
structure OriginalInheritedCanonicalIncidenceRouteSuffixes
    {Variable : Type*}
    (target :
      PositionedPeriodicCNF
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (placement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (splicePoint : Nat → Nat → Cell) where
  routes : PositionedPeriodicCNF.IncidenceRoutes
  endpoints :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ target.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        ∀ sourceAtom,
          literal.atom = .inl (.inl sourceAtom) →
          (routes clauseIndex literalIndex).head? =
              some (splicePoint clauseIndex literalIndex) ∧
            (routes clauseIndex literalIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  placement clause literal)
  orthogonal :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈ target.clauses.zipIdx →
      ∀ literal literalIndex,
        (literal, literalIndex) ∈ clause.literals.zipIdx →
        ∀ sourceAtom,
          literal.atom = .inl (.inl sourceAtom) →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex)

/-- Original and final incidence data needed to construct one direct
composed inherited suffix. -/
structure InheritedIncidenceData
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) where
  generatedClause :
    PositionedPeriodicClause
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
  generatedLiteral :
    PeriodicLiteral
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
  sourceClause : PositionedPeriodicClause Variable
  sourceClauseIndex : Nat
  sourceLiteral : PeriodicLiteral Variable
  sourceLiteralIndex : Nat
  generatedClauseMember :
    (generatedClause, clauseIndex) ∈
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx
  generatedLiteralMember :
    (generatedLiteral, literalIndex) ∈
      generatedClause.literals.zipIdx
  sourceClauseMember :
    (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx
  sourceLiteralMember :
    (sourceLiteral, sourceLiteralIndex) ∈
      sourceClause.literals.zipIdx
  literalAtom :
    generatedLiteral.atom =
      .inl (.inl sourceLiteral.atom)
  literalOffset :
    generatedLiteral.offset = sourceLiteral.offset
  localEndpoint :
    normalizedLocalEndpoint source sourcePlacement
        clauseIndex literalIndex =
      normalizedSourcePort
        (composedPlacement source sourcePlacement)
        sourceClause generatedClause sourceLiteralIndex

/-- Select original-incidence data whenever such data exists. -/
noncomputable def inheritedIncidenceData?
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) :
    Option
      (InheritedIncidenceData
        source sourcePlacement clauseIndex literalIndex) := by
  classical
  exact
    if existsData :
        Nonempty
          (InheritedIncidenceData
            source sourcePlacement clauseIndex literalIndex)
    then some (Classical.choice existsData)
    else none

/-- Every genuine twice-inherited incidence makes the total data selector
succeed. -/
theorem inheritedIncidenceData?_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource :
      literal.atom = .inl (.inl sourceAtom)) :
    ∃ data,
      inheritedIncidenceData?
        source sourcePlacement clauseIndex literalIndex =
          some data := by
  rcases normalizedLocalEndpoint_inherited
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨metadata, sourceLiteral, sourceLiteralIndex,
      _metadataLookup, metadataClause, sourceClauseMember,
      sourceLiteralMember, sourceLiteralAtom,
      literalOffset, localEndpoint⟩
  have literalAtom :
      literal.atom = .inl (.inl sourceLiteral.atom) := by
    rw [literalSource, sourceLiteralAtom]
  let witness :
      InheritedIncidenceData
        source sourcePlacement clauseIndex literalIndex :=
    { generatedClause := clause
      generatedLiteral := literal
      sourceClause := metadata.sourceClause
      sourceClauseIndex := metadata.sourceClauseIndex
      sourceLiteral := sourceLiteral
      sourceLiteralIndex := sourceLiteralIndex
      generatedClauseMember := clauseMember
      generatedLiteralMember := literalMember
      sourceClauseMember := sourceClauseMember
      sourceLiteralMember := sourceLiteralMember
      literalAtom := literalAtom
      literalOffset := literalOffset
      localEndpoint := by
        simpa [metadataClause] using localEndpoint }
  have existsData :
      Nonempty
        (InheritedIncidenceData
          source sourcePlacement clauseIndex literalIndex) :=
    ⟨witness⟩
  rw [inheritedIncidenceData?, dif_pos existsData]
  exact ⟨Classical.choice existsData, rfl⟩

/-- Total direct-suffix lookup selected from original incidence metadata. -/
noncomputable def inheritedRouteSuffixesRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match inheritedIncidenceData?
        source sourcePlacement clauseIndex literalIndex with
    | none => []
    | some data =>
        inheritedRouteSuffix
          (composedPlacement source sourcePlacement)
          sourcePlacement data.sourceClause data.generatedClause
          data.sourceLiteralIndex
          (sourceRoutes
            data.sourceClauseIndex data.sourceLiteralIndex)

private theorem value_eq_of_mem_zipIdx_same_index
    {α : Type*} {values : List α}
    {first second : α} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second := by
  exact
    (List.mem_zipIdx' firstMember).2.trans
      (List.mem_zipIdx' secondMember).2.symm

/-- Pointwise source endpoint, orthogonality, and first-exit certificates
lift to the total direct composed suffix lookup. -/
theorem inheritedRouteSuffixesRoutes_valid
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
          (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).getLast? =
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
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource :
      literal.atom = .inl (.inl sourceAtom)) :
    (inheritedRouteSuffixesRoutes
        source sourcePlacement sourceRoutes
        clauseIndex literalIndex).head? =
        some
          (normalizedLocalEndpoint
            source sourcePlacement clauseIndex literalIndex) ∧
      (inheritedRouteSuffixesRoutes
        source sourcePlacement sourceRoutes
        clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (composedPlacement source sourcePlacement) clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (inheritedRouteSuffixesRoutes
          source sourcePlacement sourceRoutes
          clauseIndex literalIndex) := by
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  have generatedClauseEqual :
      data.generatedClause = clause :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedClauseMember clauseMember
  subst clause
  have generatedLiteralEqual :
      data.generatedLiteral = literal :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedLiteralMember literalMember
  subst literal
  have endpoints :=
    sourceEndpoints
      data.sourceClause data.sourceClauseIndex
      data.sourceClauseMember
      data.sourceLiteral data.sourceLiteralIndex
      data.sourceLiteralMember
  have valid :=
    inheritedRouteSuffix_valid
      source sourcePlacement
      data.sourceClause data.generatedClause
      data.sourceLiteral data.generatedLiteral
      data.sourceLiteralIndex
      (sourceRoutes
        data.sourceClauseIndex data.sourceLiteralIndex)
      endpoints.1 endpoints.2
      (sourceOrthogonal
        data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex
        data.sourceLiteralMember)
      (sourceExits
        data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex
        data.sourceLiteralMember)
      data.literalAtom data.literalOffset
  simpa [inheritedRouteSuffixesRoutes, dataLookup,
    data.localEndpoint] using valid

/-- Any canonical orthogonal source route family with certified first exits
induces all direct suffixes for variables inherited through both
transformations. -/
noncomputable def inheritedRouteSuffixes
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
          (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).getLast? =
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
            (sourceRoutes
              sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit) :
    OriginalInheritedCanonicalIncidenceRouteSuffixes
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source))
      (composedPlacement source sourcePlacement)
      (normalizedLocalEndpoint source sourcePlacement) where
  routes :=
    inheritedRouteSuffixesRoutes
      source sourcePlacement sourceRoutes
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
      sourceAtom literalSource
    have valid :=
      inheritedRouteSuffixesRoutes_valid
        source sourcePlacement sourceWidth sourceDistinct
        sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
        clauseMember literalMember sourceAtom literalSource
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
      sourceAtom literalSource
    exact
      (inheritedRouteSuffixesRoutes_valid
        source sourcePlacement sourceWidth sourceDistinct
        sourceRoutes sourceEndpoints sourceOrthogonal sourceExits
        clauseMember literalMember sourceAtom literalSource).2.2

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
