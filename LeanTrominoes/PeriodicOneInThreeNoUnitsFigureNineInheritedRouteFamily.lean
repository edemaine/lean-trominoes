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
composed inherited suffix, including the two occurrence-pair witnesses used
by global separation. -/
abbrev InheritedIncidenceData
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) :=
  InheritedEndpointProvenance
    source sourcePlacement clauseIndex literalIndex

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
  rcases inheritedEndpointProvenance_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨witness⟩
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

private theorem pair_fst_eq_of_snd_eq
    {First Second : Type*}
    (pairs : List (First × Second))
    (pairsSndNodup : (pairs.map Prod.snd).Nodup)
    {firstPair secondPair : First × Second}
    (firstMember : firstPair ∈ pairs)
    (secondMember : secondPair ∈ pairs)
    (sndEqual : firstPair.2 = secondPair.2) :
    firstPair.1 = secondPair.1 := by
  have pairsNodup : pairs.Nodup :=
    pairsSndNodup.of_map Prod.snd
  have pairEqual :=
    ((List.nodup_map_iff_inj_on pairsNodup).mp pairsSndNodup)
      _ firstMember _ secondMember sndEqual
  exact congrArg Prod.fst pairEqual

/-- Distinct final twice-inherited incidences recover distinct original
source coordinates.  Injectivity composes the global unit-elimination and
Figure 9 occurrence pairings stored in the endpoint provenance. -/
theorem InheritedEndpointProvenance.sourceCoordinatesDistinct_of_generatedDistinct
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      InheritedEndpointProvenance source sourcePlacement
        firstClauseIndex firstLiteralIndex)
    (second :
      InheritedEndpointProvenance source sourcePlacement
        secondClauseIndex secondLiteralIndex)
    (generatedDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    first.sourceClauseIndex ≠ second.sourceClauseIndex ∨
      first.sourceLiteralIndex ≠ second.sourceLiteralIndex := by
  by_contra sourceNotDistinct
  simp only [not_or, not_ne_iff] at sourceNotDistinct
  have secondSourceClauseMember :
      (second.sourceClause, first.sourceClauseIndex) ∈
        source.clauses.zipIdx := by
    simpa [sourceNotDistinct.1] using second.sourceClauseMember
  have sourceClauseEqual : first.sourceClause = second.sourceClause :=
    value_eq_of_mem_zipIdx_same_index
      first.sourceClauseMember secondSourceClauseMember
  have sourceLiteralEqual : first.sourceLiteral = second.sourceLiteral := by
    have firstSourceLiteralMember :
        (first.sourceLiteral, first.sourceLiteralIndex) ∈
          second.sourceClause.literals.zipIdx := by
      simpa [sourceClauseEqual] using first.sourceLiteralMember
    have secondSourceLiteralMember :
        (second.sourceLiteral, first.sourceLiteralIndex) ∈
          second.sourceClause.literals.zipIdx := by
      simpa [sourceNotDistinct.2] using second.sourceLiteralMember
    exact value_eq_of_mem_zipIdx_same_index
      firstSourceLiteralMember secondSourceLiteralMember
  let figureNinePairs :=
    PeriodicOneInThree.formulaOriginalOccurrencePairs
      source.erase first.sourceLiteral.atom
  have firstFigureNinePairMember :
      ((first.figureNineLiteral,
          first.unitMetadata.sourceClauseIndex,
          first.figureNineLiteralIndex),
        (first.sourceLiteral, first.sourceClauseIndex,
          first.sourceLiteralIndex)) ∈ figureNinePairs := by
    simpa [figureNinePairs] using first.figureNineOriginalOccurrencePair
  have secondFigureNinePairMember :
      ((second.figureNineLiteral,
          second.unitMetadata.sourceClauseIndex,
          second.figureNineLiteralIndex),
        (second.sourceLiteral, second.sourceClauseIndex,
          second.sourceLiteralIndex)) ∈ figureNinePairs := by
    simpa [figureNinePairs, sourceLiteralEqual] using
      second.figureNineOriginalOccurrencePair
  have figureNinePairsSndNodup :
      (figureNinePairs.map Prod.snd).Nodup := by
    rw [show
      figureNinePairs.map Prod.snd =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          source.erase first.sourceLiteral.atom by
      simpa [figureNinePairs] using
        PeriodicOneInThree.formulaOriginalOccurrencePairs_snd
          source.erase sourceWidth first.sourceLiteral.atom]
    exact PeriodicOneInThreeToThreeDM.occurrencesOf_nodup _ _
  have sourceOccurrencesEqual :
      (first.sourceLiteral, first.sourceClauseIndex,
          first.sourceLiteralIndex) =
        (second.sourceLiteral, second.sourceClauseIndex,
          second.sourceLiteralIndex) := by
    simp [sourceLiteralEqual, sourceNotDistinct.1,
      sourceNotDistinct.2]
  have figureNineOccurrencesEqual :=
    pair_fst_eq_of_snd_eq figureNinePairs
      figureNinePairsSndNodup
      firstFigureNinePairMember secondFigureNinePairMember
      sourceOccurrencesEqual
  have figureNineLiteralEqual :
      first.figureNineLiteral = second.figureNineLiteral :=
    congrArg (fun occurrence => occurrence.1)
      figureNineOccurrencesEqual
  let unitPairs :=
    PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs
      (PeriodicOneInThreePositioned.formula source).erase
      first.figureNineLiteral.atom
  have firstUnitPairMember :
      ((first.generatedLiteral, firstClauseIndex, firstLiteralIndex),
        (first.figureNineLiteral,
          first.unitMetadata.sourceClauseIndex,
          first.figureNineLiteralIndex)) ∈ unitPairs := by
    simpa [unitPairs] using first.unitOriginalOccurrencePair
  have secondUnitPairMember :
      ((second.generatedLiteral, secondClauseIndex, secondLiteralIndex),
        (second.figureNineLiteral,
          second.unitMetadata.sourceClauseIndex,
          second.figureNineLiteralIndex)) ∈ unitPairs := by
    simpa [unitPairs, figureNineLiteralEqual] using
      second.unitOriginalOccurrencePair
  have unitPairsSndNodup : (unitPairs.map Prod.snd).Nodup := by
    rw [show
      unitPairs.map Prod.snd =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (PeriodicOneInThreePositioned.formula source).erase
          first.figureNineLiteral.atom by
      simpa [unitPairs] using
        PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs_snd
          (PeriodicOneInThreePositioned.formula source).erase
          first.figureNineLiteral.atom]
    exact PeriodicOneInThreeToThreeDM.occurrencesOf_nodup _ _
  have generatedOccurrencesEqual :=
    pair_fst_eq_of_snd_eq unitPairs unitPairsSndNodup
      firstUnitPairMember secondUnitPairMember
      figureNineOccurrencesEqual
  have generatedCoordinatesEqual :
      (firstClauseIndex, firstLiteralIndex) =
        (secondClauseIndex, secondLiteralIndex) := by
    exact congrArg
      (fun occurrence => (occurrence.2.1, occurrence.2.2))
      generatedOccurrencesEqual
  exact generatedDistinct.elim
    (fun clauseNe => clauseNe (congrArg Prod.fst generatedCoordinatesEqual))
    (fun literalNe => literalNe (congrArg Prod.snd generatedCoordinatesEqual))

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
