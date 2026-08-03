import LeanTrominoes.PeriodicOneInThreePositionedAuxiliaryEndpoints
import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteSplicing
import LeanTrominoes.PeriodicOneInThreePositionedOriginalOccurrenceProvenance

/-!
# Complete inherited Figure 9 route families

The semantic and endpoint classification of an inherited Figure 9 incidence
provides all indices needed to reuse its source route.  This file packages
that information in a proof-backed total selector and instantiates the
inherited-suffix interface consumed by the existing local-route splice.

The selector is noncomputable because route geometry is proof data rather
than part of the reduction algorithm.  Every genuine inherited incidence is
proved to select valid data; invalid presentation indices receive an empty
route.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- Source and generated incidence data needed to build one inherited Figure
9 suffix. -/
structure InheritedIncidenceData
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) where
  generatedClause :
    PositionedPeriodicClause (OneInThreeVariable Variable)
  generatedLiteral :
    PeriodicLiteral (OneInThreeVariable Variable)
  sourceClause : PositionedPeriodicClause Variable
  sourceClauseIndex : Nat
  sourceLiteral : PeriodicLiteral Variable
  sourceLiteralIndex : Nat
  metadata : ClauseMetadata Variable
  metadataLookup :
    (formulaClauseMetadata source)[clauseIndex]? = some metadata
  metadataGeneratedClause : metadata.clause = generatedClause
  metadataSourceClause : metadata.sourceClause = sourceClause
  generatedClauseMember :
    (generatedClause, clauseIndex) ∈ (formula source).clauses.zipIdx
  generatedLiteralMember :
    (generatedLiteral, literalIndex) ∈ generatedClause.literals.zipIdx
  sourceClauseMember :
    (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx
  sourceLiteralMember :
    (sourceLiteral, sourceLiteralIndex) ∈ sourceClause.literals.zipIdx
  literalAtom : generatedLiteral.atom = .inl sourceLiteral.atom
  literalOffset : generatedLiteral.offset = sourceLiteral.offset
  localEndpoint :
    normalizedLocalEndpoint source sourcePlacement
        clauseIndex literalIndex =
      normalizedSourcePort
        (placement source sourcePlacement)
        sourceClause generatedClause sourceLiteralIndex
  originalOccurrencePair :
    ((generatedLiteral, clauseIndex, literalIndex),
      (sourceLiteral, sourceClauseIndex, sourceLiteralIndex)) ∈
        PeriodicOneInThree.formulaOriginalOccurrencePairs
          source.erase sourceLiteral.atom

/-- Select inherited-incidence data whenever such data exists. -/
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

/-- Every genuine inherited Figure 9 incidence makes the total data selector
succeed. -/
theorem inheritedIncidenceData?_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    ∃ data,
      inheritedIncidenceData?
        source sourcePlacement clauseIndex literalIndex =
          some data := by
  rcases normalizedLocalEndpoint_inherited
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨metadata, sourceLiteral, sourceLiteralIndex,
      metadataLookup, metadataClause, sourceClauseMember,
      sourceLiteralMember, sourceLiteralAtom,
      literalOffset, localEndpoint⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [metadataClause] using literalMember
  have literalAtom :
      literal.atom = .inl sourceLiteral.atom := by
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
      metadata := metadata
      metadataLookup := metadataLookup
      metadataGeneratedClause := metadataClause
      metadataSourceClause := rfl
      generatedClauseMember := clauseMember
      generatedLiteralMember := literalMember
      sourceClauseMember := sourceClauseMember
      sourceLiteralMember := sourceLiteralMember
      literalAtom := literalAtom
      literalOffset := literalOffset
      localEndpoint := by
        simpa [metadataClause] using localEndpoint
      originalOccurrencePair :=
        originalOccurrencePair_of_formulaMetadataLookup
          source sourceWidth sourceDistinct sourceLiteral.atom
          metadataLookup metadataLiteralMember
          sourceLiteralMember literalAtom rfl }
  have existsData :
      Nonempty
        (InheritedIncidenceData
          source sourcePlacement clauseIndex literalIndex) :=
    ⟨witness⟩
  rw [inheritedIncidenceData?, dif_pos existsData]
  exact ⟨Classical.choice existsData, rfl⟩

/-- Total suffix lookup obtained by selecting source incidence metadata and
applying the per-incidence inherited-route splice. -/
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
          (placement source sourcePlacement)
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

/-- Distinct generated Figure 9 incidences select distinct source incidence
coordinates.  The ordered occurrence pairing is injective in its source
projection because tagged source occurrences are pairwise distinct. -/
theorem InheritedIncidenceData.sourceCoordinatesDistinct_of_generatedDistinct
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      InheritedIncidenceData source sourcePlacement
        firstClauseIndex firstLiteralIndex)
    (second :
      InheritedIncidenceData source sourcePlacement
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
  let pairs :=
    PeriodicOneInThree.formulaOriginalOccurrencePairs
      source.erase first.sourceLiteral.atom
  have firstPairMember :
      ((first.generatedLiteral, firstClauseIndex, firstLiteralIndex),
        (first.sourceLiteral, first.sourceClauseIndex,
          first.sourceLiteralIndex)) ∈ pairs := by
    simpa [pairs] using first.originalOccurrencePair
  have secondPairMember :
      ((second.generatedLiteral, secondClauseIndex, secondLiteralIndex),
        (second.sourceLiteral, second.sourceClauseIndex,
          second.sourceLiteralIndex)) ∈ pairs := by
    simpa [pairs, sourceLiteralEqual] using second.originalOccurrencePair
  have pairsSndNodup : (pairs.map Prod.snd).Nodup := by
    rw [show
      pairs.map Prod.snd =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          source.erase first.sourceLiteral.atom by
      simpa [pairs] using
        PeriodicOneInThree.formulaOriginalOccurrencePairs_snd
          source.erase sourceWidth first.sourceLiteral.atom]
    exact PeriodicOneInThreeToThreeDM.occurrencesOf_nodup _ _
  have pairsNodup : pairs.Nodup :=
    pairsSndNodup.of_map Prod.snd
  have sourceOccurrencesEqual :
      (first.sourceLiteral, first.sourceClauseIndex,
          first.sourceLiteralIndex) =
        (second.sourceLiteral, second.sourceClauseIndex,
          second.sourceLiteralIndex) := by
    simp [sourceLiteralEqual, sourceNotDistinct.1,
      sourceNotDistinct.2]
  have pairEqual :=
    ((List.nodup_map_iff_inj_on pairsNodup).mp pairsSndNodup)
      _ firstPairMember _ secondPairMember sourceOccurrencesEqual
  have generatedCoordinatesEqual :
      (firstClauseIndex, firstLiteralIndex) =
        (secondClauseIndex, secondLiteralIndex) := by
    exact congrArg
      (fun pair => (pair.1.2.1, pair.1.2.2)) pairEqual
  exact generatedDistinct.elim
    (fun clauseNe => clauseNe (congrArg Prod.fst generatedCoordinatesEqual))
    (fun literalNe => literalNe (congrArg Prod.snd generatedCoordinatesEqual))

/-- Pointwise source endpoint and orthogonality certificates lift to the
total inherited Figure 9 suffix lookup. -/
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
    {clause :
      PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
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
            (placement source sourcePlacement) clause literal) ∧
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
      data.literalAtom data.literalOffset
  simpa [inheritedRouteSuffixesRoutes, dataLookup,
    data.localEndpoint] using valid

/-- Any canonical orthogonal route family for the source formula induces
all inherited Figure 9 suffixes required by the local gadget splice. -/
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
            (sourceRoutes sourceClauseIndex sourceLiteralIndex)) :
    PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
      (formula source)
      (placement source sourcePlacement)
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
        sourceRoutes sourceEndpoints sourceOrthogonal
        clauseMember literalMember sourceAtom literalSource
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
      sourceAtom literalSource
    exact
      (inheritedRouteSuffixesRoutes_valid
        source sourcePlacement sourceWidth sourceDistinct
        sourceRoutes sourceEndpoints sourceOrthogonal
        clauseMember literalMember sourceAtom literalSource).2.2

end PeriodicOneInThreePositioned
end LeanTrominoes
