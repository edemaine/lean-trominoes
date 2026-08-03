import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedRouteFamily
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteSplicing

/-!
# Ordered composed inherited suffix families

The two-stage incidence metadata recovers one original source-clause
occurrence from every twice-inherited final literal.  For a width-three
source, that occurrence index is a slot of the clause's certified ordered
exit fan.  This file uses that slot to build a total direct-suffix lookup and
packages the genuine entries behind the standard canonical suffix interface.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

namespace InheritedIncidenceData

/-- The recovered original occurrence index is within its source clause. -/
theorem sourceLiteralIndex_lt
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {clauseIndex literalIndex : Nat}
    (data :
      InheritedIncidenceData
        source sourcePlacement clauseIndex literalIndex) :
    data.sourceLiteralIndex < data.sourceClause.literals.length := by
  have lookup :=
    (List.mem_zipIdx_iff_getElem?).mp data.sourceLiteralMember
  exact (List.getElem?_eq_some_iff.mp lookup).1

/-- A global width-three bound applies to the recovered source clause. -/
theorem sourceClause_width
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {clauseIndex literalIndex : Nat}
    (sourceWidth : source.erase.WidthAtMost 3)
    (data :
      InheritedIncidenceData
        source sourcePlacement clauseIndex literalIndex) :
    data.sourceClause.literals.length ≤ 3 := by
  exact sourceWidth data.sourceClause.literals
    (List.mem_map.mpr
      ⟨data.sourceClause,
        List.fst_mem_of_mem_zipIdx data.sourceClauseMember, rfl⟩)

/-- The recovered occurrence index regarded as one of the three composed
source-port slots. -/
def sourceSlot
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {clauseIndex literalIndex : Nat}
    (sourceWidth : source.erase.WidthAtMost 3)
    (data :
      InheritedIncidenceData
        source sourcePlacement clauseIndex literalIndex) : Fin 3 :=
  ⟨data.sourceLiteralIndex, by
    have indexLt := data.sourceLiteralIndex_lt
    have width := data.sourceClause_width sourceWidth
    omega⟩

@[simp]
theorem sourceSlot_val
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {clauseIndex literalIndex : Nat}
    (sourceWidth : source.erase.WidthAtMost 3)
    (data :
      InheritedIncidenceData
        source sourcePlacement clauseIndex literalIndex) :
    (data.sourceSlot sourceWidth).val = data.sourceLiteralIndex :=
  rfl

end InheritedIncidenceData

/-- Total direct-suffix lookup using the ordered fan selected by each
recovered source clause. -/
noncomputable def orderedInheritedRouteSuffixesRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    match inheritedIncidenceData?
        source sourcePlacement clauseIndex literalIndex with
    | none => []
    | some data =>
        fanInheritedRouteSuffix
          (composedPlacement source sourcePlacement)
          sourcePlacement data.sourceClause data.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            data.sourceClause data.sourceClauseIndex sourceRoutes)
          (data.sourceSlot sourceWidth)
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

/-- Pointwise source certificates and valid ordered clause fans lift to the
total direct composed suffix lookup. -/
theorem orderedInheritedRouteSuffixesRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceFanValid :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        (PositionedPeriodicCNF.clauseExitFanData
          sourceClause sourceClauseIndex sourceRoutes).IsValid)
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
              sourceClauseIndex sourceLiteralIndex).tail.head? = some exit)
    (sourceUnitSteps :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).IsChain
            AxisDirection.IsUnitAxisStep)
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
    (orderedInheritedRouteSuffixesRoutes
        source sourcePlacement sourceWidth sourceRoutes
        clauseIndex literalIndex).head? =
        some
          (normalizedLocalEndpoint
            source sourcePlacement clauseIndex literalIndex) ∧
      (orderedInheritedRouteSuffixesRoutes
        source sourcePlacement sourceWidth sourceRoutes
        clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (composedPlacement source sourcePlacement) clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (orderedInheritedRouteSuffixesRoutes
          source sourcePlacement sourceWidth sourceRoutes
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
  let fanData :=
    PositionedPeriodicCNF.clauseExitFanData
      data.sourceClause data.sourceClauseIndex sourceRoutes
  let slot := data.sourceSlot sourceWidth
  have sourceIndexLt := data.sourceLiteralIndex_lt
  have sourceClauseWidth := data.sourceClause_width sourceWidth
  have sourceClausePositive : 0 < data.sourceClause.literals.length := by
    omega
  have fanCount : fanData.count = data.sourceClause.literals.length :=
    PositionedPeriodicCNF.clauseExitFanData_count_eq
      data.sourceClause data.sourceClauseIndex sourceRoutes
      sourceClausePositive sourceClauseWidth
  have slotActive : fanData.SlotActive slot := by
    unfold ComposedClauseExitFanData.SlotActive
    rw [fanCount]
    exact sourceIndexLt
  have directionEq :
      fanData.direction slot =
        AxisDirection.polylineFirstDirection
          (sourceRoutes
            data.sourceClauseIndex data.sourceLiteralIndex) := by
    rfl
  have endpoints :=
    sourceEndpoints
      data.sourceClause data.sourceClauseIndex data.sourceClauseMember
      data.sourceLiteral data.sourceLiteralIndex data.sourceLiteralMember
  have valid :=
    fanInheritedRouteSuffix_valid
      source sourcePlacement data.sourceClause data.generatedClause
      data.sourceLiteral data.generatedLiteral
      fanData slot
      (sourceRoutes
        data.sourceClauseIndex data.sourceLiteralIndex)
      (sourceFanValid
        data.sourceClause data.sourceClauseIndex data.sourceClauseMember)
      slotActive directionEq endpoints.1 endpoints.2
      (sourceOrthogonal
        data.sourceClause data.sourceClauseIndex data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex data.sourceLiteralMember)
      (sourceExits
        data.sourceClause data.sourceClauseIndex data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex data.sourceLiteralMember)
      (sourceUnitSteps
        data.sourceClause data.sourceClauseIndex data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex data.sourceLiteralMember)
      data.literalAtom data.literalOffset
  simpa [orderedInheritedRouteSuffixesRoutes, dataLookup,
    fanData, slot, data.localEndpoint] using valid

/-- Any canonical orthogonal unit-step source family with valid ordered
clause fans induces all direct suffixes inherited through both clause
transformations. -/
noncomputable def orderedInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceFanValid :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        (PositionedPeriodicCNF.clauseExitFanData
          sourceClause sourceClauseIndex sourceRoutes).IsValid)
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
              sourceClauseIndex sourceLiteralIndex).tail.head? = some exit)
    (sourceUnitSteps :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).IsChain
            AxisDirection.IsUnitAxisStep) :
    OriginalInheritedCanonicalIncidenceRouteSuffixes
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source))
      (composedPlacement source sourcePlacement)
      (normalizedLocalEndpoint source sourcePlacement) where
  routes :=
    orderedInheritedRouteSuffixesRoutes
      source sourcePlacement sourceWidth sourceRoutes
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember sourceAtom literalSource
    have valid :=
      orderedInheritedRouteSuffixesRoutes_valid
        source sourcePlacement sourceWidth sourceDistinct
        sourceRoutes sourceFanValid sourceEndpoints sourceOrthogonal
        sourceExits sourceUnitSteps
        clauseMember literalMember sourceAtom literalSource
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember sourceAtom literalSource
    exact
      (orderedInheritedRouteSuffixesRoutes_valid
        source sourcePlacement sourceWidth sourceDistinct
        sourceRoutes sourceFanValid sourceEndpoints sourceOrthogonal
        sourceExits sourceUnitSteps
        clauseMember literalMember sourceAtom literalSource).2.2

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
