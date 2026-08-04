import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineRouteFamily
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseRouteOrder

/-!
# Clause route order for the composed Figure 9 drawing

The coordinated Figure 9-plus-unit-elimination templates replace the first
few segments of the ordinary unit-elimination routes.  Nevertheless every
ternary output clause retains the canonical literal-index exit order:
literal `0` leaves south, literal `1` leaves west, and literal `2` leaves
east.

This file checks that finite fact on the four composed templates and then
transports it through logical renaming, geometric translation, anchor
normalization, and inherited-suffix splicing.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Every ternary incidence in a finite embedded drawing initially leaves
its clause in the canonical unit-elimination direction. -/
def EmbeddedCNFIncidenceDrawing.TernaryRoutesInUnitEliminationOrder
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ index : Fin drawing.incidences.length,
    (drawing.incidenceAt index).clause.literals.length = 3 →
      AxisDirection.polylineFirstDirection
          (drawing.routeAt (drawing.incidenceAt index)) =
        AxisDirection.unitEliminationClauseExitDirection
          (drawing.incidenceAt index).literalIndex

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.TernaryRoutesInUnitEliminationOrder := by
  unfold EmbeddedCNFIncidenceDrawing.TernaryRoutesInUnitEliminationOrder
  infer_instance

namespace EmbeddedCNFIncidenceDrawing

/-- Logical renaming preserves the ternary clause route order. -/
theorem TernaryRoutesInUnitEliminationOrder.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (ordered : drawing.TernaryRoutesInUnitEliminationOrder)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename variableMap targetPosition)
      |>.TernaryRoutesInUnitEliminationOrder := by
  intro renamedIndex arity
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  have originalArity :
      (drawing.incidenceAt originalIndex).clause.literals.length = 3 := by
    simpa [incidenceEqual, EmbeddedCNFIncidence.rename,
      EmbeddedClause.rename, EmbeddedClause.map] using arity
  have base := ordered originalIndex originalArity
  rw [incidenceEqual, routeAt_rename_incidence]
  simpa [EmbeddedCNFIncidence.rename] using base

/-- A common geometric translation preserves the ternary clause route
order. -/
theorem TernaryRoutesInUnitEliminationOrder.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (ordered : drawing.TernaryRoutesInUnitEliminationOrder)
    (offset : Cell) :
    (drawing.translate offset).TernaryRoutesInUnitEliminationOrder := by
  intro translatedIndex arity
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  have originalArity :
      (drawing.incidenceAt originalIndex).clause.literals.length = 3 := by
    simpa [incidenceEqual, EmbeddedCNFIncidence.translate,
      EmbeddedClause.translate] using arity
  have base := ordered originalIndex originalArity
  rw [incidenceEqual, routeAt_translate_incidence]
  change
    AxisDirection.polylineFirstDirection
        (PeriodicOrthocrossing.translatePolyline offset
          (drawing.routeAt (drawing.incidenceAt originalIndex))) = _
  rw [AxisDirection.polylineFirstDirection_translatePolyline]
  simpa [EmbeddedCNFIncidence.translate,
    PeriodicOrthocrossing.translatePolyline] using base

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT

namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- The full-width composed template has the canonical route order for all
eight source-polarity patterns. -/
theorem fullDrawingFor_ternaryRoutesInUnitEliminationOrder
    (first second third : Bool) :
    (fullDrawingFor first second third)
      |>.TernaryRoutesInUnitEliminationOrder := by
  cases first <;> cases second <;> cases third <;> native_decide

/-- The binary-source composed template has the canonical route order for
all four source-polarity patterns. -/
theorem twoDrawingFor_ternaryRoutesInUnitEliminationOrder
    (first second : Bool) :
    (twoDrawingFor first second)
      |>.TernaryRoutesInUnitEliminationOrder := by
  cases first <;> cases second <;> native_decide

/-- The unit-source composed template has the canonical route order for
both source polarities. -/
theorem oneDrawingFor_ternaryRoutesInUnitEliminationOrder
    (first : Bool) :
    (oneDrawingFor first).TernaryRoutesInUnitEliminationOrder := by
  cases first <;> native_decide

/-- The empty-source composed template has the canonical route order. -/
theorem zeroDrawing_ternaryRoutesInUnitEliminationOrder :
    zeroDrawing.TernaryRoutesInUnitEliminationOrder := by
  native_decide

/-- The arity-selected finite template always has the canonical ternary
route order. -/
theorem templateDrawing_ternaryRoutesInUnitEliminationOrder
    {Variable : Type*}
    (source : PositionedPeriodicClause Variable) :
    (templateDrawing source).TernaryRoutesInUnitEliminationOrder := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact zeroDrawing_ternaryRoutesInUnitEliminationOrder
  · rcases rest with _ | ⟨second, rest⟩
    · exact oneDrawingFor_ternaryRoutesInUnitEliminationOrder first.value
    · rcases rest with _ | ⟨third, tail⟩
      · exact twoDrawingFor_ternaryRoutesInUnitEliminationOrder
          first.value second.value
      · exact fullDrawingFor_ternaryRoutesInUnitEliminationOrder
          first.value second.value third.value

/-- Every instantiated, renamed, and translated composed drawing retains
the finite template's canonical ternary route order. -/
theorem instantiatedDrawing_ternaryRoutesInUnitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source)
        |>.TernaryRoutesInUnitEliminationOrder := by
  rw [instantiatedDrawing_eq]
  apply
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.TernaryRoutesInUnitEliminationOrder.translate
  unfold EmbeddedCNFIncidenceDrawing.renameToImage
  apply
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.TernaryRoutesInUnitEliminationOrder.rename
  exact templateDrawing_ternaryRoutesInUnitEliminationOrder source

/-- Metadata selection preserves the canonical direction of every ternary
composed local route. -/
theorem localRoutes_firstDirection_of_ternary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (arity : clause.literals.length = 3)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (localRoutes source clauseIndex literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection literalIndex := by
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      _sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  let drawing :=
    instantiatedDrawing
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        composedClauseGadget
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause := by
    exact instantiatedDrawing_formula
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause
      (by
        have sourceClauseMember :
            metadata.sourceClause ∈ source.clauses :=
          List.fst_mem_of_mem_zipIdx _sourceClauseMember
        apply sourceWidth metadata.sourceClause.literals
        exact List.mem_map.mpr
          ⟨metadata.sourceClause, sourceClauseMember, rfl⟩)
  let incidence :
      EmbeddedCNFIncidence
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)) :=
    ⟨PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
      metadata.localClauseIndex,
      (literal.atom, literal.value), literalIndex⟩
  have incidenceMember : incidence ∈ drawing.incidences := by
    apply (mem_embeddedCNFIncidences_iff drawing.formula incidence).mpr
    constructor
    · rw [drawingFormula]
      exact localClauseMember
    · unfold incidence PlanarOneInThreeNoUnits.embedPositionedClause
      rw [List.zipIdx_map]
      exact List.mem_map.mpr
        ⟨(literal, literalIndex), metadataLiteralMember, rfl⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  change drawing.incidenceAt incidenceIndex = incidence at incidenceEqual
  have embeddedArity : incidence.clause.literals.length = 3 := by
    simpa [incidence, PlanarOneInThreeNoUnits.embedPositionedClause,
      clauseEqual] using arity
  have ordered :=
    instantiatedDrawing_ternaryRoutesInUnitEliminationOrder
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause
  have direction := ordered incidenceIndex (by
    rw [incidenceEqual]
    exact embeddedArity)
  rw [incidenceEqual] at direction
  simpa [drawing, incidence,
    EmbeddedCNFIncidenceDrawing.routeAt, localRoutes,
    metadataLookup] using direction

/-- Anchor normalization preserves the canonical direction of every
ternary composed local route. -/
theorem normalizedLocalRoutes_firstDirection_of_ternary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (arity : clause.literals.length = 3)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection literalIndex := by
  rcases formulaClauseMetadata_lookup source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have direction := localRoutes_firstDirection_of_ternary
    source sourceWidth clauseMember arity literalMember
  simp only [normalizedLocalRoutes, metadataLookup,
    PositionedPeriodicCNF.normalizeIncidenceRoute]
  rw [AxisDirection.polylineFirstDirection_map_sub]
  exact direction

/-- Splicing any inherited suffix preserves the canonical direction of
every ternary composed route. -/
theorem splicedRoutes_firstDirection_of_ternary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (arity : clause.literals.length = 3)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (splicedRoutes source sourcePlacement sourceWidth sourceDistinct
          original clauseIndex literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection literalIndex := by
  have localDirection :=
    normalizedLocalRoutes_firstDirection_of_ternary
      source sourcePlacement sourceWidth clauseMember arity literalMember
  have genuine :
      (AxisDirection.polylineFirstDirection
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex)).IsGenuine := by
    rw [localDirection]
    exact
      AxisDirection.unitEliminationClauseExitDirection_isGenuine
        literalIndex
  unfold splicedRoutes PositionedPeriodicCNF.spliceLocalIncidenceRoutes
  rw [AxisDirection.polylineFirstDirection_joinAtEndpoint_of_genuine
    genuine]
  exact localDirection

/-- Every fully spliced composed route family has the canonical ternary
clause order expected by the 3DM ribbon source. -/
theorem splicedRoutes_ternaryClauseRoutesInUnitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement)) :
    PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source))
      (splicedRoutes source sourcePlacement sourceWidth sourceDistinct
        original) := by
  intro indexed indexedMember arity
  have incidenceMember :
      indexed.1 ∈
        PeriodicCNF.incidencesWithMetadata
          (PeriodicOneInThreeNoUnitsPositioned.formula
            (PeriodicOneInThreePositioned.formula source)).erase :=
    List.fst_mem_of_mem_zipIdx indexedMember
  rcases
      (PeriodicCNF.mem_incidencesWithMetadata_iff
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).erase
        indexed.1).mp incidenceMember with
    ⟨clauseMember, indexedLiteralMember⟩
  change
    (indexed.1.clause, indexed.1.clauseIndex) ∈
      ((PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source)).clauses.map
          PositionedPeriodicClause.literals).zipIdx
    at clauseMember
  rw [List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, clauseEq⟩
  have indexEq : taggedClause.2 = indexed.1.clauseIndex :=
    congrArg Prod.snd clauseEq
  have literalsEq : taggedClause.1.literals = indexed.1.clause :=
    congrArg Prod.fst clauseEq
  have literalMember :
      (indexed.1.literal, indexed.1.literalIndex) ∈
        taggedClause.1.literals.zipIdx := by
    simpa [literalsEq] using indexedLiteralMember
  have result := splicedRoutes_firstDirection_of_ternary
    source sourcePlacement sourceWidth sourceDistinct original
    taggedClauseMember
    (by simpa [literalsEq] using arity)
    literalMember
  simpa [indexEq] using result

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
