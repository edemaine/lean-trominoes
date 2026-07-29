import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedAuxiliaryEndpoints
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-!
# Clause rotation order of unit-elimination routes

Every ternary clause emitted by exact-one unit elimination uses the same
local rotation order.  Its literal-index `0`, `1`, and `2` routes initially
leave the clause toward the south, west, and east, respectively.  Thus the
opposite incoming directions are north, east, and west in clockwise order.

This file proves that invariant first for the four finite local templates,
then transports it through anchor normalization and arbitrary inherited
route splicing.  Consequently the invariant applies without inspecting the
long source-route suffix used by the hardness pipeline.
-/

namespace LeanTrominoes

namespace AxisDirection

/-- Canonical outgoing route direction at a ternary unit-elimination clause,
indexed by its literal position. -/
def unitEliminationClauseExitDirection : Nat → AxisDirection
  | 0 => .south
  | 1 => .west
  | _ => .east

theorem unitEliminationClauseExitDirection_isGenuine
    (literalIndex : Nat) :
    (unitEliminationClauseExitDirection literalIndex).IsGenuine := by
  cases literalIndex with
  | zero => simp [unitEliminationClauseExitDirection, IsGenuine]
  | succ literalIndex =>
      cases literalIndex with
      | zero => simp [unitEliminationClauseExitDirection, IsGenuine]
      | succ literalIndex =>
          simp [unitEliminationClauseExitDirection, IsGenuine]

/-- Subtracting one common offset from every point preserves the first
directed axis. -/
@[simp]
theorem polylineFirstDirection_map_sub
    (offset : Cell) (points : List Cell) :
    polylineFirstDirection
        (points.map fun point => Cell.sub point offset) =
      polylineFirstDirection points := by
  cases points with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          rcases offset with ⟨offsetX, offsetY⟩
          rcases first with ⟨firstX, firstY⟩
          rcases second with ⟨secondX, secondY⟩
          simp [polylineFirstDirection, between, Cell.sub]

/-- Joining a suffix preserves a genuine first direction. -/
theorem polylineFirstDirection_joinAtEndpoint_of_genuine
    {first second : List Cell}
    (genuine : (polylineFirstDirection first).IsGenuine) :
    polylineFirstDirection (joinAtEndpoint first second) =
      polylineFirstDirection first := by
  cases first with
  | nil => simp [polylineFirstDirection, IsGenuine] at genuine
  | cons first rest =>
      cases rest with
      | nil => simp [polylineFirstDirection, IsGenuine] at genuine
      | cons second rest =>
          rfl

end AxisDirection

namespace PlanarOneInThreeNoUnits

open PlanarThreeSAT

/-- Every ternary clause in every instantiated unit-elimination template has
the canonical literal-index exit directions. -/
theorem instantiatedDrawing_firstDirection_of_ternary
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    {clause : EmbeddedClause (OneInThreeNoUnitVariable Variable)}
    {localClauseIndex : Nat}
    (clauseMember :
      (clause, localClauseIndex) ∈
        (instantiatedDrawing
          sourceClauseIndex source).formula.zipIdx)
    (arity : clause.literals.length = 3)
    {literal : OneInThreeNoUnitVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        ((instantiatedDrawing
          sourceClauseIndex source).routes
            localClauseIndex literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection literalIndex := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · simp [instantiatedDrawing, instantiatedEmptyDrawing,
      emptyDrawing, emptyFormula, PlanarOneInThreeNoUnits.clause,
      EmbeddedCNFIncidenceDrawing.rename,
      EmbeddedCNFIncidenceDrawing.translate] at clauseMember
    rcases clauseMember with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (
      change (2 : Nat) = 3 at arity
      omega)
  · rcases rest with _ | ⟨second, rest⟩
    · simp [instantiatedDrawing, instantiatedUnitDrawing,
        unitDrawingFor, unitFormulaFor,
        PlanarOneInThreeNoUnits.clause,
        EmbeddedCNFIncidenceDrawing.rename,
        EmbeddedCNFIncidenceDrawing.translate] at clauseMember
      rcases clauseMember with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have literalLt :=
          List.snd_lt_of_mem_zipIdx literalMember
        change literalIndex < 3 at literalLt
        have literalCases :
            literalIndex = 0 ∨ literalIndex = 1 ∨
              literalIndex = 2 := by
          omega
        rcases literalCases with rfl | rfl | rfl <;>
          simp [instantiatedDrawing, instantiatedUnitDrawing,
            unitDrawingFor, EmbeddedCNFIncidenceDrawing.rename,
            EmbeddedCNFIncidenceDrawing.translate,
            unitRoute,
            AxisDirection.polylineFirstDirection,
            AxisDirection.between,
            AxisDirection.unitEliminationClauseExitDirection,
            Cell.add]
      · change (2 : Nat) = 3 at arity
        omega
    · rcases rest with _ | ⟨third, tail⟩
      · simp [instantiatedDrawing, instantiatedTwoDrawing,
          twoDrawingFor, twoFormulaFor,
          PlanarOneInThreeNoUnits.clause,
          EmbeddedCNFIncidenceDrawing.rename,
          EmbeddedCNFIncidenceDrawing.translate] at clauseMember
        rcases clauseMember with ⟨rfl, rfl⟩
        change (2 : Nat) = 3 at arity
        omega
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        simp [instantiatedDrawing, instantiatedThreeDrawing,
          threeDrawingFor, threeFormulaFor,
          PlanarOneInThreeNoUnits.clause,
          EmbeddedCNFIncidenceDrawing.rename,
          EmbeddedCNFIncidenceDrawing.translate] at clauseMember
        rcases clauseMember with ⟨rfl, rfl⟩
        have literalLt :=
          List.snd_lt_of_mem_zipIdx literalMember
        change literalIndex < 3 at literalLt
        have literalCases :
            literalIndex = 0 ∨ literalIndex = 1 ∨
              literalIndex = 2 := by
          omega
        rcases literalCases with rfl | rfl | rfl <;>
          simp [instantiatedDrawing, instantiatedThreeDrawing,
            threeDrawingFor, EmbeddedCNFIncidenceDrawing.rename,
            EmbeddedCNFIncidenceDrawing.translate,
            threeRoute,
            AxisDirection.polylineFirstDirection,
            AxisDirection.between,
            AxisDirection.unitEliminationClauseExitDirection,
            Cell.add]

end PlanarOneInThreeNoUnits

namespace PeriodicOneInThreeNoUnitsPositioned

open PlanarThreeSAT

/-- Metadata selection preserves the canonical direction of every ternary
local route. -/
theorem localRoutes_firstDirection_of_ternary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    (arity : clause.literals.length = 3)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (localRoutes source clauseIndex literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection literalIndex := by
  rcases formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have sourceClauseMember' :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, sourceClauseMember', rfl⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  let drawing :=
    PlanarOneInThreeNoUnits.instantiatedDrawing
      metadata.sourceClauseIndex metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        (clauseGadget metadata.sourceClauseIndex
          metadata.sourceClause).map
            PlanarOneInThreeNoUnits.embedPositionedClause :=
    PlanarOneInThreeNoUnits.instantiatedDrawing_formula
      metadata.sourceClauseIndex metadata.sourceClause metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
          metadata.localClauseIndex) ∈ drawing.formula.zipIdx := by
    rw [drawingFormula, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(metadata.clause, metadata.localClauseIndex),
        localClauseMember, rfl⟩
  have embeddedArity :
      (PlanarOneInThreeNoUnits.embedPositionedClause
        metadata.clause).literals.length = 3 := by
    simpa [PlanarOneInThreeNoUnits.embedPositionedClause,
      clauseEqual] using arity
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex), metadataLiteralMember, rfl⟩
  have direction :=
    PlanarOneInThreeNoUnits.instantiatedDrawing_firstDirection_of_ternary
        metadata.sourceClauseIndex metadata.sourceClause metadataWidth
        embeddedClauseMember embeddedArity embeddedLiteralMember
  simpa [localRoutes, metadataLookup, drawing] using direction

/-- Anchor normalization preserves the canonical direction of every
ternary local route. -/
theorem normalizedLocalRoutes_firstDirection_of_ternary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    (arity : clause.literals.length = 3)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection literalIndex := by
  rcases formulaClauseMetadata_lookup source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have direction :=
    localRoutes_firstDirection_of_ternary
      source sourceWidth clauseMember arity literalMember
  simp only [normalizedLocalRoutes, metadataLookup,
    PositionedPeriodicCNF.normalizeIncidenceRoute]
  rw [AxisDirection.polylineFirstDirection_map_sub]
  exact direction

/-- Splicing any inherited suffix preserves the canonical direction of every
ternary unit-elimination route. -/
theorem splicedRoutes_firstDirection_of_ternary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
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
    (arity : clause.literals.length = 3)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (splicedRoutes source sourcePlacement inherited
          clauseIndex literalIndex) =
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
      AxisDirection.unitEliminationClauseExitDirection_isGenuine literalIndex
  unfold splicedRoutes PositionedPeriodicCNF.spliceLocalIncidenceRoutes
  rw [AxisDirection.polylineFirstDirection_joinAtEndpoint_of_genuine
    genuine]
  exact localDirection

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
