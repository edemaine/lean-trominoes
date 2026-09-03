/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineClauseRouteOrder

/-! # Binary-clause route order for the composed Figure 9 drawing -/

namespace LeanTrominoes

namespace AxisDirection

/-- The two finite Figure 9 exits of a generated binary clause. -/
def binaryUnitEliminationClauseExitDirection (literalIndex : Nat) :
    AxisDirection :=
  if literalIndex = 0 then .west else .east

@[simp] theorem binaryUnitEliminationClauseExitDirection_zero :
    binaryUnitEliminationClauseExitDirection 0 = .west := by
  rfl

@[simp] theorem binaryUnitEliminationClauseExitDirection_one :
    binaryUnitEliminationClauseExitDirection 1 = .east := by
  rfl

theorem binaryUnitEliminationClauseExitDirection_isGenuine
    (literalIndex : Nat) :
    (binaryUnitEliminationClauseExitDirection literalIndex).IsGenuine := by
  unfold binaryUnitEliminationClauseExitDirection
  split <;> simp [IsGenuine]

end AxisDirection

namespace PlanarThreeSAT

/-- Every binary incidence in a finite embedded drawing initially leaves its
clause west at index zero and east at index one. -/
def EmbeddedCNFIncidenceDrawing.BinaryRoutesInUnitEliminationOrder
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ index : Fin drawing.incidences.length,
    (drawing.incidenceAt index).clause.literals.length = 2 →
      AxisDirection.polylineFirstDirection
          (drawing.routeAt (drawing.incidenceAt index)) =
        AxisDirection.binaryUnitEliminationClauseExitDirection
          (drawing.incidenceAt index).literalIndex

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.BinaryRoutesInUnitEliminationOrder := by
  unfold EmbeddedCNFIncidenceDrawing.BinaryRoutesInUnitEliminationOrder
  infer_instance

namespace EmbeddedCNFIncidenceDrawing

theorem BinaryRoutesInUnitEliminationOrder.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (ordered : drawing.BinaryRoutesInUnitEliminationOrder)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename variableMap targetPosition)
      |>.BinaryRoutesInUnitEliminationOrder := by
  intro renamedIndex arity
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename drawing variableMap targetPosition renamedIndex
  have originalArity :
      (drawing.incidenceAt originalIndex).clause.literals.length = 2 := by
    simpa [incidenceEqual, EmbeddedCNFIncidence.rename,
      EmbeddedClause.rename, EmbeddedClause.map] using arity
  have base := ordered originalIndex originalArity
  rw [incidenceEqual, routeAt_rename_incidence]
  simpa [EmbeddedCNFIncidence.rename] using base

theorem BinaryRoutesInUnitEliminationOrder.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (ordered : drawing.BinaryRoutesInUnitEliminationOrder)
    (offset : Cell) :
    (drawing.translate offset).BinaryRoutesInUnitEliminationOrder := by
  intro translatedIndex arity
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  have originalArity :
      (drawing.incidenceAt originalIndex).clause.literals.length = 2 := by
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

theorem fullDrawingFor_binaryRoutesInUnitEliminationOrder
    (first second third : Bool) :
    (fullDrawingFor first second third)
      |>.BinaryRoutesInUnitEliminationOrder := by
  cases first <;> cases second <;> cases third <;> native_decide

theorem twoDrawingFor_binaryRoutesInUnitEliminationOrder
    (first second : Bool) :
    (twoDrawingFor first second)
      |>.BinaryRoutesInUnitEliminationOrder := by
  cases first <;> cases second <;> native_decide

theorem oneDrawingFor_binaryRoutesInUnitEliminationOrder
    (first : Bool) :
    (oneDrawingFor first).BinaryRoutesInUnitEliminationOrder := by
  cases first <;> native_decide

theorem zeroDrawing_binaryRoutesInUnitEliminationOrder :
    zeroDrawing.BinaryRoutesInUnitEliminationOrder := by
  native_decide

/-- Every arity-selected finite template has the west/east binary exit
order. -/
theorem templateDrawing_binaryRoutesInUnitEliminationOrder
    {Variable : Type*}
    (source : PositionedPeriodicClause Variable) :
    (templateDrawing source).BinaryRoutesInUnitEliminationOrder := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact zeroDrawing_binaryRoutesInUnitEliminationOrder
  · rcases rest with _ | ⟨second, rest⟩
    · exact oneDrawingFor_binaryRoutesInUnitEliminationOrder first.value
    · rcases rest with _ | ⟨third, tail⟩
      · exact twoDrawingFor_binaryRoutesInUnitEliminationOrder
          first.value second.value
      · exact fullDrawingFor_binaryRoutesInUnitEliminationOrder
          first.value second.value third.value

/-- Renaming and translating a selected template preserve its binary exit
order. -/
theorem instantiatedDrawing_binaryRoutesInUnitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source)
        |>.BinaryRoutesInUnitEliminationOrder := by
  rw [instantiatedDrawing_eq]
  apply
    EmbeddedCNFIncidenceDrawing.BinaryRoutesInUnitEliminationOrder.translate
  unfold EmbeddedCNFIncidenceDrawing.renameToImage
  apply
    EmbeddedCNFIncidenceDrawing.BinaryRoutesInUnitEliminationOrder.rename
  exact templateDrawing_binaryRoutesInUnitEliminationOrder source

/-- Metadata selection preserves the finite west/east direction at every
binary composed local route. -/
theorem localRoutes_firstDirection_of_binary
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
    (arity : clause.literals.length = 2)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (localRoutes source clauseIndex literalIndex) =
      AxisDirection.binaryUnitEliminationClauseExitDirection
        literalIndex := by
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
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
        have sourceMember : metadata.sourceClause ∈ source.clauses :=
          List.fst_mem_of_mem_zipIdx sourceClauseMember
        apply sourceWidth metadata.sourceClause.literals
        exact List.mem_map.mpr
          ⟨metadata.sourceClause, sourceMember, rfl⟩)
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
  have embeddedArity : incidence.clause.literals.length = 2 := by
    simpa [incidence, PlanarOneInThreeNoUnits.embedPositionedClause,
      clauseEqual] using arity
  have ordered :=
    instantiatedDrawing_binaryRoutesInUnitEliminationOrder
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

/-- Anchor normalization changes no binary local first direction. -/
theorem normalizedLocalRoutes_firstDirection_of_binary
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
    (arity : clause.literals.length = 2)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex) =
      AxisDirection.binaryUnitEliminationClauseExitDirection
        literalIndex := by
  rcases formulaClauseMetadata_lookup source clauseMember with
    ⟨metadata, metadataLookup, _clauseEqual⟩
  have direction := localRoutes_firstDirection_of_binary
    source sourceWidth clauseMember arity literalMember
  simp only [normalizedLocalRoutes, metadataLookup,
    PositionedPeriodicCNF.normalizeIncidenceRoute]
  rw [AxisDirection.polylineFirstDirection_map_sub]
  exact direction

/-- Splicing any inherited suffix preserves the genuine binary local first
direction. -/
theorem splicedRoutes_firstDirection_of_binary
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
    (arity : clause.literals.length = 2)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineFirstDirection
        (splicedRoutes source sourcePlacement sourceWidth sourceDistinct
          original clauseIndex literalIndex) =
      AxisDirection.binaryUnitEliminationClauseExitDirection
        literalIndex := by
  have localDirection :=
    normalizedLocalRoutes_firstDirection_of_binary
      source sourcePlacement sourceWidth clauseMember arity literalMember
  have genuine :
      (AxisDirection.polylineFirstDirection
        (normalizedLocalRoutes source sourcePlacement
          clauseIndex literalIndex)).IsGenuine := by
    rw [localDirection]
    exact
      AxisDirection.binaryUnitEliminationClauseExitDirection_isGenuine
        literalIndex
  unfold splicedRoutes PositionedPeriodicCNF.spliceLocalIncidenceRoutes
  rw [AxisDirection.polylineFirstDirection_joinAtEndpoint_of_genuine
    genuine]
  exact localDirection

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
