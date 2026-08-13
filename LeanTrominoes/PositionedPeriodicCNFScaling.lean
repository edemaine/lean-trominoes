/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalRoutes

/-!
# Positive integral scaling of positioned periodic CNF drawings

Local incidence substitutions need room around clause and variable vertices.
This file lifts the generic `PeriodicGridDrawing.scale` operation to the
positioned-CNF data from which an incidence drawing is assembled.

Scaling changes only physical coordinates and the physical period.  Logical
literals, their semantic lattice offsets, and the incidence graph are
unchanged.  The main theorem identifies assembly after scaling with scaling
the already assembled drawing exactly.
-/

namespace LeanTrominoes

namespace PositionedPeriodicClause

/-- Scale the displayed clause vertex without changing its logical clause. -/
def scale {Variable : Type*}
    (factor : Nat) (clause : PositionedPeriodicClause Variable) :
    PositionedPeriodicClause Variable where
  position := Cell.scale factor clause.position
  literals := clause.literals

@[simp]
theorem scale_position {Variable : Type*}
    (factor : Nat) (clause : PositionedPeriodicClause Variable) :
    (clause.scale factor).position =
      Cell.scale factor clause.position :=
  rfl

@[simp]
theorem scale_literals {Variable : Type*}
    (factor : Nat) (clause : PositionedPeriodicClause Variable) :
    (clause.scale factor).literals = clause.literals :=
  rfl

end PositionedPeriodicClause

namespace PositionedPeriodicCNF

/-- Scale every displayed clause vertex in a positioned formula. -/
def scale {Variable : Type*}
    (factor : Nat) (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicCNF Variable :=
  ⟨source.clauses.map (PositionedPeriodicClause.scale factor)⟩

@[simp]
theorem scale_clauses {Variable : Type*}
    (factor : Nat) (source : PositionedPeriodicCNF Variable) :
    (source.scale factor).clauses =
      source.clauses.map (PositionedPeriodicClause.scale factor) :=
  rfl

/-- Coordinate scaling leaves the underlying periodic CNF unchanged. -/
@[simp]
theorem erase_scale {Variable : Type*}
    (factor : Nat) (source : PositionedPeriodicCNF Variable) :
    (source.scale factor).erase = source.erase := by
  simp [scale, erase, List.map_map, Function.comp_def]

end PositionedPeriodicCNF

namespace PeriodicVariablePlacement

/-- Scale a physical variable placement and its period uniformly. -/
def scale {Variable : Type*}
    (factor : Nat) (placement : PeriodicVariablePlacement Variable) :
    PeriodicVariablePlacement Variable where
  period := factor * placement.period
  position := fun atom => Cell.scale factor (placement.position atom)

@[simp]
theorem scale_period {Variable : Type*}
    (factor : Nat) (placement : PeriodicVariablePlacement Variable) :
    (placement.scale factor).period = factor * placement.period :=
  rfl

@[simp]
theorem scale_position {Variable : Type*}
    (factor : Nat) (placement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (placement.scale factor).position atom =
      Cell.scale factor (placement.position atom) :=
  rfl

/-- Physical translation of a semantic lattice offset scales uniformly. -/
@[simp]
theorem translation_scale {Variable : Type*}
    (factor : Nat) (placement : PeriodicVariablePlacement Variable)
    (offset : Cell) :
    (placement.scale factor).translation offset =
      Cell.scale factor (placement.translation offset) := by
  unfold scale translation
  rw [Nat.cast_mul]
  exact
    (Cell.scale_scale
      (factor : Int) (placement.period : Int) offset).symm

/-- Physical literal endpoints scale uniformly. -/
@[simp]
theorem literalPosition_scale {Variable : Type*}
    (factor : Nat) (placement : PeriodicVariablePlacement Variable)
    (literal : PeriodicLiteral Variable) :
    (placement.scale factor).literalPosition literal =
      Cell.scale factor (placement.literalPosition literal) := by
  simp [literalPosition, Cell.scale_add]

end PeriodicVariablePlacement

namespace PositionedPeriodicCNF

/-- Scale every point of every incidence route. -/
def scaleIncidenceRoutes
    (factor : Nat) (routes : IncidenceRoutes) :
    IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    scalePolyline factor (routes clauseIndex literalIndex)

@[simp]
theorem scaleIncidenceRoutes_apply
    (factor : Nat) (routes : IncidenceRoutes)
    (clauseIndex literalIndex : Nat) :
    scaleIncidenceRoutes factor routes clauseIndex literalIndex =
      scalePolyline factor (routes clauseIndex literalIndex) :=
  rfl

/-- Canonical clause prototype positions scale uniformly. -/
@[simp]
theorem canonicalClausePosition_scale
    {Variable : Type*}
    (factor : Nat)
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable) :
    canonicalClausePosition
        (placement.scale factor) (clause.scale factor) =
      Cell.scale factor
        (canonicalClausePosition placement clause) := by
  rcases clause.position with ⟨clauseX, clauseY⟩
  rcases
      placement.translation
        (PeriodicCNF.clauseAnchor clause.literals) with
    ⟨translationX, translationY⟩
  simp only [canonicalClausePosition,
    PositionedPeriodicClause.scale_position,
    PositionedPeriodicClause.scale_literals,
    PeriodicVariablePlacement.translation_scale]
  simp [Cell.scale, Cell.sub]
  constructor <;> ring

/-- The complete variable-then-clause vertex list scales pointwise. -/
@[simp]
theorem incidenceVertexPositions_scale
    {Variable : Type*} [DecidableEq Variable]
    (factor : Nat)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable) :
    incidenceVertexPositions
        (source.scale factor) (placement.scale factor) =
      (incidenceVertexPositions source placement).map
        (Cell.scale factor) := by
  unfold incidenceVertexPositions
  rw [erase_scale, List.map_append, scale_clauses]
  apply congrArg₂ (· ++ ·)
  · rw [List.map_map]
    apply List.map_congr_left
    intro vertex _vertexMember
    cases vertex <;> simp [Cell.scale]
  · simp only [List.map_map]
    apply List.map_congr_left
    intro clause clauseMember
    exact canonicalClausePosition_scale factor placement clause

/-- Scaling clause positions alone does not change the flat logical
incidence-route enumeration. -/
@[simp]
theorem incidenceEdgeRoutes_source_scale
    {Variable : Type*}
    (factor : Nat)
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) :
    incidenceEdgeRoutes (source.scale factor) routes =
      incidenceEdgeRoutes source routes := by
  unfold incidenceEdgeRoutes
  rw [scale_clauses, List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  simp

/-- The complete clause-major route list scales pointwise. -/
@[simp]
theorem incidenceEdgeRoutes_scale
    {Variable : Type*}
    (factor : Nat)
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) :
    incidenceEdgeRoutes
        (source.scale factor)
        (scaleIncidenceRoutes factor routes) =
      (incidenceEdgeRoutes source routes).map
        (scalePolyline factor) := by
  rw [incidenceEdgeRoutes_source_scale]
  simp [incidenceEdgeRoutes, scaleIncidenceRoutes,
    List.map_flatMap, List.map_map, Function.comp_def]

/-- Assembling uniformly scaled positioned data is exactly the generic
whole-drawing scale operation. -/
theorem incidenceDrawing_scale
    {Variable : Type*} [DecidableEq Variable]
    (factor : Nat)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (periodPositive : 0 < placement.period) :
    incidenceDrawing
        (source.scale factor)
        (placement.scale factor)
        (scaleIncidenceRoutes factor routes) =
      (incidenceDrawing source placement routes).scale factor := by
  have oldGridSize :
      Nat.pred placement.period + 1 = placement.period := by
    exact Nat.succ_pred_eq_of_pos periodPositive
  apply PeriodicGridDrawing.equivData.injective
  simp only [PeriodicGridDrawing.equivData, incidenceDrawing,
    PeriodicVariablePlacement.scale_period,
    PeriodicGridDrawing.scale, incidenceVertexPositions_scale,
    incidenceEdgeRoutes_scale]
  change
    (Nat.pred (factor * placement.period),
      (incidenceVertexPositions source placement).map
        (Cell.scale factor),
      (incidenceEdgeRoutes source routes).map
        (scalePolyline factor)) =
    (factor * (Nat.pred placement.period + 1) - 1,
      (incidenceVertexPositions source placement).map
        (Cell.scale factor),
      (incidenceEdgeRoutes source routes).map
        (scalePolyline factor))
  rw [oldGridSize, Nat.pred_eq_sub_one]

namespace CanonicalOrthogonalIncidenceRoutes

/-- Positive uniform coordinate scaling preserves a canonical orthogonal
incidence-route family. -/
def scale
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {factor : Nat} (factorPositive : 0 < factor)
    (family :
      CanonicalOrthogonalIncidenceRoutes source placement) :
    CanonicalOrthogonalIncidenceRoutes
      (source.scale factor) (placement.scale factor) where
  routes := scaleIncidenceRoutes factor family.routes
  endpoints := by
    intro scaledClause clauseIndex scaledClauseMember
      literal literalIndex literalMember
    rw [scale_clauses, List.zipIdx_map] at scaledClauseMember
    rcases List.mem_map.mp scaledClauseMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
    have clauseIndexEqual : taggedClause.2 = clauseIndex :=
      congrArg Prod.snd taggedClauseEqual
    have scaledClauseEqual :
        taggedClause.1.scale factor = scaledClause :=
      congrArg Prod.fst taggedClauseEqual
    subst clauseIndex
    subst scaledClause
    have sourceLiteralMember :
        (literal, literalIndex) ∈
          taggedClause.1.literals.zipIdx := by
      simpa using literalMember
    have sourceEndpoints :=
      family.endpoints
        taggedClause.1 taggedClause.2 taggedClauseMember
        literal literalIndex sourceLiteralMember
    constructor
    · simpa [scaleIncidenceRoutes, scalePolyline,
        sourceEndpoints.1]
    · simpa [scaleIncidenceRoutes, scalePolyline,
        sourceEndpoints.2, canonicalLiteralPosition,
        Cell.scale_add]
  orthogonal := by
    intro scaledClause clauseIndex scaledClauseMember
      literal literalIndex literalMember
    rw [scale_clauses, List.zipIdx_map] at scaledClauseMember
    rcases List.mem_map.mp scaledClauseMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
    have clauseIndexEqual : taggedClause.2 = clauseIndex :=
      congrArg Prod.snd taggedClauseEqual
    have scaledClauseEqual :
        taggedClause.1.scale factor = scaledClause :=
      congrArg Prod.fst taggedClauseEqual
    subst clauseIndex
    subst scaledClause
    have sourceLiteralMember :
        (literal, literalIndex) ∈
          taggedClause.1.literals.zipIdx := by
      simpa using literalMember
    exact
      (family.orthogonal
        taggedClause.1 taggedClause.2 taggedClauseMember
        literal literalIndex sourceLiteralMember).scalePolyline
          (by exact_mod_cast factorPositive)

end CanonicalOrthogonalIncidenceRoutes

/-- Positive scaling transports a continuously planar positioned incidence
presentation to the uniformly refined coordinates. -/
def ContinuousPlanarIncidencePresentation.scale
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {factor : Nat} (factorPositive : 0 < factor)
    (presentation :
      ContinuousPlanarIncidencePresentation source placement) :
    ContinuousPlanarIncidencePresentation
      (source.scale factor) (placement.scale factor) where
  routes := scaleIncidenceRoutes factor presentation.routes
  periodPositive :=
    Nat.mul_pos factorPositive presentation.periodPositive
  compatible := by
    rw [incidenceDrawing_scale factor source placement
      presentation.routes presentation.periodPositive]
    simpa using
      PeriodicGridDrawing.isCompatible_scale
        factorPositive source.erase.incidenceGraph
        (incidenceDrawing source placement presentation.routes)
        presentation.compatible
  orthogonal := by
    rw [incidenceDrawing_scale factor source placement
      presentation.routes presentation.periodPositive]
    exact
      PeriodicGridDrawing.isOrthogonal_scale
        factorPositive
        (incidenceDrawing source placement presentation.routes)
        presentation.orthogonal
  planar := by
    rw [incidenceDrawing_scale factor source placement
      presentation.routes presentation.periodPositive]
    exact
      (PeriodicGridDrawing.isContinuouslyPlanar_scale
        factorPositive
        (incidenceDrawing source placement presentation.routes)
        presentation.continuouslyPlanar).isPlanar
  continuouslyPlanar := by
    rw [incidenceDrawing_scale factor source placement
      presentation.routes presentation.periodPositive]
    exact
      PeriodicGridDrawing.isContinuouslyPlanar_scale
        factorPositive
        (incidenceDrawing source placement presentation.routes)
        presentation.continuouslyPlanar

end PositionedPeriodicCNF

end LeanTrominoes
