/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing

/-!
# Membership consequences of finite embedded planarity

`EmbeddedCNFIncidenceDrawing.IsPlanar` is stated over finite indices so fixed
gadgets can discharge it by computation.  Assembly proofs instead identify
incidences by their clause and literal presentation indices.  This module
bridges those two views for route simplicity and pairwise continuous
separation.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Route simplicity, factored out from the first field of finite embedded
planarity so input-dependent assemblies can prove it locally. -/
def EmbeddedCNFIncidenceDrawing.RoutesAreSimple
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    LocalIncidenceDrawing.RouteIsSimple
      (drawing.routeAt (drawing.incidenceAt incidenceIndex))

/-- The three global separation fields of finite embedded planarity. -/
def EmbeddedCNFIncidenceDrawing.GlobalSeparation
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  (∀ firstIndex secondIndex : Fin drawing.incidences.length,
    firstIndex ≠ secondIndex →
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        (drawing.routeAt (drawing.incidenceAt firstIndex))
        (drawing.routeAt (drawing.incidenceAt secondIndex))) ∧
    drawing.VerticesAvoidRouteInteriors ∧
    drawing.vertexPositions.Nodup

/-- Finite embedded planarity is exactly local route simplicity plus global
separation. -/
theorem EmbeddedCNFIncidenceDrawing.isPlanar_iff
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    drawing.IsPlanar ↔
      drawing.RoutesAreSimple ∧ drawing.GlobalSeparation := by
  rfl

/-- Once route simplicity is known componentwise, only global separation
remains. -/
theorem EmbeddedCNFIncidenceDrawing.isPlanar_iff_globalSeparation
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (routesAreSimple : drawing.RoutesAreSimple) :
    drawing.IsPlanar ↔ drawing.GlobalSeparation := by
  rw [drawing.isPlanar_iff, and_iff_right routesAreSimple]

/-- A membership-style simplicity proof for every presented literal implies
indexed simplicity for the packaged drawing. -/
theorem EmbeddedCNFIncidenceDrawing.routesAreSimple_of_members
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (simple :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ drawing.formula.zipIdx →
          ∀ literal literalIndex,
            (literal, literalIndex) ∈ clause.literals.zipIdx →
              LocalIncidenceDrawing.RouteIsSimple
                (drawing.routes clauseIndex literalIndex)) :
    drawing.RoutesAreSimple := by
  intro incidenceIndex
  let incidence := drawing.incidenceAt incidenceIndex
  have incidenceMember :
      incidence ∈ drawing.incidences :=
    List.get_mem drawing.incidences incidenceIndex
  have members :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mp incidenceMember
  exact simple incidence.clause incidence.clauseIndex members.1
    incidence.literal incidence.literalIndex members.2

/-- Extract route simplicity for one genuine presentation-indexed incidence
from a finite drawing's indexed planarity certificate. -/
theorem EmbeddedCNFIncidenceDrawing.embeddedRoute_isSimple_of_members
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (planar : drawing.IsPlanar)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (drawing.routes clauseIndex literalIndex) := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember :
      incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mpr
        ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have selected := planar.1 incidenceIndex
  change
    LocalIncidenceDrawing.RouteIsSimple
      (drawing.routeAt
        (drawing.incidenceAt incidenceIndex)) at selected
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence :=
    incidenceEqual
  rw [incidenceAtEqual] at selected
  exact selected

/-- Extract axis alignment for one segment of a genuine
presentation-indexed incidence route from the drawing's orthogonality
certificate. -/
theorem EmbeddedCNFIncidenceDrawing.embeddedSegment_isAxisAligned_of_members
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (orthogonal : drawing.IsOrthogonal)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      segment ∈
        gridPolylineSegments
          (drawing.routes clauseIndex literalIndex)) :
    segment.IsAxisAligned := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember :
      incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mpr
        ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, segmentEqual⟩
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence :=
    incidenceEqual
  have routeEq :
      drawing.routeAt (drawing.incidenceAt incidenceIndex) =
        drawing.routes clauseIndex literalIndex := by
    rw [incidenceAtEqual]
    rfl
  have selected := orthogonal incidenceIndex
  change
    ∀ segmentIndex :
        Fin
          (gridPolylineSegments
            (drawing.routeAt
              (drawing.incidenceAt incidenceIndex))).length,
      ((gridPolylineSegments
        (drawing.routeAt
          (drawing.incidenceAt incidenceIndex))).get
            segmentIndex).IsAxisAligned at selected
  rw [routeEq] at selected
  have aligned := selected segmentIndex
  simpa only [segmentEqual] using aligned

/-- Extract vertex/interior avoidance for one genuine graph-vertex
position and one segment of a genuine presentation-indexed incidence route
from a finite drawing's indexed planarity certificate. -/
theorem EmbeddedCNFIncidenceDrawing.embeddedVertex_avoidsRouteInterior_of_members
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (planar : drawing.IsPlanar)
    {vertexPosition : Cell}
    (vertexMember : vertexPosition ∈ drawing.vertexPositions)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      segment ∈
        gridPolylineSegments
          (drawing.routes clauseIndex literalIndex)) :
    ¬segment.InteriorContains vertexPosition := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember :
      incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mpr
        ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp vertexMember with
    ⟨vertexIndex, vertexEqual⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, segmentEqual⟩
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence :=
    incidenceEqual
  have routeEqual :
      drawing.routeAt (drawing.incidenceAt incidenceIndex) =
        drawing.routes clauseIndex literalIndex := by
    rw [incidenceAtEqual]
    rfl
  have selected :=
    planar.2.2.1 vertexIndex incidenceIndex
  dsimp only at selected
  rw [routeEqual] at selected
  have avoids := selected segmentIndex
  simpa only [segmentEqual, vertexEqual] using avoids

/-- Extract continuous separation for two distinct genuine
presentation-indexed incidences from a finite drawing's indexed planarity
certificate. -/
theorem EmbeddedCNFIncidenceDrawing.embeddedRoutes_avoidEachOther_of_members
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (planar : drawing.IsPlanar)
    {firstClause secondClause : EmbeddedClause Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈ drawing.formula.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈ drawing.formula.zipIdx)
    {firstLiteral secondLiteral : Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (incidencesDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (drawing.routes firstClauseIndex firstLiteralIndex)
      (drawing.routes secondClauseIndex secondLiteralIndex) := by
  let firstIncidence : EmbeddedCNFIncidence Variable :=
    ⟨firstClause, firstClauseIndex,
      firstLiteral, firstLiteralIndex⟩
  let secondIncidence : EmbeddedCNFIncidence Variable :=
    ⟨secondClause, secondClauseIndex,
      secondLiteral, secondLiteralIndex⟩
  have firstIncidenceMember :
      firstIncidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula firstIncidence).mpr
        ⟨firstClauseMember, firstLiteralMember⟩
  have secondIncidenceMember :
      secondIncidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff
      drawing.formula secondIncidence).mpr
        ⟨secondClauseMember, secondLiteralMember⟩
  rcases List.mem_iff_get.mp firstIncidenceMember with
    ⟨firstIndex, firstIncidenceEqual⟩
  rcases List.mem_iff_get.mp secondIncidenceMember with
    ⟨secondIndex, secondIncidenceEqual⟩
  have indexDistinct : firstIndex ≠ secondIndex := by
    intro indexEqual
    have incidencesEqual :
        firstIncidence = secondIncidence := by
      rw [← firstIncidenceEqual,
        ← secondIncidenceEqual, indexEqual]
    rcases incidencesDistinct with
      clauseIndexDistinct | literalIndexDistinct
    · exact clauseIndexDistinct
        (congrArg EmbeddedCNFIncidence.clauseIndex
          incidencesEqual)
    · exact literalIndexDistinct
        (congrArg EmbeddedCNFIncidence.literalIndex
          incidencesEqual)
  have separated :=
    planar.2.1 firstIndex secondIndex indexDistinct
  change
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (drawing.routeAt
        (drawing.incidenceAt firstIndex))
      (drawing.routeAt
        (drawing.incidenceAt secondIndex)) at separated
  have firstIncidenceAtEqual :
      drawing.incidenceAt firstIndex = firstIncidence :=
    firstIncidenceEqual
  have secondIncidenceAtEqual :
      drawing.incidenceAt secondIndex = secondIncidence :=
    secondIncidenceEqual
  rw [firstIncidenceAtEqual,
    secondIncidenceAtEqual] at separated
  exact separated

end PlanarThreeSAT
end LeanTrominoes
