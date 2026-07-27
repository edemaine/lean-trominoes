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
