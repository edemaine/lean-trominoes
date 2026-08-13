/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Vertical two-point routes in finite incidence drawings

This small finite invariant records that every route consisting of exactly
two listed points is vertical.  It is decidable for concrete drawings and is
preserved by translation and logical-variable renaming.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Every genuine two-point route has equal endpoint `x` coordinates. -/
def TwoPointRoutesVertical
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    let route := drawing.routeAt (drawing.incidenceAt incidenceIndex)
    route.length = 2 →
      (route.head?.getD (0, 0)).1 =
        (route.getLast?.getD (0, 0)).1

/-- Predicate-restricted version of `TwoPointRoutesVertical`. -/
def TwoPointRoutesVerticalOn
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (selected : Variable → Prop) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    selected (drawing.incidenceAt incidenceIndex).literal.1 →
      let route := drawing.routeAt (drawing.incidenceAt incidenceIndex)
      route.length = 2 →
        (route.head?.getD (0, 0)).1 =
          (route.getLast?.getD (0, 0)).1

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.TwoPointRoutesVertical := by
  unfold TwoPointRoutesVertical incidenceAt incidences routeAt
  infer_instance

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (selected : Variable → Prop) [DecidablePred selected] :
    Decidable (drawing.TwoPointRoutesVerticalOn selected) := by
  unfold TwoPointRoutesVerticalOn incidenceAt incidences routeAt
  infer_instance

/-- Translation preserves verticality of every two-point route. -/
theorem TwoPointRoutesVertical.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (vertical : drawing.TwoPointRoutesVertical)
    (offset : Cell) :
    (drawing.translate offset).TwoPointRoutesVertical := by
  intro translatedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  rw [incidenceEqual, routeAt_translate_incidence]
  dsimp only
  intro translatedLength
  have originalLength :
      (drawing.routeAt
        (drawing.incidenceAt originalIndex)).length = 2 := by
    simpa [PeriodicOrthocrossing.translatePolyline] using translatedLength
  have originalVertical := vertical originalIndex originalLength
  cases routeEquation :
      drawing.routeAt (drawing.incidenceAt originalIndex) with
  | nil => simp [routeEquation] at originalLength
  | cons first rest =>
      cases rest with
      | nil => simp [routeEquation] at originalLength
      | cons second tail =>
          have tailEmpty : tail = [] := by
            simpa [routeEquation] using originalLength
          subst tail
          simpa [routeEquation, PeriodicOrthocrossing.translatePolyline,
            Cell.add] using originalVertical

/-- Logical-variable renaming changes no route geometry. -/
theorem TwoPointRoutesVertical.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (vertical : drawing.TwoPointRoutesVertical)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename variableMap targetPosition).TwoPointRoutesVertical := by
  intro renamedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
  exact vertical originalIndex

/-- Translation preserves predicate-restricted verticality. -/
theorem TwoPointRoutesVerticalOn.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {selected : Variable → Prop}
    (vertical : drawing.TwoPointRoutesVerticalOn selected)
    (offset : Cell) :
    (drawing.translate offset).TwoPointRoutesVerticalOn selected := by
  intro translatedIndex selectedLiteral
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  have originalSelected :
      selected (drawing.incidenceAt originalIndex).literal.1 := by
    rw [incidenceEqual] at selectedLiteral
    simpa [EmbeddedCNFIncidence.translate] using selectedLiteral
  rw [incidenceEqual, routeAt_translate_incidence]
  dsimp only
  intro translatedLength
  have originalLength :
      (drawing.routeAt
        (drawing.incidenceAt originalIndex)).length = 2 := by
    simpa [PeriodicOrthocrossing.translatePolyline] using translatedLength
  have originalVertical :=
    vertical originalIndex originalSelected originalLength
  cases routeEquation :
      drawing.routeAt (drawing.incidenceAt originalIndex) with
  | nil => simp [routeEquation] at originalLength
  | cons first rest =>
      cases rest with
      | nil => simp [routeEquation] at originalLength
      | cons second tail =>
          have tailEmpty : tail = [] := by
            simpa [routeEquation] using originalLength
          subst tail
          simpa [routeEquation, PeriodicOrthocrossing.translatePolyline,
            Cell.add] using originalVertical

/-- Renaming preserves restricted verticality when selected target atoms
come from selected source atoms. -/
theorem TwoPointRoutesVerticalOn.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    {sourceSelected : Source → Prop}
    {targetSelected : Target → Prop}
    (vertical : drawing.TwoPointRoutesVerticalOn sourceSelected)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (selectedMap :
      ∀ sourceAtom,
        targetSelected (variableMap sourceAtom) →
          sourceSelected sourceAtom) :
    (drawing.rename variableMap targetPosition).TwoPointRoutesVerticalOn
      targetSelected := by
  intro renamedIndex selectedLiteral
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename drawing variableMap targetPosition renamedIndex
  have originalSelected :
      sourceSelected (drawing.incidenceAt originalIndex).literal.1 := by
    apply selectedMap
    rw [incidenceEqual] at selectedLiteral
    simpa [EmbeddedCNFIncidence.rename] using selectedLiteral
  rw [incidenceEqual, routeAt_rename_incidence]
  exact vertical originalIndex originalSelected

/-- Membership-style consequence for one selected route. -/
theorem twoPointRoute_vertical_of_members
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (vertical : drawing.TwoPointRoutesVertical)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {head exit : Cell}
    (routePair : drawing.routes clauseIndex literalIndex = [head, exit]) :
    exit.1 = head.1 := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember : incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff drawing.formula incidence).mpr
      ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence :=
    incidenceEqual
  have routeEqual :
      drawing.routeAt (drawing.incidenceAt incidenceIndex) =
        [head, exit] := by
    rw [incidenceAtEqual]
    exact routePair
  have selected := vertical incidenceIndex
  rw [routeEqual] at selected
  have endpointsEqual : head.1 = exit.1 := by
    simpa using selected rfl
  exact endpointsEqual.symm

/-- Membership-style consequence of the predicate-restricted invariant. -/
theorem twoPointRoute_verticalOn_of_members
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (selected : Variable → Prop)
    (vertical : drawing.TwoPointRoutesVerticalOn selected)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (literalSelected : selected literal.1)
    {head exit : Cell}
    (routePair : drawing.routes clauseIndex literalIndex = [head, exit]) :
    exit.1 = head.1 := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember : incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff drawing.formula incidence).mpr
      ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence := incidenceEqual
  have routeEqual :
      drawing.routeAt (drawing.incidenceAt incidenceIndex) =
        [head, exit] := by
    rw [incidenceAtEqual]
    exact routePair
  have selectedAtIncidence :
      selected (drawing.incidenceAt incidenceIndex).literal.1 := by
    simpa [incidenceAtEqual] using literalSelected
  have selected := vertical incidenceIndex selectedAtIncidence
  rw [routeEqual] at selected
  have endpointsEqual : head.1 = exit.1 := by
    simpa using selected rfl
  exact endpointsEqual.symm

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
