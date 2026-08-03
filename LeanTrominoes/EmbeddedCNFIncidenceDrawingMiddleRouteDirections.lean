import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.OrthogonalPolylineJoin

/-!
# Middle-literal clause exits in finite incidence drawings

The unit-elimination connector only needs one directional fact about its
source drawing: a route at literal index `1` must not leave its clause toward
larger `x`.  This finite coordinate predicate is decidable on concrete
gadgets and survives translation and logical-variable renaming.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Every nondegenerate literal-index-one route first moves weakly left. -/
def MiddleRoutesDoNotExitRight
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    (drawing.incidenceAt incidenceIndex).literalIndex = 1 →
      let route := drawing.routeAt (drawing.incidenceAt incidenceIndex)
      2 ≤ route.length →
        (route.tail.head?.getD (0, 0)).1 ≤
          (route.head?.getD (0, 0)).1

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.MiddleRoutesDoNotExitRight := by
  unfold MiddleRoutesDoNotExitRight incidenceAt incidences routeAt
  infer_instance

/-- Translation preserves the middle-route weak-left inequality. -/
theorem MiddleRoutesDoNotExitRight.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (directions : drawing.MiddleRoutesDoNotExitRight)
    (offset : Cell) :
    (drawing.translate offset).MiddleRoutesDoNotExitRight := by
  intro translatedIndex middleIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  have originalMiddle :
      (drawing.incidenceAt originalIndex).literalIndex = 1 := by
    rw [incidenceEqual] at middleIndex
    simpa [EmbeddedCNFIncidence.translate] using middleIndex
  rw [incidenceEqual, routeAt_translate_incidence]
  dsimp only
  intro translatedLength
  have originalLength :
      2 ≤
        (drawing.routeAt
          (drawing.incidenceAt originalIndex)).length := by
    simpa [PeriodicOrthocrossing.translatePolyline]
      using translatedLength
  have originalDirection :=
    directions originalIndex originalMiddle originalLength
  cases routeEquation :
      drawing.routeAt (drawing.incidenceAt originalIndex) with
  | nil => simp [routeEquation] at originalLength
  | cons first rest =>
      cases rest with
      | nil => simp [routeEquation] at originalLength
      | cons exit tail =>
          simpa [routeEquation,
            PeriodicOrthocrossing.translatePolyline,
            Cell.add] using originalDirection

/-- Logical-variable renaming preserves the middle-route inequality. -/
theorem MiddleRoutesDoNotExitRight.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    (directions : drawing.MiddleRoutesDoNotExitRight)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename variableMap targetPosition).MiddleRoutesDoNotExitRight := by
  intro renamedIndex middleIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename drawing variableMap targetPosition renamedIndex
  have originalMiddle :
      (drawing.incidenceAt originalIndex).literalIndex = 1 := by
    rw [incidenceEqual] at middleIndex
    simpa [EmbeddedCNFIncidence.rename] using middleIndex
  rw [incidenceEqual, routeAt_rename_incidence]
  exact directions originalIndex originalMiddle

/-- Membership-style consequence for one middle route. -/
theorem middleRoute_doesNotExitRight_of_members
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (directions : drawing.MiddleRoutesDoNotExitRight)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    (literalMember : (literal, 1) ∈ clause.literals.zipIdx)
    {head exit : Cell}
    (routeHead : (drawing.routes clauseIndex 1).head? = some head)
    (routeExit : (drawing.routes clauseIndex 1).tail.head? = some exit) :
    exit.1 ≤ head.1 := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, 1⟩
  have incidenceMember : incidence ∈ drawing.incidences :=
    (mem_embeddedCNFIncidences_iff drawing.formula incidence).mpr
      ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence := incidenceEqual
  have routeLength : 2 ≤ (drawing.routes clauseIndex 1).length :=
    List.two_le_length_of_tail_head?_eq_some routeExit
  have selected := directions incidenceIndex
  rw [incidenceAtEqual] at selected
  have inequality := selected rfl (by simpa [incidence, routeAt]
    using routeLength)
  simpa [incidence, routeAt, routeHead, routeExit] using inequality

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
