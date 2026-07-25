import LeanTrominoes.PeriodicCNFPlanarDegree

/-!
# Soundness at routed CNF variable gadgets

When the source presentation has at most three occurrences per
protovariable, every routed target at a lifted variable site appears among
the three duplicator ports.  Thus a satisfying variable gadget equates every
target terminal with its central atom.  Complete-route soundness then carries
that equality back to the corresponding routed clause terminal.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- If a list has length at most three, equality at its first three total
`getD` selections covers every actual member. -/
theorem assignment_eq_center_of_mem_length_le_three
    {Node : Type*}
    (assignment : Node → Bool)
    (nodes : List Node) (center node : Node)
    (nodeMem : node ∈ nodes)
    (lengthLe : nodes.length ≤ 3)
    (firstEq :
      assignment (nodes.getD 0 center) = assignment center)
    (secondEq :
      assignment (nodes.getD 1 center) = assignment center)
    (thirdEq :
      assignment (nodes.getD 2 center) = assignment center) :
    assignment node = assignment center := by
  rcases List.getElem_of_mem nodeMem with
    ⟨index, indexBound, nodeEq⟩
  rw [← nodeEq]
  have indexLe : index ≤ 2 := by omega
  have indexCases :
      index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases indexCases with indexEq | indexEq | indexEq
  · subst index
    rw [← List.getD_eq_getElem nodes center indexBound]
    exact firstEq
  · subst index
    rw [← List.getD_eq_getElem nodes center indexBound]
    exact secondEq
  · subst index
    rw [← List.getD_eq_getElem nodes center indexBound]
    exact thirdEq

/-- Under the occurrence-three premise, a satisfying routed variable family
equates every enumerated target terminal with its central lifted atom. -/
theorem drawingRoutedVariableFormula_target_eq_atom
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (assignment : PlanarSATNode Variable → Bool)
    (variablesHold :
      FormulaHolds assignment
        (drawingRoutedVariableFormula formula))
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    assignment
        (.carrier (.terminal
          (occurrence.targetTerminal formula))) =
      assignment (.atom occurrence.variableOccurrence) := by
  let site := occurrence.variableOccurrence
  let occurrenceNode : PlanarSATNode Variable :=
    .carrier (.terminal
      (occurrence.targetTerminal formula))
  let center : PlanarSATNode Variable := .atom site
  let nodes : List (PlanarSATNode Variable) :=
    (variableRouteOccurrencesAt formula site).map fun routed =>
      .carrier (.terminal (routed.targetTerminal formula))
  have siteMem :
      site ∈ drawingVariableRouteSites formula := by
    simp only [drawingVariableRouteSites, List.mem_dedup,
      List.mem_map]
    exact ⟨occurrence, occurrenceMem, rfl⟩
  have occurrenceAtMem :
      occurrence ∈ variableRouteOccurrencesAt formula site := by
    simp [variableRouteOccurrencesAt, site, occurrenceMem]
  have nodeMem : occurrenceNode ∈ nodes := by
    exact List.mem_map.mpr
      ⟨occurrence, occurrenceAtMem, rfl⟩
  have lengthLe : nodes.length ≤ 3 := by
    simpa [nodes] using
      variableRouteOccurrencesAt_length_le_three
        formula occurrences site
  have portLaws :=
    (drawingRoutedVariableFormula_holds_iff
      formula assignment).mp variablesHold site siteMem
  change
    assignment (nodes.getD 0 center) = assignment center ∧
      assignment (nodes.getD 1 center) = assignment center ∧
        assignment (nodes.getD 2 center) = assignment center
      at portLaws
  exact assignment_eq_center_of_mem_length_le_three
    assignment nodes center occurrenceNode nodeMem lengthLe
    portLaws.1 portLaws.2.1 portLaws.2.2

/-- In any satisfying combined planar formula for an occurrence-three source,
each routed clause terminal equals the central lifted atom reached at the
other end of its incidence route. -/
theorem drawingPlanarSATFormula_source_eq_atom
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (assignment : PlanarSATVariable Variable → Bool)
    (holds :
      FormulaHolds assignment
        (drawingPlanarSATFormula formula))
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    assignment
        (.inl (.carrier (.terminal
          (occurrence.sourceTerminal formula)))) =
      assignment
        (.inl (.atom occurrence.variableOccurrence)) := by
  have components :=
    (drawingPlanarSATFormula_holds_iff
      formula assignment).mp holds
  have routeEq :=
    drawingCNFRoutePlanarCore_source_eq_target
      formula
      (assignment ∘ planarSATCoreVariableMap)
      components.1 occurrenceMem
  have targetEq :=
    drawingRoutedVariableFormula_target_eq_atom
      formula occurrences
      (assignment ∘ planarSATExternalVariableMap)
      components.2.2 occurrenceMem
  exact routeEq.trans targetEq

end PeriodicOrthocrossing
end LeanTrominoes
