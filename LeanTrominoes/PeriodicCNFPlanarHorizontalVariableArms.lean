/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEqualityOneDimensional
import LeanTrominoes.PeriodicGraphHorizontal
import LeanTrominoes.PeriodicCNFPlanarVariableNormalizationDegree

/-!
# One-dimensional normalized variable-arm clauses

A routed variable arm joins its target terminal at an explicit translated
route occurrence to the source atom at that occurrence's translated target.
The only relative shift left by anchor normalization is therefore the
incidence edge offset.  Horizontal source incidence graphs make every such
equality clause one dimensional.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every represented CNF route occurrence routes an edge of the source
incidence graph. -/
theorem CNFRouteOccurrence.edge_mem_incidenceGraph
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember : occurrence ∈ drawingCNFRouteOccurrences formula) :
    occurrence.edge ∈ (PeriodicCNF.incidenceGraph formula).edges := by
  rcases List.mem_flatMap.mp occurrenceMember with
    ⟨tagged, taggedMember, occurrenceMember⟩
  rcases List.mem_map.mp occurrenceMember with
    ⟨translate, _translateMember, rfl⟩
  exact List.fst_mem_of_mem_zipIdx
    (PeriodicCNF.tagged_incidence_edge_mem formula taggedMember)

/-- The endpoints of every routed variable-arm link normalize with equal
vertical shifts when the source incidence graph is horizontal. -/
theorem drawingRoutedVariableLinks_verticalEqual
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (horizontal :
      (PeriodicCNF.incidenceGraph formula).HasZeroVerticalOffsets)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMember : link ∈ drawingRoutedVariableLinks formula) :
    (normalizePlanarSATNode
        (PeriodicCNF.incidenceGraph formula) link.first).2.2 =
      (normalizePlanarSATNode
        (PeriodicCNF.incidenceGraph formula) link.second).2.2 := by
  rcases drawingRoutedVariableLink_witness formula linkMember with
    ⟨site, occurrence, occurrenceMember, siteEq, firstEq, secondEq⟩
  subst site
  have edgeVertical := horizontal occurrence.edge
    (occurrence.edge_mem_incidenceGraph formula occurrenceMember)
  rw [firstEq, secondEq]
  simp [normalizePlanarSATNode,
    CNFRouteOccurrence.targetTerminal,
    CNFRouteOccurrence.variableOccurrence, Cell.add, edgeVertical]

/-- The normalized routed variable-arm equality family is one dimensional
whenever the source incidence graph is horizontal. -/
theorem normalizedDrawingRoutedVariableClauses_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (horizontal :
      (PeriodicCNF.incidenceGraph formula).HasZeroVerticalOffsets) :
    PeriodicCNF.IsOneDimensional
      ⟨PeriodicEquality.normalizedFormulaClauses
        (normalizePlanarSATNode (PeriodicCNF.incidenceGraph formula))
        (drawingRoutedVariableLinks formula)⟩ := by
  apply PeriodicEquality.normalizedFormulaClauses_isOneDimensional
  intro link linkMember
  exact drawingRoutedVariableLinks_verticalEqual
    formula horizontal linkMember

end PeriodicOrthocrossing
end LeanTrominoes
