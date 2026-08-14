/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEqualityOneDimensional
import LeanTrominoes.PeriodicCNFPlanarNormalizationComponents

/-!
# One-dimensional normalized route-bend clauses

Both terminals joined across a route bend retain the same explicit periodic
translate.  Their anchor-normalized equality clauses therefore have zero
vertical offsets, before and after embedding into the planar-SAT variable
type.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The two endpoints of every route-bend link normalize with the same
vertical shift. -/
theorem drawingRouteBendLinks_verticalEqual
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMember : link ∈ drawingRouteBendLinks graph) :
    (normalizeCarrierNode graph link.first).2.2 =
      (normalizeCarrierNode graph link.second).2.2 := by
  rcases List.mem_map.mp linkMember with
    ⟨routeBend, _routeBendMember, rfl⟩
  rfl

/-- The normalized route-bend equality family is one dimensional. -/
theorem normalizedRouteBendClauses_isOneDimensional
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    PeriodicCNF.IsOneDimensional
      ⟨PeriodicEquality.normalizedFormulaClauses
        (normalizeCarrierNode graph) (drawingRouteBendLinks graph)⟩ := by
  apply PeriodicEquality.normalizedFormulaClauses_isOneDimensional
  intro link linkMember
  exact drawingRouteBendLinks_verticalEqual graph linkMember

/-- Embedding normalized bend literals into the combined planar-SAT variable
type preserves their zero vertical offsets. -/
theorem embeddedNormalizedRouteBendClauses_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF.IsOneDimensional
      ⟨embeddedNormalizedRouteBendClauses formula⟩ := by
  have horizontal := normalizedRouteBendClauses_isOneDimensional
    (PeriodicCNF.incidenceGraph formula)
  intro clause clauseMember literal literalMember
  simp only [embeddedNormalizedRouteBendClauses, List.mem_map]
    at clauseMember
  obtain ⟨carrierClause, carrierClauseMember, rfl⟩ := clauseMember
  simp only [embedPeriodicCarrierClause, List.mem_map] at literalMember
  obtain ⟨carrierLiteral, carrierLiteralMember, rfl⟩ := literalMember
  exact horizontal carrierClause carrierClauseMember
    carrierLiteral carrierLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
