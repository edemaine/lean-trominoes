/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorFacts

/-! # Exact size of the CNF incidence metadata stream -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- There is exactly one metadata incidence per presented literal. -/
@[simp] theorem incidencesWithMetadata_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (incidencesWithMetadata formula).length =
      presentationLiteralCount formula := by
  calc
    (incidencesWithMetadata formula).length =
        formula.incidenceGraph.edges.length :=
      (incidenceGraph_edges_length_eq_metadata formula).symm
    _ = presentationLiteralCount formula :=
      incidenceGraph_edges_length formula

end PeriodicCNF
end LeanTrominoes
