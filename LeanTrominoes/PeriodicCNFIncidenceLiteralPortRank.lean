/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataLocalRanks
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorData

/-! # Clause-side incidence ranks are literal indices -/

namespace LeanTrominoes

namespace PeriodicOrthocrossing

/-- A genuine CNF incidence's geometric source-port rank is exactly its
within-clause literal index. -/
theorem incidenceSourcePortRank_eq_literalIndex
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember :
      tagged ∈ (PeriodicCNF.incidencesWithMetadata formula).zipIdx) :
    portRank formula.incidenceGraph
        (sourcePort tagged.1.edge tagged.2) =
      tagged.1.literalIndex := by
  rw [incidenceSourcePortRank_eq_priorClauseCount
    formula tagged taggedMember]
  exact PeriodicCNF.metadataIncidence_priorClauseCount_eq_literalIndex
    formula tagged taggedMember

end PeriodicOrthocrossing

namespace CNFIncidence

/-- The clause-side rank field of a genuine numeric descriptor can be copied
directly from the incidence metadata. -/
@[simp] theorem numericRouteDescriptor_sourcePortRank_eq_literalIndex
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember :
      tagged ∈ (PeriodicCNF.incidencesWithMetadata formula).zipIdx) :
    (tagged.1.numericRouteDescriptor formula tagged.2).sourcePortRank =
      tagged.1.literalIndex := by
  unfold numericRouteDescriptor
  exact PeriodicCNF.metadataIncidence_priorClauseCount_eq_literalIndex
    formula tagged taggedMember

end CNFIncidence
end LeanTrominoes
