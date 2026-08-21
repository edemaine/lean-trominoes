/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataPortRanks

/-! # CNF incidence metadata and variable-occurrence order -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Erasing clause and presentation indices from the metadata-rich incidence
stream recovers the formula's literal-atom occurrence stream exactly. -/
theorem incidencesWithMetadata_atoms
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    (incidencesWithMetadata formula).map
        (fun incidence => incidence.literal.atom) =
      formula.variableOccurrences := by
  unfold incidencesWithMetadata variableOccurrences
  rw [List.map_flatMap]
  calc
    (formula.clauses.zipIdx.flatMap fun taggedClause =>
      (taggedClause.1.zipIdx.map fun taggedLiteral =>
        (⟨taggedClause.2, taggedClause.1,
          taggedLiteral.2, taggedLiteral.1⟩ :
            CNFIncidence Variable)).map
              fun incidence => incidence.literal.atom) =
        formula.clauses.zipIdx.flatMap fun taggedClause =>
          taggedClause.1.map PeriodicLiteral.atom := by
            apply List.flatMap_congr
            intro taggedClause _
            rw [List.map_map]
            change (taggedClause.1.zipIdx.map fun taggedLiteral =>
              taggedLiteral.1.atom) = _
            rw [show (taggedClause.1.zipIdx.map fun taggedLiteral =>
                taggedLiteral.1.atom) =
              (taggedClause.1.zipIdx.map Prod.fst).map
                PeriodicLiteral.atom by
                  rw [List.map_map]
                  rfl,
              List.zipIdx_map_fst]
    _ = formula.clauses.flatMap fun clause =>
          clause.map PeriodicLiteral.atom :=
      zipIdx_flatMap_fst
        (fun clause => clause.map PeriodicLiteral.atom)
        formula.clauses 0

end PeriodicCNF

namespace PeriodicOrthocrossing

/-- The target-port rank of a metadata incidence is its zero-based occurrence
number in the formula's complete literal-atom stream. -/
theorem incidenceTargetPortRank_eq_variableOccurrencePrefixCount
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember :
      tagged ∈ (PeriodicCNF.incidencesWithMetadata formula).zipIdx) :
    portRank formula.incidenceGraph
        (targetPort tagged.1.edge tagged.2) =
      (formula.variableOccurrences.take tagged.2).count
        tagged.1.literal.atom := by
  rw [incidenceTargetPortRank_eq_priorAtomCount formula tagged taggedMember,
    List.map_take, PeriodicCNF.incidencesWithMetadata_atoms]

end PeriodicOrthocrossing
end LeanTrominoes
