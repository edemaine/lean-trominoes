/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataAppend
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Shifted implication-cycle incidence data -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Metadata incidences contributed by the implication-cycle suffix, with
clause indices shifted past all copied source clauses. -/
def cycleIncidences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (CNFIncidence (ThreeOccurrenceVariable Variable)) :=
  PeriodicCNF.incidenceMetadataBlocksFrom source.clauses.length
    (allCycleClauses source)

end PeriodicThreeSATThree
end LeanTrominoes
