/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeCNFClauseZeroAnchors

/-! # Zero anchors under width-three conversion -/

namespace LeanTrominoes
namespace PeriodicThreeCNF

/-- Width-three conversion preserves a presentation in which every clause
starts at the current slice. -/
theorem formula_zeroAnchored
    {Variable : Type*} (source : PeriodicCNF Variable)
    (sourceAnchored : source.IsZeroAnchored) :
    (formula source).IsZeroAnchored := by
  intro clause clauseMember
  unfold formula at clauseMember
  rw [List.mem_flatMap] at clauseMember
  obtain ⟨sourceClause, sourceClauseMember, clauseMember⟩ := clauseMember
  rw [clauseClauses_clauseAnchor sourceClause clause clauseMember]
  simpa [PeriodicCNF.IsZeroAnchored, PeriodicCNF.ClausesZeroAnchored,
    anchor, PeriodicCNF.clauseAnchor] using
    sourceAnchored sourceClause sourceClauseMember

end PeriodicThreeCNF
end LeanTrominoes
