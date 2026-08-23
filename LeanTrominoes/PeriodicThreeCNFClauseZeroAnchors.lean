/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFZeroAnchorData
import LeanTrominoes.PeriodicThreeCNF

/-! # Clause anchors under width-three conversion -/

namespace LeanTrominoes
namespace PeriodicThreeCNF

/-- Every continuation-chain clause begins with an auxiliary literal placed
at the source clause's anchor. -/
theorem continuation_clauseAnchor
    {Variable : Type*} (source remaining : PeriodicClause Variable) :
    ∀ clause ∈ continuation source remaining,
      PeriodicCNF.clauseAnchor clause = anchor source := by
  induction remaining with
  | nil =>
      simp [continuation, PeriodicCNF.clauseAnchor, auxiliary]
  | cons first rest induction =>
      cases rest with
      | nil =>
          simp [continuation, PeriodicCNF.clauseAnchor, auxiliary]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [continuation, PeriodicCNF.clauseAnchor, auxiliary]
          | cons third rest =>
              intro clause clauseMember
              simp only [continuation, List.mem_cons] at clauseMember
              rcases clauseMember with rfl | clauseMember
              · simp [PeriodicCNF.clauseAnchor, auxiliary]
              · exact induction clause clauseMember

/-- Every clause produced from one source clause inherits that source
clause's anchor. -/
theorem clauseClauses_clauseAnchor
    {Variable : Type*} (source : PeriodicClause Variable) :
    ∀ clause ∈ clauseClauses source,
      PeriodicCNF.clauseAnchor clause = anchor source := by
  cases source with
  | nil =>
      simp [clauseClauses, anchor, PeriodicCNF.clauseAnchor]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [clauseClauses, anchor, PeriodicCNF.clauseAnchor,
            liftLiteral]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [clauseClauses, anchor, PeriodicCNF.clauseAnchor,
                liftLiteral]
          | cons third rest =>
              cases rest with
              | nil =>
                  simp [clauseClauses, anchor, PeriodicCNF.clauseAnchor,
                    liftLiteral]
              | cons fourth rest =>
                  intro clause clauseMember
                  simp only [clauseClauses, List.mem_cons] at clauseMember
                  rcases clauseMember with rfl | clauseMember
                  · simp [anchor, PeriodicCNF.clauseAnchor, liftLiteral]
                  · exact continuation_clauseAnchor
                      (first :: second :: third :: fourth :: rest)
                      (third :: fourth :: rest) clause clauseMember

end PeriodicThreeCNF
end LeanTrominoes
