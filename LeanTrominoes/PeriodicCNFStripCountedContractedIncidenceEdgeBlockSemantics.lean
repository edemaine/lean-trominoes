/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceBlockSemantics

/-! # Explicit edge blocks of counted contraction -/

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace CountedContractedIncidence

open PeriodicThreeDM

/-- Regroup an element-major incidence-body stream into its canonical
contracted edges.  Degree two produces one through edge, while degree three
retains its three incidences as three separate edges.  Malformed inputs are
irrelevant under the validity and alignment hypotheses below. -/
def edgeBlocks : List Nat → List (List AxisDirection) →
    List ContractedDirectionAssembler.EdgeBlock
  | 2 :: sizes, first :: second :: bodies =>
      .through first second :: edgeBlocks sizes bodies
  | 3 :: sizes, first :: second :: third :: bodies =>
      .retained first :: .retained second :: .retained third ::
        edgeBlocks sizes bodies
  | _, _ => []

/-- Regrouping aligned bodies preserves exactly the flat role-tagged input
consumed by the contracted-direction assembler. -/
theorem inputTokens_edgeBlocks
    (sizes : List Nat) (bodies : List (List AxisDirection))
    (aligned : bodies.length = (roles sizes).length)
    (valid : ∀ size ∈ sizes, size = 2 ∨ size = 3) :
    ContractedDirectionAssembler.inputTokens (edgeBlocks sizes bodies) =
      ((roles sizes).zip bodies).flatMap fun pair =>
        ContractedDirectionAssembler.roleBlock pair.1 pair.2 := by
  induction sizes generalizing bodies with
  | nil =>
      change bodies.length = 0 at aligned
      have bodiesNil : bodies = [] :=
        List.eq_nil_of_length_eq_zero aligned
      subst bodies
      rfl
  | cons size sizes induction =>
      have headValid : size = 2 ∨ size = 3 := valid size (by simp)
      have tailValid : ∀ other ∈ sizes, other = 2 ∨ other = 3 := by
        intro other member
        exact valid other (by simp [member])
      rcases headValid with rfl | rfl
      · cases bodies with
        | nil => simp at aligned
        | cons first bodies =>
            cases bodies with
            | nil => simp at aligned
            | cons second bodies =>
                have tailAligned :
                    bodies.length = (roles sizes).length := by
                  simpa using aligned
                simp [edgeBlocks,
                  ContractedDirectionAssembler.inputTokens,
                  ContractedDirectionAssembler.EdgeBlock.inputTokens]
                exact induction bodies tailAligned tailValid
      · cases bodies with
        | nil => simp at aligned
        | cons first bodies =>
            cases bodies with
            | nil => simp at aligned
            | cons second bodies =>
                cases bodies with
                | nil => simp at aligned
                | cons third bodies =>
                    have tailAligned :
                        bodies.length = (roles sizes).length := by
                      simpa using aligned
                    simp [edgeBlocks,
                      ContractedDirectionAssembler.inputTokens,
                      ContractedDirectionAssembler.EdgeBlock.inputTokens]
                    exact induction bodies tailAligned tailValid

/-- The assembler output of aligned counted bodies is therefore precisely
the independently delimited direction word of each explicit edge block. -/
theorem output_roleBodies_eq_edgeBlocks
    (sizes : List Nat) (bodies : List (List AxisDirection))
    (aligned : bodies.length = (roles sizes).length)
    (valid : ∀ size ∈ sizes, size = 2 ∨ size = 3) :
    ContractedDirectionAssembler.output
        (((roles sizes).zip bodies).flatMap fun pair =>
          ContractedDirectionAssembler.roleBlock pair.1 pair.2) =
      ContractedDirectionAssembler.outputTokens (edgeBlocks sizes bodies) := by
  rw [← inputTokens_edgeBlocks sizes bodies aligned valid]
  exact ContractedDirectionAssembler.output_inputTokens _

end CountedContractedIncidence
end LeanTrominoes.PeriodicCNFStripReduction
