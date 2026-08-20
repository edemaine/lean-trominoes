/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestPositionData

/-! # Computed-position affine requests split by vertex kind -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Lookup-free compact request for one retained monochromatic element. -/
def directSparseComputedAffineElementRequestRecordAt
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) :
    List GadgetSparseAffineVertexTokens.Token :=
  let position := horizontalThreeDMVertexPositionAtComputed source
    (.element color atom)
  GadgetSparseAffineVertexTokens.record position.1.toNat
    (2 * input.drawing.gridSize - position.2.toNat - 1)
    (.monochromaticVertex color)

@[simp] theorem directSparseComputedAffineVertexRequestRecordAt_element
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) :
    directSparseComputedAffineVertexRequestRecordAt source input
        (.element color atom) =
      directSparseComputedAffineElementRequestRecordAt
        source input color atom := by
  rfl

/-- Lookup-free pointwise requests split into the triple prefix and retained
element suffix. -/
theorem directSparseComputedAffineVertexRequestsAt_eq_triples_elements
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    input.problem.contractedGraph.vertices.flatMap
        (directSparseComputedAffineVertexRequestRecordAt source input) =
      input.problem.tripleVertices.flatMap
          (directSparseComputedAffineVertexRequestRecordAt source input) ++
        input.problem.contractedElementVertices.flatMap
          (directSparseComputedAffineVertexRequestRecordAt source input) := by
  simp [PeriodicThreeDM.contractedGraph]

/-- The pointwise retained-element suffix remains in red, green, blue order. -/
theorem directSparseComputedAffineElementRequestsAt_eq_colors
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    input.problem.contractedElementVertices.flatMap
        (directSparseComputedAffineVertexRequestRecordAt source input) =
      (input.problem.contractedElementVerticesForColor .red).flatMap
          (directSparseComputedAffineVertexRequestRecordAt source input) ++
        ((input.problem.contractedElementVerticesForColor .green).flatMap
          (directSparseComputedAffineVertexRequestRecordAt source input) ++
        (input.problem.contractedElementVerticesForColor .blue).flatMap
          (directSparseComputedAffineVertexRequestRecordAt source input)) := by
  simp [PeriodicThreeDM.contractedElementVertices,
    PeriodicThreeDM.incidenceColors]

/-- A lookup-free constant-color block scans exactly its degree-three atom
indices. -/
theorem directSparseComputedAffineElementRequestsAtForColor_eq_atoms
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) :
    (input.problem.contractedElementVerticesForColor color).flatMap
        (directSparseComputedAffineVertexRequestRecordAt source input) =
      ((List.range (input.problem.elementCount color)).filter fun atom =>
          input.problem.degree color atom = 3).flatMap
        (directSparseComputedAffineElementRequestRecordAt
          source input color) := by
  unfold PeriodicThreeDM.contractedElementVerticesForColor
  rw [List.flatMap_map]
  rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance
    directSparseAffineVertexRequestPositionSplitStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The lookup-free direct request stream is the concatenation of one triple
scan and three constant-color degree-three element scans. -/
theorem directSparseComputedAffineVertexRequestsAtOfSymbols_eq_vertexKinds
    (symbols : List encoding.Γ) :
    directSparseComputedAffineVertexRequestsAtOfSymbols decider symbols =
      let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
        decider symbols
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.tripleVertices.flatMap
          (directSparseComputedAffineVertexRequestRecordAt source input) ++
        (((List.range (input.problem.elementCount .red)).filter fun atom =>
            input.problem.degree .red atom = 3).flatMap
            (directSparseComputedAffineElementRequestRecordAt
              source input .red) ++
        (((List.range (input.problem.elementCount .green)).filter fun atom =>
            input.problem.degree .green atom = 3).flatMap
            (directSparseComputedAffineElementRequestRecordAt
              source input .green) ++
        ((List.range (input.problem.elementCount .blue)).filter fun atom =>
            input.problem.degree .blue atom = 3).flatMap
            (directSparseComputedAffineElementRequestRecordAt
              source input .blue))) := by
  unfold directSparseComputedAffineVertexRequestsAtOfSymbols
  dsimp only
  rw [directSparseComputedAffineVertexRequestsAt_eq_triples_elements,
    directSparseComputedAffineElementRequestsAt_eq_colors,
    directSparseComputedAffineElementRequestsAtForColor_eq_atoms,
    directSparseComputedAffineElementRequestsAtForColor_eq_atoms,
    directSparseComputedAffineElementRequestsAtForColor_eq_atoms]

end PeriodicCNFStripReduction
end LeanTrominoes
