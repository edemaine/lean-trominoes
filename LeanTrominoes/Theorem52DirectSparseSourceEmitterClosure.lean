/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTablePhaseCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRecordCompiler
import LeanTrominoes.Theorem52DirectSparseClosure

/-! # Final Theorem 5.2 closure from source-side geometry emitters -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- The two remaining source-specific obligations after all generic geometry
machines: five finite affine vertex families and one compact route-request
emitter. -/
def DirectSparseSourceGeometryEmitters : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language),
    Nonempty (DirectSparseAffineTablePhaseFamilies decider) ∧
      Nonempty (DirectSparseRouteRasterRequestTokenCompiler decider)

/-- Source-side geometry emitters instantiate both retained-input record
appenders used by the established sparse assignment pipeline. -/
theorem directSparseSplitRecordAppenders_of_sourceGeometryEmitters
    (emitters : DirectSparseSourceGeometryEmitters) :
    DirectSparseSplitRecordAppenders := by
  intro Input encoding language decider
  obtain ⟨⟨phases⟩, ⟨routes⟩⟩ :=
    emitters encoding language decider
  exact
    ⟨⟨directSparseVertexRecordAppenderOfTablePhases decider phases⟩,
      ⟨directSparseRouteRecordAppenderOfRasterRequests decider routes⟩⟩

/-- No further theorem-level work remains once the two explicit source
emitters are constructed. -/
theorem theorem52_statement_of_directSparseSourceGeometryEmitters
    (emitters : DirectSparseSourceGeometryEmitters) :
    Theorem52.statement :=
  theorem52_statement_of_directSparseSplitRecordAppenders
    (directSparseSplitRecordAppenders_of_sourceGeometryEmitters emitters)

end PeriodicCNFStripReduction
end LeanTrominoes

end
