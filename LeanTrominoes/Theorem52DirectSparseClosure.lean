/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatStripDeciderSpace
import LeanTrominoes.PeriodicCNFStripDirectSparsePreparedTokenEmitterCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseRecordAppenderPackaging
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction

/-! # Final Theorem 5.2 closure from the two sparse geometry appenders -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- The verified plane reduction, strip membership decider, and all fixed
postprocessing leave exactly two uniform geometry machines: the vertex-record
prefix appender and route-record suffix appender. -/
theorem theorem52_statement_of_directSparseSplitRecordAppenders
    (appenders : DirectSparseSplitRecordAppenders) :
    Theorem52.statement := by
  refine ⟨PeriodicWangPlanarThreeDMReduction.theorem52_planeStatement, ?_⟩
  exact theorem52_stripStatement_of_directSparsePreparedTokenEmitters
    PeriodicStrip.RawWindowState.FlatStripDeciderPartrec.flatPeriodicStripTrominoTiling_inPSPACE
    (directSparseCompiledTrominoStripPreparedTokenEmitters_of_assignmentRecordEmitters
      (directSparseAssignmentRecordEmitters_of_splitAppenders appenders))

end PeriodicCNFStripReduction
end LeanTrominoes

