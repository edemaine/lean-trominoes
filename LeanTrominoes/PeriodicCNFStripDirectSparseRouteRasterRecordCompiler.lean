/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordBatchCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRequestCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRecordCompiler

/-! # Concrete direct sparse route-record compiler pipeline -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteRasterRecordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compact source requests, fixed affine expansion, dynamic three-round
normalization, and the complement-counter batch machine compile the exact
canonical route-record suffix. -/
noncomputable def directSparseCanonicalRouteRecordsComputableInPolyTimeOfRasterRequests
    (requests : DirectSparseRouteRasterRequestTokenCompiler decider) :
    DirectSparseCanonicalRouteRecordCompiler decider := by
  let validRequests :=
    directSparseValidRouteRasterRequestsComputableInPolyTime
      decider requests
  let records := TM2CompositionMachine.computableInPolyTime validRequests
    GadgetSparseRouteRecordBatch.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq records
    (fun symbols => by
      simp only [id_eq]
      rw [directSparseValidRouteRecordBatchOutput_eq,
        directSparseComputedRouteRasterDirectionRecordsOfSymbols_eq,
        directSparseComputedRouteDirectionRecordsOfSymbols_eq_routeRecords])

/-- Thus the one compact source-request emitter supplies the complete
retained-workspace route appender required by Theorem 5.2. -/
noncomputable def directSparseRouteRecordAppenderOfRasterRequests
    (requests : DirectSparseRouteRasterRequestTokenCompiler decider) :
    DirectSparseRouteRecordAppender decider :=
  directSparseRouteRecordAppenderOfCompiler decider
    (directSparseCanonicalRouteRecordsComputableInPolyTimeOfRasterRequests
      decider requests)

end PeriodicCNFStripReduction
end LeanTrominoes

end
