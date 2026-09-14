/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitCertificates
import LeanTrominoes.CompletionCircuitTruthTables

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-- The nine concrete macro layouts pass the wiring and forest checker. -/
theorem circuit_wiring_checked (kind : CircuitKind) : (circuitFor kind).Checked := by
  cases kind <;> decide +kernel

end LeanTrominoes.CompletionPattern.LBricks
