/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVariableEncoding
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData

/-! # Injective numeric codes for final direct-source atoms -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing

/-- Canonical input-independent code of one wrapped routed atom. -/
def directSourceFinalAtomCode
    (atom : WrappedPeriodicPlanarSATVariable Variable) : Nat :=
  Encodable.encode atom

/-- The canonical final atom code is injective. -/
theorem directSourceFinalAtomCode_injective :
    Function.Injective directSourceFinalAtomCode :=
  Encodable.encode_injective

end PeriodicCNFStripReduction
end LeanTrominoes

end
