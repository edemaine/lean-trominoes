/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryData

/-! # Finite occurrence-role data for final copied-clause queries -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

/-- One finite control token per occurrence of a final copied-clause query:
the whole finite query together with its zero-based literal position. -/
abbrev RetainedFinalCopiedClauseOccurrenceRole :=
  RetainedFinalCopiedClauseQuery × Fin 3

end LeanTrominoes.PeriodicEightOccurrenceSplit
