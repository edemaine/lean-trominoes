/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedDirectionQuery

/-! # Finite queries for complete normalized direct-source tails -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Fixed finite input selecting one complete normalized direct-atlas route.
Unlike the first-direction query, the full tail depends on the Figure Seven
occurrence slot. -/
structure RetainedDirectSourceNormalizedTailQuery where
  kind : RetainedDirectClauseKind
  literalIndex : Fin 3
  slot : RetainedTerminalSlot
  deriving DecidableEq, Fintype

instance : Inhabited RetainedDirectSourceNormalizedTailQuery :=
  ⟨⟨.routedClause, 0, default⟩⟩

/-- Embed one genuine dependent atlas index into the fixed-width complete
route query alphabet. -/
def retainedDirectSourceNormalizedTailQueryOfIndex
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    RetainedDirectSourceNormalizedTailQuery := {
  kind := kind
  literalIndex := ⟨index.val,
    Nat.lt_of_lt_of_le index.isLt
      (retainedDirectSourcePrefixChoices_length_le_three kind)⟩
  slot := slot }

end PeriodicEightOccurrenceSplit
end LeanTrominoes
