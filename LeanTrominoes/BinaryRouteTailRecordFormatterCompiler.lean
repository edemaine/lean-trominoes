/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordFormatterData
import LeanTrominoes.FiniteStateTransducerTime

/-! # Compiler for binary-clause route-tail formatting -/

noncomputable section

namespace LeanTrominoes
namespace BinaryRouteTailRecordFormatter

open Computability Turing
open PeriodicCNF

/-- Four complete route-delimited words compile to two flat binary-clause
tail records by one fixed finite-state pass. -/
noncomputable def outputComputableInPolyTime
    (firstProfile secondProfile :
      FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    TM2ComputableInPolyTime id id (output firstProfile secondProfile) := by
  unfold output
  exact FiniteStateTransducer.computableInPolyTime Control.firstHead
    (transition firstProfile secondProfile) finish

end BinaryRouteTailRecordFormatter
end LeanTrominoes

end
