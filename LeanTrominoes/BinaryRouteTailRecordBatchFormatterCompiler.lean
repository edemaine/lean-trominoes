/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterData
import LeanTrominoes.FiniteStateTransducerTime

/-! # Compiler for batched binary route-tail records -/

noncomputable section

namespace LeanTrominoes
namespace BinaryRouteTailRecordBatchFormatter

open Computability Turing

/-- Profile framing and four-route record formatting form one fixed
finite-state linear-time compiler. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

end BinaryRouteTailRecordBatchFormatter
end LeanTrominoes

end
