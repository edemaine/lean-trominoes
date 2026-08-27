/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalFiniteIncidenceDirectionQueryData

/-! # Compiler for finite horizontal incidence direction queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalFiniteIncidenceDirectionQuery

open Computability Turing

local instance : Inhabited AxisDirection := ⟨.east⟩

/-- Map any list of finite local queries to the concatenation of their exact
direction words. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  change TM2ComputableInPolyTime id id
    (fun queries : List HorizontalFiniteIncidenceDirectionQuery =>
      queries.flatMap directions)
  exact FiniteBlockTransducer.computableInPolyTime directions

/-- Map finite local queries independently to delimited incidence words. -/
noncomputable def delimitedOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id delimitedOutput := by
  change TM2ComputableInPolyTime id id
    (fun queries : List HorizontalFiniteIncidenceDirectionQuery =>
      queries.flatMap block)
  exact FiniteBlockTransducer.computableInPolyTime block

end HorizontalFiniteIncidenceDirectionQuery
end PeriodicCNFStripReduction
end LeanTrominoes

end
