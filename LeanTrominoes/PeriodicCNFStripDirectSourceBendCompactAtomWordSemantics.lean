/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBendCompactAtomWordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicOrthocrossingBendCompactAtomWordStreamSemantics

/-! # Exact semantics of direct-source compact bend atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceBendCompactSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceBendCompactSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The physical direct bend token stream encodes exactly its semantic
route-major compact occurrence words. -/
theorem directSourceBendCompactAtomWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceBendCompactAtomWordTokens decider symbols =
      DelimitedBinaryWords.encode
        (directSourceBendCompactAtomWords decider symbols) := by
  unfold directSourceBendCompactAtomWordTokens
  rw [directSourceRouteDescriptorPairFieldTags_eq,
    BendCompactAtomWordStream.emittedStream_encodeDescriptorPairs,
    RouteDescriptorPairAffine.affineBaseBendCompactAtomWordStream_numericRouteDescriptors
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSourceFormula_isForwardLocal decider symbols)]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
