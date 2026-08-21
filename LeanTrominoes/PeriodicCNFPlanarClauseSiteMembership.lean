/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVertexGadgets

/-! # Clause sites represented by incidence metadata -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Pairing a genuine incidence's clause index with a neighboring translation
produces a represented clause site. -/
theorem CNFIncidence.clauseSite_mem_drawingClauseRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {incidence : CNFIncidence Variable}
    (incidenceMem : incidence ∈
      PeriodicCNF.incidencesWithMetadata formula)
    {translate : Cell} (translateMem : translate ∈ neighborTranslations) :
    (incidence.clauseIndex, translate) ∈
      drawingClauseRouteSites formula := by
  have clauseMem :=
    ((PeriodicCNF.mem_incidencesWithMetadata_iff
      formula incidence).mp incidenceMem).1
  unfold drawingClauseRouteSites
  apply List.mem_flatMap.mpr
  refine ⟨(incidence.clause, incidence.clauseIndex), clauseMem, ?_⟩
  exact List.mem_map.mpr ⟨translate, translateMem, rfl⟩

end LeanTrominoes.PeriodicOrthocrossing
