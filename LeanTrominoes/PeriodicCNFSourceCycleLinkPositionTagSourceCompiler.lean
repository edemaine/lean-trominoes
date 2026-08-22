/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkPositionTagCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomGroupSizeCompiler

/-! # Polynomial-time source cycle-link position tags -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkPositionTags

open Computability Turing

/-- The source's already compiled group sizes produce its exact cycle-link
boundary tags in polynomial time. -/
noncomputable def sourceTagsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode id
      (fun source =>
        tags (PeriodicCNF.SourceOccurrenceAtomGroupSizes.sizes source)) :=
  TM2CompositionMachine.computableInPolyTime
    PeriodicCNF.SourceOccurrenceAtomGroupSizes.unaryFieldsComputableInPolyTime
    computableInPolyTime

end LeanTrominoes.PeriodicCNF.SourceCycleLinkPositionTags

end
