/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataBendClauseDescriptorData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiling direct retained bend descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile direct-source route pairs, then scan each tagged pair for its
retained bend descriptor block. -/
noncomputable def
    directRetainedPlanarMetadataCompiledBendClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataCompiledBendClauseDescriptorCompiler
      decider := by
  let fields :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let bends :=
    PeriodicOrthocrossing.RouteDescriptorPairAffine.affineBendDescriptorStreamComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime fields bends
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
