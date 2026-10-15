/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendTerminalColumnStreamSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Base.PeriodicCNFStripDirectSourceBaseBendTerminalColumnData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldEncoderNestedFlatMapSemantics

/-! # Direct retained-bend terminal-direction semantics -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

local instance directBaseBendTerminalDirectionVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The selected physical direction stream is the canonical unary encoding
of the semantic bend direction ranks. -/
theorem directSourceBaseBendTerminalDirectionStream_eq
    (symbols : List encoding.Γ) :
    directSourceBaseBendTerminalDirectionStream decider symbols =
      UnaryFieldEncoderMachine.unaryFields
        (directSourceBaseBendTerminalDirectionRanks decider symbols) := by
  unfold directSourceBaseBendTerminalDirectionStream
    directSourceBaseBendTerminalDirectionRanks
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  rw [RouteDescriptorPairAffine.affineBaseBendTerminalDirectionStream_eq_portStream]
  rw [RouteDescriptorPairAffine.affineBaseBendPortStream_numericRouteDescriptors
    RouteDescriptorPairAffine.canonicalBendTerminalDirectionBlock
    (directSourceFormula decider symbols)
    (PeriodicCNF.incidenceGraph_isWellFormed _)
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
    (by
      unfold directSourceFormula
      exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
    (directSourceFormula_isForwardLocal decider symbols)]
  unfold RouteDescriptorPairAffine.canonicalBendTerminalDirectionBlock
  rw [UnaryFieldEncoderMachine.unaryFields_flatMap]
  apply List.flatMap_congr
  intro descriptor _descriptorMember
  rw [UnaryFieldEncoderMachine.unaryFields_flatMap]

end LeanTrominoes.PeriodicCNFStripReduction

end
