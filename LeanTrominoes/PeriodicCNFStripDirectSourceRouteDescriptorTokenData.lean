/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTokensData

/-! # Direct-source numeric route-descriptor tokens -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteDescriptorTokenDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceRouteDescriptorTokenDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Exact counted unary records for every direct source incidence route, in
edge-presentation order. -/
def directSourceRouteDescriptorTokens
    (symbols : List encoding.Γ) :
    List PeriodicCNF.UnaryProgramTokens.Token :=
  routeDescriptorTokens
    (numericRouteDescriptors (directSourceFormula decider symbols))

/-- Concrete polynomial-time boundary for the direct numeric route records. -/
abbrev DirectSourceRouteDescriptorTokenCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List PeriodicCNF.UnaryProgramTokens.Token)
    encoding.Γ PeriodicCNF.UnaryProgramTokens.Token
    id id (directSourceRouteDescriptorTokens decider)

end LeanTrominoes.PeriodicCNFStripReduction
