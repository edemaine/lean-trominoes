/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkGenericUnfolding
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkEqualityTransport
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkStartTransport
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkUnfolding
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkGenericStartTransport

/-! # Generic presentation of direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The direct tagged-link family is the generic final-carrier family of the
direct source formula. -/
theorem directSourceFinalCarrierTaggedLinks_eq_generic
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierTaggedLinks decider symbols =
      @finalCarrierTaggedLinks (ThreeCNFVariable Nat)
        directSourceFinalStructuralBaseDecidableEq
        (directThreeCNFSourceFormula decider symbols) := by
  exact (directSourceFinalCarrierTaggedLinks_unfolded decider symbols).eq.trans
    ((directSourceFinalCarrierTaggedLinks_equalityTransport
      decider symbols).eq.trans
      ((directSourceFinalCarrierTaggedLinks_startTransport
        decider symbols).eq.trans
        ((directSourceFinalCarrierTaggedLinks_genericStartTransport
          decider symbols).eq.trans
          (directSourceFinalCarrierTaggedLinks_generic decider symbols).eq)))

end LeanTrominoes.PeriodicCNFStripReduction

end
