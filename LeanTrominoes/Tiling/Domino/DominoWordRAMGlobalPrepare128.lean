/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareCall

/-! # Global determinant preparation from the original binary input

The header is separately exposed so the complete solver can handle the empty
representative set before allocating any determinant workspace.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

noncomputable def afterHeader (d : Nat) : Code := .seq (Reserve.program (factor d)) <|
  .seq (prepareSources d) <| .seq ((SourceLoad.completeProgram d).embed 64) (determinantCall d)
noncomputable def program (d : Nat) : Code := .seq header (afterHeader d)
noncomputable def costBound {n d : Nat} (B : BasisData n d) : Nat :=
  4*(factor d*WordRAM.precision B)+(7*WordRAM.precision B+11)*(d*d+2*d)+determinantCost B+71

theorem afterHeader_exec {n d w : Nat} (B : BasisData n d) (positive : 0<n) (nonzero : B.basis.det≠0)
    (width : Fits w (resourceBound B)) :
    ∃ result cost, NaturalData.Exec w (afterHeader d) (headerState (WordRAM.initialData 128 B)) result cost ∧
      cost≤costBound B ∧ Candidate.Frame B ⟨0,positive⟩ ⟨0,positive⟩ result ∧
      result.1 H.n=n ∧ result.1 H.frontier=endAddress B := by
  have reserved := (reserve_exec B width).2
  obtain ⟨sources,sourcesRun,sourcesReady⟩ := prepareSources_exec B (reservedData B) reserved width
  obtain ⟨loaded,loadCost,loadRun,loadBudget,known,frame,fixed⟩ := load_exec B positive sources sourcesReady width
  have ready := loaded_ready B positive sourcesReady known frame fixed
  obtain ⟨result,detCost,detRun,detBudget,correct,nEq,frontierEq⟩ := determinantCall_exec B positive nonzero loaded ready width
  refine ⟨result,_,(reserve_after_header_exec B width).seq (sourcesRun.seq (loadRun.seq detRun)),?_,correct,nEq,frontierEq⟩
  unfold costBound
  omega

theorem program_exec {n d w : Nat} (B : BasisData n d) (positive : 0<n) (nonzero : B.basis.det≠0)
    (width : Fits w (resourceBound B)) :
    ∃ result cost, NaturalData.Exec w (program d) (WordRAM.initialData 128 B) result cost ∧
      cost≤8+costBound B ∧ Candidate.Frame B ⟨0,positive⟩ ⟨0,positive⟩ result ∧
      result.1 H.n=n ∧ result.1 H.frontier=endAddress B := by
  obtain ⟨result,cost,run,budget,correct,nEq,frontierEq⟩ := afterHeader_exec B positive nonzero width
  exact ⟨result,8+cost,(header_exec B width).seq run,Nat.add_le_add_left budget 8,correct,nEq,frontierEq⟩

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
