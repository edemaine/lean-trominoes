/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMPackingBoundary
import LeanTrominoes.Tiling.Domino.DominoWordRAMEmptyBranch
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMPackProgram

/-! # Polynomial-time bounded-word RAM for periodic domino tiling

At every fixed dimension one fixed program reads the original binary period
matrix and representative coordinates, computes the determinant and candidate
neighbors using bounded binary arithmetic, writes the entire padded parity
cover, packs its endpoint arrays, and runs the actual matching program.
All allocation, copying, arithmetic, loop, clearing and halt instructions are
counted. The word size is a constant multiple of the logarithm of input size.
-/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM Binary
variable {n d : ℕ}

noncomputable def positiveProgram (d : ℕ) : Structured.Code 128 :=
  .seq (graphProgram d) (BipartiteMatching.PackWordRAM.program d)

noncomputable def program (d : ℕ) : Structured.Code 128 :=
  headerWrap (positiveProgram d) BipartiteMatching.PackWordRAM.output

abbrev output : Fin 128 := BipartiteMatching.PackWordRAM.output

noncomputable def positiveBound (B : BasisData n d) : ℕ :=
  GlobalPrepare128.costBound B+17+FinalBounds.scanCost n d (precision B)+18*SizeBounds.edgeCount n d+75+
    (4*(4*(BipartiteMatching.DenseWordRAM.size (SizeBounds.matchingInput B)+2)^8)+70+
      1000*(BipartiteMatching.DenseWordRAM.size (SizeBounds.matchingInput B)+1)^4)

 theorem coldCapacity_eq (B : BasisData n d) :
    BipartiteMatching.PackWordRAM.coldCapacity (SizeBounds.matchingInput B).1 (SizeBounds.matchingInput B).2.2.length=
      4*(BipartiteMatching.DenseWordRAM.size (SizeBounds.matchingInput B)+2)^8 := by
  unfold BipartiteMatching.PackWordRAM.coldCapacity BipartiteMatching.DenseWordRAM.size SizeBounds.matchingInput
  dsimp only
  congr 2
  omega

 theorem positiveProgram_exec {w : ℕ} (B : BasisData n d) (valid : B.Valid) (positive : 0<n)
    (prepareWord : Fits w (GlobalPrepare128.resourceBound B))
    (operationWord : Fits w (SizeBounds.operationBound B : ℕ))
    (arenaWord : Fits w (4*(BipartiteMatching.DenseWordRAM.size (SizeBounds.matchingInput B)+2)^8 : ℕ))
    (matchingWidth : BipartiteMatching.DenseWordRAM.callWidth (SizeBounds.matchingInput B)≤w) :
    ∃ result : Data 128, ∃ steps,
      Structured.Exec w (positiveProgram d) (GlobalPrepare128.headerState (initialData 128 B)).word result steps ∧
      steps≤positiveBound B ∧ Fits w (result.1 output) ∧ (result.1 output=0 ∨ result.1 output=1) ∧
      (result.1 output=1 ↔ Tileable (B.chart valid).region) := by
  obtain ⟨generated,graphCost,graphRun,graphBound,state⟩ := graphProgram_exec B positive valid.1 prepareWord operationWord
  have arrays := generated_arrays B generated state
  have valuesFit := generated_values_fit B generated state operationWord
  have sourceFit : Fits w (GlobalPrepare128.endAddress B+2*(PaddedGraph.edges B).length : ℕ) := by
    apply Allocation.nat_fits_le operationWord
    rw [←edgeCount_edges B]
    exact (Driver.initial_tables_bound B).trans (Driver.heap_le_operation B)
  have phaseFit : Fits w (2^d : ℕ) := Allocation.nat_fits_le operationWord (Driver.graphResources B).capacity
  obtain ⟨result,packCost,packRun,packBound,fits,boolean,correct⟩ := BipartiteMatching.PackWordRAM.program_exec
    (n:=n) (d:=d) (SizeBounds.matchingInput B) generated.word rfl rfl
    (by exact congrArg Int.ofNat state.vertices)
    (by exact congrArg Int.ofNat state.left)
    (by simpa only [edgeCount_edges B,SizeBounds.matchingInput,NaturalData.word,Int.ofNat_eq_natCast,Nat.cast_add] using congrArg Int.ofNat state.right)
    (by simpa only [edgeCount_edges B,SizeBounds.matchingInput,NaturalData.word,Int.ofNat_eq_natCast] using congrArg Int.ofNat state.count)
    (Driver.initial_base_four B) sourceFit
    (by rw [coldCapacity_eq]; exact arenaWord) phaseFit arrays.1 arrays.2 valuesFit.1 valuesFit.2 matchingWidth
  refine ⟨result,graphCost+packCost,graphRun.seq packRun,?_,fits,boolean,?_⟩
  · rw [coldCapacity_eq] at packBound
    have subtract := Nat.sub_le
      (4*(BipartiteMatching.DenseWordRAM.size (SizeBounds.matchingInput B)+2)^8)
      (4+2*(SizeBounds.matchingInput B).2.2.length)
    have edgeLength : (SizeBounds.matchingInput B).2.2.length=SizeBounds.edgeCount n d := PaddedGraph.edges_length B
    rw [edgeLength] at packBound
    unfold positiveBound
    omega
  · exact correct.trans (PaddedGraph.matching_iff_tileable B valid)

 theorem program_verified (input : Input d) (w : ℕ)
    (width : FinalBounds.wordCoefficient d*Nat.log2 (inputSize input+2)+2≤w) :
    ∃ result : Data 128, ∃ steps,
      Structured.Exec w (program d) (initial (r:=128) (encode input)).data result steps ∧
      steps+1≤FinalBounds.totalCost input.2.val ∧ Fits w (result.1 output) ∧
      (result.1 output=0 ∨ result.1 output=1) ∧ (result.1 output=1 ↔ predicate input) := by
  obtain ⟨prepareWord,operationWord,arenaWord,matchingWidth⟩ := FinalBounds.word_bounds input.2.val w width
  have unitWord : Fits w 1 := Allocation.nat_fits_le (a:=1) operationWord
    (by have := (Driver.graphResources input.2.val).small; omega)
  obtain ⟨result,steps,run,time,fits,boolean,correct⟩ := headerWrap_exec input.2.val input.2.property
    (positiveProgram d) output prepareWord unitWord
    (fun positive => positiveProgram_exec input.2.val input.2.property positive prepareWord operationWord arenaWord matchingWidth)
  refine ⟨result,steps,run,time.trans ?_,fits,boolean,correct⟩
  unfold positiveBound FinalBounds.totalCost
  omega

/-- A genuine polynomial-time word-RAM algorithm on the original binary
presentation, for each fixed dimension and every sufficient word size. -/
theorem polynomialTime (d : ℕ) : PolynomialTime (encode (d:=d)) inputSize predicate := by
  let k := FinalBounds.wordCoefficient d+Nat.log2 ((program d).size+1)
  refine ⟨FinalBounds.timeFactor d,16,k,?_⟩
  apply Structured.decidesWithin (program d) output encode predicate
  intro input w width inputFits
  have resourceWidth : FinalBounds.wordCoefficient d*Nat.log2 (inputSize input+2)+2≤w :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right _
      (Nat.le_add_right (FinalBounds.wordCoefficient d) (Nat.log2 ((program d).size+1)))) 2).trans width
  obtain ⟨result,steps,run,time,fits,boolean,correct⟩ := program_verified input w resourceWidth
  have pcWidth : (Nat.log2 ((program d).size+1)+2*0)*Nat.log2 (inputSize input+2)+2≤w := by
    simpa only [Nat.mul_zero,Nat.add_zero] using
      (Nat.add_le_add_right (Nat.mul_le_mul_right _
        (Nat.le_add_left (Nat.log2 ((program d).size+1)) (FinalBounds.wordCoefficient d))) 2).trans width
  have pcWord : Fits w ((program d).size : ℕ) := WordBounds.polynomial_fits_uniform
    (program d).size 0 (inputSize input) w (program d).size pcWidth
    (by simp only [Int.natAbs_natCast,pow_zero,Nat.mul_one]; exact Nat.le_refl _)
  have pc : (program d).size<2^w := Int.ofNat_lt.mp (Allocation.nat_address pcWord)
  refine ⟨pc,result,steps,run,time.trans ?_,fits,boolean,correct⟩
  exact FinalBounds.total_bound input.2.val

end LeanTrominoes.Domino.WordRAM
