/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMLayout
import LeanTrominoes.Computation.RAM.NaturalSemantics

/-! # Natural-state execution certificates for the original RAM instructions

This relation is a proof view of the existing primitive instructions. It
requires every written natural value and every dereferenced address to be at
most a fixed bound, and requires subtraction not to underflow. Its refinement
theorem supplies all signed-word and address checks of the actual RAM.
-/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM


theorem native_read {bound : Nat} (data : Data) (base index dst : Fin 64)
    (address : data.1 base+data.1 index≤bound)
    (value : data.2 (data.1 base+data.1 index)≤bound) :
    Natural.Exec bound (read base index dst) data (readState data base index dst) 2 := by
  have first := Natural.Exec.atom (Natural.Step.add data Reg.scratch base index address)
  have second := Natural.Exec.atom (Natural.Step.load
    (data.set Reg.scratch (data.1 base+data.1 index)) dst Reg.scratch
    (by simpa [NaturalData.set] using address) (by simpa [NaturalData.set] using value))
  simpa [read,Allocation.readProgram,readState,NaturalData.set] using first.seq second

theorem native_write {bound : Nat} (data : Data) (base index value : Fin 64)
    (different : value≠Reg.scratch) (address : data.1 base+data.1 index≤bound) (word : data.1 value≤bound) :
    Natural.Exec bound (write base index value) data (writeState data base index value) 2 := by
  have first := Natural.Exec.atom (Natural.Step.add data Reg.scratch base index address)
  have second := Natural.Exec.atom (Natural.Step.store
    (data.set Reg.scratch (data.1 base+data.1 index)) Reg.scratch value
    (by simpa [NaturalData.set] using address) (by simpa [NaturalData.set,different] using word))
  simpa [write,Allocation.writeProgram,writeState,NaturalData.set,NaturalData.store,different] using first.seq second

end LeanTrominoes.BipartiteMatching.DenseWordRAM
