/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMProbeGeometry

/-! # Checked allocation and pointer setup for one fresh decoder call -/
namespace LeanTrominoes.Domino.WordRAM.Binary.FreshProbe
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
abbrev Code := Structured.Code 128

def reserved (data : Data) (slots : ℕ) : Data :=
  Reserve.saved ((Reserve.prepared data (slots+3)).allocated (data.1 Reserve.frontier) ((slots+3)*data.1 Reserve.precision))
def prepared (data : Data) (output slots : ℕ) : Data :=
  ProbeHeaders.state (reserved data slots) output slots
def prepareProgram (output slots : ℕ) : Code :=
  .seq (Reserve.program (slots+3)) (ProbeHeaders.program output slots)

theorem prepare_exec {w : ℕ} (data : Data) (output slots : ℕ)
    (factorFits : Fits w (slots+3 : ℕ)) (requestFits : Fits w ((slots+3)*data.1 Reserve.precision : ℕ))
    (endpointFits : Fits w (data.1 Reserve.frontier+(slots+3)*data.1 Reserve.precision : ℕ)) (unit : Fits w (1:ℕ))
    (values : ∀ pair∈ProbeHeaders.moves, Fits w ((reserved data slots).1 pair.2)) (four : Fits w (4:ℕ))
    (indices : ∀ slot∈[output,slots,slots+1,slots+2], Fits w slot)
    (products : ∀ slot∈[output,slots,slots+1,slots+2], Fits w (slot*(reserved data slots).1 Reserve.precision : ℕ))
    (addresses : ∀ slot∈[output,slots,slots+1,slots+2], Fits w ((reserved data slots).1 Reserve.base+slot*(reserved data slots).1 Reserve.precision : ℕ)) :
    NaturalData.Exec w (prepareProgram output slots) data (prepared data output slots)
      (4*((slots+3)*data.1 Reserve.precision)+34) := by
  obtain ⟨result,run,front,base,memory,registers,equal⟩ := Reserve.program_exec data (slots+3) factorFits requestFits endpointFits unit
  change result=reserved data slots at equal
  subst result
  have header := ProbeHeaders.program_exec (reserved data slots) output slots values four indices products addresses
  have full : NaturalData.Exec w (prepareProgram output slots) data (prepared data output slots)
      ((4*((slots+3)*data.1 Reserve.precision)+12)+22) := run.seq header
  convert full using 1 <;> omega

theorem prepared_memory (data : Data) (output slots : ℕ) :
    (prepared data output slots).2=NaturalData.clear data.2 (data.1 Reserve.frontier) ((slots+3)*data.1 Reserve.precision) := rfl

theorem reserved_reg (data : Data) (slots : ℕ) (i : Fin 128) (high : 7≤ i.val)
    (notFront : i≠Reserve.frontier) (notBase : i≠Reserve.base) :
    (reserved data slots).1 i=data.1 i := by
  have ne (j : Fin 128) (small : j.val<7) : i≠j := by intro eq; have := congrArg Fin.val eq; omega
  simp only [reserved,Reserve.saved,NaturalData.set,Function.update_of_ne notBase,Function.update_of_ne notFront,
    NaturalData.allocated,NaturalData.allocatedRegisters]
  rw [if_neg (ne (Allocation.frontier 122) (by decide)),if_neg (ne (Allocation.count 122) (by decide)),
    if_neg (ne (Allocation.result 122) (by decide)),if_neg (ne (Allocation.cursor 122) (by decide)),
    if_neg (ne (Allocation.zero 122) (by decide)),if_neg (ne (Allocation.one 122) (by decide))]
  simp only [Reserve.prepared,NaturalData.set,Function.update_of_ne (ne (Allocation.frontier 122) (by decide)),
    Function.update_of_ne (ne (Allocation.count 122) (by decide)),Function.update_of_ne (ne Reserve.factorRegister (by decide))]

theorem reserved_base (data : Data) (slots : ℕ) : (reserved data slots).1 Reserve.base=data.1 Reserve.frontier := by
  simp [reserved,Reserve.saved,Reserve.prepared,NaturalData.set,NaturalData.allocated,NaturalData.allocatedRegisters,
    Reserve.base,Reserve.frontier,Allocation.result,Allocation.frontier,Allocation.count]

theorem reserved_frontier (data : Data) (slots : ℕ) :
    (reserved data slots).1 Reserve.frontier=data.1 Reserve.frontier+(slots+3)*data.1 Reserve.precision := by
  simp [reserved,Reserve.saved,Reserve.prepared,NaturalData.set,NaturalData.allocated,NaturalData.allocatedRegisters,
    Reserve.base,Reserve.frontier,Allocation.result,Allocation.frontier,Allocation.count]

theorem prepared_caller (data : Data) (output slots : ℕ) (i : Fin 128) (high : 64≤ i.val)
    (notFront : i≠Reserve.frontier) (notBase : i≠Reserve.base) :
    (prepared data output slots).1 i=data.1 i := by
  rw [prepared,ProbeHeaders.state_high _ _ _ _ high]
  exact reserved_reg data slots i (by omega) notFront notBase

end LeanTrominoes.Domino.WordRAM.Binary.FreshProbe
