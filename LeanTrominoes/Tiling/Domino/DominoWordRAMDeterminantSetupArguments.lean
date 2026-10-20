/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantSetupProgram

/-! # Checked argument setup for determinant binary routines -/
namespace LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
open ComplexityAbstract.RAM

attribute [local simp] Reg.length Reg.first Reg.second Reg.output Reg.carry
  Circuit.baseRegister Circuit.low low circuitReg
  G.precision G.circuit G.zero G.absolute G.twice G.signed NaturalData.set

theorem embed_preserves {r s : Nat} (code : Structured.Code r) (i : Fin (r+s))
    (high : r≤ i.val) : (code.embed s).PreservesRegister i := by
  induction code with
  | atom op =>
    cases op <;> simp only [Structured.Code.embed,Structured.Primitive.embed,
      Structured.Code.PreservesRegister,Structured.Primitive.PreservesRegister]
    all_goals intro same; have equal := congrArg Fin.val same; simp only [Fin.val_castAdd] at equal; omega
  | seq a b ihA ihB => exact ⟨ihA,ihB⟩
  | branch c a b ihA ihB => exact ⟨ihA,ihB⟩
  | loop c a ih => exact ih

def PreservesHeaders (code : Code) : Prop := ∀ i : Fin 64, 40≤ i.val → i.val≤60 → code.PreservesRegister i

private theorem assignments_preserves (finish anchor : Fin 64) (moves : List (Fin 64 × Fin 64))
    (i : Fin 64) (last : i≠finish) (others : ∀ p∈moves, i≠p.1) :
    (Assignments.code finish anchor moves).PreservesRegister i := by
  induction moves with
  | nil => exact last
  | cons p rest ih => exact ⟨others p List.mem_cons_self,ih (fun q hq => others q (List.mem_cons_of_mem _ hq))⟩

theorem circuit_preserves (d : Nat) : PreservesHeaders (circuitCode d) := by
  intro i high upper
  constructor
  · apply assignments_preserves
    · intro same; have := congrArg Fin.val same; simp at this; omega
    · intro p hp
      simp only [circuitMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl <;> intro same <;> have eq := congrArg Fin.val same <;> simp at eq <;> omega
  · exact embed_preserves (s:=47) (Circuit.program (compiled d).nodes (arity d)) i (by omega)

theorem absolute_preserves (d : Nat) : PreservesHeaders (absoluteCode d) := by
  intro i high upper
  constructor
  · simp only [pointerCode,Structured.Code.PreservesRegister,Structured.Primitive.PreservesRegister]
    have different : i≠G.signed := by intro same; have := congrArg Fin.val same; simp at this; omega
    exact ⟨different,different,different⟩
  · constructor
    · apply assignments_preserves
      · intro same; have := congrArg Fin.val same; simp at this; omega
      · intro p hp
        simp only [absoluteMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> intro same <;> have eq := congrArg Fin.val same <;> simp at eq <;> omega
    · exact embed_preserves (s:=48) Absolute.program i (by omega)

theorem copy_preserves : PreservesHeaders copyCode := by
  intro i high upper
  constructor
  · apply assignments_preserves
    · intro same; have := congrArg Fin.val same; simp at this; omega
    · intro p hp
      simp only [copyMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl <;> intro same <;> have eq := congrArg Fin.val same <;> simp at eq <;> omega
  · exact embed_preserves (s:=48) copyProgram i (by omega)

theorem shift_preserves : PreservesHeaders shiftCode := by
  intro i high upper
  constructor
  · constructor
    · apply assignments_preserves
      · intro same; have := congrArg Fin.val same; simp at this; omega
      · intro p hp
        simp only [shiftMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl <;> intro same <;> have eq := congrArg Fin.val same <;> simp at eq <;> omega
    · intro same; have := congrArg Fin.val same; simp at this; omega
  · exact embed_preserves (s:=48) shiftProgram i (by omega)

theorem Controls.after {d w cost : Nat} {g : Geometry d} {code : Code} {before after : Data}
    (h : Controls g before) (run : NaturalData.Exec w code before after cost) (preserves : PreservesHeaders code) : Controls g after := by
  have same (i : Fin 64) (high : 40≤ i.val) (upper : i.val≤60) : after.1 i=before.1 i := by
    have equal := run.register_eq (preserves i high upper)
    simpa only [NaturalData.word,Int.natCast_inj] using equal
  constructor
  · rw [same _ (by decide) (by decide)]; exact h.precision
  · rw [same _ (by decide) (by decide)]; exact h.circuit
  · rw [same _ (by decide) (by decide)]; exact h.zero
  · rw [same _ (by decide) (by decide)]; exact h.absolute
  · rw [same _ (by decide) (by decide)]; exact h.twice

theorem circuitSetup_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w) (h : Controls g data) :
    NaturalData.Exec w circuitSetup data (circuitPrepared data) 3 := by
  apply Assignments.exec data (low Reg.length) G.precision circuitMoves (h.precision ▸ width.precision)
  · intro p hp
    simp only [circuitMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact h.circuit ▸ width.base
    · exact h.precision ▸ width.precision
  · simp [circuitMoves]
  · simp [circuitMoves]

theorem circuitPrepared_controls {d : Nat} (g : Geometry d) (data : Data) (h : Controls g data) :
    (circuitPrepared data).1 (circuitReg Circuit.baseRegister)=g.base ∧
    (circuitPrepared data).1 (low Reg.length)=g.precision := by
  simp [circuitPrepared,Assignments.state,circuitMoves,h.precision,h.circuit]

end LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
