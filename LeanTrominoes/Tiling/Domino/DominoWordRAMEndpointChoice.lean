/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointStore

/-! # The checked active/dummy branch -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

structure ChosenResult (before after : Data) : Prop where
  memory : after.2=before.2
  source : after.1 R.source=if before.1 H.active=0 then before.1 R.dummy else before.1 R.source
  target : after.1 R.target=if before.1 H.active=0 then before.1 R.dummy else before.1 R.target
  fixed : ∀ reg : Fin 128, (reg.val<106 ∨ 111<reg.val) → after.1 reg=before.1 reg

attribute [local simp] H.active R.source R.target R.dummy R.constant R.phase copy NaturalData.set

theorem choose_exec {B : Nat} (data : Data) (zero : data.1 R.phase=0)
    (dummy : data.1 R.dummy≤B) (scratch : data.1 R.constant≤B) :
    ∃ result, Natural.Exec B choose data result 3 ∧ ChosenResult data result := by
  dsimp only [R.dummy,R.constant,R.phase,H.active] at *
  by_cases active : data.1 H.active=0
  · let a := data.set R.source (data.1 R.dummy)
    let result := a.set R.target (data.1 R.dummy)
    have first : Natural.Exec B (copy R.source R.dummy) data a 1 := Natural.Exec.atom (Natural.Step.copy _ _ _ dummy)
    have second : Natural.Exec B (copy R.target R.dummy) a result 1 := by
      simpa [a,result] using Natural.Exec.atom (Natural.Step.copy (bound:=B) a R.target R.dummy (by simpa [a] using dummy))
    have branch := Natural.Exec.branch_yes (no:=copy R.constant R.constant)
      (show Natural.Holds (.eq H.active R.phase) data by simp only [Natural.Holds,active,zero]) (first.seq second)
    refine ⟨result,branch,rfl,?_,?_,?_⟩
    · simp [result,a,active]
    · simp [result,a,active]
    · intro reg outside
      have sourceNe : reg≠R.source := by intro same; have := congrArg Fin.val same; simp only [R.source] at this; omega
      have targetNe : reg≠R.target := by intro same; have := congrArg Fin.val same; simp only [R.target] at this; omega
      simp only [result,a,NaturalData.set,Function.update_of_ne sourceNe,Function.update_of_ne targetNe]
  · have skipped : Natural.Exec B (copy R.constant R.constant) data data 1 := by
      simpa only [copy,NaturalData.set,Function.update_eq_self,Prod.mk.eta] using Natural.Exec.atom (Natural.Step.copy data R.constant R.constant scratch)
    have branch := Natural.Exec.branch_no (yes:=.seq (copy R.source R.dummy) (copy R.target R.dummy))
      (show ¬Natural.Holds (.eq H.active R.phase) data by simpa only [Natural.Holds,zero] using active) skipped
    exact ⟨data,branch,rfl,by simp [active],by simp [active],fun _ _ => rfl⟩

end LeanTrominoes.Domino.WordRAM.EndpointWriter
