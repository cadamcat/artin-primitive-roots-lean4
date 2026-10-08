import ArtinPrimitiveRoots.TypeII.PD.Memory
set_option autoImplicit false
open Classical MeasureTheory
namespace ArtinPrimitiveRoots.TypeII.PD

private theorem sum_fin_function_prod_local {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (w : α → ℝ) :
    (∑ g : Fin n → α, ∏ i : Fin n, w (g i)) = (∑ a : α, w a) ^ n := by
  classical
  rw [← Fintype.piFinset_univ]
  calc
    _ = ∏ i : Fin n, ∑ a : α, w a := by
      simpa using (Finset.prod_univ_sum (fun _ : Fin n => Finset.univ)
        (fun _ a => w a)).symm
    _ = _ := by simp [Finset.prod_const]

private theorem ghost_group_batch_summable_check {K : ℕ} (F : PDFix K)
    (i : Fin K) {x : ℝ} (c : ℝ) :
    Summable (fun l : ℕ =>
      ∑ batch : Fin l → {p // p ∈ primeBand x (F.a i)},
        c ^ l / (l.factorial : ℝ) *
          ∏ k : Fin l, memoryNu x K F.a F.q_d i (batch k).1) := by
  classical
  let P := primeBand x (F.a i)
  let α := {p // p ∈ P}
  letI : Fintype α := Fintype.ofFinset P (by intro p; simp [P])
  let ν : α → ℝ := fun p => memoryNu x K F.a F.q_d i p.1
  let s : ℝ := ∑ p : α, ν p
  have hinner (l : ℕ) :
      (∑ batch : Fin l → α,
        c ^ l / (l.factorial : ℝ) * ∏ k : Fin l, ν (batch k)) =
        (c * s) ^ l / (l.factorial : ℝ) := by
    calc
      _ = c ^ l / (l.factorial : ℝ) *
            ∑ batch : Fin l → α, ∏ k : Fin l, ν (batch k) := by
              rw [← Finset.mul_sum]
      _ = c ^ l / (l.factorial : ℝ) * s ^ l := by
              rw [sum_fin_function_prod_local]
      _ = (c * s) ^ l / (l.factorial : ℝ) := by
              calc
                c ^ l / (l.factorial : ℝ) * s ^ l =
                    (c ^ l * s ^ l) / (l.factorial : ℝ) := by ring
                _ = (c * s) ^ l / (l.factorial : ℝ) := by rw [← mul_pow]
  have hs : Summable (fun l : ℕ => (c * s) ^ l / (l.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp (c * s)).summable
  have heq :
      (fun l : ℕ =>
        ∑ batch : Fin l → {p // p ∈ primeBand x (F.a i)},
          c ^ l / (l.factorial : ℝ) *
            ∏ k : Fin l, memoryNu x K F.a F.q_d i (batch k).1) =
        fun l : ℕ => (c * s) ^ l / (l.factorial : ℝ) := by
    funext l
    simpa [P, α, ν, s] using hinner l
  exact heq ▸ hs
end ArtinPrimitiveRoots.TypeII.PD
