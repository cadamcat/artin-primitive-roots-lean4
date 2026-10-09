import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.LabelIntegral

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD MeasureTheory

noncomputable section

/-- The raw Kronecker kernel minus its major contribution is the minor integral. -/
theorem signed_kernel_minor_integral (x Y A : ℝ) (t : ℤ) (aa bb : ℕ) (ψ : ℝ → ℝ) :
    (if t = (bb : ℤ)-aa then (ψ ((t : ℝ)/Y) : ℂ) else 0) -
      majorKernel x Y A (t : ℝ) aa bb ψ =
    (ψ ((t : ℝ)/Y) : ℂ)*
      (∫ θ in (0 : ℝ)..1, if ¬ majorArc x Y A θ then
        additiveCharacter (θ*((t : ℝ)-(bb : ℝ)+(aa : ℝ))) else 0) := by
  let P : Set ℝ := {θ | majorArc x Y A θ}
  let e := fun θ : ℝ => additiveCharacter (θ*((t : ℝ)-(bb : ℝ)+(aa : ℝ)))
  let n : ℤ := t-(bb : ℤ)+(aa : ℤ)
  have hP : MeasurableSet P := by
    dsimp only [P]
    unfold majorArc
    measurability
  have he : Continuous e := by dsimp only [e]; unfold additiveCharacter; fun_prop
  have heInt : IntervalIntegrable e volume 0 1 := he.intervalIntegrable 0 1
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hmajorInt : IntervalIntegrable (fun θ => if θ ∈ P then e θ else 0) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mpr (heInt.1.indicator hP)
  have hminorInt : IntervalIntegrable (fun θ => if θ ∉ P then e θ else 0) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mpr
    have hcomp : Pᶜ.indicator e = fun θ => if θ ∉ P then e θ else 0 := by
      funext θ
      by_cases hθ : θ ∈ P <;> simp [hθ]
    rw [← hcomp]
    exact heInt.1.indicator hP.compl
  have hn : n = 0 ↔ t = (bb : ℤ)-aa := by dsimp only [n]; omega
  have heqn : e = fun θ : ℝ => additiveCharacter ((n : ℝ)*θ) := by
    funext θ
    dsimp only [e, n]
    congr 1
    push_cast
    ring
  have hdelta : (if t = (bb : ℤ)-aa then (1 : ℂ) else 0) = ∫ θ in (0 : ℝ)..1, e θ := by
    calc
      _ = if n = 0 then 1 else 0 := by simp only [hn]
      _ = ∫ θ in (0 : ℝ)..1, additiveCharacter ((n : ℝ)*θ) := (integer_character_integral n).symm
      _ = _ := by rw [heqn]
  have hsplit : (∫ θ in (0 : ℝ)..1, e θ) =
      (∫ θ in (0 : ℝ)..1, if θ ∈ P then e θ else 0)+
      (∫ θ in (0 : ℝ)..1, if θ ∉ P then e θ else 0) := by
    calc
      _ = ∫ θ in (0 : ℝ)..1,
          (if θ ∈ P then e θ else 0)+(if θ ∉ P then e θ else 0) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        by_cases hθP : θ ∈ P <;> simp [hθP]
      _ = _ := intervalIntegral.integral_add hmajorInt hminorInt
  have hraw : (if t = (bb : ℤ)-aa then (ψ ((t : ℝ)/Y) : ℂ) else 0) =
      (ψ ((t : ℝ)/Y) : ℂ)*(if t = (bb : ℤ)-aa then 1 else 0) := by
    by_cases ht : t = (bb : ℤ)-aa <;> simp [ht]
  change (if t = (bb : ℤ)-aa then (ψ ((t : ℝ)/Y) : ℂ) else 0)-
    ((ψ ((t : ℝ)/Y) : ℂ)*(∫ θ in (0 : ℝ)..1, if θ ∈ P then e θ else 0)) =
      (ψ ((t : ℝ)/Y) : ℂ)*(∫ θ in (0 : ℝ)..1, if θ ∉ P then e θ else 0)
  rw [hraw, hdelta, hsplit]
  ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
