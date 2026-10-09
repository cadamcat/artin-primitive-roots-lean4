import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.LabelBessel
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.LabelParseval

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII MeasureTheory

noncomputable section

/-- A uniform minor-fibre estimate transfers to the finite product-label kernel. -/
theorem minor_label_matrix_bound {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (U : Finset ℤ) (D : ι → ι → ℝ)
    (ψ : ℝ → ℝ) (Y r : ℝ) (hr : 0 ≤ r)
    (P : Set ℝ) (hP : MeasurableSet P)
    (hfibre : ∀ θ ∈ Set.Icc (0 : ℝ) 1 ∩ P, ∀ g : ι → ℂ,
      (∑ i ∈ I, ‖∑ j ∈ I,
        (ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*g j‖^2) ≤
      r^2*(∑ j ∈ I, ‖g j‖^2))
    (f : ι × ℤ → ℂ) :
    (∑ v ∈ I.product U, ‖∑ w ∈ I.product U,
      ((ψ (D v.1 w.1/Y) : ℂ)*
        (∫ θ in (0 : ℝ)..1, if θ ∈ P then
          additiveCharacter (θ*(D v.1 w.1-(v.2 : ℝ)+(w.2 : ℝ))) else 0))*
        f w‖^2) ≤ r^2*(∑ w ∈ I.product U, ‖f w‖^2) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hcharNorm (x : ℝ) : ‖additiveCharacter x‖ = 1 := by
    unfold additiveCharacter
    rw [Complex.norm_exp]
    simp
  have hcharAdd (x y : ℝ) :
      additiveCharacter (x+y) = additiveCharacter x*additiveCharacter y := by
    unfold additiveCharacter
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  let F := fun (j : ι) (θ : ℝ) => ∑ a ∈ U, additiveCharacter ((a : ℝ)*θ)*f (j,a)
  let B := fun (i : ι) (θ : ℝ) => ∑ j ∈ I,
    (ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*F j θ
  let G := fun (i : ι) => P.indicator (B i)
  have hFcont (j : ι) : Continuous (F j) := by
    dsimp only [F]
    unfold additiveCharacter
    fun_prop
  have hBcont (i : ι) : Continuous (B i) := by
    dsimp only [B, F]
    unfold additiveCharacter
    fun_prop
  have hFbound (j : ι) (θ : ℝ) : ‖F j θ‖ ≤ ∑ a ∈ U, ‖f (j,a)‖ := by
    calc
      _ ≤ ∑ a ∈ U, ‖additiveCharacter ((a : ℝ)*θ)*f (j,a)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, hcharNorm, one_mul]
  let C := fun i => ∑ j ∈ I, ‖(ψ (D i j/Y) : ℂ)‖*(∑ a ∈ U, ‖f (j,a)‖)
  have hC (i : ι) : 0 ≤ C i := by dsimp only [C]; positivity
  have hBbound (i : ι) (θ : ℝ) : ‖B i θ‖ ≤ C i := by
    calc
      _ ≤ ∑ j ∈ I, ‖(ψ (D i j/Y) : ℂ)*additiveCharacter (θ*D i j)*F j θ‖ :=
        norm_sum_le _ _
      _ = ∑ j ∈ I, ‖(ψ (D i j/Y) : ℂ)‖*‖F j θ‖ := by
        simp only [norm_mul, hcharNorm, mul_one]
      _ ≤ C i := Finset.sum_le_sum (fun j hj =>
        mul_le_mul_of_nonneg_left (hFbound j θ) (norm_nonneg _))
  have hGbound (i : ι) (θ : ℝ) : ‖G i θ‖ ≤ C i := by
    by_cases hθ : θ ∈ P
    · simpa only [G, Set.indicator_of_mem hθ] using hBbound i θ
    · simpa only [G, Set.indicator_of_notMem hθ, norm_zero] using hC i
  have hGmem (i : ι) : MemLp (G i) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound ((hBcont i).aestronglyMeasurable.indicator hP) (C i)
      (Filter.Eventually.of_forall (hGbound i))
  have hGint (i : ι) : IntervalIntegrable (fun θ => ‖G i θ‖^2) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mpr
    exact (memLp_two_iff_integrable_sq_norm (hGmem i).aestronglyMeasurable).mp (hGmem i)
  have hFint (j : ι) : IntervalIntegrable (fun θ => ‖F j θ‖^2) volume 0 1 :=
    ((hFcont j).norm.pow 2).intervalIntegrable 0 1
  have hpoint (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
      (∑ i ∈ I, ‖G i θ‖^2) ≤ r^2*(∑ j ∈ I, ‖F j θ‖^2) := by
    by_cases hθP : θ ∈ P
    · simpa only [G, Set.indicator_of_mem hθP, B] using hfibre θ ⟨hθ, hθP⟩ (fun j => F j θ)
    · simp only [G, Set.indicator_of_notMem hθP, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        Finset.sum_const_zero]
      positivity
  have houtput (i : ι) (b : ℤ) :
      (∑ j ∈ I, ∑ a ∈ U,
        ((ψ (D i j/Y) : ℂ)*(∫ θ in (0 : ℝ)..1, if θ ∈ P then
          additiveCharacter (θ*(D i j-(b : ℝ)+(a : ℝ))) else 0))*f (j,a)) =
        ∫ θ in (0 : ℝ)..1, additiveCharacter (-(b : ℝ)*θ)*G i θ := by
    let E := fun (j : ι) (a : ℤ) => P.indicator (fun θ : ℝ =>
      additiveCharacter (θ*(D i j-(b : ℝ)+(a : ℝ))))
    have hEint (j : ι) (a : ℤ) : IntervalIntegrable (E j a) volume 0 1 := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mpr
      have hc : Continuous (fun θ : ℝ => additiveCharacter (θ*(D i j-(b : ℝ)+(a : ℝ)))) := by
        unfold additiveCharacter
        fun_prop
      exact (hc.intervalIntegrable 0 1).1.indicator hP
    have heq (θ : ℝ) : additiveCharacter (-(b : ℝ)*θ)*G i θ =
        ∑ j ∈ I, ∑ a ∈ U, ((ψ (D i j/Y) : ℂ)*f (j,a))*E j a θ := by
      by_cases hθ : θ ∈ P
      · simp only [G, E, Set.indicator_of_mem hθ]
        dsimp only [B, F]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro a ha
        have hprod : additiveCharacter (-(b : ℝ)*θ)*additiveCharacter (θ*D i j)*
            additiveCharacter ((a : ℝ)*θ) = additiveCharacter (θ*(D i j-(b : ℝ)+(a : ℝ))) := by
          rw [← hcharAdd, ← hcharAdd]
          congr 1
          ring
        calc
          _ = ((ψ (D i j/Y) : ℂ)*f (j,a))*(additiveCharacter (-(b : ℝ)*θ)*
              additiveCharacter (θ*D i j)*additiveCharacter ((a : ℝ)*θ)) := by ring
          _ = _ := by rw [hprod]
      · simp only [G, E, Set.indicator_of_notMem hθ, mul_zero, Finset.sum_const_zero]
    have hterm (j : ι) (a : ℤ) :
        IntervalIntegrable (fun θ => ((ψ (D i j/Y) : ℂ)*f (j,a))*E j a θ) volume 0 1 :=
      (hEint j a).const_mul _
    have hterms (j : ι) : IntervalIntegrable (fun θ =>
        ∑ a ∈ U, ((ψ (D i j/Y) : ℂ)*f (j,a))*E j a θ) volume 0 1 := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum U (fun a ha => hterm j a)
    rw [intervalIntegral.integral_congr (fun θ hθ => heq θ)]
    rw [intervalIntegral.integral_finsetSum (fun j hj => hterms j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_finsetSum (fun a ha => hterm j a)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [intervalIntegral.integral_const_mul]
    have hEeq : E j a = fun θ : ℝ => if θ ∈ P then
        additiveCharacter (θ*(D i j-(b : ℝ)+(a : ℝ))) else 0 := rfl
    rw [hEeq]
    ring
  have hrow (i : ι) :
      (∑ b ∈ U, ‖∑ j ∈ I, ∑ a ∈ U,
        ((ψ (D i j/Y) : ℂ)*(∫ θ in (0 : ℝ)..1, if θ ∈ P then
          additiveCharacter (θ*(D i j-(b : ℝ)+(a : ℝ))) else 0))*f (j,a)‖^2) ≤
        ∫ θ in (0 : ℝ)..1, ‖G i θ‖^2 := by
    simpa only [houtput] using finite_label_bessel_bound U (G i) (hGmem i)
  have hGsInt : IntervalIntegrable (fun θ => ∑ i ∈ I, ‖G i θ‖^2) volume 0 1 := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum I (fun i hi => hGint i)
  have hFsInt : IntervalIntegrable (fun θ => r^2*(∑ j ∈ I, ‖F j θ‖^2)) volume 0 1 := by
    have h : IntervalIntegrable (fun θ => ∑ j ∈ I, ‖F j θ‖^2) volume 0 1 := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum I (fun j hj => hFint j)
    exact h.const_mul (r^2)
  change (∑ v ∈ I ×ˢ U, ‖∑ w ∈ I ×ˢ U,
    ((ψ (D v.1 w.1/Y) : ℂ)*
      (∫ θ in (0 : ℝ)..1, if θ ∈ P then
        additiveCharacter (θ*(D v.1 w.1-(v.2 : ℝ)+(w.2 : ℝ))) else 0))*f w‖^2) ≤
    r^2*(∑ w ∈ I ×ˢ U, ‖f w‖^2)
  simp only [Finset.sum_product]
  calc
    _ ≤ ∑ i ∈ I, ∫ θ in (0 : ℝ)..1, ‖G i θ‖^2 :=
      Finset.sum_le_sum (fun i hi => hrow i)
    _ = ∫ θ in (0 : ℝ)..1, ∑ i ∈ I, ‖G i θ‖^2 :=
      (intervalIntegral.integral_finsetSum (fun i hi => hGint i)).symm
    _ ≤ ∫ θ in (0 : ℝ)..1, r^2*(∑ j ∈ I, ‖F j θ‖^2) :=
      intervalIntegral.integral_mono_on h01 hGsInt hFsInt hpoint
    _ = r^2*(∑ j ∈ I, ∫ θ in (0 : ℝ)..1, ‖F j θ‖^2) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun j hj => hFint j)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact finite_label_parseval U (fun a => f (j,a))

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
