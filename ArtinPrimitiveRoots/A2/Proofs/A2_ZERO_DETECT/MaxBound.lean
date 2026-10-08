import ArtinPrimitiveRoots.A2.Proofs.A2_ZERO_DETECT.Sobolev

/-!
# A2-ZERO-DETECT: maximal bound for finite complex Dirichlet polynomials

A finite Dirichlet polynomial `∑ a ∈ B, d a * exp (-(σ + t i) λ a)` is viewed as a function of the
two real variables `σ` and `t`. Under a large-sieve hypothesis for a finite family of coefficient
twists `χ x`, the sum over the family of its squared values at arbitrary points
`σ x ∈ [0, 1]`, `|t x| ≤ T` is bounded by `3 (1 + 4T) S (1 + Λ²)² ∑ ‖c a‖²`. The proof applies the
one-dimensional Sobolev bound in `t` and then in `σ`, and the sieve at each fixed `(σ, t)`.
-/

set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect

/-- A finite Dirichlet polynomial in the real variables `σ` (real part) and `t` (height). -/
def dpoly {α : Type*} (B : Finset α) (d : α → ℂ) (lam : α → ℝ) (σ t : ℝ) : ℂ :=
  ∑ a ∈ B, d a * Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ))

theorem dpoly_hasDerivAt_t {α : Type*} (B : Finset α) (d : α → ℂ) (lam : α → ℝ) (σ t : ℝ) :
    HasDerivAt (fun t => dpoly B d lam σ t)
      (dpoly B (fun a => -(Complex.I * (lam a : ℂ)) * d a) lam σ t) t := by
  unfold dpoly
  have hterm : ∀ a ∈ B, HasDerivAt
      (fun t : ℝ => d a * Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ)))
      (-(Complex.I * (lam a : ℂ)) * d a *
        Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ))) t := by
    intro a _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h2 : HasDerivAt (fun t : ℝ => -((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ))
        (-(1 * Complex.I) * (lam a : ℂ)) t :=
      ((h1.mul_const Complex.I).const_add (σ : ℂ)).neg.mul_const (lam a : ℂ)
    have h3 := (h2.cexp).const_mul (d a)
    convert h3 using 1
    ring
  convert HasDerivAt.sum hterm using 1
  ext t
  simp

theorem dpoly_hasDerivAt_σ {α : Type*} (B : Finset α) (d : α → ℂ) (lam : α → ℝ) (σ t : ℝ) :
    HasDerivAt (fun σ => dpoly B d lam σ t)
      (dpoly B (fun a => -(lam a : ℂ) * d a) lam σ t) σ := by
  unfold dpoly
  have hterm : ∀ a ∈ B, HasDerivAt
      (fun σ : ℝ => d a * Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ)))
      (-(lam a : ℂ) * d a *
        Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ))) σ := by
    intro a _
    have h1 : HasDerivAt (fun σ : ℝ => (σ : ℂ)) 1 σ := by
      simpa using (hasDerivAt_id σ).ofReal_comp
    have h2 : HasDerivAt (fun σ : ℝ => -((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ))
        (-1 * (lam a : ℂ)) σ :=
      (h1.add_const ((t : ℂ) * Complex.I)).neg.mul_const (lam a : ℂ)
    have h3 := (h2.cexp).const_mul (d a)
    convert h3 using 1
    ring
  convert HasDerivAt.sum hterm using 1
  ext σ
  simp

theorem dpoly_continuous_t {α : Type*} (B : Finset α) (d : α → ℂ) (lam : α → ℝ) (σ : ℝ) :
    Continuous fun t => dpoly B d lam σ t :=
  continuous_iff_continuousAt.2 fun t => (dpoly_hasDerivAt_t B d lam σ t).continuousAt

theorem dpoly_continuous_σ {α : Type*} (B : Finset α) (d : α → ℂ) (lam : α → ℝ) (t : ℝ) :
    Continuous fun σ => dpoly B d lam σ t :=
  continuous_iff_continuousAt.2 fun σ => (dpoly_hasDerivAt_σ B d lam σ t).continuousAt

/-- The sieve at one fixed point `(σ, t)` with `σ ≥ 0` and nonnegative frequencies. -/
theorem dpoly_family_sq_le {ι α : Type*} (X : Finset ι) (B : Finset α) (χ : ι → α → ℂ)
    (lam : α → ℝ) (hlam : ∀ a ∈ B, 0 ≤ lam a) {S : ℝ} (hS : 0 ≤ S)
    (hsieve : ∀ b : α → ℂ, ∑ x ∈ X, ‖∑ a ∈ B, b a * χ x a‖ ^ 2 ≤ S * ∑ a ∈ B, ‖b a‖ ^ 2)
    (e : α → ℂ) {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    ∑ x ∈ X, ‖dpoly B (fun a => e a * χ x a) lam σ t‖ ^ 2 ≤ S * ∑ a ∈ B, ‖e a‖ ^ 2 := by
  let b : α → ℂ := fun a => e a * Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ))
  have hrw : ∀ x ∈ X, dpoly B (fun a => e a * χ x a) lam σ t = ∑ a ∈ B, b a * χ x a := by
    intro x _
    unfold dpoly
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [b]
    ring
  rw [Finset.sum_congr rfl fun x hx => by rw [hrw x hx]]
  refine (hsieve b).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hS
  refine Finset.sum_le_sum fun a ha => ?_
  have hexp : ‖Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ)).re = -(σ * lam a) := by
      simp [Complex.mul_re]
    rw [hre]
    have := mul_nonneg hσ (hlam a ha)
    linarith
  have hb : ‖b a‖ ≤ ‖e a‖ := by
    simp only [b, norm_mul]
    calc ‖e a‖ * ‖Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (lam a : ℂ))‖
        ≤ ‖e a‖ * 1 := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = ‖e a‖ := mul_one _
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

/-- The `t`-step: maximal control in the height at a fixed real part `σ ≥ 0`. -/
theorem dpoly_t_step {ι α : Type*} (X : Finset ι) (B : Finset α) (χ : ι → α → ℂ)
    (lam : α → ℝ) (hlam : ∀ a ∈ B, 0 ≤ lam a) {S : ℝ} (hS : 0 ≤ S)
    (hsieve : ∀ b : α → ℂ, ∑ x ∈ X, ‖∑ a ∈ B, b a * χ x a‖ ^ 2 ≤ S * ∑ a ∈ B, ‖b a‖ ^ 2)
    (e : α → ℂ) {σ : ℝ} (hσ : 0 ≤ σ) {T : ℝ} (hT : 0 < T) (γ : ι → ℝ)
    (hγ : ∀ x ∈ X, γ x ∈ Icc (-T) T) :
    ∑ x ∈ X, ‖dpoly B (fun a => e a * χ x a) lam σ (γ x)‖ ^ 2 ≤
      (1 + 2 * T) * (S * ∑ a ∈ B, ‖e a‖ ^ 2) +
        2 * T * (S * ∑ a ∈ B, ‖-(Complex.I * (lam a : ℂ)) * e a‖ ^ 2) := by
  have hderiv : ∀ (x : ι) (t : ℝ), HasDerivAt (fun t => dpoly B (fun a => e a * χ x a) lam σ t)
      (dpoly B (fun a => (-(Complex.I * (lam a : ℂ)) * e a) * χ x a) lam σ t) t := by
    intro x t
    have h := dpoly_hasDerivAt_t B (fun a => e a * χ x a) lam σ t
    convert h using 2
    funext a
    ring
  have hlen : T - -T = 2 * T := by ring
  have := family_sobolev_sum_le X (fun x t => dpoly B (fun a => e a * χ x a) lam σ t)
    (fun x t => dpoly B (fun a => (-(Complex.I * (lam a : ℂ)) * e a) * χ x a) lam σ t)
    (by linarith : -T < T) hderiv (fun x => dpoly_continuous_t B _ lam σ) γ hγ
    (A := S * ∑ a ∈ B, ‖e a‖ ^ 2)
    (A' := S * ∑ a ∈ B, ‖-(Complex.I * (lam a : ℂ)) * e a‖ ^ 2)
    (fun t _ => dpoly_family_sq_le X B χ lam hlam hS hsieve e hσ t)
    (fun t _ => dpoly_family_sq_le X B χ lam hlam hS hsieve _ hσ t)
  rw [hlen] at this
  exact this

/-- **Maximal bound for finite complex Dirichlet polynomials** (A2-ZERO-DETECT). The real parts
`σ x ∈ [0, 1]` and heights `|γ x| ≤ T` vary with the family member. -/
theorem dirichlet_poly_max_bound {ι α : Type*} (X : Finset ι) (B : Finset α) (χ : ι → α → ℂ)
    (c : α → ℂ) (lam : α → ℝ) {Λ T S : ℝ} (hlam : ∀ a ∈ B, 0 ≤ lam a ∧ lam a ≤ Λ)
    (hT : 0 < T) (hS : 0 ≤ S)
    (hsieve : ∀ b : α → ℂ, ∑ x ∈ X, ‖∑ a ∈ B, b a * χ x a‖ ^ 2 ≤ S * ∑ a ∈ B, ‖b a‖ ^ 2)
    (σ γ : ι → ℝ) (hσ : ∀ x ∈ X, σ x ∈ Icc (0 : ℝ) 1) (hγ : ∀ x ∈ X, γ x ∈ Icc (-T) T) :
    ∑ x ∈ X, ‖dpoly B (fun a => c a * χ x a) lam (σ x) (γ x)‖ ^ 2 ≤
      3 * (1 + 4 * T) * S * (1 + Λ ^ 2) ^ 2 * ∑ a ∈ B, ‖c a‖ ^ 2 := by
  have hlam0 : ∀ a ∈ B, 0 ≤ lam a := fun a ha => (hlam a ha).1
  set Q : ℝ := ∑ a ∈ B, ‖c a‖ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun a _ => by positivity
  set R : ℝ := (1 + Λ ^ 2) ^ 2 * Q with hR
  -- coefficient bounds
  have hnI : ∀ a, ‖-(Complex.I * (lam a : ℂ))‖ = |lam a| := by
    intro a
    simp [Complex.norm_real]
  have hnR : ∀ a, ‖-(lam a : ℂ)‖ = |lam a| := by
    intro a
    simp [Complex.norm_real]
  have hsq : ∀ a ∈ B, |lam a| ^ 2 ≤ Λ ^ 2 := by
    intro a ha
    rw [sq_abs]
    exact pow_le_pow_left₀ (hlam a ha).1 (hlam a ha).2 2
  have hΛ0 : ∀ a ∈ B, 0 ≤ Λ := fun a ha => (hlam a ha).1.trans (hlam a ha).2
  have hR1 : Q ≤ R := by
    have : 1 ≤ (1 + Λ ^ 2) ^ 2 := one_le_pow₀ (by nlinarith [sq_nonneg Λ])
    simp only [hR]
    nlinarith
  have hcoef1 : ∀ (w : α → ℂ), (∀ a ∈ B, ‖w a‖ ≤ |lam a|) →
      ∑ a ∈ B, ‖w a * c a‖ ^ 2 ≤ R := by
    intro w hw
    calc ∑ a ∈ B, ‖w a * c a‖ ^ 2 ≤ ∑ a ∈ B, (1 + Λ ^ 2) ^ 2 * ‖c a‖ ^ 2 := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [norm_mul, mul_pow]
          have h1 : ‖w a‖ ^ 2 ≤ |lam a| ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hw a ha) 2
          have h2 : |lam a| ^ 2 ≤ (1 + Λ ^ 2) ^ 2 := by
            nlinarith [hsq a ha, sq_nonneg Λ, sq_nonneg (Λ ^ 2)]
          exact mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
      _ = R := by rw [← Finset.mul_sum]
  have hcoef2 : ∀ (w : α → ℂ), (∀ a ∈ B, ‖w a‖ ≤ |lam a| ^ 2) →
      ∑ a ∈ B, ‖w a * c a‖ ^ 2 ≤ R := by
    intro w hw
    calc ∑ a ∈ B, ‖w a * c a‖ ^ 2 ≤ ∑ a ∈ B, (1 + Λ ^ 2) ^ 2 * ‖c a‖ ^ 2 := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [norm_mul, mul_pow]
          have h1 : ‖w a‖ ^ 2 ≤ (|lam a| ^ 2) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hw a ha) 2
          have h2 : (|lam a| ^ 2) ^ 2 ≤ (1 + Λ ^ 2) ^ 2 := by
            have := hsq a ha
            exact pow_le_pow_left₀ (by positivity) (by linarith) 2
          exact mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
      _ = R := by rw [← Finset.mul_sum]
  -- the `t`-step at every real part in `[0, 1]`
  have hA : ∀ s ∈ Icc (0 : ℝ) 1,
      ∑ x ∈ X, ‖dpoly B (fun a => c a * χ x a) lam s (γ x)‖ ^ 2 ≤ (1 + 4 * T) * (S * R) := by
    intro s hs
    have h := dpoly_t_step X B χ lam hlam0 hS hsieve c hs.1 hT γ hγ
    have h1 : S * Q ≤ S * R := mul_le_mul_of_nonneg_left hR1 hS
    have h2 : S * ∑ a ∈ B, ‖-(Complex.I * (lam a : ℂ)) * c a‖ ^ 2 ≤ S * R :=
      mul_le_mul_of_nonneg_left (hcoef1 _ fun a _ => (hnI a).le) hS
    nlinarith
  have hA' : ∀ s ∈ Icc (0 : ℝ) 1,
      ∑ x ∈ X, ‖dpoly B (fun a => (-(lam a : ℂ) * c a) * χ x a) lam s (γ x)‖ ^ 2 ≤
        (1 + 4 * T) * (S * R) := by
    intro s hs
    have h := dpoly_t_step X B χ lam hlam0 hS hsieve (fun a => -(lam a : ℂ) * c a) hs.1 hT γ hγ
    have h1 : S * ∑ a ∈ B, ‖-(lam a : ℂ) * c a‖ ^ 2 ≤ S * R :=
      mul_le_mul_of_nonneg_left (hcoef1 _ fun a _ => (hnR a).le) hS
    have h2 : S * ∑ a ∈ B, ‖-(Complex.I * (lam a : ℂ)) * (-(lam a : ℂ) * c a)‖ ^ 2 ≤ S * R := by
      refine mul_le_mul_of_nonneg_left ?_ hS
      have := hcoef2 (fun a => -(Complex.I * (lam a : ℂ)) * -(lam a : ℂ)) fun a _ => by
        rw [norm_mul, hnI, hnR, sq]
      simpa only [mul_assoc] using this
    nlinarith
  -- the `σ`-step
  have hderiv : ∀ (x : ι) (s : ℝ), HasDerivAt (fun s => dpoly B (fun a => c a * χ x a) lam s (γ x))
      (dpoly B (fun a => (-(lam a : ℂ) * c a) * χ x a) lam s (γ x)) s := by
    intro x s
    have h := dpoly_hasDerivAt_σ B (fun a => c a * χ x a) lam s (γ x)
    convert h using 2
    funext a
    ring
  have hmain := family_sobolev_sum_le X (fun x s => dpoly B (fun a => c a * χ x a) lam s (γ x))
    (fun x s => dpoly B (fun a => (-(lam a : ℂ) * c a) * χ x a) lam s (γ x))
    (by norm_num : (0 : ℝ) < 1) hderiv (fun x => dpoly_continuous_σ B _ lam (γ x)) σ hσ hA hA'
  have hSR : 0 ≤ S * R := mul_nonneg hS (by positivity)
  calc ∑ x ∈ X, ‖dpoly B (fun a => c a * χ x a) lam (σ x) (γ x)‖ ^ 2
      ≤ (1 + (1 - 0)) * ((1 + 4 * T) * (S * R)) + (1 - 0) * ((1 + 4 * T) * (S * R)) := hmain
    _ = 3 * (1 + 4 * T) * S * (1 + Λ ^ 2) ^ 2 * Q := by
      simp only [hR]
      ring

end ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect
