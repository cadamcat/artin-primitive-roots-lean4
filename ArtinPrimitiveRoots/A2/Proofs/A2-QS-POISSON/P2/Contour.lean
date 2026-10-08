import Mathlib

/-!
# Contour shifts across a vertical strip (helpers for P2)

The rectangle winding integral and the rectangle Cauchy formula are adapted from AINTLIB
`DedekindResidue/ExplicitFormula/RectangleContour.lean` (Chris Birkbeck, Apache 2.0), whose
module has no prebuilt artifact in the shared set.  New here: the limits `T → ∞` that turn the
rectangle identities into identities between vertical line integrals.
-/

set_option autoImplicit false

open MeasureTheory Complex intervalIntegral Filter Topology

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSP2

/-- The counterclockwise boundary integral of the rectangle with corners `z`, `w`
(bottom − top + i·right − i·left). -/
def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
    + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

theorem log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    Complex.log (-u) = Complex.log u - Real.pi * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hu]
  push_cast
  ring

theorem log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    Complex.log (-u) = Complex.log u + Real.pi * I := by
  have h := log_neg_of_im_pos (u := -u) (by simp only [Complex.neg_im]; linarith)
  rw [neg_neg] at h
  linear_combination -h

theorem integral_horizontal_inv_sub {a b c : ℝ} {ρ : ℂ}
    (h : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * I - ρ) ∈ Complex.slitPlane) :
    ∫ x : ℝ in a..b, ((x:ℂ) + (c:ℂ) * I - ρ)⁻¹
      = Complex.log ((b:ℂ) + (c:ℂ) * I - ρ) - Complex.log ((a:ℂ) + (c:ℂ) * I - ρ) := by
  have hne : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * I - ρ) ≠ 0 :=
    fun x hx => Complex.slitPlane_ne_zero (h x hx)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log ((t:ℂ) + (c:ℂ) * I - ρ))
        (((x:ℂ) + (c:ℂ) * I - ρ)⁻¹) x := by
    intro x hx
    have hlin : HasDerivAt (fun t : ℝ => (t:ℂ) + (c:ℂ) * I - ρ) 1 x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((c:ℂ) * I)).sub_const ρ
    have := hlin.clog_real (h x hx)
    simpa using this
  have hcont : IntervalIntegrable (fun x : ℝ => ((x:ℂ) + (c:ℂ) * I - ρ)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ ?_ hne
    fun_prop
  exact integral_eq_sub_of_hasDerivAt hderiv hcont

theorem smul_integral_vertical_inv_sub {b c d : ℝ} {ρ : ℂ}
    (h : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * I - ρ) ∈ Complex.slitPlane) :
    I • (∫ y : ℝ in c..d, ((b:ℂ) + (y:ℂ) * I - ρ)⁻¹)
      = Complex.log ((b:ℂ) + (d:ℂ) * I - ρ) - Complex.log ((b:ℂ) + (c:ℂ) * I - ρ) := by
  have hne : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * I - ρ) ≠ 0 :=
    fun y hy => Complex.slitPlane_ne_zero (h y hy)
  have hderiv : ∀ y ∈ Set.uIcc c d,
      HasDerivAt (fun t : ℝ => Complex.log ((b:ℂ) + (t:ℂ) * I - ρ))
        (I * ((b:ℂ) + (y:ℂ) * I - ρ)⁻¹) y := by
    intro y hy
    have hlin : HasDerivAt (fun t : ℝ => (b:ℂ) + (t:ℂ) * I - ρ) I y := by
      have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) * I) I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      simpa using (h1.const_add ((b:ℂ))).sub_const ρ
    have := hlin.clog_real (h y hy)
    rw [div_eq_mul_inv] at this
    simpa [mul_comm] using this
  have hcont : IntervalIntegrable
      (fun y : ℝ => I * ((b:ℂ) + (y:ℂ) * I - ρ)⁻¹) volume c d := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ hne
    fun_prop
  have hint := integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [intervalIntegral.integral_const_mul] at hint
  rw [smul_eq_mul]
  exact hint

/-- The rectangle winding integral `∮ (ζ − ρ)⁻¹ dζ = 2πi` for `ρ` in the open rectangle. -/
theorem rectInt_inv_sub {z w ρ : ℂ}
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectInt (fun ζ => (ζ - ρ)⁻¹) z w = 2 * Real.pi * I := by
  rw [rectInt]
  have hbot : ∀ x ∈ Set.uIcc z.re w.re,
      ((x:ℂ) + (z.im:ℂ) * I - ρ) ∈ Complex.slitPlane := by
    intro x _
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have him : ((x:ℂ) + (z.im:ℂ) * I - ρ).im = z.im - ρ.im := by simp
    rw [him]
    exact ne_of_lt (by linarith)
  have htop : ∀ x ∈ Set.uIcc z.re w.re,
      ((x:ℂ) + (w.im:ℂ) * I - ρ) ∈ Complex.slitPlane := by
    intro x _
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have him : ((x:ℂ) + (w.im:ℂ) * I - ρ).im = w.im - ρ.im := by simp
    rw [him]
    exact ne_of_gt (by linarith)
  have hright : ∀ y ∈ Set.uIcc z.im w.im,
      ((w.re:ℂ) + (y:ℂ) * I - ρ) ∈ Complex.slitPlane := by
    intro y _
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : ((w.re:ℂ) + (y:ℂ) * I - ρ).re = w.re - ρ.re := by simp
    rw [hre]
    linarith
  have hB := integral_horizontal_inv_sub (a := z.re) (b := w.re) (c := z.im) (ρ := ρ) hbot
  have hT := integral_horizontal_inv_sub (a := z.re) (b := w.re) (c := w.im) (ρ := ρ) htop
  have hR := smul_integral_vertical_inv_sub (b := w.re) (c := z.im) (d := w.im) (ρ := ρ) hright
  have hleftpt : ∀ y ∈ Set.uIcc z.im w.im,
      (-((z.re:ℂ) + (y:ℂ) * I - ρ)) ∈ Complex.slitPlane := by
    intro y _
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : (-((z.re:ℂ) + (y:ℂ) * I - ρ)).re = ρ.re - z.re := by simp
    rw [hre]
    linarith
  have hLderiv : ∀ y ∈ Set.uIcc z.im w.im,
      HasDerivAt (fun t : ℝ => Complex.log (-((z.re:ℂ) + (t:ℂ) * I - ρ)))
        (I * ((z.re:ℂ) + (y:ℂ) * I - ρ)⁻¹) y := by
    intro y hy
    have hlin : HasDerivAt (fun t : ℝ => -((z.re:ℂ) + (t:ℂ) * I - ρ)) (-I) y := by
      have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) * I) I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
      exact ((h1.const_add ((z.re:ℂ))).sub_const ρ).neg
    have := hlin.clog_real (hleftpt y hy)
    have hne : ((z.re:ℂ) + (y:ℂ) * I - ρ) ≠ 0 := by
      intro h0
      have := hleftpt y hy
      rw [h0] at this
      simp [Complex.slitPlane] at this
    rw [show -I / -((z.re:ℂ) + (y:ℂ) * I - ρ) = I * ((z.re:ℂ) + (y:ℂ) * I - ρ)⁻¹ by
      field_simp] at this
    exact this
  have hLcont : IntervalIntegrable
      (fun y : ℝ => I * ((z.re:ℂ) + (y:ℂ) * I - ρ)⁻¹) volume z.im w.im := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ ?_
    · fun_prop
    · intro y hy h0
      have := hleftpt y hy
      rw [h0] at this
      simp [Complex.slitPlane] at this
  have hL0 := integral_eq_sub_of_hasDerivAt hLderiv hLcont
  rw [intervalIntegral.integral_const_mul] at hL0
  set u₁ : ℂ := (z.re:ℂ) + (z.im:ℂ) * I - ρ with hu₁
  set u₄ : ℂ := (z.re:ℂ) + (w.im:ℂ) * I - ρ with hu₄
  have hL : I • (∫ y : ℝ in z.im..w.im, ((z.re:ℂ) + (y:ℂ) * I - ρ)⁻¹)
      = Complex.log (-u₄) - Complex.log (-u₁) := by
    rw [smul_eq_mul, hL0]
  have hu₁im : u₁.im < 0 := by
    rw [hu₁]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    simp
    linarith
  have hu₄im : 0 < u₄.im := by
    rw [hu₄]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    simp
    linarith
  rw [hB, hT, hR, hL, log_neg_of_im_pos hu₄im, log_neg_of_im_neg hu₁im]
  ring

/-- Goursat on a rectangle (countable exceptional set). -/
theorem rectInt_eq_zero {f : ℂ → ℂ} {z w : ℂ} {s : Set ℂ} (hs : s.Countable)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : ∀ x ∈ (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Set.Ioo (min z.im w.im) (max z.im w.im)) \ s, DifferentiableAt ℂ f x) :
    rectInt f z w = 0 := by
  rw [rectInt]
  exact Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs Hc Hd

/-- `rectInt` only sees the boundary. -/
theorem rectInt_congr {f g : ℂ → ℂ} {z w : ℂ}
    (h : ∀ ζ, (ζ.im = z.im ∨ ζ.im = w.im) ∧ ζ.re ∈ Set.uIcc z.re w.re ∨
      (ζ.re = z.re ∨ ζ.re = w.re) ∧ ζ.im ∈ Set.uIcc z.im w.im → f ζ = g ζ) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  have e1 : (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) = ∫ x : ℝ in z.re..w.re, g (x + z.im * I) :=
    intervalIntegral.integral_congr fun x hx => h _ (Or.inl ⟨Or.inl (by simp), by simpa using hx⟩)
  have e2 : (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) = ∫ x : ℝ in z.re..w.re, g (x + w.im * I) :=
    intervalIntegral.integral_congr fun x hx => h _ (Or.inl ⟨Or.inr (by simp), by simpa using hx⟩)
  have e3 : (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) = ∫ y : ℝ in z.im..w.im, g (w.re + y * I) :=
    intervalIntegral.integral_congr fun y hy => h _ (Or.inr ⟨Or.inr (by simp), by simpa using hy⟩)
  have e4 : (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) = ∫ y : ℝ in z.im..w.im, g (z.re + y * I) :=
    intervalIntegral.integral_congr fun y hy => h _ (Or.inr ⟨Or.inl (by simp), by simpa using hy⟩)
  rw [e1, e2, e3, e4]

/-- Linearity of `rectInt` for functions continuous on the boundary segments. -/
theorem rectInt_sub {f g : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (hg : ContinuousOn g (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)) :
    rectInt (fun ζ => f ζ - g ζ) z w = rectInt f z w - rectInt g z w := by
  have hseg1 : ∀ c ∈ Set.uIcc z.im w.im, ∀ F : ℂ → ℂ,
      ContinuousOn F (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) →
      IntervalIntegrable (fun x : ℝ => F (x + c * I)) volume z.re w.re := by
    intro c hc F hF
    refine ContinuousOn.intervalIntegrable ?_
    refine hF.comp (by fun_prop) ?_
    intro x hx
    exact ⟨by simpa using hx, by simpa using hc⟩
  have hseg2 : ∀ c ∈ Set.uIcc z.re w.re, ∀ F : ℂ → ℂ,
      ContinuousOn F (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) →
      IntervalIntegrable (fun y : ℝ => F (c + y * I)) volume z.im w.im := by
    intro c hc F hF
    refine ContinuousOn.intervalIntegrable ?_
    refine hF.comp (by fun_prop) ?_
    intro y hy
    exact ⟨by simpa using hc, by simpa using hy⟩
  have hz1 : z.im ∈ Set.uIcc z.im w.im := Set.left_mem_uIcc
  have hw1 : w.im ∈ Set.uIcc z.im w.im := Set.right_mem_uIcc
  have hz2 : z.re ∈ Set.uIcc z.re w.re := Set.left_mem_uIcc
  have hw2 : w.re ∈ Set.uIcc z.re w.re := Set.right_mem_uIcc
  unfold rectInt
  rw [intervalIntegral.integral_sub (hseg1 _ hz1 f hf) (hseg1 _ hz1 g hg),
    intervalIntegral.integral_sub (hseg1 _ hw1 f hf) (hseg1 _ hw1 g hg),
    intervalIntegral.integral_sub (hseg2 _ hw2 f hf) (hseg2 _ hw2 g hg),
    intervalIntegral.integral_sub (hseg2 _ hz2 f hf) (hseg2 _ hz2 g hg)]
  simp only [smul_sub]
  ring

theorem rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectInt (fun ζ => c * f ζ) z w = c * rectInt f z w := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- The rectangle Cauchy formula `∮ Ψ(ζ)(ζ − ρ)⁻¹ dζ = 2πi Ψ(ρ)`. -/
theorem rectInt_cauchy {Ψ : ℂ → ℂ} {z w ρ : ℂ}
    (hΨ : ∀ ζ ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, DifferentiableAt ℂ Ψ ζ)
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectInt (fun ζ => Ψ ζ * (ζ - ρ)⁻¹) z w = 2 * Real.pi * I * Ψ ρ := by
  set R : Set ℂ := Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im with hR
  have hρR : R ∈ 𝓝 ρ := by
    rw [← mem_interior_iff_mem_nhds, hR, Complex.interior_reProdIm]
    rw [Set.uIcc_of_le (by linarith : z.re ≤ w.re), Set.uIcc_of_le (by linarith : z.im ≤ w.im),
      interior_Icc, interior_Icc]
    rw [Complex.mem_reProdIm]
    exact ⟨Set.mem_Ioo.mpr ⟨h1, h2⟩, Set.mem_Ioo.mpr ⟨h3, h4⟩⟩
  have hcont : ContinuousOn (dslope Ψ ρ) R :=
    (continuousOn_dslope hρR).mpr
      ⟨fun ζ hζ => (hΨ ζ hζ).continuousAt.continuousWithinAt, hΨ ρ (mem_of_mem_nhds hρR)⟩
  have hzero : rectInt (dslope Ψ ρ) z w = 0 := by
    refine rectInt_eq_zero (s := {ρ}) (Set.countable_singleton ρ) hcont ?_
    intro x hx
    have hxρ : x ≠ ρ := fun h => hx.2 (by simp [h])
    have hxR : x ∈ R := by
      have := hx.1
      rw [Complex.mem_reProdIm] at this ⊢
      refine ⟨Set.Ioo_subset_Icc_self.trans (by simp [Set.uIcc]) this.1,
        Set.Ioo_subset_Icc_self.trans (by simp [Set.uIcc]) this.2⟩
    exact (differentiableAt_dslope_of_ne hxρ).mpr (hΨ x hxR)
  -- on the boundary `ζ ≠ ρ`
  have hbd : ∀ ζ, (ζ.im = z.im ∨ ζ.im = w.im) ∧ ζ.re ∈ Set.uIcc z.re w.re ∨
      (ζ.re = z.re ∨ ζ.re = w.re) ∧ ζ.im ∈ Set.uIcc z.im w.im →
      Ψ ζ * (ζ - ρ)⁻¹ = dslope Ψ ρ ζ + Ψ ρ * (ζ - ρ)⁻¹ := by
    intro ζ hζ
    have hne : ζ ≠ ρ := by
      rintro rfl
      rcases hζ with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> linarith
    rw [dslope_of_ne _ hne, slope_def_field]
    have : ζ - ρ ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  have hinvc : ContinuousOn (fun ζ => Ψ ρ * (ζ - ρ)⁻¹) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im \
      {ρ}) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) ?_)
    intro ζ hζ
    exact sub_ne_zero.mpr (fun h => hζ.2 (by simp [h]))
  -- assemble directly on the four segments
  rw [rectInt_congr hbd]
  have hsplit : rectInt (fun ζ => dslope Ψ ρ ζ + Ψ ρ * (ζ - ρ)⁻¹) z w
      = rectInt (dslope Ψ ρ) z w + Ψ ρ * rectInt (fun ζ => (ζ - ρ)⁻¹) z w := by
    unfold rectInt
    have hb : ∀ c : ℝ, c ≠ ρ.im → c ∈ Set.uIcc z.im w.im →
        IntervalIntegrable (fun x : ℝ => (((x : ℂ) + c * I) - ρ)⁻¹) volume z.re w.re := by
      intro c hc _
      refine ContinuousOn.intervalIntegrable (ContinuousOn.inv₀ (by fun_prop) ?_)
      intro x _ h0
      have := congrArg Complex.im h0
      simp at this
      exact hc (by linarith)
    have hv : ∀ c : ℝ, c ≠ ρ.re → c ∈ Set.uIcc z.re w.re →
        IntervalIntegrable (fun y : ℝ => (((c : ℂ) + y * I) - ρ)⁻¹) volume z.im w.im := by
      intro c hc _
      refine ContinuousOn.intervalIntegrable (ContinuousOn.inv₀ (by fun_prop) ?_)
      intro y _ h0
      have := congrArg Complex.re h0
      simp at this
      exact hc (by linarith)
    have hdb : ∀ c ∈ Set.uIcc z.im w.im,
        IntervalIntegrable (fun x : ℝ => dslope Ψ ρ (x + c * I)) volume z.re w.re := by
      intro c hc
      refine ContinuousOn.intervalIntegrable (hcont.comp (by fun_prop) ?_)
      intro x hx
      exact ⟨by simpa using hx, by simpa using hc⟩
    have hdv : ∀ c ∈ Set.uIcc z.re w.re,
        IntervalIntegrable (fun y : ℝ => dslope Ψ ρ (c + y * I)) volume z.im w.im := by
      intro c hc
      refine ContinuousOn.intervalIntegrable (hcont.comp (by fun_prop) ?_)
      intro y hy
      exact ⟨by simpa using hc, by simpa using hy⟩
    rw [intervalIntegral.integral_add (hdb _ Set.left_mem_uIcc)
        ((hb _ (by linarith) Set.left_mem_uIcc).const_mul (Ψ ρ)),
      intervalIntegral.integral_add (hdb _ Set.right_mem_uIcc)
        ((hb _ (by linarith) Set.right_mem_uIcc).const_mul (Ψ ρ)),
      intervalIntegral.integral_add (hdv _ Set.right_mem_uIcc)
        ((hv _ (by linarith) Set.right_mem_uIcc).const_mul (Ψ ρ)),
      intervalIntegral.integral_add (hdv _ Set.left_mem_uIcc)
        ((hv _ (by linarith) Set.left_mem_uIcc).const_mul (Ψ ρ))]
    simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  rw [hsplit, hzero, rectInt_inv_sub h1 h2 h3 h4]
  ring

/-! ### From rectangles to vertical lines -/

/-- Tall rectangles: if `F` is continuous on the closed strip `a ≤ Re ≤ b`, integrable on its two
edges, and `O(1/t²)` uniformly for `|Im| ≥ 1`, then the rectangle integrals over
`[a,b] × [-T,T]` tend to `i (∫_{(b)} F - ∫_{(a)} F)`. -/
theorem tendsto_rectInt_vertical {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hia : Integrable (fun t : ℝ => F (a + t * I)))
    (hib : Integrable (fun t : ℝ => F (b + t * I)))
    (C : ℝ) (hC : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖F s‖ ≤ C / s.im ^ 2) :
    Tendsto (fun T : ℝ => rectInt F ((a : ℂ) - T * I) ((b : ℂ) + T * I)) atTop
      (𝓝 (I * ((∫ t : ℝ, F (b + t * I)) - ∫ t : ℝ, F (a + t * I)))) := by
  -- horizontal edges
  have hbound : ∀ T : ℝ, 1 ≤ T → ∀ σ : ℝ, σ = T ∨ σ = -T →
      ‖∫ x : ℝ in a..b, F (x + σ * I)‖ ≤ (b - a) * (C / T ^ 2) := by
    intro T hT σ hσ
    have hle : ∀ x ∈ Set.uIoc a b, ‖F (x + σ * I)‖ ≤ C / T ^ 2 := by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      have him : ((x : ℂ) + σ * I).im = σ := by simp
      have hre : ((x : ℂ) + σ * I).re = x := by simp
      have habs : |σ| = T := by
        rcases hσ with h | h <;> rw [h]
        · exact abs_of_pos (by linarith)
        · rw [abs_neg]; exact abs_of_pos (by linarith)
      have hsq : σ ^ 2 = T ^ 2 := by rcases hσ with h | h <;> rw [h]; ring
      have h := hC ((x : ℂ) + σ * I) (by rw [hre]; linarith [hx.1]) (by rw [hre]; linarith [hx.2])
        (by rw [him, habs]; exact hT)
      rwa [him, hsq] at h
    have := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at this
    calc _ ≤ C / T ^ 2 * (b - a) := this
      _ = (b - a) * (C / T ^ 2) := by ring
  have hzero : ∀ c : ℝ, (c = 1 ∨ c = -1) →
      Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F (x + (c * T : ℝ) * I)) atTop (𝓝 0) := by
    intro c hc
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun T : ℝ => (b - a) * (C / T ^ 2)) atTop (𝓝 0) := by
      have : Tendsto (fun T : ℝ => C / T ^ 2) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop two_ne_zero)
      simpa using this.const_mul (b - a)
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact hbound T hT _ (by rcases hc with rfl | rfl <;> simp)
  have hbot := hzero (-1) (Or.inr rfl)
  have htop := hzero 1 (Or.inl rfl)
  -- vertical edges
  have hvert : ∀ σ : ℝ, Integrable (fun t : ℝ => F (σ + t * I)) →
      Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, F (σ + y * I)) atTop
        (𝓝 (∫ t : ℝ, F (σ + t * I))) :=
    fun σ hi => intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id
  have hva := hvert a hia
  have hvb := hvert b hib
  have hcomb := ((hbot.sub htop).add (hvb.const_smul I)).sub (hva.const_smul I)
  refine hcomb.congr' ?_ |>.trans ?_
  · filter_upwards with T
    simp only [rectInt]
    simp
  · simp only [sub_self, zero_add, smul_eq_mul]
    rw [mul_sub]

/-- Contour shift across two simple poles: for `Ψ` holomorphic near the closed strip
`a ≤ Re ≤ b` (`a < 0`, `1 < b`), with `F = Ψ/(s(s-1))` integrable on both edges and
`O(1/t²)` for `|Im| ≥ 1`: `∫_{(b)} F - ∫_{(a)} F = 2π (Ψ 1 - Ψ 0)`. -/
theorem vline_sub_two_poles {Ψ : ℂ → ℂ} {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hΨ : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ Ψ s)
    (hia : Integrable (fun t : ℝ => Ψ (a + t * I) * ((a + t * I) * ((a + t * I) - 1))⁻¹))
    (hib : Integrable (fun t : ℝ => Ψ (b + t * I) * ((b + t * I) * ((b + t * I) - 1))⁻¹))
    (C : ℝ) (hC : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖Ψ s * (s * (s - 1))⁻¹‖ ≤ C / s.im ^ 2) :
    (∫ t : ℝ, Ψ (b + t * I) * ((b + t * I) * ((b + t * I) - 1))⁻¹) -
      (∫ t : ℝ, Ψ (a + t * I) * ((a + t * I) * ((a + t * I) - 1))⁻¹) =
        2 * Real.pi * (Ψ 1 - Ψ 0) := by
  set F : ℂ → ℂ := fun s => Ψ s * (s * (s - 1))⁻¹ with hF
  -- rectangle identity for every `T ≥ 1`
  have hrect : ∀ T : ℝ, 1 ≤ T →
      rectInt F ((a : ℂ) - T * I) ((b : ℂ) + T * I) = 2 * Real.pi * I * (Ψ 1 - Ψ 0) := by
    intro T hT
    set z : ℂ := (a : ℂ) - T * I
    set w : ℂ := (b : ℂ) + T * I
    have hzre : z.re = a := by simp [z]
    have hzim : z.im = -T := by simp [z]
    have hwre : w.re = b := by simp [w]
    have hwim : w.im = T := by simp [w]
    have hdiff : ∀ ζ ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, DifferentiableAt ℂ Ψ ζ := by
      intro ζ hζ
      rw [Complex.mem_reProdIm, hzre, hwre, Set.uIcc_of_le (by linarith)] at hζ
      exact hΨ ζ hζ.1.1 hζ.1.2
    have hbd : ∀ ζ, (ζ.im = z.im ∨ ζ.im = w.im) ∧ ζ.re ∈ Set.uIcc z.re w.re ∨
        (ζ.re = z.re ∨ ζ.re = w.re) ∧ ζ.im ∈ Set.uIcc z.im w.im →
        F ζ = Ψ ζ * (ζ - 1)⁻¹ - Ψ ζ * (ζ - 0)⁻¹ := by
      intro ζ hζ
      have h0 : ζ ≠ 0 := by
        rintro rfl
        rcases hζ with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> simp_all <;> linarith
      have h1 : ζ - 1 ≠ 0 := by
        intro h
        have hζ1 : ζ = 1 := sub_eq_zero.mp h
        subst hζ1
        rcases hζ with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> simp_all <;> linarith
      simp only [hF, sub_zero]
      field_simp
      ring
    have hcontΨ : ContinuousOn Ψ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) :=
      fun ζ hζ => (hdiff ζ hζ).continuousAt.continuousWithinAt
    rw [rectInt_congr hbd]
    -- linearity on the boundary: write with explicit segment-wise continuity
    have hsplit : rectInt (fun ζ => Ψ ζ * (ζ - 1)⁻¹ - Ψ ζ * (ζ - 0)⁻¹) z w =
        rectInt (fun ζ => Ψ ζ * (ζ - 1)⁻¹) z w - rectInt (fun ζ => Ψ ζ * (ζ - 0)⁻¹) z w := by
      unfold rectInt
      have hseg : ∀ ρ : ℂ, (ρ = 0 ∨ ρ = 1) →
          (∀ c : ℝ, (c = z.im ∨ c = w.im) →
            IntervalIntegrable (fun x : ℝ => Ψ (x + c * I) * ((x + c * I) - ρ)⁻¹) volume
              z.re w.re) ∧
          (∀ c : ℝ, (c = z.re ∨ c = w.re) →
            IntervalIntegrable (fun y : ℝ => Ψ (c + y * I) * ((c + y * I) - ρ)⁻¹) volume
              z.im w.im) := by
        intro ρ hρ
        have hρim : ρ.im = 0 := by rcases hρ with h | h <;> rw [h] <;> simp
        have hρre : ρ.re = 0 ∨ ρ.re = 1 := by
          rcases hρ with h | h <;> rw [h]
          · left; simp
          · right; simp
        constructor
        · intro c hc
          have hc0 : c ≠ 0 := by
            rcases hc with h | h
            · rw [h, hzim]; intro h0; linarith
            · rw [h, hwim]; intro h0; linarith
          refine ContinuousOn.intervalIntegrable ?_
          refine ContinuousOn.mul (hcontΨ.comp (by fun_prop) ?_) ?_
          · intro x hx
            refine ⟨by simpa using hx, ?_⟩
            rcases hc with h | h <;> rw [h] <;> simp
          · refine ContinuousOn.inv₀ (by fun_prop) ?_
            intro x _ h0
            have him := congrArg Complex.im h0
            have him' : ((x : ℂ) + c * I - ρ).im = c - ρ.im := by simp
            rw [him', hρim, Complex.zero_im] at him
            exact hc0 (by linarith)
        · intro c hc
          have hcab : c = a ∨ c = b := by
            rcases hc with h | h
            · left; rw [h, hzre]
            · right; rw [h, hwre]
          refine ContinuousOn.intervalIntegrable ?_
          refine ContinuousOn.mul (hcontΨ.comp (by fun_prop) ?_) ?_
          · intro y hy
            refine ⟨?_, by simpa using hy⟩
            rcases hc with h | h <;> rw [h] <;> simp
          · refine ContinuousOn.inv₀ (by fun_prop) ?_
            intro y _ h0
            have hre := congrArg Complex.re h0
            have hre' : ((c : ℂ) + y * I - ρ).re = c - ρ.re := by simp
            rw [hre', Complex.zero_re] at hre
            rcases hcab with h1 | h1 <;> rcases hρre with h2 | h2 <;> linarith
      obtain ⟨h0b, h0v⟩ := hseg 0 (Or.inl rfl)
      obtain ⟨h1b, h1v⟩ := hseg 1 (Or.inr rfl)
      rw [intervalIntegral.integral_sub (h1b _ (Or.inl rfl)) (h0b _ (Or.inl rfl)),
        intervalIntegral.integral_sub (h1b _ (Or.inr rfl)) (h0b _ (Or.inr rfl)),
        intervalIntegral.integral_sub (h1v _ (Or.inr rfl)) (h0v _ (Or.inr rfl)),
        intervalIntegral.integral_sub (h1v _ (Or.inl rfl)) (h0v _ (Or.inl rfl))]
      simp only [smul_sub]
      ring
    rw [hsplit, rectInt_cauchy hdiff (by simp [hzre]; linarith) (by simp [hwre]; linarith)
        (by simp [hzim]; linarith) (by simp [hwim]; linarith),
      rectInt_cauchy hdiff (by simp [hzre]; linarith) (by simp [hwre]; linarith)
        (by simp [hzim]; linarith) (by simp [hwim]; linarith)]
    ring
  -- pass to the limit
  have hlim := tendsto_rectInt_vertical (F := F) (by linarith) hia hib C hC
  have hconst : Tendsto (fun T : ℝ => rectInt F ((a : ℂ) - T * I) ((b : ℂ) + T * I)) atTop
      (𝓝 (2 * Real.pi * I * (Ψ 1 - Ψ 0))) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      exact (hrect T hT).symm)
  have heq := tendsto_nhds_unique hlim hconst
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  calc (∫ t : ℝ, F (b + t * I)) - ∫ t : ℝ, F (a + t * I)
      = I⁻¹ * (I * ((∫ t : ℝ, F (b + t * I)) - ∫ t : ℝ, F (a + t * I))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hI, one_mul]
    _ = I⁻¹ * (2 * Real.pi * I * (Ψ 1 - Ψ 0)) := by rw [heq]
    _ = 2 * Real.pi * (Ψ 1 - Ψ 0) := by field_simp

/-- Pole-free contour shift: `∫_{(b)} G = ∫_{(a)} G` for `G` holomorphic near the closed strip,
integrable on both edges and `O(1/t²)` for `|Im| ≥ 1`. -/
theorem vline_eq_of_differentiable {G : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hG : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ G s)
    (hia : Integrable (fun t : ℝ => G (a + t * I)))
    (hib : Integrable (fun t : ℝ => G (b + t * I)))
    (C : ℝ) (hC : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖G s‖ ≤ C / s.im ^ 2) :
    (∫ t : ℝ, G (b + t * I)) = ∫ t : ℝ, G (a + t * I) := by
  have hrect : ∀ T : ℝ, 1 ≤ T → rectInt G ((a : ℂ) - T * I) ((b : ℂ) + T * I) = 0 := by
    intro T hT
    have hzre : ((a : ℂ) - T * I).re = a := by simp
    have hwre : ((b : ℂ) + T * I).re = b := by simp
    refine rectInt_eq_zero (s := ∅) Set.countable_empty ?_ ?_
    · intro ζ hζ
      rw [Complex.mem_reProdIm, hzre, hwre, Set.uIcc_of_le hab] at hζ
      exact (hG ζ hζ.1.1 hζ.1.2).continuousAt.continuousWithinAt
    · intro ζ hζ
      have h1 := hζ.1
      rw [Complex.mem_reProdIm, hzre, hwre, min_eq_left hab, max_eq_right hab] at h1
      exact hG ζ h1.1.1.le h1.1.2.le
  have hlim := tendsto_rectInt_vertical (F := G) hab hia hib C hC
  have hconst : Tendsto (fun T : ℝ => rectInt G ((a : ℂ) - T * I) ((b : ℂ) + T * I)) atTop
      (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      exact (hrect T hT).symm)
  have heq := tendsto_nhds_unique hlim hconst
  have h2 := (mul_eq_zero.mp heq).resolve_left I_ne_zero
  exact sub_eq_zero.mp h2

end ArtinPrimitiveRoots.A2.QSP2
