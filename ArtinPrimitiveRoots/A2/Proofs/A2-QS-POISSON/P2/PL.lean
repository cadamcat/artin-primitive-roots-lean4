import Mathlib

/-!
# Phragmén–Lindelöf with polynomial boundary bounds (helper for P2)

Wrapper around `PhragmenLindelof.vertical_strip`: a function holomorphic near a closed vertical
strip, of at most exponential growth in `|Im s|`, bounded by `C (1 + |Im s|)^N` on both edges,
is bounded by a constant multiple of `(1 + |Im s|)^N` on the whole strip.
-/

set_option autoImplicit false

open Complex Filter Topology

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSP2

theorem pl_poly_strip {f : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (κ C₀ : ℝ)
    (hgr : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖f s‖ ≤ C₀ * Real.exp (κ * |s.im|))
    (N : ℕ) (C : ℝ)
    (hA : ∀ s : ℂ, s.re = a → ‖f s‖ ≤ C * (1 + |s.im|) ^ N)
    (hB : ∀ s : ℂ, s.re = b → ‖f s‖ ≤ C * (1 + |s.im|) ^ N) :
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖f s‖ ≤ C * 2 ^ N * (b - a + 2) ^ N * (1 + |s.im|) ^ N := by
  -- `C ≥ 0`
  have hC : 0 ≤ C := by
    have h := hA (a : ℂ) (by simp)
    have h1 : (0 : ℝ) < (1 + |((a : ℂ)).im|) ^ N := by positivity
    by_contra hneg
    push Not at hneg
    have : C * (1 + |((a : ℂ)).im|) ^ N < 0 := mul_neg_of_neg_of_pos hneg h1
    linarith [norm_nonneg (f (a : ℂ))]
  set c₀ : ℂ := ((a - 1 : ℝ) : ℂ) with hc₀
  -- basic facts on `‖s - c₀‖`
  have hre : ∀ s : ℂ, (s - c₀).re = s.re - (a - 1) := by intro s; simp [hc₀]
  have him : ∀ s : ℂ, (s - c₀).im = s.im := by intro s; simp [hc₀]
  have hlow : ∀ s : ℂ, a ≤ s.re → (1 + |s.im|) / 2 ≤ ‖s - c₀‖ := by
    intro s hs
    have h1 : 1 ≤ ‖s - c₀‖ := by
      have := Complex.abs_re_le_norm (s - c₀)
      rw [hre, abs_of_nonneg (by linarith)] at this
      linarith
    have h2 : |s.im| ≤ ‖s - c₀‖ := by
      have := Complex.abs_im_le_norm (s - c₀)
      rwa [him] at this
    linarith
  have hupp : ∀ s : ℂ, s.re ≤ b → a ≤ s.re → ‖s - c₀‖ ≤ (b - a + 2) * (1 + |s.im|) := by
    intro s hs hs'
    calc ‖s - c₀‖ ≤ |(s - c₀).re| + |(s - c₀).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = (s.re - (a - 1)) + |s.im| := by rw [hre, him, abs_of_nonneg (by linarith)]
      _ ≤ (b - a + 2) * (1 + |s.im|) := by
        have : 0 ≤ |s.im| := abs_nonneg _
        nlinarith
  have hne : ∀ s : ℂ, a ≤ s.re → s - c₀ ≠ 0 := by
    intro s hs h0
    have := hre s
    rw [h0] at this
    simp at this
    linarith
  set g : ℂ → ℂ := fun s => f s * ((s - c₀) ^ N)⁻¹ with hg
  have hgd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ g s := by
    intro s h1 h2
    exact (hd s h1 h2).mul ((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => (s - c₀) ^ N) s).inv
      (pow_ne_zero _ (hne s h1)))
  have hgnorm : ∀ s : ℂ, a ≤ s.re → ‖g s‖ = ‖f s‖ / ‖s - c₀‖ ^ N := by
    intro s hs
    simp [hg, norm_inv, norm_pow, div_eq_mul_inv]
  -- edge bounds for `g`
  have hedge : ∀ s : ℂ, (s.re = a ∨ s.re = b) → ‖g s‖ ≤ C * 2 ^ N := by
    intro s hs
    have hsa : a ≤ s.re := by rcases hs with h | h <;> linarith
    rw [hgnorm s hsa]
    have hpos : 0 < ‖s - c₀‖ := norm_pos_iff.mpr (hne s hsa)
    have hfs : ‖f s‖ ≤ C * (1 + |s.im|) ^ N := by rcases hs with h | h; exact hA s h; exact hB s h
    rw [div_le_iff₀ (pow_pos hpos N)]
    calc ‖f s‖ ≤ C * (1 + |s.im|) ^ N := hfs
      _ = C * 2 ^ N * ((1 + |s.im|) / 2) ^ N := by rw [div_pow]; field_simp
      _ ≤ C * 2 ^ N * ‖s - c₀‖ ^ N := by
          gcongr
          exact hlow s hsa
  -- Phragmén–Lindelöf
  have hPL : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖g s‖ ≤ C * 2 ^ N := by
    intro s h1 h2
    refine PhragmenLindelof.vertical_strip (a := a) (b := b) ?_ ?_ (fun z hz => hedge z (Or.inl hz))
      (fun z hz => hedge z (Or.inr hz)) h1 h2
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_preimage_re, closure_Ioo hab.ne]
      intro z hz
      exact (hgd z hz.1 hz.2).differentiableWithinAt
    · set c : ℝ := Real.pi / (2 * (b - a)) with hcdef
      have hba : 0 < b - a := by linarith
      have hcpos : 0 < c := by positivity
      refine ⟨c, ?_, |Real.log (max C₀ 1)| + |κ| / c + 1, ?_⟩
      · rw [hcdef]
        have : Real.pi / (2 * (b - a)) < Real.pi / (b - a) := by
          apply div_lt_div_of_pos_left Real.pi_pos hba
          linarith
        exact this
      · refine Asymptotics.IsBigO.of_bound 1 ?_
        have hev1 : ∀ᶠ z in comap (abs ∘ im) atTop ⊓ Filter.principal (re ⁻¹' Set.Ioo a b),
            1 ≤ |z.im| :=
          (tendsto_comap.eventually (eventually_ge_atTop (1:ℝ))).filter_mono inf_le_left
        have hev2 : ∀ᶠ z in comap (abs ∘ im) atTop ⊓ Filter.principal (re ⁻¹' Set.Ioo a b),
            z ∈ re ⁻¹' Set.Ioo a b :=
          Filter.mem_inf_of_right (Filter.mem_principal_self _)
        filter_upwards [hev1, hev2] with z hz1 hz2
        have hza : a ≤ z.re := hz2.1.le
        have hzb : z.re ≤ b := hz2.2.le
        have hn1 : 1 ≤ ‖z - c₀‖ := by
          have := Complex.abs_re_le_norm (z - c₀)
          rw [hre, abs_of_nonneg (by linarith)] at this
          linarith
        rw [hgnorm z hza, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
        set t : ℝ := |z.im| with ht
        have ht0 : 0 ≤ t := abs_nonneg _
        set L : ℝ := Real.log (max C₀ 1) with hL
        have hk : |κ| / c * c = |κ| := div_mul_cancel₀ _ hcpos.ne'
        have hkt : (|κ| / c) * (c * t) = |κ| * t := by rw [← mul_assoc, hk]
        have he : 1 + c * t ≤ Real.exp (c * t) := by linarith [Real.add_one_le_exp (c * t)]
        calc ‖f z‖ / ‖z - c₀‖ ^ N ≤ ‖f z‖ := div_le_self (norm_nonneg _) (one_le_pow₀ hn1)
          _ ≤ C₀ * Real.exp (κ * t) := hgr z hza hzb hz1
          _ ≤ max C₀ 1 * Real.exp (|κ| * t) := by
              apply mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
                (by positivity)
              exact mul_le_mul_of_nonneg_right (le_abs_self κ) ht0
          _ = Real.exp (L + |κ| * t) := by
              rw [Real.exp_add, hL, Real.exp_log (by positivity)]
          _ ≤ Real.exp ((|L| + |κ| / c + 1) * Real.exp (c * t)) := by
              apply Real.exp_le_exp.2
              have hL0 : 0 ≤ |L| := abs_nonneg _
              have hkc : 0 ≤ |κ| / c := div_nonneg (abs_nonneg κ) hcpos.le
              have hct : 0 ≤ c * t := mul_nonneg hcpos.le ht0
              calc L + |κ| * t ≤ |L| + |κ| * t := by linarith [le_abs_self L]
                _ ≤ (|L| + |κ| / c + 1) * (1 + c * t) := by
                    nlinarith [mul_nonneg hL0 hct]
                _ ≤ (|L| + |κ| / c + 1) * Real.exp (c * t) :=
                    mul_le_mul_of_nonneg_left he (by positivity)
  intro s h1 h2
  have hpos : 0 < ‖s - c₀‖ := norm_pos_iff.mpr (hne s h1)
  have hg' := hPL s h1 h2
  rw [hgnorm s h1, div_le_iff₀ (pow_pos hpos N)] at hg'
  calc ‖f s‖ ≤ C * 2 ^ N * ‖s - c₀‖ ^ N := hg'
    _ ≤ C * 2 ^ N * ((b - a + 2) * (1 + |s.im|)) ^ N := by
        gcongr
        exact hupp s h2 h1
    _ = C * 2 ^ N * (b - a + 2) ^ N * (1 + |s.im|) ^ N := by rw [mul_pow]; ring

end ArtinPrimitiveRoots.A2.QSP2
