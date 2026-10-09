import Mathlib

namespace ArtinPrimitiveRoots.Proofs.r_impl_muse

open Classical MeasureTheory
open scoped BigOperators

/-- The phase `exp (I * u * log y)` has norm one. -/
theorem phase_exp_norm (u y : ℝ) :
    ‖Complex.exp (Complex.I * u * Real.log y)‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (u : ℂ) * Real.log y).re = 0 := by simp
  rw [hre, Real.exp_zero]

/-- HasDerivAt for the phase in `y`, used for the Lipschitz bound below. -/
theorem phase_exp_hasDerivAt (u y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun z : ℝ => Complex.exp (Complex.I * u * Real.log z))
      (Complex.exp (Complex.I * u * Real.log y) * (Complex.I * u / y)) y := by
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy
  have harg : HasDerivAt (fun z : ℝ => Complex.I * (u : ℂ) * Real.log z)
      (Complex.I * (u : ℂ) * y⁻¹) y := hlog.ofReal_comp.const_mul _
  have hcomp := (Complex.hasDerivAt_exp _).comp y harg
  simpa [Function.comp_def, div_eq_mul_inv, Complex.ofReal_inv] using hcomp

/-- The phase is Lipschitz in `y` on `[M, 2M]` with constant `|u| / M`. -/
theorem phase_exp_lipschitz (u M : ℝ) (hM : 0 < M) (y₁ y₂ : ℝ)
    (h1 : M ≤ y₁) (h2 : y₁ ≤ 2 * M) (h3 : M ≤ y₂) (h4 : y₂ ≤ 2 * M) :
    ‖Complex.exp (Complex.I * u * Real.log y₁) -
      Complex.exp (Complex.I * u * Real.log y₂)‖ ≤ (|u| / M) * |y₁ - y₂| := by
  have hderiv : ∀ x ∈ Set.Icc M (2 * M),
      DifferentiableAt ℝ (fun z : ℝ => Complex.exp (Complex.I * u * Real.log z)) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hM (Set.mem_Icc.mp hx).1
    exact (phase_exp_hasDerivAt u x hxpos.ne').differentiableAt
  have hbound : ∀ x ∈ Set.Icc M (2 * M),
      ‖deriv (fun z : ℝ => Complex.exp (Complex.I * u * Real.log z)) x‖ ≤ |u| / M := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hM (Set.mem_Icc.mp hx).1
    have hxM : M ≤ x := (Set.mem_Icc.mp hx).1
    rw [(phase_exp_hasDerivAt u x hxpos.ne').deriv]
    have hnorm : ‖Complex.I * (u : ℂ) / (x : ℂ)‖ = |u| / |x| := by
      simp [norm_div, norm_mul]
    rw [norm_mul, phase_exp_norm, one_mul, hnorm, abs_of_pos hxpos]
    exact div_le_div_of_nonneg_left (abs_nonneg u) hM hxM
  have hconv : Convex ℝ (Set.Icc M (2 * M)) := convex_Icc M (2 * M)
  have hmem1 : y₁ ∈ Set.Icc M (2 * M) := Set.mem_Icc.mpr ⟨h1, h2⟩
  have hmem2 : y₂ ∈ Set.Icc M (2 * M) := Set.mem_Icc.mpr ⟨h3, h4⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbound hconv hmem1 hmem2
  simpa [Real.norm_eq_abs, norm_sub_rev, abs_sub_comm] using h

/-- Finite chains telescope: the sum over the last set is the sum over the first
plus the successive differences. The induction step normalizes its beta-redex
by `rfl` before the linear combination. Stated over a commutative ring so it
applies to both complex summands and real norm masses. -/
theorem sum_chain_decomp {R : Type*} [CommRing R] (F : ℕ → Finset ℕ) (f : ℕ → R) (N : ℕ)
    (hsub : ∀ i, i < N → F i ⊆ F (i + 1)) :
    ∑ n ∈ F N, f n = ∑ n ∈ F 0, f n +
      ∑ i ∈ Finset.range N, (∑ n ∈ F (i + 1), f n - ∑ n ∈ F i, f n) := by
  revert hsub
  induction N with
  | zero =>
    intro hsub
    simp
  | succ k ih =>
    intro hsub
    have ih' := ih (fun i hi => hsub i (lt_of_lt_of_le hi (Nat.le_succ k)))
    rw [Finset.sum_range_succ]
    linear_combination ih'

/-- Summation by parts on `range (N+1)` with an explicit boundary term. -/
theorem summation_by_parts (G D : ℕ → ℂ) (N : ℕ) :
    G 1 * D 0 + ∑ i ∈ Finset.range (N + 1), G (i + 1) * (D (i + 1) - D i) =
      G (N + 1) * D (N + 1) - ∑ i ∈ Finset.Ioo 0 (N + 1), D i * (G (i + 1) - G i) := by
  induction N with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    simp only [zero_add]
    have hIoo : Finset.Ioo (0 : ℕ) 1 = ∅ := by decide
    rw [hIoo, Finset.sum_empty]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hIoo : Finset.Ioo 0 (k + 1 + 1) = insert (k + 1) (Finset.Ioo 0 (k + 1)) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    rw [hIoo, Finset.sum_insert (by simp)]
    linear_combination ih

/-- Restriction of a function continuous on a closed interval to a subinterval
is interval integrable. -/
theorem continuousOn_intervalIntegrable_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {l r : ℝ} {f : ℝ → E} (hf : ContinuousOn f (Set.Icc l r))
    {a b : ℝ} (ha1 : l ≤ a) (ha2 : a ≤ b) (hb2 : b ≤ r) :
    IntervalIntegrable f MeasureTheory.volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc ha2
    (hf.mono (Set.Icc_subset_Icc ha1 hb2))

/-- Finite splitting of an interval integral over a monotone mesh. -/
theorem interval_split_of_continuousOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {l r : ℝ} {f : ℝ → E}
    (hf : ContinuousOn f (Set.Icc l r)) (p : ℕ → ℝ) (j : ℕ)
    (hp0 : p 0 = l) (hmem : ∀ i, i ≤ j → l ≤ p i ∧ p i ≤ r)
    (hmono : ∀ i, p i ≤ p (i + 1)) :
    ∑ i ∈ Finset.range j, ∫ y in p i..p (i + 1), f y = ∫ y in p 0..p j, f y := by
  induction j with
  | zero =>
    rw [Finset.sum_range_zero, hp0]
    exact intervalIntegral.integral_same.symm
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hmemk : l ≤ p k ∧ p k ≤ r := hmem k (by omega)
    have hmemk1 : l ≤ p (k + 1) ∧ p (k + 1) ≤ r := hmem (k + 1) le_rfl
    have hp0le : l ≤ p 0 := by rw [hp0]
    have h01 : p 0 ≤ p k := by rw [hp0]; exact hmemk.1
    have hi1 : IntervalIntegrable f MeasureTheory.volume (p 0) (p k) :=
      continuousOn_intervalIntegrable_sub hf hp0le h01 hmemk.2
    have hi2 : IntervalIntegrable f MeasureTheory.volume (p k) (p (k + 1)) :=
      continuousOn_intervalIntegrable_sub hf hmemk.1 (hmono k) hmemk1.2
    have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have ih' := ih (fun i hi => hmem i (by omega))
    rw [ih']
    exact hadj

/-- Weighted interval error via Abel summation (`weighted_interval_error` from the
R-LOW proof guide). A uniform count hypothesis on all subintervals upgrades to a
Lipschitz-weighted estimate. The proof uses a uniform `N`-partition: the step
telescope is bounded by `sum_chain_decomp`/`summation_by_parts`, the mesh error
tends to zero by the epsilon choice `N = ⌊V/ε⌋₊ + 1`. -/
theorem weighted_interval_error (M l r E B K : ℝ) (a : ℕ → ℂ) (q g : ℝ → ℂ)
    (hM : 0 < M) (hl : M ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * M)
    (hE : 0 ≤ E) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hq : ContinuousOn q (Set.Icc l r))
    (hg : ∀ s ∈ Set.Icc l r, ∀ t ∈ Set.Icc l r, ‖g s - g t‖ ≤ K * |s - t|)
    (hgb : ∀ s ∈ Set.Icc l r, ‖g s‖ ≤ B)
    (hcount : ∀ s ∈ Set.Icc l r,
      ‖(∑ n ∈ (Finset.range (⌊s⌋₊ + 1)).filter
          (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s), a n) -
        ∫ y in l..s, q y‖ ≤ E) :
    ‖(∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
        (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r), a n * g n) -
      ∫ y in l..r, q y * g y‖ ≤ 2 * E * (B + K * (r - l)) := by
  classical
  by_cases hlr_eq : l = r
  · -- Degenerate interval: at most one atom, vanishing integral.
    have hE0 : ‖∑ n ∈ (Finset.range (⌊l⌋₊ + 1)).filter
          (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l), a n‖ ≤ E := by
      have h := hcount l (Set.mem_Icc.mpr ⟨le_rfl, hlr⟩)
      rwa [intervalIntegral.integral_same, sub_zero] at h
    have hSeq : (Finset.range (⌊r⌋₊ + 1)).filter
          (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r) =
        (Finset.range (⌊l⌋₊ + 1)).filter
          (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l) := by
      rw [hlr_eq]
    have hInt : (∫ y in l..r, q y * g y) = 0 := by
      rw [hlr_eq]
      exact intervalIntegral.integral_same
    have hSl : ∀ n ∈ (Finset.range (⌊l⌋₊ + 1)).filter
        (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l), (n : ℝ) = l := by
      intro n hn
      have h2 := (Finset.mem_filter.mp hn).2
      exact le_antisymm h2.2 h2.1
    have hmeml : l ∈ Set.Icc l r := Set.mem_Icc.mpr ⟨le_rfl, hlr⟩
    have hsum : (∑ n ∈ (Finset.range (⌊l⌋₊ + 1)).filter
        (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l), a n * g ↑n) =
        (∑ n ∈ (Finset.range (⌊l⌋₊ + 1)).filter
        (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l), a n) * g l := by
      calc (∑ n ∈ (Finset.range (⌊l⌋₊ + 1)).filter
              (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l), a n * g ↑n)
          = ∑ n ∈ (Finset.range (⌊l⌋₊ + 1)).filter
              (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l), a n * g l :=
            Finset.sum_congr rfl fun n hn => by rw [hSl n hn]
        _ = _ := (Finset.sum_mul _ _ _).symm
    have hfin : r - l = 0 := by rw [← hlr_eq, sub_self]
    rw [hSeq, hInt, sub_zero, hsum]
    calc ‖(∑ n ∈ (Finset.range (⌊l⌋₊ + 1)).filter
            (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l), a n) * g l‖
        ≤ ‖∑ n ∈ (Finset.range (⌊l⌋₊ + 1)).filter
            (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ l), a n‖ * ‖g l‖ :=
          le_of_eq (norm_mul _ _)
      _ ≤ E * B := mul_le_mul hE0 (hgb l hmeml) (norm_nonneg _) hE
      _ ≤ 2 * E * (B + K * (r - l)) := by
          rw [hfin]
          simp only [mul_zero, add_zero]
          nlinarith [mul_nonneg hE hB]
  · -- Proper interval: Abel summation on a uniform partition.
    have hlt : l < r := lt_of_le_of_ne hlr hlr_eq
    have hgLip : LipschitzOnWith (Real.toNNReal K) g (Set.Icc l r) :=
      LipschitzOnWith.of_dist_le' fun x hx y hy => by
        have h := hg x hx y hy
        rwa [dist_eq_norm, Real.dist_eq]
    have hgCont : ContinuousOn g (Set.Icc l r) := hgLip.continuousOn
    have hqgCont : ContinuousOn (fun y => q y * g y) (Set.Icc l r) :=
      hq.mul hgCont
    have hqnCont : ContinuousOn (fun y => ‖q y‖) (Set.Icc l r) := hq.norm
    have hFilt : ∀ s : ℝ, l ≤ s → s ≤ r →
        (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s) =
        (Finset.range (⌊s⌋₊ + 1)).filter (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s) := by
      intro s hs1 hs2
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have hs' : n ≤ ⌊s⌋₊ := Nat.le_floor h3
        have hs'' : n < ⌊s⌋₊ + 1 := by omega
        exact ⟨hs'', h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        have h1' : n ≤ ⌊s⌋₊ := by
          have : n < ⌊s⌋₊ + 1 := h1
          omega
        have hnsR : (n : ℝ) ≤ (⌊s⌋₊ : ℝ) := by exact_mod_cast h1'
        have hsR : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le (le_trans (le_trans hM.le hl) hs1)
        have hr' : n < ⌊r⌋₊ + 1 := by
          have h2' : n ≤ ⌊r⌋₊ := Nat.le_floor (hnsR.trans (hsR.trans hs2))
          omega
        exact ⟨hr', h2, h3⟩
    have hD : ∀ s ∈ Set.Icc l r,
        ‖(∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
            (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ s), a n) -
          (∫ y in l..s, q y)‖ ≤ E := by
      intro s hs
      rw [hFilt s hs.1 hs.2]
      exact hcount s hs
    -- Epsilon argument over the mesh.
    apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    have hεpos : 0 < c - 2 * E * (B + K * (r - l)) := sub_pos.mpr hc
    have hT₁nn : 0 ≤ ∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
        (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r), ‖a n‖ :=
      Finset.sum_nonneg fun n _ => norm_nonneg _
    have hT₂nn : 0 ≤ ∫ y in l..r, ‖q y‖ := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hlr
      exact Filter.Eventually.of_forall fun y => norm_nonneg _
    set ε : ℝ := c - 2 * E * (B + K * (r - l)) with hεdef
    set T₁ : ℝ := ∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
      (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r), ‖a n‖ with hT₁
    set T₂ : ℝ := ∫ y in l..r, ‖q y‖ with hT₂
    have hVnn : 0 ≤ K * (r - l) * (T₁ + T₂) :=
      mul_nonneg (mul_nonneg hK (sub_nonneg.mpr hlr)) (add_nonneg hT₁nn hT₂nn)
    set V : ℝ := K * (r - l) * (T₁ + T₂) with hV
    set N : ℕ := ⌊V / ε⌋₊ with hNdef
    have hNε : V / ε < (N : ℝ) + 1 := by
      rw [hNdef]
      exact Nat.lt_floor_add_one _
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hNne : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hNpos
    set d : ℝ := (r - l) / ((N : ℝ) + 1) with hd
    have hd_nn : 0 ≤ d := div_nonneg (sub_nonneg.mpr hlr) (le_of_lt hNpos)
    have hNd : d * ((N : ℝ) + 1) = r - l := by
      rw [hd]
      exact div_mul_cancel₀ _ hNne
    set p : ℕ → ℝ := fun i => l + d * (i : ℝ) with hp_def
    have hp0 : p 0 = l := by simp [hp_def]
    have hprN : p (N + 1) = r := by
      have cN : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by simp
      have h1 : l + d * (((N + 1 : ℕ)) : ℝ) = r := by
        rw [cN]
        linarith [hNd]
      simpa [hp_def] using h1
    have hmem : ∀ i, i ≤ N + 1 → l ≤ p i ∧ p i ≤ r := by
      intro i hi
      have hiR : (i : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hi
      constructor
      · simp only [hp_def]
        have h1 : 0 ≤ d * (i : ℝ) := mul_nonneg hd_nn (Nat.cast_nonneg i)
        linarith
      · simp only [hp_def]
        have h1 : d * (i : ℝ) ≤ d * ((N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hiR hd_nn
        linarith [h1, hNd]
    have hmono : ∀ i, p i ≤ p (i + 1) := by
      intro i
      have c : (((i + 1 : ℕ)) : ℝ) = (i : ℝ) + 1 := by simp
      simp only [hp_def]
      rw [c]
      have h1 : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hd_nn
      linarith
    have hmesh : ∀ i, i < N + 1 → p (i + 1) - p i ≤ d := by
      intro i hi
      have c : (((i + 1 : ℕ)) : ℝ) = (i : ℝ) + 1 := by simp
      have e : p (i + 1) - p i = d := by
        simp only [hp_def]
        rw [c]
        ring
      linarith [e]
    set F : ℕ → Finset ℕ := fun i => (Finset.range (⌊r⌋₊ + 1)).filter
      (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ p i) with hFdef
    have hFsub : ∀ i, i < N + 1 → F i ⊆ F (i + 1) := by
      intro i hi n hn
      have hn' : n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
          (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ p i) := by
        simpa [hFdef] using hn
      have hnb := (Finset.mem_filter.mp hn').2
      have hsub : n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
          (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ p (i + 1)) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn').1,
          hnb.1, hnb.2.trans (hmono i)⟩
      simpa [hFdef] using hsub
    have hFmem : ∀ (i : ℕ) (n : ℕ), n ∈ F i → l ≤ (n : ℝ) ∧ (n : ℝ) ≤ p i := by
      intro i n hn
      have hn' : n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
          (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ p i) := by
        simpa [hFdef] using hn
      exact (Finset.mem_filter.mp hn').2
    have hFN : (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r) =
        F (N + 1) := by
      have e : F (N + 1) = (Finset.range (⌊r⌋₊ + 1)).filter
          (fun (n : ℕ) => l ≤ (n : ℝ) ∧ (n : ℝ) ≤ p (N + 1)) := rfl
      rw [e, hprN]
    have hDi : ∀ i, i ≤ N + 1 → ‖(∑ n ∈ F i, a n) - (∫ y in l..p i, q y)‖ ≤ E := by
      intro i hi
      have hmem' : p i ∈ Set.Icc l r := Set.mem_Icc.mpr (hmem i hi)
      have hbase := hD (p i) hmem'
      simpa [hFdef] using hbase
    have hgi : ∀ i, i ≤ N + 1 → ‖g (p i)‖ ≤ B := fun i hi =>
      hgb _ (Set.mem_Icc.mpr (hmem i hi))
    have hgdiff : ∀ i, i < N + 1 → ‖g (p (i + 1)) - g (p i)‖ ≤ K * d := by
      intro i hi
      have hi1 : i + 1 ≤ N + 1 := hi
      have h1 := hg _ (Set.mem_Icc.mpr (hmem (i + 1) hi1))
        _ (Set.mem_Icc.mpr (hmem i (le_trans (Nat.le_succ i) hi1)))
      have h2 : |p (i + 1) - p i| ≤ d := by
        rw [abs_le]
        constructor <;> linarith [hmesh i hi, hd_nn, hmono i]
      calc ‖g (p (i + 1)) - g (p i)‖ ≤ K * |p (i + 1) - p i| := h1
        _ ≤ K * d := mul_le_mul_of_nonneg_left h2 hK
    -- Exact per-cell identities.
    have emini : ∀ (s : Finset ℕ) (c : ℂ), (∑ n ∈ s, (a n * g ↑n - c * a n)) =
        (∑ n ∈ s, a n * g ↑n) - c * (∑ n ∈ s, a n) := by
      intro s c
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hchainw : (∑ n ∈ F (N + 1), a n * g ↑n) =
        (∑ n ∈ F 0, a n * g ↑n) +
        ∑ i ∈ Finset.range (N + 1), ((∑ n ∈ F (i + 1), a n * g ↑n) -
          (∑ n ∈ F i, a n * g ↑n)) :=
      sum_chain_decomp F (fun n => a n * g ↑n) _ hFsub
    have hchainn : (∑ n ∈ F (N + 1), ‖a n‖) =
        (∑ n ∈ F 0, ‖a n‖) +
        ∑ i ∈ Finset.range (N + 1), ((∑ n ∈ F (i + 1), ‖a n‖) -
          (∑ n ∈ F i, ‖a n‖)) :=
      sum_chain_decomp F (fun n => ‖a n‖) _ hFsub
    have hcell_eq : ∀ i ∈ Finset.range (N + 1),
        ((∑ n ∈ F (i + 1), a n * g ↑n) - (∑ n ∈ F i, a n * g ↑n)) -
          g (p (i + 1)) * ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n)) =
        ∑ n ∈ (F (i + 1) \ F i), (a n * g ↑n - g (p (i + 1)) * a n) := by
      intro i hi
      have h1 := Finset.sum_sdiff (hFsub i (Finset.mem_range.mp hi))
        (f := fun n => a n * g ↑n)
      have h2 := Finset.sum_sdiff (hFsub i (Finset.mem_range.mp hi))
        (f := fun n => a n)
      have hW : (∑ n ∈ F (i + 1), a n * g ↑n) - (∑ n ∈ F i, a n * g ↑n) =
          ∑ n ∈ (F (i + 1) \ F i), a n * g ↑n := by
        linear_combination -h1
      have hA : (∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n) =
          ∑ n ∈ (F (i + 1) \ F i), a n := by
        linear_combination -h2
      have e := emini (F (i + 1) \ F i) (g (p (i + 1)))
      rw [hW, hA]
      exact e.symm
    have hsd : ∀ i ∈ Finset.range (N + 1),
        (∑ n ∈ F (i + 1), ‖a n‖) - (∑ n ∈ F i, ‖a n‖) =
        ∑ n ∈ (F (i + 1) \ F i), ‖a n‖ := by
      intro i hi
      have h1 := Finset.sum_sdiff (hFsub i (Finset.mem_range.mp hi))
        (f := fun n => ‖a n‖)
      linear_combination -h1
    -- E1: discrete step error assembly and bound.
    have hE1eq : (∑ n ∈ F (N + 1), a n * g ↑n) -
        (g (p 1) * (∑ n ∈ F 0, a n) +
          ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n))) =
        (∑ n ∈ F 0, (a n * g ↑n - g (p 1) * a n)) +
        ∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i),
          (a n * g ↑n - g (p (i + 1)) * a n) := by
      have e0 : (∑ n ∈ F 0, a n * g ↑n) - g (p 1) * (∑ n ∈ F 0, a n) =
          ∑ n ∈ F 0, (a n * g ↑n - g (p 1) * a n) := (emini _ _).symm
      have eS : (∑ i ∈ Finset.range (N + 1), ((∑ n ∈ F (i + 1), a n * g ↑n) -
          (∑ n ∈ F i, a n * g ↑n))) -
          (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n))) =
          ∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i),
            (a n * g ↑n - g (p (i + 1)) * a n) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i hi => hcell_eq i hi
      rw [hchainw]
      linear_combination e0 + eS
    -- Diff-cell locations.
    have hdiffmem : ∀ (i : ℕ) (n : ℕ), n ∈ F (i + 1) \ F i →
        p i < (n : ℝ) ∧ (n : ℝ) ≤ p (i + 1) := by
      intro i n hn
      have hnmem := (Finset.mem_sdiff.mp hn).1
      have hni := (Finset.mem_sdiff.mp hn).2
      have hnb := hFmem (i + 1) n hnmem
      have hnge : p i < (n : ℝ) := by
        by_contra hcon
        push_neg at hcon
        have hrange : n ∈ Finset.range (⌊r⌋₊ + 1) := by
          have h1 : n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
              (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ p (i + 1)) := by
            simpa [hFdef] using hnmem
          exact (Finset.mem_filter.mp h1).1
        have hin : n ∈ F i := by
          have h2 : n ∈ (Finset.range (⌊r⌋₊ + 1)).filter
              (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ p i) :=
            Finset.mem_filter.mpr ⟨hrange, hnb.1, hcon⟩
          simpa [hFdef] using h2
        exact hni hin
      exact ⟨hnge, hnb.2⟩
    -- Per-atom estimate.
    have hatom : ∀ (n : ℕ) (c : ℝ), (n : ℝ) ∈ Set.Icc l r → c ∈ Set.Icc l r →
        |(n : ℝ) - c| ≤ d → ‖a n * g ↑n - g c * a n‖ ≤ (K * d) * ‖a n‖ := by
      intro n c hn hc hdcell
      have eatom : a n * g ↑n - g c * a n = a n * (g ↑n - g c) := by ring
      have hglip : ‖g ↑n - g c‖ ≤ K * d := by
        calc ‖g ↑n - g c‖ ≤ K * |(n : ℝ) - c| := hg _ hn _ hc
          _ ≤ K * d := mul_le_mul_of_nonneg_left hdcell hK
      calc ‖a n * g ↑n - g c * a n‖ = ‖a n‖ * ‖g ↑n - g c‖ := by
            rw [eatom, norm_mul]
        _ ≤ ‖a n‖ * (K * d) := mul_le_mul_of_nonneg_left hglip (norm_nonneg _)
        _ = (K * d) * ‖a n‖ := by ring
    have hE1bound : ‖(∑ n ∈ F (N + 1), a n * g ↑n) -
        (g (p 1) * (∑ n ∈ F 0, a n) +
          ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n)))‖ ≤
        K * d * T₁ := by
      have hT1chain : (∑ n ∈ F 0, ‖a n‖) +
          (∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i), ‖a n‖) =
          ∑ n ∈ F (N + 1), ‖a n‖ := by
        have hch2 : (∑ i ∈ Finset.range (N + 1), ((∑ n ∈ F (i + 1), ‖a n‖) -
            (∑ n ∈ F i, ‖a n‖))) =
            ∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i), ‖a n‖ :=
          Finset.sum_congr rfl fun i hi => hsd i hi
        rw [← hch2]
        exact hchainn.symm
      have hT1 : (∑ n ∈ F (N + 1), ‖a n‖) = T₁ := by
        rw [hT₁, hFN]
      have hC0 : ‖∑ n ∈ F 0, (a n * g ↑n - g (p 1) * a n)‖ ≤
          (K * d) * (∑ n ∈ F 0, ‖a n‖) := by
        calc ‖∑ n ∈ F 0, (a n * g ↑n - g (p 1) * a n)‖
            ≤ ∑ n ∈ F 0, ‖a n * g ↑n - g (p 1) * a n‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ F 0, (K * d) * ‖a n‖ := by
              apply Finset.sum_le_sum
              intro n hn
              have hnb := hFmem 0 n hn
              have hn0le : (n : ℝ) ≤ l := by
                have hle := hnb.2
                rw [hp0] at hle
                exact hle
              have hnl : (n : ℝ) = l := le_antisymm hn0le hnb.1
              have hnlr : (n : ℝ) ∈ Set.Icc l r :=
                Set.mem_Icc.mpr ⟨hnb.1, le_trans hnl.le hlr⟩
              have hp1mem : p 1 ∈ Set.Icc l r :=
                Set.mem_Icc.mpr (hmem 1 (by omega))
              have hdist : |(n : ℝ) - p 1| ≤ d := by
                have hm0 : p 1 - p 0 ≤ d := hmesh 0 (by omega)
                have hmo0 : p 0 ≤ p 1 := hmono 0
                rw [abs_le]
                constructor
                · linarith [hm0, hmo0, hnl, hp0, hd_nn]
                · linarith [hm0, hmo0, hnl, hp0, hd_nn]
              exact hatom n (p 1) hnlr hp1mem hdist
          _ = (K * d) * (∑ n ∈ F 0, ‖a n‖) := by rw [← Finset.mul_sum]
      have hCc : ‖∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i),
            (a n * g ↑n - g (p (i + 1)) * a n)‖ ≤
          (K * d) * (∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i), ‖a n‖) := by
        calc ‖∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i),
                (a n * g ↑n - g (p (i + 1)) * a n)‖
            ≤ ∑ i ∈ Finset.range (N + 1),
                ‖∑ n ∈ (F (i + 1) \ F i), (a n * g ↑n - g (p (i + 1)) * a n)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (N + 1),
                (K * d) * (∑ n ∈ (F (i + 1) \ F i), ‖a n‖) := by
              apply Finset.sum_le_sum
              intro i hi
              calc ‖∑ n ∈ (F (i + 1) \ F i), (a n * g ↑n - g (p (i + 1)) * a n)‖
                  ≤ ∑ n ∈ (F (i + 1) \ F i), ‖a n * g ↑n - g (p (i + 1)) * a n‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ n ∈ (F (i + 1) \ F i), (K * d) * ‖a n‖ := by
                    apply Finset.sum_le_sum
                    intro n hn
                    have hcell := hdiffmem i n hn
                    have hiN : i < N + 1 := Finset.mem_range.mp hi
                    have hi1 : i + 1 ≤ N + 1 := hiN
                    have hnlr : (n : ℝ) ∈ Set.Icc l r :=
                      Set.mem_Icc.mpr ⟨le_trans (hmem i (by omega)).1 (le_of_lt hcell.1),
                        le_trans hcell.2 (hmem (i + 1) hi1).2⟩
                    have hpmem : p (i + 1) ∈ Set.Icc l r :=
                      Set.mem_Icc.mpr (hmem (i + 1) hi1)
                    have hdist : |(n : ℝ) - p (i + 1)| ≤ d := by
                      rw [abs_le]
                      constructor
                      · linarith [(le_of_lt hcell.1), hmesh i hiN, hd_nn]
                      · linarith [hcell.2, hd_nn]
                    exact hatom n (p (i + 1)) hnlr hpmem hdist
                _ = (K * d) * (∑ n ∈ (F (i + 1) \ F i), ‖a n‖) := by
                    rw [← Finset.mul_sum]
          _ = (K * d) * (∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i), ‖a n‖) := by
              rw [← Finset.mul_sum]
      rw [hE1eq]
      refine (norm_add_le _ _).trans ?_
      calc ‖(∑ n ∈ F 0, (a n * g ↑n - g (p 1) * a n))‖ +
              ‖∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i),
                (a n * g ↑n - g (p (i + 1)) * a n)‖
          ≤ ((K * d) * (∑ n ∈ F 0, ‖a n‖)) +
              ((K * d) * (∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i), ‖a n‖)) :=
            add_le_add hC0 hCc
        _ = (K * d) * ((∑ n ∈ F 0, ‖a n‖) +
              (∑ i ∈ Finset.range (N + 1), ∑ n ∈ (F (i + 1) \ F i), ‖a n‖)) := by
            ring
        _ = K * d * T₁ := by rw [hT1chain, hT1]
    -- TD: telescoped difference via summation by parts.
    have hQ0 : (∫ y in l..p 0, q y) = 0 := by
      rw [hp0]
      exact intervalIntegral.integral_same
    have hQcell : ∀ i ∈ Finset.range (N + 1),
        (∫ y in p i..p (i + 1), q y) =
          (∫ y in l..p (i + 1), q y) - (∫ y in l..p i, q y) := by
      intro i hi
      have hiN : i < N + 1 := Finset.mem_range.mp hi
      have hi1 : i + 1 ≤ N + 1 := hiN
      have hi1' : i ≤ N + 1 := by omega
      have h1 : l ≤ p i := (hmem i hi1').1
      have h1r : p i ≤ r := (hmem i hi1').2
      have h2 : p i ≤ p (i + 1) := hmono i
      have h3 : p (i + 1) ≤ r := (hmem (i + 1) hi1).2
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (continuousOn_intervalIntegrable_sub hq le_rfl h1 h1r)
        (continuousOn_intervalIntegrable_sub hq h1 h2 h3)
      linear_combination hadj
    have hstepQ' : (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y)) =
        ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
          ((∫ y in l..p (i + 1), q y) - (∫ y in l..p i, q y)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hQcell i hi]
    have hsbp : g (p 1) * ((∑ n ∈ F 0, a n) - (∫ y in l..p 0, q y)) +
        ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
          (((∑ n ∈ F (i + 1), a n) - (∫ y in l..p (i + 1), q y)) -
            ((∑ n ∈ F i, a n) - (∫ y in l..p i, q y))) =
        (g (p (N + 1)) * ((∑ n ∈ F (N + 1), a n) - (∫ y in l..p (N + 1), q y))) -
        ∑ i ∈ Finset.Ioo 0 (N + 1), ((∑ n ∈ F i, a n) - (∫ y in l..p i, q y)) *
          (g (p (i + 1)) - g (p i)) :=
      summation_by_parts (fun i => g (p i))
        (fun i => (∑ n ∈ F i, a n) - (∫ y in l..p i, q y)) N
    have hTD : (g (p 1) * (∑ n ∈ F 0, a n) +
          ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n))) -
        (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y)) =
        (g (p 1) * ((∑ n ∈ F 0, a n) - (∫ y in l..p 0, q y)) +
          ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            (((∑ n ∈ F (i + 1), a n) - (∫ y in l..p (i + 1), q y)) -
              ((∑ n ∈ F i, a n) - (∫ y in l..p i, q y)))) := by
      have eS : (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n))) -
          (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            ((∫ y in l..p (i + 1), q y) - (∫ y in l..p i, q y))) =
          ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            (((∑ n ∈ F (i + 1), a n) - (∫ y in l..p (i + 1), q y)) -
              ((∑ n ∈ F i, a n) - (∫ y in l..p i, q y))) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have eQ : g (p 1) * (∑ n ∈ F 0, a n) =
          g (p 1) * ((∑ n ∈ F 0, a n) - (∫ y in l..p 0, q y)) := by
        rw [hQ0, sub_zero]
      rw [hstepQ']
      linear_combination eQ + eS
    have hTDbound : ‖(g (p 1) * (∑ n ∈ F 0, a n) +
          ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
            ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n))) -
        (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y))‖ ≤
        E * B + E * K * (r - l) := by
      rw [hTD, hsbp]
      have hb1 : ‖g (p (N + 1)) * ((∑ n ∈ F (N + 1), a n) - (∫ y in l..p (N + 1), q y))‖ ≤
          E * B := by
        calc ‖g (p (N + 1)) * ((∑ n ∈ F (N + 1), a n) - (∫ y in l..p (N + 1), q y))‖
            ≤ ‖g (p (N + 1))‖ * ‖(∑ n ∈ F (N + 1), a n) - (∫ y in l..p (N + 1), q y)‖ :=
              le_of_eq (norm_mul _ _)
          _ ≤ B * E :=
              mul_le_mul (hgi _ le_rfl) (hDi _ le_rfl) (norm_nonneg _) hB
          _ = E * B := by ring
      have hb2 : ‖∑ i ∈ Finset.Ioo 0 (N + 1), ((∑ n ∈ F i, a n) - (∫ y in l..p i, q y)) *
            (g (p (i + 1)) - g (p i))‖ ≤ E * K * (r - l) := by
        calc ‖∑ i ∈ Finset.Ioo 0 (N + 1), ((∑ n ∈ F i, a n) - (∫ y in l..p i, q y)) *
                (g (p (i + 1)) - g (p i))‖
            ≤ ∑ i ∈ Finset.Ioo 0 (N + 1),
                ‖((∑ n ∈ F i, a n) - (∫ y in l..p i, q y)) * (g (p (i + 1)) - g (p i))‖ :=
              norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.Ioo 0 (N + 1), E * (K * d) := by
              apply Finset.sum_le_sum
              intro i hi
              have hiN : i < N + 1 := (Finset.mem_Ioo.mp hi).2
              calc ‖((∑ n ∈ F i, a n) - (∫ y in l..p i, q y)) * (g (p (i + 1)) - g (p i))‖
                  ≤ ‖(∑ n ∈ F i, a n) - (∫ y in l..p i, q y)‖ * ‖g (p (i + 1)) - g (p i)‖ :=
                    le_of_eq (norm_mul _ _)
                _ ≤ E * (K * d) :=
                    mul_le_mul (hDi i (by omega)) (hgdiff i hiN) (norm_nonneg _) hE
          _ ≤ ∑ i ∈ Finset.range (N + 1), E * (K * d) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => mul_nonneg hE (mul_nonneg hK hd_nn))
              intro x hx
              exact Finset.mem_range.mpr (by have := Finset.mem_Ioo.mp hx; omega)
          _ = E * K * (r - l) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by simp
              rw [hcast]
              have hNd' : ((N : ℝ) + 1) * d = r - l := by
                rw [mul_comm ((N : ℝ) + 1) d]
                exact hNd
              calc ((N : ℝ) + 1) * (E * (K * d)) = E * K * (((N : ℝ) + 1) * d) := by ring
                _ = E * K * (r - l) := by rw [hNd']
      refine (norm_sub_le _ _).trans ?_
      exact add_le_add hb1 hb2
    -- E2: continuous step error.
    have hsplit_qg : (∑ i ∈ Finset.range (N + 1), ∫ y in p i..p (i + 1), q y * g y) =
        ∫ y in l..r, q y * g y := by
      have h := interval_split_of_continuousOn hqgCont p (N + 1) hp0 hmem hmono
      rw [hp0, hprN] at h
      exact h
    have hsplit_n : (∑ i ∈ Finset.range (N + 1), ∫ y in p i..p (i + 1), ‖q y‖) =
        ∫ y in l..r, ‖q y‖ := by
      have h := interval_split_of_continuousOn hqnCont p (N + 1) hp0 hmem hmono
      rw [hp0, hprN] at h
      exact h
    have hcell : ∀ i ∈ Finset.range (N + 1),
        ‖g (p (i + 1)) * (∫ y in p i..p (i + 1), q y) -
          (∫ y in p i..p (i + 1), q y * g y)‖ ≤
        K * d * (∫ y in p i..p (i + 1), ‖q y‖) := by
      intro i hi
      have hiN : i < N + 1 := Finset.mem_range.mp hi
      have hi1 : i + 1 ≤ N + 1 := hiN
      have hlo_i : l ≤ p i := (hmem i (by omega)).1
      have hhi_i : p i ≤ r := (hmem i (by omega)).2
      have hlo_i1 : l ≤ p (i + 1) := (hmem (i + 1) hi1).1
      have hhi_i1 : p (i + 1) ≤ r := (hmem (i + 1) hi1).2
      have hle_i : p i ≤ p (i + 1) := hmono i
      have hcont1 : ContinuousOn (fun y => g (p (i + 1)) * q y) (Set.Icc l r) :=
        continuousOn_const.mul hq
      have hcont2 : ContinuousOn (fun y => q y * g y) (Set.Icc l r) := hqgCont
      have hcontN : ContinuousOn
          (fun y => ‖g (p (i + 1)) * q y - q y * g y‖) (Set.Icc l r) :=
        continuous_norm.comp_continuousOn
          ((continuousOn_const.mul hq).sub hqgCont)
      have hcontK : ContinuousOn (fun y => K * d * ‖q y‖) (Set.Icc l r) :=
        continuousOn_const.mul hqnCont
      have e1 : g (p (i + 1)) * (∫ y in p i..p (i + 1), q y) =
          ∫ y in p i..p (i + 1), g (p (i + 1)) * q y :=
        (intervalIntegral.integral_const_mul _ _).symm
      rw [e1]
      have e2 : (∫ y in p i..p (i + 1), g (p (i + 1)) * q y) -
          (∫ y in p i..p (i + 1), q y * g y) =
          ∫ y in p i..p (i + 1), (g (p (i + 1)) * q y - q y * g y) :=
        (intervalIntegral.integral_sub
          (continuousOn_intervalIntegrable_sub hcont1 hlo_i hle_i hhi_i1)
          (continuousOn_intervalIntegrable_sub hcont2 hlo_i hle_i hhi_i1)).symm
      rw [e2]
      calc ‖∫ y in p i..p (i + 1), (g (p (i + 1)) * q y - q y * g y)‖
          ≤ ∫ y in p i..p (i + 1), ‖g (p (i + 1)) * q y - q y * g y‖ :=
            intervalIntegral.norm_integral_le_integral_norm hle_i
        _ ≤ ∫ y in p i..p (i + 1), K * d * ‖q y‖ := by
            apply intervalIntegral.integral_mono_on hle_i _ _ _
            · exact continuousOn_intervalIntegrable_sub hcontN hlo_i hle_i hhi_i1
            · exact continuousOn_intervalIntegrable_sub hcontK hlo_i hle_i hhi_i1
            · intro y hy
              have hymem : y ∈ Set.Icc l r :=
                Set.mem_Icc.mpr ⟨le_trans hlo_i hy.1, le_trans hy.2 hhi_i1⟩
              have hpmem : p (i + 1) ∈ Set.Icc l r :=
                Set.mem_Icc.mpr ⟨hlo_i1, hhi_i1⟩
              have hdist : |y - p (i + 1)| ≤ d := by
                have hy_le : y ≤ p (i + 1) := hy.2
                have hy_ge : p i ≤ y := hy.1
                have hm := hmesh i hiN
                rw [abs_le]
                constructor
                · linarith [hm, hy_ge, hle_i, hd_nn]
                · linarith [hy_ge, hle_i, hd_nn]
              have hglip : ‖g (p (i + 1)) - g y‖ ≤ K * d := by
                have hglip' : ‖g y - g (p (i + 1))‖ ≤ K * d := by
                  calc ‖g y - g (p (i + 1))‖ ≤ K * |y - p (i + 1)| :=
                        hg _ hymem _ hpmem
                    _ ≤ K * d := mul_le_mul_of_nonneg_left hdist hK
                rwa [norm_sub_rev] at hglip'
              calc ‖g (p (i + 1)) * q y - q y * g y‖
                  = ‖q y‖ * ‖g (p (i + 1)) - g y‖ := by
                    have e3 : g (p (i + 1)) * q y - q y * g y =
                        q y * (g (p (i + 1)) - g y) := by ring
                    rw [e3, norm_mul]
                _ ≤ ‖q y‖ * (K * d) :=
                    mul_le_mul_of_nonneg_left hglip (norm_nonneg _)
                _ = K * d * ‖q y‖ := by ring
        _ = K * d * (∫ y in p i..p (i + 1), ‖q y‖) :=
            intervalIntegral.integral_const_mul _ _
    have hE2eq : (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y)) -
        (∑ i ∈ Finset.range (N + 1), ∫ y in p i..p (i + 1), q y * g y) =
        ∑ i ∈ Finset.range (N + 1), (g (p (i + 1)) * (∫ y in p i..p (i + 1), q y) -
          (∫ y in p i..p (i + 1), q y * g y)) := by
      rw [← Finset.sum_sub_distrib]
    have hE2bound : ‖(∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y)) -
        (∫ y in l..r, q y * g y)‖ ≤ K * d * T₂ := by
      rw [← hsplit_qg, hE2eq]
      calc ‖∑ i ∈ Finset.range (N + 1), (g (p (i + 1)) * (∫ y in p i..p (i + 1), q y) -
              (∫ y in p i..p (i + 1), q y * g y))‖
          ≤ ∑ i ∈ Finset.range (N + 1),
              ‖g (p (i + 1)) * (∫ y in p i..p (i + 1), q y) -
                (∫ y in p i..p (i + 1), q y * g y)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (N + 1), K * d * (∫ y in p i..p (i + 1), ‖q y‖) :=
            Finset.sum_le_sum fun i hi => hcell i hi
        _ = K * d * T₂ := by
            rw [← Finset.mul_sum, hsplit_n, ← hT₂]
    have hC0C : E * B + E * K * (r - l) ≤ 2 * E * (B + K * (r - l)) := by
      have h1 : 0 ≤ E * B := mul_nonneg hE hB
      have h2 : 0 ≤ E * K * (r - l) := mul_nonneg (mul_nonneg hE hK) (sub_nonneg.mpr hlr)
      linarith
    have hVN : V / ((N : ℝ) + 1) ≤ ε := by
      have h3 : V < ((N : ℝ) + 1) * ε := (div_lt_iff₀ hεpos).mp hNε
      have h4 : V ≤ ε * ((N : ℝ) + 1) := by linarith
      exact (div_le_iff₀ hNpos).mpr h4
    have hKd : K * d * (T₁ + T₂) = V / ((N : ℝ) + 1) := by
      rw [hV, hd]
      field_simp
    have hmesh_le : K * d * (T₁ + T₂) ≤ ε := by
      rw [hKd]
      exact hVN
    have hFinal : ‖(∑ n ∈ F (N + 1), a n * g ↑n) - (∫ y in l..r, q y * g y)‖ ≤
        (E * B + E * K * (r - l)) + K * d * (T₁ + T₂) := by
      have hsplit3 : ((∑ n ∈ F (N + 1), a n * g ↑n) -
          (g (p 1) * (∑ n ∈ F 0, a n) +
            ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
              ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n)))) +
          (((g (p 1) * (∑ n ∈ F 0, a n) +
            ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
              ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n))) -
          (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y))) +
          ((∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y)) -
            (∫ y in l..r, q y * g y))) =
          (∑ n ∈ F (N + 1), a n * g ↑n) - (∫ y in l..r, q y * g y) := by
        abel
      rw [← hsplit3]
      refine (norm_add_le _ _).trans ?_
      calc ‖(∑ n ∈ F (N + 1), a n * g ↑n) -
                (g (p 1) * (∑ n ∈ F 0, a n) +
                  ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
                    ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n)))‖ +
              ‖((g (p 1) * (∑ n ∈ F 0, a n) +
                ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
                  ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n))) -
              (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y))) +
                ((∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y)) -
                  (∫ y in l..r, q y * g y))‖
          ≤ ‖(∑ n ∈ F (N + 1), a n * g ↑n) -
                (g (p 1) * (∑ n ∈ F 0, a n) +
                  ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
                    ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n)))‖ +
              (‖(g (p 1) * (∑ n ∈ F 0, a n) +
                ∑ i ∈ Finset.range (N + 1), g (p (i + 1)) *
                  ((∑ n ∈ F (i + 1), a n) - (∑ n ∈ F i, a n))) -
              (∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y))‖ +
              ‖(∑ i ∈ Finset.range (N + 1), g (p (i + 1)) * (∫ y in p i..p (i + 1), q y)) -
                (∫ y in l..r, q y * g y)‖) :=
            add_le_add le_rfl (norm_add_le _ _)
        _ ≤ (K * d * T₁) + ((E * B + E * K * (r - l)) + (K * d * T₂)) :=
            add_le_add hE1bound (add_le_add hTDbound hE2bound)
        _ = (E * B + E * K * (r - l)) + K * d * (T₁ + T₂) := by ring
    rw [hFN]
    -- hFinal is about F-sums; the goal also needs the r-filter form restored for T₁.
    -- T₁ is already the r-form by set; hFinal's T₁ matches. Conclude:
    have hdone : (E * B + E * K * (r - l)) + K * d * (T₁ + T₂) ≤ c := by
      linarith [hC0C, hmesh_le, hεdef]
    exact hFinal.trans hdone

end ArtinPrimitiveRoots.Proofs.r_impl_muse
