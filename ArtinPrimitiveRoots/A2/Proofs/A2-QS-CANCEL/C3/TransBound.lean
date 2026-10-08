import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Trans
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Estimate

/-!
# The bound for one dual transition block

`pair_mellin_bound` with the Mellin form of the transition weight (`trans_weight_eq`), the
majorant `(M/E) √(2Λn) zb ‖D‖/(2π)` (from `u ≤ zhi`), the up-to norms through duality and
`HasExponent α`, and the scalar estimate `E3_estimate`.  Blocks whose divisor dyad exceeds the
dual cutoff vanish (the majorant is cut by the same indicator).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSC3

open QSC2 QSP2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

theorem zhi_eq {M n Λ E A : ℝ} (hn : 0 ≤ n) :
    zhi M n Λ E A = 2 * Λ * (n * Real.sqrt (E / (M * A))) := by
  unfold zhi
  rw [show E * n ^ 2 / (M * A) = n ^ 2 * (E / (M * A)) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hn]

theorem zhi_anti {M n Λ E A A' : ℝ} (hM : 0 < M) (hE : 0 ≤ E) (hΛ : 0 ≤ Λ) (hn : 0 ≤ n)
    (hA : 0 < A) (hAA' : A ≤ A') : zhi M n Λ E A' ≤ zhi M n Λ E A := by
  rw [zhi_eq hn, zhi_eq hn]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hn)
    (by positivity)
  exact div_le_div_of_nonneg_left hE (by positivity) (mul_le_mul_of_nonneg_left hAA' hM.le)

theorem cinv_le {M n Λ E A u : ℝ} (hM : 0 < M) (hE : 0 < E) (hA : 0 < A) (hu : 0 < u)
    (hΛ : 0 < Λ) (hn : 0 < n) (hzhi : u ≤ zhi M n Λ E A) :
    (Real.sqrt (E / (M * A)) / u) ^ (-(1/2 : ℝ)) ≤ Real.sqrt (2 * Λ * n) := by
  have hs : 0 < Real.sqrt (E / (M * A)) := Real.sqrt_pos.mpr (by positivity)
  rw [zhi_eq hn.le] at hzhi
  have hc : 1 / (2 * Λ * n) ≤ Real.sqrt (E / (M * A)) / u := by
    rw [div_le_div_iff₀ (by positivity) hu]
    nlinarith
  calc (Real.sqrt (E / (M * A)) / u) ^ (-(1/2 : ℝ)) ≤ (1 / (2 * Λ * n)) ^ (-(1/2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hc (by norm_num)
    _ = Real.sqrt (2 * Λ * n) := by
        rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
          Real.sqrt_eq_rpow]

theorem norm_bound_hexp (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    {Cα ε α : ℝ} (hHE : ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → qsNorm F M N ≤ Cα * (M * N) ^ ε * (M + N ^ α))
    (hε : 0 < ε) (hCα : 0 < Cα) (hα : 0 < α) {n B D : ℝ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hD : 1 ≤ D) :
    qsNorm F (2 * B) (2 * n / D) ≤ Cα * (4 * n * B) ^ ε * (2 * n / D + 2 * (2 * B) ^ α) := by
  set X := max (2 * n / D) 1 with hX
  have hX1 : 1 ≤ X := le_max_right _ _
  have hX2n : X ≤ 2 * n := max_le (div_le_self (by positivity) hD) (by linarith)
  have h2Bα : 1 ≤ (2 * B) ^ α := Real.one_le_rpow (by linarith) hα.le
  calc qsNorm F (2 * B) (2 * n / D) ≤ qsNorm F (2 * B) X :=
        qs_norm_mono_M0 F le_rfl (le_max_left _ _)
    _ = qsNorm F X (2 * B) := qs_norm_symm_M0 F hrf _ _
    _ ≤ Cα * (X * (2 * B)) ^ ε * (X + (2 * B) ^ α) := hHE X (2 * B) hX1 (by linarith)
    _ ≤ Cα * (4 * n * B) ^ ε * (2 * n / D + 2 * (2 * B) ^ α) := by
        have h1 : (X * (2 * B)) ^ ε ≤ (4 * n * B) ^ ε :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) hε.le
        have h2 : X + (2 * B) ^ α ≤ 2 * n / D + 2 * (2 * B) ^ α := by
          have : X ≤ 2 * n / D + 1 := max_le (by linarith) (by
            have : 0 ≤ 2 * n / D := by positivity
            linarith)
          linarith
        have h0 : 0 ≤ X + (2 * B) ^ α := by positivity
        calc Cα * (X * (2 * B)) ^ ε * (X + (2 * B) ^ α)
            ≤ Cα * (4 * n * B) ^ ε * (X + (2 * B) ^ α) := by gcongr
          _ ≤ Cα * (4 * n * B) ^ ε * (2 * n / D + 2 * (2 * B) ^ α) := by gcongr

open Classical in
/-- The bound for one dual transition block `(e, a₂, k, j₁, j₂)`. -/
theorem block_bound [IsTotallyComplex K] (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (hexp : QSHasExponent F α) (ε : ℝ) (hε : 0 < ε) (η₂ : ℝ) (hη₂ : 0 < η₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M n κ Λ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
      (z : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K))) (R e a₂ : Ideal (𝓞 K)) (k j₁ j₂ : ℕ),
      0 < M → 1 ≤ n → 1 ≤ Λ → QSBlockCols m qS 𝔮 n cols → e ≠ ⊥ → (2 : ℝ) ^ k ≤ κ →
      1 ≤ qsN a₂ →
      ‖∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) *
          (((qsMu e : ℂ) * twist F c e * twist F c a₂) * (twistInv F d e * twistInv F d a₂) *
            ∑ e₁ ∈ (qsDivisors c).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₁),
              ∑ e₂ ∈ (qsDivisors d).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₂),
                (qsMu (e₁ * e₂) : ℂ) *
                  ∑ a₁ ∈ qsUpTo m qS (2 ^ (k + 1)),
                    rhoT S R a₂ k a₁ *
                      (F.character c).idealValue a₁ * (F.character d).idealValue a₁ *
                        phiT K W M n Λ (qsN e) (qsN a₂) k (2 ^ j₁ * 2 ^ j₂) (qsN a₁)
                          (qsN (e₁ * e₂)) (qsN (c * d))) else 0‖ ≤
        C * (n * 2 ^ k) ^ η₂ * (4 * n * 2 ^ k) ^ ε * Λ ^ (3/2 : ℝ) *
          (M + Real.sqrt M * κ ^ (α - 1/2)) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  obtain ⟨C₂, hC₂, hpair⟩ := pair_mellin_bound F hrf η₂ hη₂
  obtain ⟨Cα, hCα, hHE⟩ := hexp ε hε
  set P := caseBData (K := K) hW.1 with hPdef
  set CD := ∫ t : ℝ, ‖P.D (uL t)‖ with hCD
  have hCD0 : 0 ≤ CD := integral_nonneg fun t => norm_nonneg _
  set KD := zb K * CD / (2 * Real.pi) with hKD
  have hKD0 : 0 ≤ KD := by have := zb_nonneg (K := K); positivity
  refine ⟨C₂ * (KD + 1) * 64 * Cα, by positivity, ?_⟩
  intro M n κ Λ 𝔮 cols z S R e a₂ k j₁ j₂ hM hn hΛ hblock he hk ha₂
  obtain ⟨_, _, hcols, _⟩ := hblock
  have hn0 : 0 < n := by linarith
  have hΛ0 : 0 < Λ := by linarith
  set E := qsN e with hEdef
  have hE1 : 1 ≤ E := one_le_qsN he
  have hE0 : 0 < E := by linarith
  set A₂ := qsN a₂ with hA₂
  set B : ℝ := 2 ^ k with hBdef
  have hB1 : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hB0 : 0 < B := by linarith
  set D₁ : ℝ := 2 ^ j₁ with hD₁def
  set D₂ : ℝ := 2 ^ j₂ with hD₂def
  have hD₁ : 1 ≤ D₁ := one_le_pow₀ (by norm_num)
  have hD₂ : 1 ≤ D₂ := one_le_pow₀ (by norm_num)
  set ID : ℝ := if D₁ * D₂ ≤ zhi M n Λ E B then 1 else 0 with hID
  have hID0 : 0 ≤ ID := by rw [hID]; split_ifs <;> norm_num
  set g0 : ℝ := M / E * Real.sqrt (2 * Λ * n) / (2 * Real.pi) * zb K with hg0
  have hg00 : 0 ≤ g0 := by have := zb_nonneg (K := K); positivity
  set gmaj : ℝ → ℝ := fun t => ID * (g0 * ‖P.D (uL t)‖) with hgmaj
  set cnd : ℝ → ℝ → Prop := fun y u => 0 < y ∧ 0 < u ∧ ylo M n Λ E (A₂ * y) < u ∧
    u ≤ zhi M n Λ E (A₂ * y) ∧ (2 : ℝ) ^ k ≤ y ∧ D₁ * D₂ ≤ u with hcnd
  set φ : ℝ → ℝ → ℝ → ℂ := fun y u t =>
    if cnd y u then gT (F0 K W) P M E (A₂ * y) u t else 0 with hφ
  set Φ : ℝ → ℝ → ℝ → ℂ := fun y u x => phiT K W M n Λ E A₂ k (D₁ * D₂) y u x with hΦdef
  have hΦ : ∀ y u x : ℝ, 0 < x → Φ y u x = ∫ t, ((x : ℂ) ^ (sT t)) * φ y u t := by
    intro y u x hx
    simp only [hΦdef, hφ, phiT]
    by_cases h : cnd y u
    · have h' : 0 < y ∧ 0 < u ∧ ylo M n Λ E (A₂ * y) < u ∧ u ≤ zhi M n Λ E (A₂ * y) ∧
          (2 : ℝ) ^ k ≤ y ∧ D₁ * D₂ ≤ u := h
      rw [if_pos h']
      rw [wtT, trans_weight_eq P hM hE0 (mul_pos (by linarith) h'.1) h'.2.1 hx]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [if_pos h]
    · have h' : ¬ (0 < y ∧ 0 < u ∧ ylo M n Λ E (A₂ * y) < u ∧ u ≤ zhi M n Λ E (A₂ * y) ∧
          (2 : ℝ) ^ k ≤ y ∧ D₁ * D₂ ≤ u) := h
      rw [if_neg h']
      simp only [if_neg h, mul_zero, integral_zero]
  have hDi : Integrable (fun t : ℝ => P.D (uL t)) := integrable_D_line P (σ := 3/2)
    (by norm_num) (by norm_num)
  have hg : Integrable gmaj := (hDi.norm.const_mul g0).const_mul ID
  have hφb : ∀ y u t, ‖φ y u t‖ ≤ gmaj t := by
    intro y u t
    simp only [hφ, hgmaj]
    by_cases h : cnd y u
    · rw [if_pos h]
      have h' : 0 < y ∧ 0 < u ∧ ylo M n Λ E (A₂ * y) < u ∧ u ≤ zhi M n Λ E (A₂ * y) ∧
          (2 : ℝ) ^ k ≤ y ∧ D₁ * D₂ ≤ u := h
      obtain ⟨hy, hu, _, hzh, hky, hDu⟩ := h'
      have hA : 0 < A₂ * y := mul_pos (by linarith) hy
      have hzB : zhi M n Λ E (A₂ * y) ≤ zhi M n Λ E B :=
        zhi_anti hM hE0.le hΛ0.le hn0.le hB0 (by nlinarith)
      have hIDe : ID = 1 := by rw [hID, if_pos (by linarith)]
      rw [hIDe, one_mul]
      refine (norm_gT P hM hE0 hA hu t).trans ?_
      have hc := cinv_le hM hE0 hA hu hΛ0 hn0 hzh
      have hz0 := zb_nonneg (K := K)
      rw [hg0]
      gcongr
    · rw [if_neg h, norm_zero]
      positivity
  have hΛg : ∫ t, gmaj t = ID * (g0 * CD) := by
    simp only [hgmaj]
    rw [integral_const_mul, integral_const_mul]
  -- the pair-lemma form
  set z₁ : Ideal (𝓞 K) → ℂ := fun c => z c * ((qsMu e : ℂ) * twist F c e * twist F c a₂) with hz₁
  set z₂ : Ideal (𝓞 K) → ℂ := fun d => conj (z d) * (twistInv F d e * twistInv F d a₂) with hz₂
  set ρ : Ideal (𝓞 K) → ℂ := fun a₁ => rhoT S R a₂ k a₁ with hρ
  set p₁ : Ideal (𝓞 K) → Prop := fun e => e ≠ ⊥ ∧ Nat.log 2 (Ideal.absNorm e) = j₁ with hp₁
  set p₂ : Ideal (𝓞 K) → Prop := fun e => e ≠ ⊥ ∧ Nat.log 2 (Ideal.absNorm e) = j₂ with hp₂
  set Z : Ideal (𝓞 K) → ℝ := fun c => ‖z c‖ * qsN c ^ (-(3/4 : ℝ)) with hZ
  set rows := qsUpTo m qS (2 ^ (k + 1)) with hrows
  have hconv : (∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) *
          (((qsMu e : ℂ) * twist F c e * twist F c a₂) * (twistInv F d e * twistInv F d a₂) *
            ∑ e₁ ∈ (qsDivisors c).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₁),
              ∑ e₂ ∈ (qsDivisors d).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j₂),
                (qsMu (e₁ * e₂) : ℂ) *
                  ∑ a₁ ∈ rows,
                    rhoT S R a₂ k a₁ *
                      (F.character c).idealValue a₁ * (F.character d).idealValue a₁ *
                        phiT K W M n Λ (qsN e) (qsN a₂) k (2 ^ j₁ * 2 ^ j₂) (qsN a₁)
                          (qsN (e₁ * e₂)) (qsN (c * d))) else 0) =
      ∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z₁ c * z₂ d *
          ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
            (qsMu (e₁ * e₂) : ℂ) *
              ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                (F.character d).idealValue a * Φ (qsN a) (qsN (e₁ * e₂)) (qsN (c * d)) else 0 := by
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
    have hc0 := ne_bot_of_QSAdm (hcols c hc).1
    have hd0 := ne_bot_of_QSAdm (hcols d hd).1
    have hf : ∀ (x : Ideal (𝓞 K)), x ≠ ⊥ → ∀ j : ℕ,
        (qsDivisors x).filter (fun e => Nat.log 2 (Ideal.absNorm e) = j) =
          (qsDivisors x).filter (fun e => e ≠ ⊥ ∧ Nat.log 2 (Ideal.absNorm e) = j) := by
      intro x hx j
      refine Finset.filter_congr fun e he => ?_
      have : e ≠ ⊥ := by
        intro h0; rw [h0] at he
        have := (mem_qsDivisors hx).mp he
        exact hx (le_bot_iff.mp (Ideal.le_of_dvd this))
      exact ⟨fun h => ⟨this, h⟩, fun h => h.2⟩
    rw [hf c hc0 j₁, hf d hd0 j₂]
    split_ifs
    · simp only [hz₁, hz₂, hρ, hΦdef, hp₁, hp₂]
      ring
    · rfl
  -- hypotheses of the pair lemma
  have hp₁b : ∀ x, p₁ x → D₁ ≤ qsN x ∧ qsN x ≤ 2 * D₁ := fun x hx => dyad_bounds hx.1 hx.2
  have hp₂b : ∀ x, p₂ x → D₂ ≤ qsN x ∧ qsN x ≤ 2 * D₂ := fun x hx => dyad_bounds hx.1 hx.2
  have hcolsb : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n :=
    fun c hc => ⟨(hcols c hc).1, (hcols c hc).2.2.2⟩
  have hrowsb : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B := by
    intro a ha
    rw [hrows, mem_qsUpTo] at ha
    refine ⟨ha.1, ?_⟩
    rw [hBdef, ← pow_succ']
    exact ha.2
  have hρb : ∀ a, ‖ρ a‖ ≤ 1 := by
    intro a; simp only [hρ, rhoT]; split_ifs <;> simp
  have hsre : ∀ t, (sT t).re = -(3/4 : ℝ) := sT_re
  have hz₁b : ∀ c ∈ cols, ‖z₁ c‖ * qsN c ^ (-(3/4 : ℝ)) ≤ Z c := by
    intro c hc
    have hcA := (hcols c hc).1
    simp only [hz₁, hZ]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [norm_mul, norm_mul, norm_mul]
    have h1 := norm_qsMu_le e
    have h2 := norm_twist_le F hcA e
    have h3 := norm_twist_le F hcA a₂
    have h4 : ‖(qsMu e : ℂ)‖ * ‖twist F c e‖ * ‖twist F c a₂‖ ≤ 1 := by
      calc ‖(qsMu e : ℂ)‖ * ‖twist F c e‖ * ‖twist F c a₂‖ ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by norm_num
    calc ‖z c‖ * (‖(qsMu e : ℂ)‖ * ‖twist F c e‖ * ‖twist F c a₂‖) ≤ ‖z c‖ * 1 :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = ‖z c‖ := mul_one _
  have hz₂b : ∀ c ∈ cols, ‖z₂ c‖ * qsN c ^ (-(3/4 : ℝ)) ≤ Z c := by
    intro c hc
    have hcA := (hcols c hc).1
    simp only [hz₂, hZ]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have h2 := norm_twistInv_le F hcA e
    have h3 := norm_twistInv_le F hcA a₂
    have h4 : ‖twistInv F c e‖ * ‖twistInv F c a₂‖ ≤ 1 := by
      calc ‖twistInv F c e‖ * ‖twistInv F c a₂‖ ≤ 1 * 1 := by gcongr
        _ = 1 := by norm_num
    calc ‖z c‖ * (‖twistInv F c e‖ * ‖twistInv F c a₂‖) ≤ ‖z c‖ * 1 :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = ‖z c‖ := mul_one _
  have hP := hpair n B D₁ D₂ (ID * (g0 * CD)) (-(3/4 : ℝ)) p₁ p₂ cols rows z₁ z₂ ρ Z volume sT φ Φ
    gmaj hn hB1 hD₁ hD₂ hp₁b hp₂b hcolsb hrowsb hρb continuous_sT hsre hΦ hg hφb (le_of_eq hΛg)
    hz₁b hz₂b
  rw [hconv]
  refine hP.trans ?_
  -- Σ Z² ≤ n^{-3/2} Σ ‖z‖²
  have hZsum : ∑ c ∈ cols, Z c ^ 2 ≤ n ^ (-(3/2 : ℝ)) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hcn : n < qsN c := (hcols c hc).2.2.1
    have hc0 : 0 < qsN c := by linarith
    simp only [hZ]
    rw [mul_pow, ← Real.rpow_natCast (qsN c ^ (-(3/4 : ℝ))), ← Real.rpow_mul hc0.le]
    have : qsN c ^ ((-(3/4 : ℝ)) * ((2 : ℕ) : ℝ)) ≤ n ^ (-(3/2 : ℝ)) := by
      rw [show (-(3/4 : ℝ)) * ((2 : ℕ) : ℝ) = -(3/2 : ℝ) by push_cast; ring]
      exact Real.rpow_le_rpow_of_nonpos hn0 hcn.le (by norm_num)
    nlinarith [sq_nonneg ‖z c‖]
  have hSz : 0 ≤ ∑ c ∈ cols, ‖z c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hN₁0 : 0 ≤ qsNorm F (2 * B) (2 * n / D₁) := by rw [qsNorm]; positivity
  have hN₂0 : 0 ≤ qsNorm F (2 * B) (2 * n / D₂) := by rw [qsNorm]; positivity
  have hC20 : 0 ≤ C₂ * (n * B) ^ η₂ := by positivity
  by_cases hIDc : D₁ * D₂ ≤ zhi M n Λ E B
  · have hIDe : ID = 1 := by rw [hID, if_pos hIDc]
    rw [hIDe, one_mul]
    have hN₁b := norm_bound_hexp F hrf hHE hε hCα (by linarith) hn hB1 hD₁
    have hN₂b := norm_bound_hexp F hrf hHE hε hCα (by linarith) hn hB1 hD₂
    rw [zhi_eq hn0.le] at hIDc
    have hest := E3_estimate (κ := κ) hα1 hα2 hM hn hB1 hk hD₁ hD₂ hE1 hΛ
      (by positivity : (0 : ℝ) ≤ Cα * (4 * n * B) ^ ε) hN₂0 hN₁b hN₂b hIDc
    set Y := M + Real.sqrt M * κ ^ (α - 1/2) with hY
    set Q := M / E * Real.sqrt (2 * Λ * n) * Real.sqrt (D₁ * D₂) *
      Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) with hQ
    have hQ0 : 0 ≤ Q := by
      have : 0 ≤ M / E := by positivity
      positivity
    have hg0CD : g0 * CD * Real.sqrt (D₁ * D₂) *
        Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) = KD * Q := by
      rw [hg0, hKD, hQ]; ring
    calc C₂ * (n * B) ^ η₂ * (g0 * CD) * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
          ∑ c ∈ cols, Z c ^ 2
        = C₂ * (n * B) ^ η₂ * (KD * Q) * ∑ c ∈ cols, Z c ^ 2 := by rw [← hg0CD]; ring
      _ ≤ C₂ * (n * B) ^ η₂ * (KD * Q) * (n ^ (-(3/2 : ℝ)) * ∑ c ∈ cols, ‖z c‖ ^ 2) := by
          gcongr
      _ = C₂ * (n * B) ^ η₂ * KD * (Q * n ^ (-(3/2 : ℝ))) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
      _ ≤ C₂ * (n * B) ^ η₂ * KD * (64 * (Cα * (4 * n * B) ^ ε) * Λ ^ (3/2 : ℝ) * Y) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
          gcongr
      _ ≤ C₂ * (n * B) ^ η₂ * (KD + 1) * (64 * (Cα * (4 * n * B) ^ ε) * Λ ^ (3/2 : ℝ) * Y) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
          have : 0 ≤ Y := by
            have : 0 ≤ κ ^ (α - 1/2) := Real.rpow_nonneg (by linarith [hB1, hk]) _
            positivity
          gcongr; linarith
      _ = C₂ * (KD + 1) * 64 * Cα * (n * B) ^ η₂ * (4 * n * B) ^ ε * Λ ^ (3/2 : ℝ) * Y *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
  · have hIDe : ID = 0 := by rw [hID, if_neg hIDc]
    rw [hIDe, zero_mul, mul_zero, zero_mul, zero_mul, zero_mul]
    have : 0 ≤ M + Real.sqrt M * κ ^ (α - 1/2) := by
      have : 0 ≤ κ ^ (α - 1/2) := Real.rpow_nonneg (by linarith [hB1, hk]) _
      positivity
    positivity

end ArtinPrimitiveRoots.A2.QSC3
