import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2.Bilinear

/-!
# A2-QS-CANCEL, part C2u: divisor-pair Cauchy–Schwarz for arbitrary divisor selections

The frozen C2 sums the divisors `e₁ ∣ c`, `e₂ ∣ d` over the dyads `(Dᵢ, 2Dᵢ]` with `Dᵢ ≥ 1`,
which never contain the unit divisor.  `qs_divisor_pair_cauchy_C2u` allows any divisor
selections `p₁, p₂` inside the closed dyads `[Dᵢ, 2Dᵢ]`: `p e := e = ⊤` with `D = 1` is the
unit divisor, `[D, 2D)` and `(D, 2D]` are both special cases, and mixed unit/dyad pairs are
covered.  The bound is the same as C2's.

Proof: Fubini over `t` (the weight is replaced by an integrable version with the same
integrals), `N(cd)^{it} = N(c)^{it} N(d)^{it}` absorbed into the columns, then the bilinear core
`QSC2.core_bound` (inclusion–exclusion for coprimality, reindexing `c = e c'`, Cauchy–Schwarz in
the rows, M0 at the reduced lengths), with `qs_divisor_bound_M1` and `qs_ideal_count_M1`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

namespace QSC2

/-- `v` is the integral of the integrable function `f`. -/
def IsIntOf (μ : Measure ℝ) (v : ℂ) (f : ℝ → ℂ) : Prop :=
  Integrable f μ ∧ ∫ t, f t ∂μ = v

theorem IsIntOf.sum {μ : Measure ℝ} {ι : Type*} (s : Finset ι) {v : ι → ℂ} {f : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, IsIntOf μ (v i) (f i)) :
    IsIntOf μ (∑ i ∈ s, v i) (fun t => ∑ i ∈ s, f i t) := by
  refine ⟨integrable_finsetSum s fun i hi => (h i hi).1, ?_⟩
  rw [integral_finsetSum s fun i hi => (h i hi).1]
  exact Finset.sum_congr rfl fun i hi => (h i hi).2

theorem IsIntOf.const_mul {μ : Measure ℝ} {v : ℂ} {f : ℝ → ℂ} (a : ℂ) (h : IsIntOf μ v f) :
    IsIntOf μ (a * v) (fun t => a * f t) :=
  ⟨h.1.const_mul a, by rw [integral_const_mul, h.2]⟩

theorem IsIntOf.ite {μ : Measure ℝ} (p : Prop) [Decidable p] {v : ℂ} {f : ℝ → ℂ}
    (h : p → IsIntOf μ v f) :
    IsIntOf μ (if p then v else 0) (fun t => if p then f t else 0) := by
  by_cases hp : p
  · simpa [hp] using h hp
  · simp [hp, IsIntOf]

theorem norm_cpow_tI_le {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    ‖(x : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · by_cases ht : (t : ℂ) * Complex.I = 0
    · rw [ht, Complex.cpow_zero, norm_one]
    · rw [Complex.ofReal_zero, Complex.zero_cpow ht, norm_zero]; exact zero_le_one
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp

theorem norm_cpow_tI_eq {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp

theorem continuous_cpow_tI {x : ℝ} (hx : 0 < x) :
    Continuous fun t : ℝ => (x : ℂ) ^ ((t : ℂ) * Complex.I) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))

open Classical in
/-- The Mellin mixture as an integral of an integrable function: the weight is replaced by
`φ' = φ` when `φ(y,u,·)` is integrable and `0` otherwise (both integrals vanish then). -/
theorem isIntOf_mixture {μ : Measure ℝ} (φ : ℝ → ℝ → ℝ → ℂ) (Φ : ℝ → ℝ → ℝ → ℂ)
    (hΦ : ∀ y u x : ℝ, Φ y u x = ∫ t, ((x : ℂ) ^ ((t : ℂ) * Complex.I)) * φ y u t ∂μ)
    (y u x : ℝ) (hx : 0 < x) :
    IsIntOf μ (Φ y u x) (fun t => ((x : ℂ) ^ ((t : ℂ) * Complex.I)) *
      (if Integrable (φ y u) μ then φ y u t else 0)) := by
  have hmeas := (continuous_cpow_tI hx).aestronglyMeasurable (μ := μ)
  by_cases hi : Integrable (φ y u) μ
  · simp only [hi, ite_true]
    refine ⟨hi.bdd_mul hmeas (ae_of_all _ fun t => (norm_cpow_tI_le hx.le t)), ?_⟩
    rw [hΦ]
  · simp only [hi, ite_false, mul_zero]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [integral_zero, hΦ, integral_undef]
    intro hint
    apply hi
    have hinv := ((continuous_cpow_tI hx).inv₀ (fun t => by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hx.ne' (Complex.ofReal_eq_zero.mp h.1))).aestronglyMeasurable (μ := μ)
    refine (hint.bdd_mul hinv (c := 1) (ae_of_all _ fun t => ?_)).congr (ae_of_all _ fun t => ?_)
    · rw [Pi.inv_apply, norm_inv, norm_cpow_tI_eq hx, inv_one]
    · have hne : (x : ℂ) ^ ((t : ℂ) * Complex.I) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hx.ne' (Complex.ofReal_eq_zero.mp h.1)
      simp only [Pi.inv_apply]
      rw [inv_mul_cancel_left₀ hne]

end QSC2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

open QSC2 in
open Classical in
/-- C2u (OPUS, new): C2 for arbitrary divisor selections `p₁, p₂` inside the closed dyads
`[Dᵢ, 2Dᵢ]`; covers the unit divisor (`p e := e = ⊤`, `Dᵢ = 1`) and mixed unit/dyad pairs. -/
theorem qs_divisor_pair_cauchy_C2u (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n B D₁ D₂ Λ : ℝ) (p₁ p₂ : Ideal (𝓞 K) → Prop) [DecidablePred p₁] [DecidablePred p₂]
        (cols rows : Finset (Ideal (𝓞 K))) (z ρ : Ideal (𝓞 K) → ℂ)
        (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : ℝ → ℝ → ℝ → ℂ) (Φ : ℝ → ℝ → ℝ → ℂ)
        (gmaj : ℝ → ℝ),
        1 ≤ n → 1 ≤ B → 1 ≤ D₁ → 1 ≤ D₂ →
        (∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁) →
        (∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂) →
        (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n) →
        (∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B) →
        (∀ a, ‖ρ a‖ ≤ 1) →
        (∀ y u x : ℝ, Φ y u x = ∫ t, ((x : ℂ) ^ ((t : ℂ) * Complex.I)) * φ y u t ∂μ) →
        Integrable gmaj μ → (∀ y u t, ‖φ y u t‖ ≤ gmaj t) → ∫ t, gmaj t ∂μ ≤ Λ →
        ‖qsPairSum cols z (fun c d =>
            ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
              (qsMu (e₁ * e₂) : ℂ) *
                ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                  (F.character d).idealValue a * Φ (qsN a) (qsN (e₁ * e₂)) (qsN (c * d)))‖ ≤
          C * (n * B) ^ η * Λ * Real.sqrt (D₁ * D₂) *
            Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  obtain ⟨CI, hCI, hcount⟩ := qs_ideal_count_M1 (K := K) (η / 3) (by positivity)
  obtain ⟨Cτ, hCτ, hdiv⟩ := qs_divisor_bound_M1 (K := K) (η / 3) (by positivity)
  refine ⟨2 * CI * Cτ ^ 2 * 4 ^ η, by positivity, ?_⟩
  intro n B D₁ D₂ Λ p₁ p₂ _ _ cols rows z ρ μ _ φ Φ gmaj hn hB hD₁ hD₂ hp₁ hp₂ hcols hrows hρ
    hΦ hg hφ hΛ
  have hgm0 : ∀ t, 0 ≤ gmaj t := fun t => (norm_nonneg _).trans (hφ 0 0 t)
  have hΛ0 : 0 ≤ Λ := (integral_nonneg hgm0).trans hΛ
  have hne : ∀ c ∈ cols, c ≠ ⊥ := fun c hc => ne_bot_of_QSAdm (hcols c hc).1
  set φ' : ℝ → ℝ → ℝ → ℂ := fun y u t => if Integrable (φ y u) μ then φ y u t else 0 with hφ'
  have hφ'b : ∀ y u t, ‖φ' y u t‖ ≤ gmaj t := by
    intro y u t
    simp only [hφ']
    split_ifs
    · exact hφ y u t
    · rw [norm_zero]; exact hgm0 t
  -- divisor and ideal counts
  set τ : ℝ := Cτ * (2 * n) ^ (η / 3) with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  have hτ : ∀ c ∈ cols, ((qsDivisors c).card : ℝ) ≤ τ := by
    intro c hc
    refine (hdiv c (hne c hc)).trans (mul_le_mul_of_nonneg_left ?_ hCτ.le)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (hcols c hc).2 (by positivity)
  have hEc : ∀ (p : Ideal (𝓞 K) → Prop) [DecidablePred p] (D : ℝ), 1 ≤ D →
      (∀ e, p e → D ≤ qsN e ∧ qsN e ≤ 2 * D) →
      ((cols.biUnion fun c => (qsDivisors c).filter p).card : ℝ) ≤
        2 * CI * D * (4 * n) ^ (η / 3) := by
    intro p _ D hD hp
    rcases (cols.biUnion fun c => (qsDivisors c).filter p).eq_empty_or_nonempty with h | ⟨e₀, he₀⟩
    · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
    · have hD2n : D ≤ 2 * n := by
        simp only [Finset.mem_biUnion, Finset.mem_filter] at he₀
        obtain ⟨c, hc, he₀c, hpe⟩ := he₀
        have hdvd := (mem_qsDivisors (hne c hc)).mp he₀c
        have hle : qsN e₀ ≤ qsN c := by
          simp only [qsN]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero
            (fun h => hne c hc (Ideal.absNorm_eq_zero_iff.mp h)))
            (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd))
        exact ((hp e₀ hpe).1.trans hle).trans (hcols c hc).2
      have hsub : (cols.biUnion fun c => (qsDivisors c).filter p) ⊆
          (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊2 * D⌋₊).toFinset := by
        intro e he
        simp only [Finset.mem_biUnion, Finset.mem_filter] at he
        obtain ⟨c, _, _, hpe⟩ := he
        rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact Nat.le_floor (hp e hpe).2
      calc ((cols.biUnion fun c => (qsDivisors c).filter p).card : ℝ)
          ≤ ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊2 * D⌋₊).toFinset.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ CI * (2 * D) ^ (1 + η / 3) := hcount (2 * D) (by linarith)
        _ = CI * (2 * D) * (2 * D) ^ (η / 3) := by
            rw [Real.rpow_add (by positivity), Real.rpow_one]; ring
        _ ≤ CI * (2 * D) * (4 * n) ^ (η / 3) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith)
              (by positivity)) (by positivity)
        _ = 2 * CI * D * (4 * n) ^ (η / 3) := by ring
  -- Fubini: the pair sum as an integral over `t`
  have hI : IsIntOf μ (qsPairSum cols z (fun c d =>
      ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
        (qsMu (e₁ * e₂) : ℂ) *
          ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
            (F.character d).idealValue a * Φ (qsN a) (qsN (e₁ * e₂)) (qsN (c * d))))
      (fun t => ∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) *
        ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
          (qsMu (e₁ * e₂) : ℂ) *
            ∑ a ∈ rows, ρ a * (F.character c).idealValue a * (F.character d).idealValue a *
              (((qsN (c * d) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) *
                φ' (qsN a) (qsN (e₁ * e₂)) t) else 0) := by
    unfold qsPairSum
    refine IsIntOf.sum _ fun c hc => IsIntOf.sum _ fun d hd => IsIntOf.ite _ fun _ =>
      IsIntOf.const_mul _ (IsIntOf.sum _ fun e₁ _ => IsIntOf.sum _ fun e₂ _ =>
        IsIntOf.const_mul _ (IsIntOf.sum _ fun a _ => IsIntOf.const_mul _
          (isIntOf_mixture φ Φ hΦ _ _ _ ?_)))
    rw [qsN_mul]
    exact mul_pos (qsN_pos (hne c hc)) (qsN_pos (hne d hd))
  -- pointwise bound by the bilinear core
  set K₁ : ℝ := Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
    Real.sqrt (((cols.biUnion fun c => (qsDivisors c).filter p₁).card : ℝ) *
      ((cols.biUnion fun c => (qsDivisors c).filter p₂).card : ℝ)) * τ ^ 2 *
    ∑ c ∈ cols, ‖z c‖ ^ 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hpt : ∀ t : ℝ, ‖∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) *
        ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
          (qsMu (e₁ * e₂) : ℂ) *
            ∑ a ∈ rows, ρ a * (F.character c).idealValue a * (F.character d).idealValue a *
              (((qsN (c * d) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) *
                φ' (qsN a) (qsN (e₁ * e₂)) t) else 0‖ ≤ gmaj t * K₁ := by
    intro t
    have hcore := core_bound F hrf p₁ p₂ (2 * n) (2 * B) D₁ D₂ (gmaj t) τ (by linarith)
      (by linarith) cols rows hcols hrows (fun e he => (hp₁ e he).1) (fun e he => (hp₂ e he).1)
      hτ hτ0 (fun c => z c * ((qsN c : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I))
      (fun d => conj (z d) * ((qsN d : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) (fun c => ‖z c‖)
      (fun c => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_cpow_tI_le (Nat.cast_nonneg _) t))
      (fun d => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_cpow_tI_le (Nat.cast_nonneg _) t))
      (fun a e₁ e₂ => ρ a * φ' (qsN a) (qsN (e₁ * e₂)) t)
      (fun a e₁ e₂ => by
        rw [norm_mul]
        calc ‖ρ a‖ * ‖φ' (qsN a) (qsN (e₁ * e₂)) t‖ ≤ 1 * gmaj t :=
              mul_le_mul (hρ a) (hφ'b _ _ t) (norm_nonneg _) zero_le_one
          _ = gmaj t := one_mul _)
    refine le_trans (le_of_eq ?_) (hcore.trans (le_of_eq (by rw [hK₁]; ring)))
    congr 1
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
    split_ifs with hcd
    · have hcp : ((qsN (c * d) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
          ((qsN c : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) * ((qsN d : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
        rw [qsN_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun e₂ _ =>
        Finset.sum_congr rfl fun a _ => ?_
      rw [hcp]
      ring
    · rfl
  -- integrate
  rw [← hI.2]
  calc ‖∫ t, (∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) *
        ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
          (qsMu (e₁ * e₂) : ℂ) *
            ∑ a ∈ rows, ρ a * (F.character c).idealValue a * (F.character d).idealValue a *
              (((qsN (c * d) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) *
                φ' (qsN a) (qsN (e₁ * e₂)) t) else 0) ∂μ‖
      ≤ ∫ t, gmaj t * K₁ ∂μ := norm_integral_le_of_norm_le (hg.mul_const K₁) (ae_of_all _ hpt)
    _ = (∫ t, gmaj t ∂μ) * K₁ := integral_mul_const K₁ gmaj
    _ ≤ Λ * K₁ := mul_le_mul_of_nonneg_right hΛ hK₁0
    _ ≤ 2 * CI * Cτ ^ 2 * 4 ^ η * (n * B) ^ η * Λ * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
        set N₁₂ := Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂))
        set Sz := ∑ c ∈ cols, ‖z c‖ ^ 2
        set ε := (4 * n) ^ (η / 3) with hε
        have hN0 : 0 ≤ N₁₂ := Real.sqrt_nonneg _
        have hSz : 0 ≤ Sz := by positivity
        have hε0 : 0 ≤ ε := by positivity
        have hE₁ := hEc p₁ D₁ hD₁ hp₁
        have hE₂ := hEc p₂ D₂ hD₂ hp₂
        have hsqE : Real.sqrt (((cols.biUnion fun c => (qsDivisors c).filter p₁).card : ℝ) *
            ((cols.biUnion fun c => (qsDivisors c).filter p₂).card : ℝ)) ≤
            2 * CI * ε * Real.sqrt (D₁ * D₂) := by
          calc _ ≤ Real.sqrt ((2 * CI * ε) ^ 2 * (D₁ * D₂)) := by
                refine Real.sqrt_le_sqrt ?_
                calc _ ≤ (2 * CI * D₁ * ε) * (2 * CI * D₂ * ε) :=
                      mul_le_mul hE₁ hE₂ (Nat.cast_nonneg _) (by positivity)
                  _ = (2 * CI * ε) ^ 2 * (D₁ * D₂) := by ring
            _ = 2 * CI * ε * Real.sqrt (D₁ * D₂) := by
                rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        have hτε : τ ≤ Cτ * ε := by
          rw [hτdef, hε]
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith)
            (by positivity)) hCτ.le
        have hε3 : ε ^ 3 ≤ 4 ^ η * (n * B) ^ η := by
          rw [hε, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
            show η / 3 * ((3 : ℕ) : ℝ) = η by push_cast; ring,
            Real.mul_rpow (by norm_num) (by positivity)]
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hη.le)
            (by positivity)
          nlinarith
        calc Λ * K₁ = Λ * N₁₂ * Real.sqrt
              (((cols.biUnion fun c => (qsDivisors c).filter p₁).card : ℝ) *
                ((cols.biUnion fun c => (qsDivisors c).filter p₂).card : ℝ)) * τ ^ 2 * Sz := by
              rw [hK₁]; ring
          _ ≤ Λ * N₁₂ * (2 * CI * ε * Real.sqrt (D₁ * D₂)) * (Cτ * ε) ^ 2 * Sz := by
              gcongr
          _ = 2 * CI * Cτ ^ 2 * ε ^ 3 * Λ * Real.sqrt (D₁ * D₂) * N₁₂ * Sz := by ring
          _ ≤ 2 * CI * Cτ ^ 2 * (4 ^ η * (n * B) ^ η) * Λ * Real.sqrt (D₁ * D₂) * N₁₂ * Sz := by
              gcongr
          _ = 2 * CI * Cτ ^ 2 * 4 ^ η * (n * B) ^ η * Λ * Real.sqrt (D₁ * D₂) * N₁₂ * Sz := by
              ring

end ArtinPrimitiveRoots.A2
