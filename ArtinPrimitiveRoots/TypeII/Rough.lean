import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.PP.Results

/-! The rough-factor Type II estimate and its coefficient (`08-type-ii.tex:321-536`). -/

namespace ArtinPrimitiveRoots.TypeII.Rough

open Classical
open MeasureTheory
open ContinuousLinearMap
open scoped Pointwise Topology Ring MulOpposite
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII.PP

/-- `def:rough-density` — 08-type-ii.tex:253-270. Alias of the shared Buchstab rough density; the
body is exactly the existing `ArtinPrimitiveRoots.Sieve.roughDensity` definition. -/
noncomputable abbrev roughDensity := ArtinPrimitiveRoots.Sieve.roughDensity

/-- The coefficient in equation `eq:rough-type-ii-coefficient`. -/
noncomputable def roughCoefficient (x γ v : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
    (((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
        roughDensity γ (Real.log (m : ℝ) / Real.log x) /
          (Real.log x * roughSieveProduct (roughCutoff x)) *
            (if roughAbove m (roughCutoff x) then (1 : ℝ) else 0)) : ℂ)

/-- The prime-indicator coefficient `1_{P⁻(m)>x^γ}`. -/
noncomputable def roughIndicator (x γ : ℝ) (m : ℕ) : ℝ :=
  if roughAbove m (Real.rpow x γ) then 1 else 0

/-- The proxy coefficient `D_γ(log m/log x)/(log x V(W))` on `W`-rough integers. -/
noncomputable def roughProxy (x γ : ℝ) (m : ℕ) : ℝ :=
  roughDensity γ (Real.log (m : ℝ) / Real.log x) /
    (Real.log x * roughSieveProduct (roughCutoff x)) *
      if roughAbove m (roughCutoff x) then 1 else 0

/-- The finite ordered-prime convolution `T_γ(m)` from `eq:rough-convolution-square-error`. -/
noncomputable def roughConvolutionTerm (x γ M : ℝ) (j m : ℕ) : ℝ :=
  (1 / (j.factorial : ℝ)) *
    ∑ t ∈ boundedTuples j (⌊2 * M⌋₊ + 1),
      if (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          (∏ i : Fin j, t i) = m then 1 else 0

noncomputable def roughConvolution (x γ wMax M : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), roughConvolutionTerm x γ M j m

/-- Prime set in a closed real interval, explicitly truncated at the upper endpoint. -/
noncomputable def primesInInterval (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (⌊hi⌋₊ + 1)).filter fun p => p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi

/-- Product-measure integral over ordered `j`-tuples of primes in logarithmic coordinates. -/
noncomputable def roughTupleIntegral (x γ lo hi : ℝ) (j : ℕ) : ℝ :=
  (1 / (j.factorial : ℝ)) *
    ∫ t : Fin j → ℝ,
      if (∀ i, Real.rpow x γ < t i) ∧
          lo ≤ ∏ i : Fin j, t i ∧ (∏ i : Fin j, t i) ≤ hi then
        ∏ i : Fin j, 1 / Real.log (t i) else 0

/-- `prop:rough-type-ii` — `08-type-ii.tex:321-536`. Fix the parameters in the
paper. Uniformly over admissible dyads, intervals, real twists, rough second-variable coefficients,
and marked-invariant multipliers, the coefficient `roughCoefficient` has the Type II saving once
`K` is sufficiently large. -/
theorem rough_type_ii
    (γ wMin wMax δ C Dstar q_d c₁ c₂ : ℝ)
    (hγ : 0 < γ) (hγwMin : γ < wMin) (hwMinMax : wMin < wMax)
    (hwMax : wMax < 1)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ a : Fin K → ℝ, ValidBands K a →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
              ∀ I : Set ℕ, I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ v : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                  ∀ beta : ℕ → ℂ,
                    (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                      roughAbove n (roughCutoff x)) →
                    (∀ n ∈ dyadicIntegers Hn,
                      ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                    ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                      ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                        ∑ n ∈ dyadicIntegers Hn,
                          roughCoefficient x γ v m * beta n * F (m * n - 1) *
                            (markedWeight x K a q_d (m * n - 1) : ℂ)‖ ≤
                        C' * (Hm * Hn) * Real.rpow (Real.log x) (-Dstar) := by
  sorry

/-- `t2:square-error` — 08-type-ii.tex:351-371. -/
theorem square_error (γ wMax δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hγw : γ < wMax) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ M : ℝ, 1 ≤ M → Real.rpow x δ ≤ M →
          let Jγ := ⌊wMax / γ⌋₊
          (∑ m ∈ dyadicIntegers M,
            |roughIndicator x γ m - roughConvolution x γ wMax M m|) ≤
              (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
                  (fun p => Real.rpow x γ < (p : ℝ)),
                ⌊2 * M / (p : ℝ) ^ 2⌋₊) ∧
              (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
                  (fun p => Real.rpow x γ < (p : ℝ)),
                ⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) ≤ C * M * Real.rpow x (-γ) := by
  sorry

/-- `t2:sw-slot` — 08-type-ii.tex:385-407, `eq:rough-slot-siegel-walfisz`. -/
theorem sw_slot (γ : ℝ) (hγ : 0 < γ) :
    ∀ A₀ A₂ : ℝ, 0 < A₀ → 0 < A₂ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ P : ℝ, Real.rpow x γ / 2 ≤ P → P ≤ 2 * x →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                P ≤ l → l ≤ r → r ≤ 2 * P →
                  ‖∑ p ∈ (primesInInterval l r),
                    (χ (p : ZMod k) : ℂ) -
                    (if χ = 1 then (1 : ℂ) else 0) *
                      (∫ y in l..r, (1 / Real.log y : ℝ) : ℂ)‖ ≤
                      C * P * Real.rpow (Real.log x) (-A₂) := by
  sorry

/-- The simplex defining a higher density term is empty below its natural support. -/
private theorem roughDensityTerm_eq_zero_of_lt (γ w : ℝ) {j : ℕ} (hγ : 0 < γ)
    (hj : 2 ≤ j) (hw : w < (j : ℝ) * γ) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j = 0 := by
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  rw [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_neg hj0, if_neg hj1]
  have hempty :
      {t : Fin (j - 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ht
    have hs : ((j - 1 : ℕ) : ℝ) * γ ≤ ∑ i, t i := by
      calc
        ((j - 1 : ℕ) : ℝ) * γ = ∑ _i : Fin (j - 1), γ := by simp
        _ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht.1 i
    have hjcast : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ j by omega)).symm
    have : (j : ℝ) * γ ≤ w := by nlinarith [ht.2]
    exact (not_lt_of_ge this) hw
  simp [hempty]

/-- Above the support threshold, the defining density series has a finite truncation. -/
private theorem roughDensity_eq_sum_upto (γ w : ℝ) (hγ : 0 < γ) (hw : γ < w) :
    ArtinPrimitiveRoots.Sieve.roughDensity γ w =
      ∑ j ∈ Finset.range (⌊w / γ⌋₊ + 1),
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j := by
  classical
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  exact tsum_eq_sum (s := Finset.range (⌊w / γ⌋₊ + 1)) fun j hj => by
    have hjbound : ⌊w / γ⌋₊ + 1 ≤ j := by simpa using hj
    have hwγ : 1 < w / γ := (lt_div_iff₀ hγ).2 (by simpa using hw)
    have hfloor : 1 ≤ ⌊w / γ⌋₊ := Nat.le_floor (by exact_mod_cast hwγ.le)
    have hj2 : 2 ≤ j := by omega
    have hfloorlt : w / γ < (j : ℝ) := by
      have h := Nat.lt_floor_add_one (w / γ)
      exact lt_of_lt_of_le h (by exact_mod_cast hjbound)
    apply roughDensityTerm_eq_zero_of_lt γ w hγ hj2
    exact (div_lt_iff₀ hγ).1 hfloorlt

/-- A common finite truncation works for every `w` in a bounded interval above `γ`. -/
private theorem roughDensity_eq_sum_bounded (γ w W : ℝ) (hγ : 0 < γ)
    (hγW : γ < W) (hwW : w ≤ W) :
    ArtinPrimitiveRoots.Sieve.roughDensity γ w =
      ∑ j ∈ Finset.range (⌊W / γ⌋₊ + 1),
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j := by
  classical
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  exact tsum_eq_sum (s := Finset.range (⌊W / γ⌋₊ + 1)) fun j hj => by
    have hjbound : ⌊W / γ⌋₊ + 1 ≤ j := by simpa using hj
    have hWγ : 1 < W / γ := (lt_div_iff₀ hγ).2 (by simpa using hγW)
    have hfloor : 1 ≤ ⌊W / γ⌋₊ := Nat.le_floor (by exact_mod_cast hWγ.le)
    have hj2 : 2 ≤ j := by omega
    have hfloorlt : W / γ < (j : ℝ) := by
      have h := Nat.lt_floor_add_one (W / γ)
      exact lt_of_lt_of_le h (by exact_mod_cast hjbound)
    have hwr : w / γ ≤ W / γ := div_le_div_of_nonneg_right hwW hγ.le
    have hwγ : w / γ < (j : ℝ) := hwr.trans_lt hfloorlt
    apply roughDensityTerm_eq_zero_of_lt γ w hγ hj2
    exact (div_lt_iff₀ hγ).1 hwγ

/-- A finite truncation uniform over all parameters with `γ` bounded below. -/
private theorem roughDensity_eq_sum_uniform (γ w W γ₀ : ℝ) (hγ : 0 < γ)
    (hγ₀ : 0 < γ₀) (hγ₀γ : γ₀ ≤ γ) (hγW : γ < W) (hwW : w ≤ W) :
    ArtinPrimitiveRoots.Sieve.roughDensity γ w =
      ∑ j ∈ Finset.range (⌊W / γ₀⌋₊ + 1),
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j := by
  classical
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  exact tsum_eq_sum (s := Finset.range (⌊W / γ₀⌋₊ + 1)) fun j hj => by
    have hjbound : ⌊W / γ₀⌋₊ + 1 ≤ j := by simpa using hj
    have hγ₀W : γ₀ < W := lt_of_le_of_lt hγ₀γ hγW
    have hWγ₀ : 1 < W / γ₀ := (lt_div_iff₀ hγ₀).2 (by simpa using hγ₀W)
    have hfloor : 1 ≤ ⌊W / γ₀⌋₊ := Nat.le_floor (by exact_mod_cast hWγ₀.le)
    have hj2 : 2 ≤ j := by omega
    have hfloorlt : W / γ₀ < (j : ℝ) := by
      have h := Nat.lt_floor_add_one (W / γ₀)
      exact lt_of_lt_of_le h (by exact_mod_cast hjbound)
    have hWpos : 0 < W := hγ₀.trans hγ₀W
    have hWratio : W / γ ≤ W / γ₀ :=
      div_le_div_of_nonneg_left hWpos.le hγ₀ hγ₀γ
    have hwratio : w / γ ≤ W / γ := div_le_div_of_nonneg_right hwW hγ.le
    have hwγ : w / γ < (j : ℝ) := (hwratio.trans hWratio).trans_lt hfloorlt
    apply roughDensityTerm_eq_zero_of_lt γ w hγ hj2
    exact (div_lt_iff₀ hγ).1 hwγ

/-- A finite product preserves a uniform Lipschitz estimate when every factor is bounded. -/
private theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (B K d : ℝ) (hB : 1 ≤ B) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (f g : ι → ℝ)
    (hf : ∀ i ∈ S, |f i| ≤ B) (hg : ∀ i ∈ S, |g i| ≤ B)
    (hfg : ∀ i ∈ S, |f i - g i| ≤ K * d) :
    |∏ i ∈ S, f i - ∏ i ∈ S, g i| ≤ (S.card : ℝ) * K * d * B ^ (S.card - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfA := hf a (Finset.mem_insert_self a S)
    have hgA := hg a (Finset.mem_insert_self a S)
    have hfgA := hfg a (Finset.mem_insert_self a S)
    have hfS : ∀ i ∈ S, |f i| ≤ B := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS : ∀ i ∈ S, |g i| ≤ B := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfgS : ∀ i ∈ S, |f i - g i| ≤ K * d := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    have hprodF : |∏ i ∈ S, f i| ≤ B ^ S.card := by
      rw [Finset.abs_prod]
      calc
        ∏ i ∈ S, |f i| ≤ ∏ _i ∈ S, B :=
          Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi => hfS i hi)
        _ = B ^ S.card := by simp
    calc
      |∏ i ∈ insert a S, f i - ∏ i ∈ insert a S, g i|
          = |(f a - g a) * (∏ i ∈ S, f i) + g a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)| := by
              simp only [Finset.prod_insert ha]
              congr 1
              ring
      _ ≤ |f a - g a| * |∏ i ∈ S, f i| + |g a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| := by
          calc
            _ = ‖(f a - g a) * (∏ i ∈ S, f i) + g a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)‖ := by
              rw [Real.norm_eq_abs]
            _ ≤ ‖(f a - g a) * (∏ i ∈ S, f i)‖ +
                  ‖g a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)‖ := norm_add_le _ _
            _ = _ := by simp [Real.norm_eq_abs, Finset.abs_prod, abs_mul]
      _ ≤ K * d * B ^ S.card + B * ((S.card : ℝ) * K * d * B ^ (S.card - 1)) := by
          apply add_le_add
          · calc
              _ ≤ K * d * |∏ i ∈ S, f i| := mul_le_mul_of_nonneg_right hfgA (abs_nonneg _)
              _ ≤ K * d * B ^ S.card := by gcongr
          · calc
              _ ≤ B * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| :=
                mul_le_mul_of_nonneg_right hgA (abs_nonneg _)
              _ ≤ B * ((S.card : ℝ) * K * d * B ^ (S.card - 1) : ℝ) := by
                gcongr
                exact ih hfS hgS hfgS
      _ = ((insert a S).card : ℝ) * K * d * B ^ ((insert a S).card - 1) := by
          rw [Finset.card_insert_of_notMem ha]
          by_cases hm : S.card = 0
          · simp [hm]
          · have hmpos : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hm
            have hp : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hmpos
            have hpow : B * B ^ (S.card - 1) = B ^ S.card := by
              calc
                B * B ^ (S.card - 1) = B ^ (S.card - 1) * B := mul_comm _ _
                _ = B ^ (S.card - 1 + 1) := (pow_succ B (S.card - 1)).symm
                _ = B ^ S.card := by rw [hp]
            have hcard : S.card + 1 - 1 = S.card := by omega
            rw [hcard, Nat.cast_add, Nat.cast_one]
            calc
              _ = K * d * B ^ S.card +
                    (S.card : ℝ) * K * d * (B * B ^ (S.card - 1)) := by ring
              _ = K * d * B ^ S.card + (S.card : ℝ) * K * d * B ^ S.card := by rw [hpow]
              _ = ((S.card : ℝ) + 1) * K * d * B ^ S.card := by ring

/-- The standard simplex for the rescaling `tᵢ = γ + s yᵢ`. -/
private def unitSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

private theorem isCompact_unitSimplex (n : ℕ) : IsCompact (unitSimplex n) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hclosed : IsClosed (unitSimplex n) := by
    have h₁ : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
    have h₂ : IsClosed {y : Fin n → ℝ | ∑ i, y i ≤ 1} :=
      isClosed_le (by fun_prop) continuous_const
    simpa only [unitSimplex, Set.setOf_and] using h₁.inter h₂
  apply IsCompact.of_isClosed_subset hbox hclosed
  intro y hy
  simp only [Set.mem_pi, Set.mem_univ, true_and, Set.mem_Icc]
  intro i
  intro _
  constructor
  · exact hy.1 i
  · have hsingle : y i ≤ ∑ k, y k :=
      Finset.single_le_sum (fun k _ => hy.1 k) (Finset.mem_univ i)
    exact hsingle.trans hy.2

private def affineSimplexMap (γ s : ℝ) {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => γ + s * y i

private noncomputable def simplexKernel (γ s : ℝ) {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  (γ + s * (1 - ∑ i, y i))⁻¹ * ∏ i, (γ + s * y i)⁻¹

private theorem simplex_affine_image (γ s : ℝ) {n : ℕ} (hs : 0 < s) :
    {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ (n : ℝ) * γ + s} =
      affineSimplexMap γ s '' unitSimplex n := by
  ext t
  constructor
  · intro ht
    refine ⟨fun i => (t i - γ) / s, ?_, ?_⟩
    · constructor
      · intro i
        exact div_nonneg (sub_nonneg.mpr (ht.1 i)) hs.le
      · have hsum :
            (∑ i : Fin n, (t i - γ) / s) = ((∑ i : Fin n, t i) - (n : ℝ) * γ) / s := by
          rw [← Finset.sum_div, Finset.sum_sub_distrib]
          simp
        rw [hsum, div_le_iff₀ hs]
        nlinarith [ht.2]
    · funext i
      dsimp [affineSimplexMap]
      field_simp [ne_of_gt hs]
      ring
  · rintro ⟨y, hy, rfl⟩
    constructor
    · intro i
      dsimp [affineSimplexMap]
      nlinarith [mul_nonneg hs.le (hy.1 i)]
    · have hsum :
          (∑ i : Fin n, (γ + s * y i)) = (n : ℝ) * γ + s * ∑ i : Fin n, y i := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      change (∑ i : Fin n, (γ + s * y i)) ≤ (n : ℝ) * γ + s
      rw [hsum]
      nlinarith [mul_le_mul_of_nonneg_left hy.2 hs.le]

/-- Rescale a higher density term onto a fixed unit simplex. -/
private theorem term_affine_simplex (γ s : ℝ) (j : ℕ) (hj : 2 ≤ j) (hs : 0 < s) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ ((j : ℝ) * γ + s) j =
      (1 / (j.factorial : ℝ)) * s ^ (j - 1) *
        ∫ y in unitSimplex (j - 1), simplexKernel γ s y := by
  let n : ℕ := j - 1
  have hn1 : 1 ≤ n := by dsimp [n]; omega
  have hn0 : n ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  let w : ℝ := (j : ℝ) * γ + s
  let S := unitSimplex n
  let F : (Fin n → ℝ) → (Fin n → ℝ) := affineSimplexMap γ s
  let c : Fin n → ℝ := fun _ => γ
  let scale : (Fin n → ℝ) → (Fin n → ℝ) := fun y => s • y
  let trans : (Fin n → ℝ) → (Fin n → ℝ) := fun z => z + c
  have hF : F = trans ∘ scale := by
    funext y
    ext i
    simp [F, affineSimplexMap, trans, scale, c, Pi.smul_apply]
    ring
  have hD : {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ (n : ℝ) * γ + s} =
      trans '' (scale '' S) := by
    calc
      _ = F '' S := simplex_affine_image γ s hs
      _ = trans '' (scale '' S) := by
        calc
          _ = (trans ∘ scale) '' S := congrArg (fun f => f '' S) hF
          _ = trans '' (scale '' S) := (Set.image_image trans scale S).symm
  have hjcast : (j : ℝ) = (n : ℝ) + 1 := by
    dsimp [n]
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ j by omega)).symm
  have hupper : (j : ℝ) * γ + s - γ = (n : ℝ) * γ + s := by
    rw [hjcast]
    ring
  have hDmeas : MeasurableSet {t : Fin n → ℝ |
      (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ (n : ℝ) * γ + s} := by
    have h₁ : MeasurableSet {t : Fin n → ℝ | ∀ i, γ ≤ t i} := by
      simpa only [Set.iInter_ofPred] using
        (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i))
    have h₂ : MeasurableSet {t : Fin n → ℝ | ∑ i, t i ≤ (n : ℝ) * γ + s} :=
      measurableSet_le (by fun_prop) measurable_const
    simpa only [Set.setOf_and] using h₁.inter h₂
  have hSmeas : MeasurableSet S := by
    have h₁ : MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      simpa only [Set.iInter_ofPred] using
        (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i))
    have h₂ : MeasurableSet {y : Fin n → ℝ | ∑ i, y i ≤ 1} :=
      measurableSet_le (by fun_prop) measurable_const
    change MeasurableSet ({y : Fin n → ℝ | ∀ i, 0 ≤ y i} ∩
      {y : Fin n → ℝ | ∑ i, y i ≤ 1})
    exact h₁.inter h₂
  have hmp : MeasurePreserving trans volume volume := by
    refine ⟨by fun_prop, ?_⟩
    exact map_add_right_eq_self volume c
  have hemb : MeasurableEmbedding trans :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  let hk : (Fin n → ℝ) → ℝ := fun t => (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹
  simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_neg hj0, if_neg hj1, hupper]
  rw [integral_indicator hDmeas]
  rw [hD]
  simp only [one_div]
  have hshift := hmp.setIntegral_image_emb hemb hk (scale '' S)
  simp only [hk] at hshift
  rw [hshift]
  have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun z => hk (trans z)) S hs
  have hfin : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [hfin, smul_eq_mul] at hscale
  have hscaleSet : scale '' S = s • S := by rfl
  have hscale' :
      (∫ z in scale '' S, hk (trans z)) = s ^ n * ∫ y in S, hk (trans (scale y)) := by
    rw [hscaleSet]
    calc
      _ = s ^ n * ((s ^ n)⁻¹ * ∫ z in s • S, hk (trans z)) := by
        field_simp [ne_of_gt (pow_pos hs n)]
      _ = s ^ n * ∫ y in S, hk (trans (scale y)) := by
        rw [hscale]
  rw [hscale']
  have hker : ∀ y ∈ S, hk (trans (scale y)) = simplexKernel γ s y := by
    intro y hy
    have hsum : (∑ i : Fin n, (s * y i + γ)) = (n : ℝ) * γ + s * ∑ i, y i := by
      calc
        _ = ∑ i : Fin n, (γ + s * y i) := Finset.sum_congr rfl fun i _ => by ring
        _ = (n : ℝ) * γ + s * ∑ i, y i := by simp [Finset.sum_add_distrib, Finset.mul_sum]
    simp only [hk, trans, scale, c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    dsimp [w]
    rw [hjcast]
    congr 2 <;> ring
  rw [setIntegral_congr_fun hSmeas hker]
  ring

/-- At the support boundary, the defining simplex collapses to a null singleton. -/
private theorem roughDensityTerm_eq_zero_at_support (γ : ℝ) (j : ℕ) (hj : 2 ≤ j) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ ((j : ℝ) * γ) j = 0 := by
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  have hn1 : 1 ≤ j - 1 := by omega
  have hjcast : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ j by omega)).symm
  have hupper : (j : ℝ) * γ - γ = ((j - 1 : ℕ) : ℝ) * γ := by
    rw [hjcast]
    ring
  let c : Fin (j - 1) → ℝ := fun _ => γ
  have hD :
      {t : Fin (j - 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ (j : ℝ) * γ - γ} = {c} := by
    ext t
    constructor
    · intro ht
      have hsumLower : ((j - 1 : ℕ) : ℝ) * γ ≤ ∑ i, t i := by
        calc
          ((j - 1 : ℕ) : ℝ) * γ = ∑ _i : Fin (j - 1), γ := by simp
          _ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht.1 i
      have hsumGap : ∑ i : Fin (j - 1), (t i - γ) = 0 := by
        have hsum : ∑ i : Fin (j - 1), (t i - γ) = ∑ i : Fin (j - 1), t i - ((j - 1 : ℕ) : ℝ) * γ := by
          rw [Finset.sum_sub_distrib]
          simp
        rw [hsum]
        rw [hupper] at ht
        nlinarith [ht.2, hsumLower]
      have hcoord : ∀ i, t i = γ := by
        intro i
        have hgap : 0 ≤ t i - γ := sub_nonneg.mpr (ht.1 i)
        have hle : t i - γ ≤ ∑ k : Fin (j - 1), (t k - γ) :=
          Finset.single_le_sum (fun k _ => sub_nonneg.mpr (ht.1 k)) (Finset.mem_univ i)
        nlinarith [hsumGap, hgap, hle]
      ext i
      exact hcoord i
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      subst t
      constructor
      · intro i
        exact le_rfl
      · have hsum : ∑ i : Fin (j - 1), γ = ((j - 1 : ℕ) : ℝ) * γ := by simp
        rw [hupper]
        exact le_of_eq hsum
  have hnull : volume ({c} : Set (Fin (j - 1) → ℝ)) = 0 := by
    haveI : Nonempty (Fin (j - 1)) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (Fin (j - 1) → ℝ) := inferInstance
    simp
  rw [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_neg hj0, if_neg hj1]
  rw [hD]
  rw [integral_indicator (MeasurableSet.singleton c)]
  rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure]
  simp

/-- A globally continuous kernel agreeing with the simplex kernel for nonnegative scale. -/
private noncomputable def simplexSafeFactor (γ a s : ℝ) : ℝ :=
  (max γ (γ + s * a))⁻¹

private noncomputable def simplexKernelSafe (γ s : ℝ) {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  simplexSafeFactor γ (1 - ∑ i, y i) s * ∏ i, simplexSafeFactor γ (y i) s

private theorem simplexSafeFactor_abs_le {γ a s : ℝ} (hγ : 0 < γ) (ha : 0 ≤ a)
    (hs : 0 ≤ s) : |simplexSafeFactor γ a s| ≤ γ⁻¹ := by
  have hd : γ ≤ γ + s * a := by nlinarith [mul_nonneg hs ha]
  rw [simplexSafeFactor, max_eq_right hd, abs_of_pos (by positivity)]
  simpa only [one_div] using one_div_le_one_div_of_le hγ hd

private theorem simplexSafeFactor_sub_le {γ a s t : ℝ} (hγ : 0 < γ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |simplexSafeFactor γ a s - simplexSafeFactor γ a t| ≤ γ⁻¹ ^ 2 * |s - t| := by
  have hds : γ ≤ γ + s * a := by nlinarith [mul_nonneg hs ha0]
  have hdt : γ ≤ γ + t * a := by nlinarith [mul_nonneg ht ha0]
  have hdspos : 0 < γ + s * a := lt_of_lt_of_le hγ hds
  have hdtpos : 0 < γ + t * a := lt_of_lt_of_le hγ hdt
  simp only [simplexSafeFactor]
  rw [max_eq_right hds, max_eq_right hdt]
  have hform : (γ + s * a)⁻¹ - (γ + t * a)⁻¹ =
      a * (t - s) / ((γ + s * a) * (γ + t * a)) := by
    field_simp [ne_of_gt hdspos, ne_of_gt hdtpos]
    ring
  rw [hform, abs_div, abs_mul, abs_of_nonneg ha0,
    abs_of_pos (mul_pos hdspos hdtpos), abs_sub_comm t s]
  have hnum : a * |s - t| ≤ |s - t| :=
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (abs_nonneg (s - t))
  have hden : γ * γ ≤ (γ + s * a) * (γ + t * a) :=
    mul_le_mul hds hdt hγ.le hdspos.le
  calc
    a * |s - t| / ((γ + s * a) * (γ + t * a)) ≤
        |s - t| / ((γ + s * a) * (γ + t * a)) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg hdspos.le hdtpos.le)
    _ ≤ |s - t| / (γ * γ) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hγ hγ) hden
    _ = γ⁻¹ ^ 2 * |s - t| := by
      rw [div_eq_mul_inv, mul_comm, mul_inv, ← pow_two]

private theorem simplexKernelSafe_sub_le (n : ℕ) (γ : ℝ) (y : Fin n → ℝ)
    (hγ : 0 < γ) (hy : y ∈ unitSimplex n) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |simplexKernelSafe γ s y - simplexKernelSafe γ t y| ≤
      ((γ⁻¹ ^ 2 * (max 1 γ⁻¹ ^ n)) +
        (max 1 γ⁻¹) * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) * |s - t| := by
  simp only [unitSimplex, Set.mem_setOf_eq] at hy
  let B : ℝ := max 1 γ⁻¹
  let K : ℝ := γ⁻¹ ^ 2
  have hB : 1 ≤ B := le_max_left _ _
  have hK : 0 ≤ K := by positivity
  have hlast0 : 0 ≤ 1 - ∑ i, y i := by
    have hsum : 0 ≤ ∑ i : Fin n, y i := Finset.sum_nonneg fun i _ => hy.1 i
    linarith [hy.2, hsum]
  have hlast1 : 1 - ∑ i, y i ≤ 1 := by
    have hsum : 0 ≤ ∑ i : Fin n, y i := Finset.sum_nonneg fun i _ => hy.1 i
    linarith [hsum]
  have hlastB_s := simplexSafeFactor_abs_le hγ hlast0 hs
  have hlastB_t := simplexSafeFactor_abs_le hγ hlast0 ht
  have hlastD := simplexSafeFactor_sub_le hγ hlast0 hlast1 hs ht
  have hprefixB_s : ∀ i ∈ Finset.univ, |simplexSafeFactor γ (y i) s| ≤ B := by
    intro i hi
    exact (simplexSafeFactor_abs_le hγ (hy.1 i) hs).trans (le_max_right _ _)
  have hprefixB_t : ∀ i ∈ Finset.univ, |simplexSafeFactor γ (y i) t| ≤ B := by
    intro i hi
    exact (simplexSafeFactor_abs_le hγ (hy.1 i) ht).trans (le_max_right _ _)
  have hprefixD : ∀ i ∈ Finset.univ,
      |simplexSafeFactor γ (y i) s - simplexSafeFactor γ (y i) t| ≤ K * |s - t| := by
    intro i hi
    exact simplexSafeFactor_sub_le hγ (hy.1 i)
      ((Finset.single_le_sum (fun k _ => hy.1 k) (Finset.mem_univ i)).trans hy.2) hs ht
  have hprodD := abs_prod_sub_prod_le (Finset.univ : Finset (Fin n)) B K |s - t| hB hK
    (abs_nonneg _) (fun i => simplexSafeFactor γ (y i) s)
    (fun i => simplexSafeFactor γ (y i) t) hprefixB_s hprefixB_t hprefixD
  have hprodB_s : |∏ i : Fin n, simplexSafeFactor γ (y i) s| ≤ B ^ n := by
    rw [Finset.abs_prod]
    calc
      ∏ i : Fin n, |simplexSafeFactor γ (y i) s| ≤ ∏ _i : Fin n, B :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hprefixB_s
      _ = B ^ n := by simp
  have hprodB_t : |∏ i : Fin n, simplexSafeFactor γ (y i) t| ≤ B ^ n := by
    rw [Finset.abs_prod]
    calc
      ∏ i : Fin n, |simplexSafeFactor γ (y i) t| ≤ ∏ _i : Fin n, B :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hprefixB_t
      _ = B ^ n := by simp
  have hB_nonneg : 0 ≤ B := le_trans (by positivity) hB
  calc
    |simplexKernelSafe γ s y - simplexKernelSafe γ t y| =
        |simplexSafeFactor γ (1 - ∑ i, y i) s *
            (∏ i, simplexSafeFactor γ (y i) s) -
          simplexSafeFactor γ (1 - ∑ i, y i) t *
            (∏ i, simplexSafeFactor γ (y i) t)| := rfl
    _ ≤ |simplexSafeFactor γ (1 - ∑ i, y i) s -
          simplexSafeFactor γ (1 - ∑ i, y i) t| *
          |∏ i, simplexSafeFactor γ (y i) s| +
        |simplexSafeFactor γ (1 - ∑ i, y i) t| *
          |(∏ i, simplexSafeFactor γ (y i) s) -
            ∏ i, simplexSafeFactor γ (y i) t| := by
          have h := norm_add_le
            ((simplexSafeFactor γ (1 - ∑ i, y i) s -
                simplexSafeFactor γ (1 - ∑ i, y i) t) *
              (∏ i, simplexSafeFactor γ (y i) s))
            (simplexSafeFactor γ (1 - ∑ i, y i) t *
              ((∏ i, simplexSafeFactor γ (y i) s) -
                ∏ i, simplexSafeFactor γ (y i) t))
          have heq :
              simplexSafeFactor γ (1 - ∑ i, y i) s *
                (∏ i, simplexSafeFactor γ (y i) s) -
              simplexSafeFactor γ (1 - ∑ i, y i) t *
                (∏ i, simplexSafeFactor γ (y i) t) =
                (simplexSafeFactor γ (1 - ∑ i, y i) s -
                  simplexSafeFactor γ (1 - ∑ i, y i) t) *
                  (∏ i, simplexSafeFactor γ (y i) s) +
                simplexSafeFactor γ (1 - ∑ i, y i) t *
                  ((∏ i, simplexSafeFactor γ (y i) s) -
                    ∏ i, simplexSafeFactor γ (y i) t) := by ring
          rw [← heq, Real.norm_eq_abs] at h
          simpa [Real.norm_eq_abs, abs_mul, Finset.abs_prod] using h
    _ ≤ K * |s - t| * B ^ n + B * ((n : ℝ) * K * |s - t| * B ^ (n - 1)) := by
          apply add_le_add
          · calc
              |simplexSafeFactor γ (1 - ∑ i, y i) s -
                  simplexSafeFactor γ (1 - ∑ i, y i) t| *
                  |∏ i, simplexSafeFactor γ (y i) s|
                  ≤ (K * |s - t|) * B ^ n :=
                    mul_le_mul hlastD hprodB_s (abs_nonneg _) (by positivity)
              _ = K * |s - t| * B ^ n := by ring
          · have hlastB : |simplexSafeFactor γ (1 - ∑ i, y i) t| ≤ B :=
              hlastB_t.trans (le_max_right _ _)
            have hprodD' :
                |∏ i, simplexSafeFactor γ (y i) s -
                  ∏ i, simplexSafeFactor γ (y i) t| ≤
                  (n : ℝ) * K * |s - t| * B ^ (n - 1) := by
              simpa [Finset.card_univ] using hprodD
            calc
              |simplexSafeFactor γ (1 - ∑ i, y i) t| *
                  |(∏ i, simplexSafeFactor γ (y i) s) -
                    ∏ i, simplexSafeFactor γ (y i) t|
                  ≤ B * ((n : ℝ) * K * |s - t| * B ^ (n - 1)) :=
                    mul_le_mul hlastB hprodD' (abs_nonneg _) (by positivity)
              _ = B * ((n : ℝ) * K * |s - t| * B ^ (n - 1)) := rfl
    _ = (K * B ^ n + B * ((n : ℝ) * K * B ^ (n - 1))) * |s - t| := by ring

private theorem simplexKernelSafe_integral_sub_le (n : ℕ) (γ : ℝ) (hγ : 0 < γ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |(∫ y in unitSimplex n, simplexKernelSafe γ s y) -
      ∫ y in unitSimplex n, simplexKernelSafe γ t y| ≤
        (γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
          (max 1 γ⁻¹) * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
          |s - t| * (volume (unitSimplex n)).toReal := by
  have hcompact := isCompact_unitSimplex n
  let g : ℝ → ℝ := fun z => (max γ z)⁻¹
  have hg : Continuous g := by
    apply (continuous_const.max continuous_id).inv₀
    intro z
    exact ne_of_gt (lt_of_lt_of_le hγ (le_max_left _ _))
  have hcont (u : ℝ) : Continuous (fun y : Fin n → ℝ => simplexKernelSafe γ u y) := by
    change Continuous (fun y : Fin n → ℝ =>
      g (γ + u * (1 - ∑ i, y i)) * ∏ i, g (γ + u * y i))
    fun_prop
  have his : IntegrableOn (fun y : Fin n → ℝ => simplexKernelSafe γ s y)
      (unitSimplex n) volume := (hcont s).continuousOn.integrableOn_compact hcompact
  have hit : IntegrableOn (fun y : Fin n → ℝ => simplexKernelSafe γ t y)
      (unitSimplex n) volume := (hcont t).continuousOn.integrableOn_compact hcompact
  have hdiff :
      (∫ y in unitSimplex n, simplexKernelSafe γ s y) -
        ∫ y in unitSimplex n, simplexKernelSafe γ t y =
          ∫ y in unitSimplex n, (simplexKernelSafe γ s y - simplexKernelSafe γ t y) := by
    rw [integral_sub his hit]
  have hbound : ∀ᵐ y ∂volume, y ∈ unitSimplex n →
      ‖simplexKernelSafe γ s y - simplexKernelSafe γ t y‖ ≤
        (γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
          (max 1 γ⁻¹) * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) * |s - t| :=
    Filter.Eventually.of_forall fun y hy => by
      simpa [Real.norm_eq_abs] using simplexKernelSafe_sub_le n γ y hγ hy hs ht
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae' hcompact.measure_lt_top hbound
  rw [← hdiff, Real.norm_eq_abs] at hnorm
  rw [Measure.real_def] at hnorm
  convert hnorm using 1 <;> ring

private theorem simplexKernelSafe_abs_le (n : ℕ) (γ s : ℝ) (y : Fin n → ℝ)
    (hγ : 0 < γ) (hy : y ∈ unitSimplex n) (hs : 0 ≤ s) :
    |simplexKernelSafe γ s y| ≤ (max 1 γ⁻¹) ^ (n + 1) := by
  simp only [unitSimplex, Set.mem_setOf_eq] at hy
  let B : ℝ := max 1 γ⁻¹
  have hB : 1 ≤ B := le_max_left _ _
  have hlast0 : 0 ≤ 1 - ∑ i, y i := by
    have hsum : 0 ≤ ∑ i : Fin n, y i := Finset.sum_nonneg fun i _ => hy.1 i
    linarith [hy.2, hsum]
  have hlast : |simplexSafeFactor γ (1 - ∑ i, y i) s| ≤ B :=
    (simplexSafeFactor_abs_le hγ hlast0 hs).trans (le_max_right _ _)
  have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      |simplexSafeFactor γ (y i) s| ≤ B := by
    intro i hi
    exact (simplexSafeFactor_abs_le hγ (hy.1 i) hs).trans (le_max_right _ _)
  have hprod : |∏ i : Fin n, simplexSafeFactor γ (y i) s| ≤ B ^ n := by
    rw [Finset.abs_prod]
    calc
      ∏ i : Fin n, |simplexSafeFactor γ (y i) s| ≤ ∏ _i : Fin n, B :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hcoord
      _ = B ^ n := by simp
  calc
    |simplexKernelSafe γ s y| =
        |simplexSafeFactor γ (1 - ∑ i, y i) s| *
          |∏ i : Fin n, simplexSafeFactor γ (y i) s| := by
          simp [simplexKernelSafe, abs_mul]
    _ ≤ B * B ^ n := mul_le_mul hlast hprod (abs_nonneg _) (by positivity)
    _ = B ^ (n + 1) := by
      rw [pow_succ]
      exact mul_comm _ _

private theorem simplexKernelSafe_integral_abs_le (n : ℕ) (γ s : ℝ)
    (hγ : 0 < γ) (hs : 0 ≤ s) :
    |∫ y in unitSimplex n, simplexKernelSafe γ s y| ≤
      (max 1 γ⁻¹) ^ (n + 1) * (volume (unitSimplex n)).toReal := by
  have hcompact := isCompact_unitSimplex n
  let g : ℝ → ℝ := fun z => (max γ z)⁻¹
  have hg : Continuous g := by
    apply (continuous_const.max continuous_id).inv₀
    intro z
    exact ne_of_gt (lt_of_lt_of_le hγ (le_max_left _ _))
  have hcont : Continuous (fun y : Fin n → ℝ => simplexKernelSafe γ s y) := by
    change Continuous (fun y : Fin n → ℝ =>
      g (γ + s * (1 - ∑ i, y i)) * ∏ i, g (γ + s * y i))
    fun_prop
  have his : IntegrableOn (fun y : Fin n → ℝ => simplexKernelSafe γ s y)
      (unitSimplex n) volume := hcont.continuousOn.integrableOn_compact hcompact
  have hbound : ∀ᵐ y ∂volume, y ∈ unitSimplex n →
      ‖simplexKernelSafe γ s y‖ ≤ (max 1 γ⁻¹) ^ (n + 1) :=
    Filter.Eventually.of_forall fun y hy => by
      simpa [Real.norm_eq_abs] using simplexKernelSafe_abs_le n γ s y hγ hy hs
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae' hcompact.measure_lt_top hbound
  rw [Real.norm_eq_abs, Measure.real_def] at hnorm
  exact hnorm

private theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a - c| * |b| + |c| * |b - d| := by
  rw [show a * b - c * d = (a - c) * b + c * (b - d) by ring]
  calc
    |(a - c) * b + c * (b - d)| ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]

private theorem simplexKernelSafe_integral_posPart_lipschitz (n : ℕ) (γ c : ℝ)
    (hγ : 0 < γ) :
    LipschitzWith (Real.toNNReal
      ((γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
        max 1 γ⁻¹ * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
        (volume (unitSimplex n)).toReal))
      (fun w : ℝ => ∫ y in unitSimplex n,
        simplexKernelSafe γ (max 0 (w - c)) y) := by
  apply LipschitzWith.of_dist_le'
  intro u v
  let a := max 0 (u - c)
  let b := max 0 (v - c)
  have ha : 0 ≤ a := le_max_left _ _
  have hb : 0 ≤ b := le_max_left _ _
  have hab : |a - b| ≤ |u - v| := by
    dsimp [a, b]
    calc
      |max 0 (u - c) - max 0 (v - c)| ≤ |(u - c) - (v - c)| :=
        by simpa using abs_max_sub_max_le_max 0 (u - c) 0 (v - c)
      _ = |u - v| := by congr 1 <;> ring
  calc
    dist (∫ y in unitSimplex n, simplexKernelSafe γ a y)
        (∫ y in unitSimplex n, simplexKernelSafe γ b y) =
        |(∫ y in unitSimplex n, simplexKernelSafe γ a y) -
          ∫ y in unitSimplex n, simplexKernelSafe γ b y| := by rw [Real.dist_eq]
    _ ≤ (γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
          max 1 γ⁻¹ * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
          |a - b| * (volume (unitSimplex n)).toReal :=
      simplexKernelSafe_integral_sub_le n γ hγ ha hb
    _ ≤ ((γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
          max 1 γ⁻¹ * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
          (volume (unitSimplex n)).toReal) * |u - v| := by
      calc
        _ = (γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
              max 1 γ⁻¹ * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
              (volume (unitSimplex n)).toReal * |a - b| := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)
    _ = _ := by rw [Real.dist_eq]

private theorem locallyLipschitz_pow (n : ℕ) :
    LocallyLipschitz (fun x : ℝ => x ^ n) := by
  have hpow : ContDiff ℝ 1 (fun x : ℝ => x ^ n) := by fun_prop
  exact hpow.locallyLipschitz

/-- The density term is a positive-part power times a fixed-simplex integral. -/
private theorem roughDensityTerm_eq_safe_simplex (γ w : ℝ) {j : ℕ}
    (hγ : 0 < γ) (hj : 2 ≤ j) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j =
      (1 / (j.factorial : ℝ)) * (max 0 (w - (j : ℝ) * γ)) ^ (j - 1) *
        ∫ y in unitSimplex (j - 1),
          simplexKernelSafe γ (max 0 (w - (j : ℝ) * γ)) y := by
  let s := w - (j : ℝ) * γ
  have hn1 : 1 ≤ j - 1 := by omega
  have hpow : (0 : ℝ) ^ (j - 1) = 0 := zero_pow (by omega)
  by_cases hsneg : s < 0
  · have hw : w < (j : ℝ) * γ := by dsimp [s] at hsneg; linarith
    rw [roughDensityTerm_eq_zero_of_lt γ w hγ hj hw]
    simp [s, max_eq_left hsneg.le, hpow]
  · by_cases hszero : s = 0
    · have heq : w = (j : ℝ) * γ := by dsimp [s] at hszero; linarith
      rw [heq, roughDensityTerm_eq_zero_at_support γ j hj]
      simp [s, hszero, hpow]
    · have hs : 0 < s := lt_of_le_of_ne (le_of_not_gt hsneg) (Ne.symm hszero)
      have hw : w = (j : ℝ) * γ + s := by dsimp [s]; ring
      have hformula := term_affine_simplex γ s j hj hs
      have hSmeas : MeasurableSet (unitSimplex (j - 1)) := by
        have h₁ : MeasurableSet {y : Fin (j - 1) → ℝ | ∀ i, 0 ≤ y i} := by
          simpa only [Set.iInter_ofPred] using
            (MeasurableSet.iInter fun i =>
              measurableSet_le measurable_const (measurable_pi_apply i))
        have h₂ : MeasurableSet {y : Fin (j - 1) → ℝ | ∑ i, y i ≤ 1} :=
          measurableSet_le (by fun_prop) measurable_const
        simpa only [unitSimplex, Set.setOf_and] using h₁.inter h₂
      have hkernel : ∀ y ∈ unitSimplex (j - 1),
          simplexKernelSafe γ s y = simplexKernel γ s y := by
        intro y hy
        simp only [unitSimplex, Set.mem_setOf_eq] at hy
        have hlast : 0 ≤ 1 - ∑ i, y i := by linarith
        have hlast' : γ ≤ γ + s * (1 - ∑ i, y i) := by
          nlinarith [mul_nonneg hs.le hlast]
        have hcoord : ∀ i, γ ≤ γ + s * y i := by
          intro i
          nlinarith [mul_nonneg hs.le (hy.1 i)]
        have hprod :
            (∏ i, (max γ (γ + s * y i))⁻¹) = ∏ i, (γ + s * y i)⁻¹ := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [max_eq_right (hcoord i)]
        simp only [simplexKernelSafe, simplexSafeFactor, simplexKernel]
        rw [max_eq_right hlast', hprod]
      calc
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j =
            ArtinPrimitiveRoots.Sieve.roughDensityTerm γ ((j : ℝ) * γ + s) j := by rw [hw]
        _ = (1 / (j.factorial : ℝ)) * s ^ (j - 1) *
              ∫ y in unitSimplex (j - 1), simplexKernel γ s y := hformula
        _ = (1 / (j.factorial : ℝ)) * (max 0 s) ^ (j - 1) *
              ∫ y in unitSimplex (j - 1),
                simplexKernelSafe γ (max 0 s) y := by
          rw [max_eq_right hs.le]
          rw [← setIntegral_congr_fun hSmeas hkernel]

private theorem locallyLipschitz_higherDensityTerm (γ : ℝ) (hγ : 0 < γ)
    (j : ℕ) (hj : 2 ≤ j) :
    LocallyLipschitz (fun w : ℝ =>
      ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j) := by
  let c : ℝ := (j : ℝ) * γ
  let u : ℝ → ℝ := fun w => max 0 (w - c)
  let J : ℝ → ℝ := fun s =>
    ∫ y in unitSimplex (j - 1), simplexKernelSafe γ s y
  have hshift : LipschitzWith 1 (fun w : ℝ => w - c) := by
    simpa using LipschitzWith.id.sub (LipschitzWith.const c)
  have huLip : LipschitzWith 1 u := by
    simpa [u, Function.comp_def] using
      (LipschitzWith.id.const_max (0 : ℝ)).comp hshift
  have hu : LocallyLipschitz u := huLip.locallyLipschitz
  have hpow : LocallyLipschitz (fun w : ℝ => (u w) ^ (j - 1)) :=
    (locallyLipschitz_pow (j - 1)).comp hu
  have hJ : LocallyLipschitz (fun w : ℝ => J (u w)) := by
    exact (simplexKernelSafe_integral_posPart_lipschitz (j - 1) γ c hγ).locallyLipschitz
  have hpair : LocallyLipschitz (fun w : ℝ => ((u w) ^ (j - 1), J (u w))) :=
    hpow.prodMk hJ
  have hbilin : ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      (1 / (j.factorial : ℝ)) * p.1 * p.2) := by fun_prop
  have hmodel : LocallyLipschitz (fun w : ℝ =>
      (1 / (j.factorial : ℝ)) * ((u w) ^ (j - 1) * J (u w))) := by
    simpa [Function.comp_def, mul_assoc] using hbilin.locallyLipschitz.comp hpair
  have heq : (fun w : ℝ => ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j) =
      (fun w : ℝ => (1 / (j.factorial : ℝ)) * ((u w) ^ (j - 1) * J (u w))) := by
    funext w
    simpa [u, J, c, mul_assoc] using
      roughDensityTerm_eq_safe_simplex γ w hγ hj
  rw [heq]
  exact hmodel

private abbrev PositiveGammaParam := {p : ℝ × ℝ // 0 < p.1}

private instance : LocallyCompactSpace PositiveGammaParam :=
  (isOpen_Ioi.preimage continuous_fst).locallyCompactSpace

private theorem continuous_simplexKernelSafe_integral (n : ℕ) :
    Continuous (fun p : PositiveGammaParam =>
      ∫ y in unitSimplex n, simplexKernelSafe p.1.1 p.1.2 y) := by
  apply continuous_parametric_integral_of_continuous
  · change Continuous (fun q : PositiveGammaParam × (Fin n → ℝ) =>
        (max q.1.1.1 (q.1.1.1 + q.1.1.2 * (1 - ∑ i, q.2 i)))⁻¹ *
          ∏ i, (max q.1.1.1 (q.1.1.1 + q.1.1.2 * q.2 i))⁻¹)
    have hγpos (q : PositiveGammaParam × (Fin n → ℝ)) : 0 < q.1.1.1 := q.1.property
    have hlast (q : PositiveGammaParam × (Fin n → ℝ)) :
        max q.1.1.1 (q.1.1.1 + q.1.1.2 * (1 - ∑ i, q.2 i)) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (hγpos q) (le_max_left _ _))
    have hcoord (q : PositiveGammaParam × (Fin n → ℝ)) (i : Fin n) :
        max q.1.1.1 (q.1.1.1 + q.1.1.2 * q.2 i) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (hγpos q) (le_max_left _ _))
    fun_prop (disch := aesop)
  · exact isCompact_unitSimplex n

private abbrev GoodDensityParam := {p : ℝ × ℝ // 0 < p.1 ∧ p.1 < p.2}

private theorem continuous_higherDensityTermModel (j : ℕ) (hj : 2 ≤ j) :
    Continuous (fun p : GoodDensityParam =>
      (1 / (j.factorial : ℝ)) *
        (max 0 (p.1.2 - (j : ℝ) * p.1.1)) ^ (j - 1) *
          ∫ y in unitSimplex (j - 1),
            simplexKernelSafe p.1.1 (max 0 (p.1.2 - (j : ℝ) * p.1.1)) y) := by
  let u : GoodDensityParam → ℝ := fun p => max 0 (p.1.2 - (j : ℝ) * p.1.1)
  let q : GoodDensityParam → PositiveGammaParam :=
    fun p => ⟨(p.1.1, u p), p.2.1⟩
  let J : PositiveGammaParam → ℝ := fun p =>
    ∫ y in unitSimplex (j - 1), simplexKernelSafe p.1.1 p.1.2 y
  have hu : Continuous u := by fun_prop
  have hq : Continuous q := by fun_prop
  have hJ : Continuous J := continuous_simplexKernelSafe_integral (j - 1)
  have hJcomp : Continuous (fun p => J (q p)) := hJ.comp hq
  have hfactor : Continuous (fun p : GoodDensityParam => (u p) ^ (j - 1)) := by fun_prop
  have hconst : Continuous (fun _ : GoodDensityParam => (1 / (j.factorial : ℝ))) :=
    continuous_const
  apply (hconst.mul (hfactor.mul hJcomp)).congr
  intro p
  simp [u, q, J]
  ring

private theorem continuousOn_roughDensityTerm (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensityTerm p.1 p.2 j)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun p : GoodDensityParam =>
    ArtinPrimitiveRoots.Sieve.roughDensityTerm p.1.1 p.1.2 j)
  by_cases hj0 : j = 0
  · subst j
    simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_pos (rfl : (0 : ℕ) = 0)]
    exact continuous_const
  · by_cases hj1 : j = 1
    · subst j
      simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm,
        if_neg (by decide : (1 : ℕ) ≠ 0), if_pos (rfl : (1 : ℕ) = 1), one_div]
      have hW : Continuous (fun p : GoodDensityParam => p.1.2) := by fun_prop
      have hWne : ∀ p : GoodDensityParam, p.1.2 ≠ 0 := fun p =>
        ne_of_gt (p.2.1.trans p.2.2)
      exact hW.inv₀ hWne
    · have hj2 : 2 ≤ j := by omega
      apply (continuous_higherDensityTermModel j hj2).congr
      intro p
      exact (roughDensityTerm_eq_safe_simplex p.1.1 p.1.2 p.2.1 hj2).symm

private theorem roughDensity_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
  intro p hp
  let γ₀ : ℝ := p.1 / 2
  let W : ℝ := p.2 + 1
  have hγ₀pos : 0 < γ₀ := by dsimp [γ₀]; linarith [hp.1]
  have hγ₀γ : γ₀ ≤ p.1 := by dsimp [γ₀]; linarith [hp.1]
  have hγ₀W : γ₀ < W := by dsimp [γ₀, W]; linarith [hp.1, hp.2]
  let N : ℕ := ⌊W / γ₀⌋₊ + 1
  let fsum : ℝ × ℝ → ℝ := fun q =>
    ∑ j ∈ Finset.range N, ArtinPrimitiveRoots.Sieve.roughDensityTerm q.1 q.2 j
  have hfsum : ContinuousOn fsum {q : ℝ × ℝ | 0 < q.1 ∧ q.1 < q.2} := by
    dsimp [fsum]
    exact continuousOn_finsetSum (Finset.range N) fun j hj => continuousOn_roughDensityTerm j
  let U : Set (ℝ × ℝ) := {q | γ₀ < q.1 ∧ q.2 < W}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (isOpen_Ioi.preimage continuous_fst).inter (isOpen_Iio.preimage continuous_snd)
  have hpU : p ∈ U := by
    simp only [U, Set.mem_setOf_eq]
    constructor
    · exact half_lt_self hp.1
    · dsimp [W]
      linarith
  have hUevent : U ∈ 𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ q.1 < q.2}] p :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hUopen.mem_nhds hpU)
  have hfinite :
      (fun q : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity q.1 q.2) =ᶠ[
        𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ q.1 < q.2}] p] fsum := by
    filter_upwards [self_mem_nhdsWithin, hUevent] with q hq hqU
    rcases hq with ⟨hqγ, hqγw⟩
    rcases hqU with ⟨hγ₀q, hqW⟩
    have hqγW : q.1 < W := hqγw.trans hqW
    simpa [fsum, N] using
      roughDensity_eq_sum_uniform q.1 q.2 W γ₀ hqγ hγ₀pos (le_of_lt hγ₀q) hqγW hqW.le
  have hpoint :
      ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2 = fsum p := by
    have hpγW : p.1 < W := by dsimp [W]; linarith [hp.2]
    have hpW : p.2 ≤ W := by dsimp [W]; linarith
    simpa [fsum, N] using
      roughDensity_eq_sum_uniform p.1 p.2 W γ₀ hp.1 hγ₀pos hγ₀γ hpγW hpW
  exact (hfsum p hp).congr_of_eventuallyEq hfinite hpoint

private theorem locallyLipschitzOn_finsetSum {ι : Type*} [DecidableEq ι]
    (s : Set ℝ) (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, LocallyLipschitzOn s (f i)) :
    LocallyLipschitzOn s (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (LocallyLipschitz.const (0 : ℝ)).locallyLipschitzOn
  | @insert a S ha ih =>
      have hfa := hf a (Finset.mem_insert_self a S)
      have hfS : ∀ i ∈ S, LocallyLipschitzOn s (f i) := fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert, ha] using hfa.add (ih hfS)

private theorem locallyLipschitzOn_roughDensityTerm (γ : ℝ) (hγ : 0 < γ) (j : ℕ) :
    LocallyLipschitzOn (Set.Ioi γ)
      (fun w => ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j) := by
  by_cases hj0 : j = 0
  · subst j
    simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_pos rfl]
    exact (LocallyLipschitz.const (0 : ℝ)).locallyLipschitzOn
  · by_cases hj1 : j = 1
    · subst j
      simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm,
        if_neg (by decide : (1 : ℕ) ≠ 0), if_pos (rfl : (1 : ℕ) = 1), one_div]
      have hrec : ContDiffOn ℝ 1 (fun w : ℝ => w⁻¹) (Set.Ioi γ) := by
        exact contDiffOn_id.inv fun w hw => ne_of_gt (lt_trans hγ hw)
      simpa [one_div] using hrec.locallyLipschitzOn (convex_Ioi γ)
    · have hj : 2 ≤ j := by omega
      exact (locallyLipschitz_higherDensityTerm γ hγ j hj).locallyLipschitzOn

private theorem locallyLipschitzOn_roughDensity (γ : ℝ) (hγ : 0 < γ) :
    LocallyLipschitzOn (Set.Ioi γ)
      (fun w => ArtinPrimitiveRoots.Sieve.roughDensity γ w) := by
  intro w hw
  let W : ℝ := w + 1
  change γ < w at hw
  have hγW : γ < W := by dsimp [W]; linarith
  let N : ℕ := ⌊W / γ⌋₊ + 1
  let f : ℝ → ℝ := fun z =>
    ∑ j ∈ Finset.range N, ArtinPrimitiveRoots.Sieve.roughDensityTerm γ z j
  have hf : LocallyLipschitzOn (Set.Ioi γ) f := by
    dsimp [f]
    exact locallyLipschitzOn_finsetSum (Set.Ioi γ) (Finset.range N)
      (fun j z => ArtinPrimitiveRoots.Sieve.roughDensityTerm γ z j) fun j hj =>
        locallyLipschitzOn_roughDensityTerm γ hγ j
  obtain ⟨K, t, ht, hLip⟩ := hf hw
  have hwW : w < W := by dsimp [W]; linarith
  have hWmem : Set.Iio W ∈ 𝓝[Set.Ioi γ] w :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds hwW)
  let t' := t ∩ Set.Iio W
  have ht' : t' ∈ 𝓝[Set.Ioi γ] w := by
    exact Filter.inter_mem ht hWmem
  refine ⟨K, t', ht', ?_⟩
  intro u hu v hv
  have huEq : ArtinPrimitiveRoots.Sieve.roughDensity γ u = f u := by
    have huW : u ≤ W := le_of_lt hu.2
    simpa [f, N] using roughDensity_eq_sum_bounded γ u W hγ hγW huW
  have hvEq : ArtinPrimitiveRoots.Sieve.roughDensity γ v = f v := by
    have hvW : v ≤ W := le_of_lt hv.2
    simpa [f, N] using roughDensity_eq_sum_bounded γ v W hγ hγW hvW
  change edist (ArtinPrimitiveRoots.Sieve.roughDensity γ u)
    (ArtinPrimitiveRoots.Sieve.roughDensity γ v) ≤ K * edist u v
  rw [huEq, hvEq]
  exact hLip hu.1 hv.1

private theorem roughDensity_lipschitzOnCompact (γ w₀ w₁ : ℝ)
    (hγ : 0 < γ) (hγw₀ : γ < w₀) (hw₀w₁ : w₀ ≤ w₁) :
    ∃ K : NNReal, LipschitzOnWith K (fun w => ArtinPrimitiveRoots.Sieve.roughDensity γ w)
      (Set.Icc w₀ w₁) := by
  have hdom : Set.Icc w₀ w₁ ⊆ Set.Ioi γ := fun _ hu => hγw₀.trans_le hu.1
  exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    ((locallyLipschitzOn_roughDensity γ hγ).mono hdom)

/-- The one-factor pushforward identity is the logarithmic integral itself. -/
private theorem roughTupleIntegral_one (γ : ℝ) (hγ : 0 < γ) (x : ℝ) (hx : 2 ≤ x)
    (l r : ℝ) (hl : Real.rpow x γ < l) (hr : l ≤ r) :
    roughTupleIntegral x γ l r 1 =
      (1 / Real.log x) * ∫ y in l..r,
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ (Real.log y / Real.log x) 1 := by
  have hx1 : 1 < x := by linarith
  have hxpow : 1 < Real.rpow x γ := Real.one_lt_rpow hx1 hγ
  have hl1 : 1 < l := lt_trans hxpow hl
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  let mp := volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
  rw [roughTupleIntegral]
  simp only [Nat.factorial_one, Nat.cast_one, one_div]
  rw [← mp.symm.integral_comp']
  simp only [MeasurableEquiv.piUnique_symm_apply, Finset.univ_unique, Finset.prod_singleton]
  simp [ArtinPrimitiveRoots.Sieve.roughDensityTerm, uniqueElim]
  have hleft :
      (∫ t : ℝ, if Real.rpow x γ < t ∧ l ≤ t ∧ t ≤ r then (Real.log t)⁻¹ else 0) =
        ∫ t in Set.Icc l r, (Real.log t)⁻¹ := by
    calc
      _ = ∫ t : ℝ, Set.indicator (Set.Icc l r) (fun t => (Real.log t)⁻¹) t := by
        apply integral_congr_ae
        filter_upwards with t
        have hP : (Real.rpow x γ < t ∧ l ≤ t ∧ t ≤ r) ↔ t ∈ Set.Icc l r := by
          constructor
          · rintro ⟨_, hlt, hrt⟩
            exact ⟨hlt, hrt⟩
          · intro ht
            exact ⟨lt_of_lt_of_le hl ht.1, ht.1, ht.2⟩
        simp only [Set.indicator]
        exact if_congr hP rfl rfl
      _ = _ := integral_indicator measurableSet_Icc
  calc
    (∫ t : ℝ, if Real.rpow x γ < t ∧ l ≤ t ∧ t ≤ r then (Real.log t)⁻¹ else 0) =
        ∫ t in Set.Icc l r, (Real.log t)⁻¹ := hleft
    _ = ∫ y in l..r, (Real.log y)⁻¹ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]
    _ = (Real.log x)⁻¹ * ∫ y in l..r, Real.log x / Real.log y := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul]
      field_simp [hlogx]

private noncomputable def roughLogProductMap (L : ℝ) {n : ℕ}
    (t : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = Fin.last n then ∏ k, t k else Real.log (t i) / L

private noncomputable def roughLogProductJac (L : ℝ) {n : ℕ}
    (t : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i k => if i = Fin.last n then
      (((List.finRange (n + 1)).map t).eraseIdx k.val).prod
    else if i = k then (L * t i)⁻¹ else 0

set_option maxHeartbeats 1000000 in
private theorem roughLogProductMap_hasFDerivAt {n : ℕ} {L : ℝ}
    (t : Fin (n + 1) → ℝ) (hL : L ≠ 0) (ht : ∀ i, t i ≠ 0) :
    HasFDerivAt (fun s => roughLogProductMap L s)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (roughLogProductJac L t))) t := by
  classical
  let D := roughLogProductJac L t
  let A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' D)
  change HasFDerivAt (fun s i => roughLogProductMap L s i) A t
  have hA : ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i ∘L A) = A := by
    ext s i
    simp
  rw [← hA]
  apply hasFDerivAt_pi.2
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    have hp := hasFDerivAt_list_prod_finRange' (𝕜 := ℝ) (n := n + 1) (x := t)
    have hp' : HasFDerivAt (fun s : Fin (n + 1) → ℝ => ∏ k, s k)
        (∑ k : Fin (n + 1),
          (((List.finRange (n + 1)).map t).eraseIdx k.val).prod •
            (ContinuousLinearMap.proj k : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)) t := by
      convert hp using 1
      · ext s
        simp [Fin.prod_univ_def]
      · ext h
        simp [List.eraseIdx_eq_take_drop_succ, List.prod_append,
          ContinuousLinearMap.smulRight_apply, smul_eq_mul, op_smul_eq_smul,
          mul_assoc, mul_comm, mul_left_comm]
    have hlin :
        ∑ k : Fin (n + 1),
          (((List.finRange (n + 1)).map t).eraseIdx k.val).prod •
            (ContinuousLinearMap.proj k : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) =
        ContinuousLinearMap.proj (Fin.last n) ∘SL A := by
      ext h
      simp [A, D, roughLogProductJac, Matrix.toLin'_apply, Matrix.mulVec,
        Matrix.mulVec_apply_eq_sum, dotProduct, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    simpa [roughLogProductMap, A, D, roughLogProductJac] using hp'.congr_fderiv hlin
  · have hscalar : HasDerivAt (fun z : ℝ => Real.log z / L)
        ((t i)⁻¹ / L) (t i) := by
      exact (Real.hasDerivAt_log (ht i)).div_const L
    have hid : HasFDerivAt (fun s : Fin (n + 1) → ℝ => s i)
        (ContinuousLinearMap.proj (R := ℝ) i) t := by
      exact hasFDerivAt_apply i t
    have hcomp := HasDerivAt.comp_hasFDerivAt
      (f := fun s : Fin (n + 1) → ℝ => s i) t hscalar hid
    have hlin : ContinuousLinearMap.proj i ∘SL A =
        ((t i)⁻¹ / L) • ContinuousLinearMap.proj i := by
      ext h
      change (∑ k : Fin (n + 1), roughLogProductJac L t i k * h k) =
        (t i)⁻¹ / L * h i
      have hcoef : (L * t i)⁻¹ = (t i)⁻¹ / L := by
        field_simp [hL, ht i]
      simp [roughLogProductJac, hi, hcoef, eq_comm]
    simpa [roughLogProductMap, Function.comp_def, hi, A, D, roughLogProductJac] using
      hcomp.congr_fderiv hlin.symm

private theorem list_finRange_take_prod {n : ℕ} (t : Fin (n + 1) → ℝ) :
    (List.take n ((List.finRange (n + 1)).map t)).prod =
      ∏ i : Fin n, t (Fin.castSucc i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.take_succ_cons, List.prod_cons,
        Fin.prod_univ_succ]
      simp only [List.map_map, Function.comp_def, Fin.castSucc_zero, Fin.castSucc_succ]
      congr 1
      simpa only [List.map_map, Function.comp_def, Fin.castSucc_succ] using
        ih (fun k => t (Fin.succ k))

private theorem roughLogProductJac_abs_det {n : ℕ} {L : ℝ}
    (t : Fin (n + 1) → ℝ) (hL : 0 < L) (ht : ∀ i, 0 < t i) :
    |(roughLogProductJac L t).det| = L⁻¹ ^ n := by
  classical
  let D := roughLogProductJac L t
  have hLower : D.IsLowerTriangular := by
    intro i k hik
    by_cases hi : i = Fin.last n
    · subst i
      exact False.elim ((not_lt_of_ge (Fin.le_last k)) hik)
    · by_cases hik' : i = k
      · subst k
        exact (lt_irrefl i hik).elim
      · simp [D, roughLogProductJac, hi, hik']
  have hlastDiag : D (Fin.last n) (Fin.last n) =
      ∏ i : Fin n, t (Fin.castSucc i) := by
    simp only [D, roughLogProductJac, if_pos rfl, Fin.val_last]
    rw [List.eraseIdx_eq_take_drop_succ, List.prod_append]
    let l : List ℝ := (List.finRange (n + 1)).map t
    have hlen : l.length = n + 1 := by simp [l]
    have hdrop : l.drop (n + 1) = [] := by
      rw [← hlen]
      exact List.drop_length
    rw [hdrop, List.prod_nil, mul_one]
    exact list_finRange_take_prod (n := n) t
  have htopDiag :
      ∏ i : Fin n, D (Fin.castSucc i) (Fin.castSucc i) =
        ∏ i : Fin n, (L * t (Fin.castSucc i))⁻¹ := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [D, roughLogProductJac]
  have hdiag :
      ∏ i : Fin (n + 1), D i i =
        (∏ i : Fin n, (L * t (Fin.castSucc i))⁻¹) *
          ∏ i : Fin n, t (Fin.castSucc i) := by
    rw [Fin.prod_univ_castSucc, htopDiag, hlastDiag]
  have hcancel :
      (∏ i : Fin n, (L * t (Fin.castSucc i))⁻¹) *
        ∏ i : Fin n, t (Fin.castSucc i) = L⁻¹ ^ n := by
    rw [← Finset.prod_mul_distrib]
    calc
      ∏ i : Fin n, (L * t (Fin.castSucc i))⁻¹ * t (Fin.castSucc i) =
          ∏ _i : Fin n, L⁻¹ := by
            apply Finset.prod_congr rfl
            intro i hi
            field_simp [ne_of_gt hL, ne_of_gt (ht (Fin.castSucc i))]
      _ = L⁻¹ ^ n := by simp
  have hdet : D.det = L⁻¹ ^ n := by
    rw [Matrix.det_of_isLowerTriangular D hLower, hdiag]
    exact hcancel
  rw [hdet]
  exact abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hL.le) n)

private def roughTupleSource {n : ℕ} (A l r : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {t | (∀ i, A ≤ t i) ∧ l ≤ ∏ i, t i ∧ (∏ i, t i) ≤ r}

private def roughTupleImage (x γ l r : ℝ) {n : ℕ} : Set (Fin (n + 1) → ℝ) :=
  {q | (∀ i : Fin n, γ ≤ q (Fin.castSucc i)) ∧
    l ≤ q (Fin.last n) ∧ q (Fin.last n) ≤ r ∧
    Real.rpow x γ * (∏ i : Fin n, Real.rpow x (q (Fin.castSucc i))) ≤ q (Fin.last n)}

private theorem roughLogProductMap_image_eq {n : ℕ} (x γ l r : ℝ)
    (hx : 2 ≤ x) (hγ : 0 < γ) :
    Set.image (roughLogProductMap (Real.log x) :
        (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
      (roughTupleSource (Real.rpow x γ) l r) = roughTupleImage x γ l r := by
  classical
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := lt_trans (by norm_num) hx1
  have hxne : x ≠ 1 := ne_of_gt hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hA : 0 < Real.rpow x γ := Real.rpow_pos_of_pos hxpos γ
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases ht with ⟨htA, htl, htr⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have hti := htA (Fin.castSucc i)
      have hlog := Real.log_le_log hA hti
      have hlogA : Real.log (Real.rpow x γ) = γ * Real.log x := Real.log_rpow hxpos γ
      rw [hlogA] at hlog
      simp only [roughLogProductMap, Fin.castSucc_ne_last]
      exact (le_div_iff₀ hL).2 hlog
    · change l ≤ roughLogProductMap (Real.log x) t (Fin.last n)
      simp only [roughLogProductMap, if_pos rfl]
      exact htl
    · change roughLogProductMap (Real.log x) t (Fin.last n) ≤ r
      simp only [roughLogProductMap, if_pos rfl]
      exact htr
    · have hfirst : ∏ i : Fin n,
          Real.rpow x (roughLogProductMap (Real.log x) t (Fin.castSucc i)) =
            ∏ i : Fin n, t (Fin.castSucc i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have htiPos : 0 < t (Fin.castSucc i) := lt_of_lt_of_le hA (htA (Fin.castSucc i))
        have hmapI : roughLogProductMap (Real.log x) t (Fin.castSucc i) =
            Real.log (t (Fin.castSucc i)) / Real.log x := by
          simp [roughLogProductMap, Fin.castSucc_ne_last]
        rw [hmapI]
        simpa [Real.logb] using Real.rpow_logb hxpos hxne htiPos
      have hlast : Real.rpow x γ ≤ t (Fin.last n) := htA (Fin.last n)
      have hPpos : 0 < ∏ i : Fin n, t (Fin.castSucc i) :=
        Finset.prod_pos fun i hi => lt_of_lt_of_le hA (htA (Fin.castSucc i))
      have hprod : ∏ i : Fin (n + 1), t i =
          (∏ i : Fin n, t (Fin.castSucc i)) * t (Fin.last n) := Fin.prod_univ_castSucc _
      change Real.rpow x γ *
          ∏ i : Fin n, Real.rpow x (roughLogProductMap (Real.log x) t (Fin.castSucc i)) ≤
        roughLogProductMap (Real.log x) t (Fin.last n)
      rw [hfirst]
      calc
        Real.rpow x γ * (∏ i : Fin n, t (Fin.castSucc i)) ≤
            (∏ i : Fin n, t (Fin.castSucc i)) * t (Fin.last n) := by
          calc
            _ = (∏ i : Fin n, t (Fin.castSucc i)) * Real.rpow x γ := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hlast hPpos.le
        _ = roughLogProductMap (Real.log x) t (Fin.last n) := by
          simp only [roughLogProductMap, if_pos rfl]
          exact hprod.symm
  · intro hq
    rcases hq with ⟨hu, hqlo, hqhi, hqprod⟩
    let p : Fin n → ℝ := fun i => Real.rpow x (q (Fin.castSucc i))
    let P : ℝ := ∏ i : Fin n, p i
    let z : ℝ := q (Fin.last n) / P
    let t : Fin (n + 1) → ℝ := Fin.snoc p z
    have hpPos : ∀ i, 0 < p i := fun i => Real.rpow_pos_of_pos hxpos _
    have hPpos : 0 < P := by
      dsimp [P]
      exact Finset.prod_pos fun i hi => hpPos i
    have htFirst : ∀ i : Fin n, Real.rpow x γ ≤ t (Fin.castSucc i) := by
      intro i
      dsimp [t, p]
      rw [Fin.snoc_castSucc]
      exact (Real.rpow_le_rpow_left_iff hx1).2 (hu i)
    have htLast : Real.rpow x γ ≤ t (Fin.last n) := by
      dsimp [t, z]
      rw [Fin.snoc_last]
      exact (le_div_iff₀ hPpos).2 hqprod
    have hprod : ∏ i : Fin (n + 1), t i = q (Fin.last n) := by
      rw [Fin.prod_univ_castSucc]
      simp only [t, Fin.snoc_castSucc, Fin.snoc_last]
      change P * z = q (Fin.last n)
      dsimp [z]
      exact mul_div_cancel₀ _ (ne_of_gt hPpos)
    have htSource : t ∈ roughTupleSource (Real.rpow x γ) l r := by
      refine ⟨?_, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
        · exact htFirst i'
        · exact htLast
      · rw [hprod]
        exact hqlo
      · rw [hprod]
        exact hqhi
    have hmap : roughLogProductMap (Real.log x) t = q := by
      funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨i, hk⟩ | hk
      · rw [hk]
        have hlogrpow : Real.log (Real.rpow x (q (Fin.castSucc i))) / Real.log x =
            q (Fin.castSucc i) := by
          have hlog : Real.log (Real.rpow x (q (Fin.castSucc i))) =
              q (Fin.castSucc i) * Real.log x := by
            simpa only [Real.rpow_eq_pow] using Real.log_rpow hxpos (q (Fin.castSucc i))
          calc
            _ = (q (Fin.castSucc i) * Real.log x) / Real.log x := by rw [hlog]
            _ = q (Fin.castSucc i) := by field_simp [ne_of_gt hL]
        have hmapI : roughLogProductMap (Real.log x) t (Fin.castSucc i) =
            q (Fin.castSucc i) := by
          simp only [roughLogProductMap, if_neg (Fin.castSucc_ne_last i)]
          simp only [t, Fin.snoc_castSucc, p]
          exact hlogrpow
        exact hmapI
      · rw [hk]
        simp only [roughLogProductMap, if_true]
        exact hprod
    exact ⟨t, htSource, hmap⟩

private theorem measurableSet_roughTupleSource {n : ℕ} (A l r : ℝ) :
    MeasurableSet (roughTupleSource (n := n) A l r) := by
  have hcoords : MeasurableSet {t : Fin (n + 1) → ℝ | ∀ i, A ≤ t i} := by
    have hconst : Measurable (fun _ : Fin (n + 1) → ℝ => A) := measurable_const
    have h := MeasurableSet.iInter fun i : Fin (n + 1) =>
      measurableSet_le hconst (measurable_pi_apply i)
    simpa only [Set.iInter_ofPred] using h
  have hprod : Measurable (fun t : Fin (n + 1) → ℝ => ∏ i, t i) := by fun_prop
  have hlo : MeasurableSet {t : Fin (n + 1) → ℝ | l ≤ ∏ i, t i} :=
    measurableSet_le measurable_const hprod
  have hhi : MeasurableSet {t : Fin (n + 1) → ℝ | (∏ i, t i) ≤ r} :=
    measurableSet_le hprod measurable_const
  simpa [roughTupleSource, Set.setOf_and] using hcoords.inter (hlo.inter hhi)

private theorem roughTupleIntegral_eq_source (x γ l r : ℝ) {n : ℕ}
    (hx : 2 ≤ x) :
    roughTupleIntegral x γ l r (n + 1) =
      (1 / ((n + 1).factorial : ℝ)) *
        ∫ t in roughTupleSource (n := n) (Real.rpow x γ) l r,
          ∏ i : Fin (n + 1), 1 / Real.log (t i) := by
  classical
  let A := Real.rpow x γ
  have hx1 : 1 < x := by linarith
  have hA : 0 < A := Real.rpow_pos_of_pos (by linarith) γ
  have hpi :
      (Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioi A)) =ᵐ[volume]
        Set.Ici (fun _ : Fin (n + 1) => A) := by
    have h := MeasureTheory.Measure.univ_pi_Ioi_ae_eq_Ici
      (μ := fun _ : Fin (n + 1) => (volume : Measure ℝ)) (f := fun _ => A)
    simpa only [← MeasureTheory.volume_pi] using h
  have hcoordsAE : ∀ᵐ t : Fin (n + 1) → ℝ ∂volume,
      (∀ i, A < t i) ↔ ∀ i, A ≤ t i := by
    filter_upwards [hpi] with t ht
    simpa [Set.mem_pi, Set.mem_univ, Set.mem_Ioi, Set.mem_Ici, Pi.le_def] using ht
  have hfun : (fun t : Fin (n + 1) → ℝ =>
        if (∀ i, Real.rpow x γ < t i) ∧ l ≤ ∏ i, t i ∧ (∏ i, t i) ≤ r then
          ∏ i : Fin (n + 1), 1 / Real.log (t i) else 0) =ᵐ[volume]
      (fun t => Set.indicator (roughTupleSource (n := n) A l r)
        (fun t : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (t i)) t) := by
    filter_upwards [hcoordsAE] with t ht
    have hcoord : (∀ i, Real.rpow x γ < t i) ↔ (∀ i, A ≤ t i) := by
      simpa [A] using ht
    simp only [Set.indicator]
    apply if_congr
    · exact and_congr hcoord Iff.rfl
    · rfl
    · rfl
  unfold roughTupleIntegral
  rw [integral_congr_ae hfun, integral_indicator (measurableSet_roughTupleSource A l r)]

private theorem roughLogProductMap_injOn_source {n : ℕ} {L A l r : ℝ}
    (hL : 0 < L) (hA : 0 < A) :
    Set.InjOn (roughLogProductMap L : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
      (roughTupleSource (n := n) A l r) := by
  intro t ht u hu hmap
  have hfirst (i : Fin n) : t (Fin.castSucc i) = u (Fin.castSucc i) := by
    have hm := congrFun hmap (Fin.castSucc i)
    simp only [roughLogProductMap, Fin.castSucc_ne_last] at hm
    have hlog : Real.log (t (Fin.castSucc i)) = Real.log (u (Fin.castSucc i)) := by
      have := congrArg (fun z : ℝ => z * L) hm
      simpa [div_eq_mul_inv, mul_assoc, ne_of_gt hL] using this
    apply Real.log_injOn_pos
      (lt_of_lt_of_le hA (ht.1 (Fin.castSucc i)))
      (lt_of_lt_of_le hA (hu.1 (Fin.castSucc i)))
    exact hlog
  have hfirstProd : ∏ i : Fin n, t (Fin.castSucc i) =
      ∏ i : Fin n, u (Fin.castSucc i) := by
    exact Finset.prod_congr rfl fun i _ => hfirst i
  have hlast : t (Fin.last n) = u (Fin.last n) := by
    have hm :
        (∏ i : Fin n, t (Fin.castSucc i)) * t (Fin.last n) =
          (∏ i : Fin n, u (Fin.castSucc i)) * u (Fin.last n) := by
      simpa [roughLogProductMap, Fin.prod_univ_castSucc] using
        congrFun hmap (Fin.last n)
    have hpos : 0 < ∏ i : Fin n, t (Fin.castSucc i) :=
      Finset.prod_pos fun i _ => lt_of_lt_of_le hA (ht.1 (Fin.castSucc i))
    have hposU : 0 < ∏ i : Fin n, u (Fin.castSucc i) := by
      rw [← hfirstProd]
      exact hpos
    rw [hfirstProd] at hm
    exact mul_left_cancel₀ (ne_of_gt hposU) hm
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · exact hfirst k
  · exact hlast

private theorem roughTupleKernel_integrableOn_source {n : ℕ} {A l r : ℝ}
    (hA1 : 1 < A) (hAl : A < l) (hlr : l ≤ r) :
    IntegrableOn (fun t : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (t i))
      (roughTupleSource (n := n) A l r) volume := by
  classical
  let K : Set (Fin (n + 1) → ℝ) := Set.univ.pi fun _ => Set.Icc A r
  have hK : IsCompact K := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hsubset : roughTupleSource (n := n) A l r ⊆ K := by
    intro t ht
    simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    refine ⟨ht.1 i, ?_⟩
    have hprodOne (s : Finset (Fin (n + 1))) : 1 ≤ ∏ k ∈ s, t k := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert k s hks ih =>
        rw [Finset.prod_insert hks]
        have hk1 : 1 ≤ t k := le_trans hA1.le (ht.1 k)
        have hs0 : 0 ≤ ∏ q ∈ s, t q :=
          Finset.prod_nonneg fun q _ => le_trans (by norm_num) (ht.1 q)
        nlinarith [mul_le_mul_of_nonneg_left hk1 hs0]
    have hrest : 1 ≤ ∏ k ∈ Finset.univ.erase i, t k := hprodOne _
    have hprodEq : t i * ∏ k ∈ Finset.univ.erase i, t k =
        ∏ k : Fin (n + 1), t k :=
      Finset.mul_prod_erase Finset.univ t (Finset.mem_univ i)
    have hsingle : t i ≤ ∏ k : Fin (n + 1), t k := by
      calc
        t i = t i * 1 := by ring
        _ ≤ t i * ∏ k ∈ Finset.univ.erase i, t k :=
          mul_le_mul_of_nonneg_left hrest
            (le_trans (by norm_num) (le_trans hA1.le (ht.1 i)))
        _ = ∏ k : Fin (n + 1), t k := hprodEq
    exact hsingle.trans ht.2.2
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  let F : (Fin (n + 1) → ℝ) → ℝ := fun t =>
    ∏ i : Fin (n + 1), (max (Real.log A) (Real.log (max A (t i))))⁻¹
  have hF : Continuous F := by
    unfold F
    apply continuous_finsetProd Finset.univ
    intro i hi
    have hmax : Continuous (fun t : Fin (n + 1) → ℝ => max A (t i)) :=
      continuous_const.max (continuous_apply i)
    have hlog : Continuous (fun t : Fin (n + 1) → ℝ => Real.log (max A (t i))) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (Real.continuousAt_log
        (ne_of_gt (lt_of_lt_of_le (lt_trans zero_lt_one hA1) (le_max_left A (t i))))).comp
          hmax.continuousAt
    have hden : Continuous (fun t : Fin (n + 1) → ℝ =>
        max (Real.log A) (Real.log (max A (t i)))) := continuous_const.max hlog
    apply hden.inv₀
    intro t
    exact ne_of_gt (lt_of_lt_of_le hlogA (le_max_left _ _))
  have hFeq : ∀ t ∈ K, F t = ∏ i : Fin (n + 1), 1 / Real.log (t i) := by
    intro t ht
    have htcoord : ∀ i, A ≤ t i := by
      have hti : ∀ i, t i ∈ Set.Icc A r := by
        simpa only [K, Set.mem_pi, Set.mem_univ, true_implies] using ht
      intro i
      exact (hti i).1
    unfold F
    apply Finset.prod_congr rfl
    intro i hi
    have hlog : Real.log A ≤ Real.log (t i) :=
      Real.log_le_log (lt_trans zero_lt_one hA1) (htcoord i)
    simp [max_eq_right (htcoord i), max_eq_right hlog]
  have hf : ContinuousOn
      (fun t : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (t i)) K :=
    hF.continuousOn.congr fun t ht => (hFeq t ht).symm
  have hsfinite : volume (roughTupleSource (n := n) A l r) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsubset) hK.measure_lt_top)
  exact hf.integrableOn_of_subset_isCompact hK
    (measurableSet_roughTupleSource A l r) hsubset hsfinite

/-- `t2:density-pushforward` — 08-type-ii.tex:272-294. -/
theorem density_pushforward (γ : ℝ) (hγ : 0 < γ) :
    ∀ x : ℝ, 2 ≤ x → ∀ j : ℕ, 1 ≤ j → ∀ l r : ℝ,
      Real.rpow x γ < l → l ≤ r →
        roughTupleIntegral x γ l r j =
          (1 / Real.log x) *
            ∫ y in l..r,
              ArtinPrimitiveRoots.Sieve.roughDensityTerm γ
                (Real.log y / Real.log x) j := by
  intro x hx j hj l r hl hr
  by_cases hj₁ : j = 1
  · subst j
    exact roughTupleIntegral_one γ hγ x hx l r hl hr
  · sorry

/-- `t2:density-regularity` — 08-type-ii.tex:296-315. Joint continuity, local Lipschitz
continuity in the second variable, and bounded variation of `w D_γ(w)`. -/
theorem density_regularity :
    ContinuousOn (fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} ∧
    (∀ γ w₀ w₁ : ℝ, 0 < γ → γ < w₀ → w₀ ≤ w₁ →
      ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, w₀ ≤ u → u ≤ w₁ → w₀ ≤ v → v ≤ w₁ →
        |ArtinPrimitiveRoots.Sieve.roughDensity γ u -
          ArtinPrimitiveRoots.Sieve.roughDensity γ v| ≤ C * |u - v|) ∧
    (∀ γ w₀ w₁ : ℝ, 0 < γ → γ < w₀ → w₀ ≤ w₁ →
      BoundedVariationOn (fun w => w * ArtinPrimitiveRoots.Sieve.roughDensity γ w)
        (Set.uIcc w₀ w₁)) := by
  refine ⟨roughDensity_continuousOn, ?_, ?_⟩
  · intro γ w₀ w₁ hγ hγw₀ hw₀w₁
    obtain ⟨K, hLip⟩ := roughDensity_lipschitzOnCompact γ w₀ w₁ hγ hγw₀ hw₀w₁
    refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
    intro u v hu₀ hu₁ hv₀ hv₁
    have hdist := hLip.dist_le_mul u (Set.mem_Icc.mpr ⟨hu₀, hu₁⟩)
      v (Set.mem_Icc.mpr ⟨hv₀, hv₁⟩)
    rw [Real.dist_eq, Real.dist_eq] at hdist
    calc
      |ArtinPrimitiveRoots.Sieve.roughDensity γ u -
          ArtinPrimitiveRoots.Sieve.roughDensity γ v| ≤
          (K : ℝ) * |u - v| := hdist
      _ ≤ ((K : ℝ) + 1) * |u - v| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        linarith [show 0 ≤ (K : ℝ) by positivity]
  · intro γ w₀ w₁ hγ hγw₀ hw₀w₁
    obtain ⟨K, hLip⟩ := roughDensity_lipschitzOnCompact γ w₀ w₁ hγ hγw₀ hw₀w₁
    have hId : BoundedVariationOn id (Set.Icc w₀ w₁) :=
      BoundedVariationOn.id_Icc w₀ w₁
    have hDensity : BoundedVariationOn
        (fun w => ArtinPrimitiveRoots.Sieve.roughDensity γ w) (Set.Icc w₀ w₁) := by
      simpa [Function.comp_def] using
        hLip.comp_boundedVariationOn (fun _ hx => hx) hId
    have hProduct : BoundedVariationOn
        (fun w => w * ArtinPrimitiveRoots.Sieve.roughDensity γ w) (Set.Icc w₀ w₁) := by
      have hProduct' := hId.mul hDensity
      change BoundedVariationOn
        (fun w => (id w) * ArtinPrimitiveRoots.Sieve.roughDensity γ w) (Set.Icc w₀ w₁)
      exact hProduct'
    simpa [Set.uIcc_of_le hw₀w₁] using hProduct

/-- `t2:low-count` — 08-type-ii.tex:373-427, `eq:rough-convolution-low-count`. -/
theorem low_count (γ : ℝ) (hγ : 0 < γ) :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x γ ≤ M →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                M ≤ l → l ≤ r → r ≤ 2 * M →
                  ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                        l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                      (roughIndicator x γ m : ℂ) * χ (m : ZMod k)) -
                    (if χ = 1 then
                      ((1 / Real.log x) *
                        ∫ y in l..r, ArtinPrimitiveRoots.Sieve.roughDensity γ
                          (Real.log y / Real.log x) : ℝ) else 0 : ℂ)‖ ≤
                    C * M * Real.rpow (Real.log x) (-A₁) := by
  sorry

/-- `t2:low-frequency` — 08-type-ii.tex:439-453. -/
theorem low_frequency (γ wMin wMax C δ : ℝ)
    (hγ : 0 < γ) (hγw : γ < wMin) (hw : wMin < wMax) (hδ : 0 < δ)
    (hC : 0 < C) :
    ∀ A₀ A B₂ : ℝ, 0 < A₀ → 0 < A → 0 < B₂ →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x δ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
            ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
              ∀ v t : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                |t| ≤ Real.rpow (Real.log x) B₂ →
                  ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                    ∀ χ : DirichletCharacter ℂ k,
                      ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                          roughCoefficient x γ v m * χ (m : ZMod k) *
                            Complex.exp (Complex.I * t * Real.log (m : ℝ))) / M‖ ≤
                        C₀ * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `t2:prime-high` — 08-type-ii.tex:455-480. -/
theorem prime_high (γ wMax : ℝ) (hγ : 0 < γ) (hw : wMax < 1) :
    ∀ τ θ A₀ A₃ : ℝ, 0 < τ → τ < γ → wMax < θ → θ < 1 →
      0 < A₀ → 0 < A₃ →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x τ / 2 ≤ M → M ≤ Real.rpow x θ →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ u : ℝ,
                Real.rpow (Real.log x) B₀ ≤ |u| → |u| ≤ Real.rpow x 2 →
                  ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        (roughIndicator x γ m : ℂ) * χ (m : ZMod k) *
                          Complex.exp (Complex.I * u * Real.log (m : ℝ)))‖ ≤
                      C₀ * M * Real.rpow (Real.log x) (-A₃) := by
  sorry

/-- `t2:proxy-high` — 08-type-ii.tex:482-516; the source estimate is also the proof of PD
Lemma 5.2 (`05-major-arcs.tex:57-125`). -/
theorem proxy_high :
    ∃ C₃ : ℝ, 0 < C₃ ∧
      ∀ δ γ wMin wMax : ℝ, 0 < δ → 0 < γ → γ < wMin → wMin < wMax → wMax < 1 →
        ∀ A₀ : ℝ, 0 < A₀ →
          ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
            ∀ A₄ : ℝ, 0 < A₄ → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
              ∀ x : ℝ, x₀ ≤ x →
              let L := Real.log x
              let Tstar := Real.exp (L / Real.log L ^ 2)
              ∀ M : ℝ, Real.rpow x δ ≤ M →
                Real.log M / L ∈ Set.Icc wMin wMax →
                Real.log (2 * M) / L ∈ Set.Icc wMin wMax →
                ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow L A₀ →
                  ∀ χ : DirichletCharacter ℂ k, ∀ l r u : ℝ,
                    M ≤ l → l ≤ r → r ≤ 2 * M → 1 ≤ |u| → |u| < Real.rpow x 2 →
                      (‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧
                              roughAbove m (roughCutoff x)),
                          (χ (m : ZMod k) : ℂ) *
                            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                            Real.log (m : ℝ)) /
                        (M * roughSieveProduct (roughCutoff x))‖ ≤
                      Real.rpow L (-A₄) +
                          C₀ * (if |u| ≤ Tstar then
                            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
                          else Real.rpow L C₀ *
                            Real.exp (-L / Real.rpow (Real.log L) C₃))) ∧
                      (‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧
                              roughAbove m (roughCutoff x)),
                          (χ (m : ZMod k) : ℂ) *
                            Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
                            roughProxy x γ m) / M‖ ≤
                        Real.rpow L (-A₄) +
                          C₀ * (if |u| ≤ Tstar then
                            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
                          else Real.rpow L C₀ *
                            Real.exp (-L / Real.rpow (Real.log L) C₃))) := by
  sorry

/-- `t2:high-frequency` — 08-type-ii.tex:513-527. -/
theorem high_frequency
    (γ wMin wMax δ C A : ℝ) (hγ : 0 < γ) (hγw : γ < wMin)
    (hw : wMin < wMax) (hwMax : wMax < 1) (hδ : 0 < δ)
    (hC : 0 < C) (hA : 0 < A) :
    ∀ B : ℝ, 0 < B →
      ∃ B₂ C₀ x₀ : ℝ, 0 < B₂ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ Hm Hn : ℝ, Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
            x / 2 ≤ Hm * Hn → Hm * Hn ≤ 2 * x →
            Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
            Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) C →
              ∀ χ : DirichletCharacter ℂ k, ∀ v t : ℝ,
                Real.rpow (Real.log x) B₂ ≤ |t| →
                |t| ≤ 2 * (Hm * Hn) * Real.rpow (Real.log x) B →
                |v| ≤ Real.rpow (Real.log x) C →
                  ∀ l r : ℝ, Hm ≤ l → l ≤ r → r ≤ 2 * Hm →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        roughCoefficient x γ v m * χ (m : ZMod k) *
                          Complex.exp (Complex.I * t * Real.log (m : ℝ))) / Hm‖ ≤
                      C₀ * Real.rpow (Real.log x) (-A) := by
  sorry

end ArtinPrimitiveRoots.TypeII.Rough
