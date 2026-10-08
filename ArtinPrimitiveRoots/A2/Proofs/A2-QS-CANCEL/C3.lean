import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Main
import ArtinPrimitiveRoots.Proofs.qs_c_p.C3Helpers

/-!
# A2-QS-CANCEL, part C3: the remainder terms of the error tuple

Guide: `runs/lanes/sol-thin-found/PROOFS.md:499-550` (table of prefactors and divisor-product
conditions; estimate (E); the per-term substitutions).  Common method: split rows `a₀` into
dyads `(B, 2B]`, `B ≤ κ`, the divisors `e ∣ 𝔮 f` into `e_𝔮 e₁ e₂` with `e₁ ∣ c`, `e₂ ∣ d` in
dyads `(D₁,2D₁]`, `(D₂,2D₂]`; apply `qs_divisor_pair_cauchy_C2`; bound
`B1(2B, 2n/D_i) = B1(2n/D_i, 2B)` (`qs_norm_symm_M0`) by `HasExponent α`; sum the dyads
(`α - 1/2 > 0`).  The divisor cutoff ratio is `Λ = (M n)^η`.  Weights that depend on
`N(cd)^{-1/2}` are absorbed into `z(c)/√N c` (columns in `(n, 2n]`).

Original pieces (`E₄` highDiv, `E₀` res, `E₅` trans): no dependence on `N(cd)` except through
the divisor; Dirac `μ`.  Dual pieces (`E₁` highDiv, `E₂` res): `M/(N e √N(cd)) · Z` does not
depend on `N(cd)`; `E₂` carries `N(cd)^{-1/2}`.  Dual transition `E₃`: the weight depends on
`N(cd)` through `Z = √(N e N(cd)/(M N a₀))` inside `T(TW∘sq)`; smooth dyadic cutoff in `N(cd)`
and inverse Mellin with a majorant from `qs_transform_bounds_P0` (found:466-470).
Tails: rapid decay (`qs_transform_bounds_P0`, `qs_tail_bound_M1`) with a large exponent `A`
chosen after the polynomial losses; the dual high-core tail needs the margin
`N𝔮 n² (M n)^θ ≤ κ M` (in the optimized range `κ M = N² P^η'`, `n = N/N g`).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open Complex MeasureTheory NumberField IsDedekindDomain
open ClassFieldTheory
open ArtinPrimitiveRoots.A2.QSP2

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- C3a (IMPL): original remainders `E₄` (high divisors), `E₀` (zero residue), `E₅`
(transition) are `≪ (N𝔮)^8 (Mn)^δ (M + n + √M κ^{α-1/2} + n√(M/κ)) ‖z‖²`. -/
theorem qs_orig_remainders_C3a [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        ‖qsPairSum cols z (qsOrigKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) 𝔮)‖ +
            ‖qsPairSum cols z (qsOrigKernel (qsInnerRes K) F W M κ ((M * n) ^ η) 𝔮)‖ +
            ‖qsPairSum cols z (qsOrigKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) 𝔮)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

/-- C3b (IMPL): dual main-type remainders `E₁` (high divisors) and `E₂` (the transformed
residue at zero, retained for every field). -/
theorem qs_dual_main_remainders_C3b [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        ‖qsPairSum cols z (qsDualKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) n 𝔮)‖ +
            ‖qsPairSum cols z (qsDualKernel (qsInnerRes K) F W M κ ((M * n) ^ η) n 𝔮)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

/-- C3c (SOL-LEAD): the dual transition remainder `E₃`, whose weight depends on the product of
the column norms; inverse Mellin separation with an integrable majorant. -/
theorem qs_dual_transition_C3c [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        ‖qsPairSum cols z (qsDualKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) n 𝔮)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 :=
  QSC3.c3c_main F hrf hqS W hW α hα1 hα2 hexp δ hδ

private theorem qs_pairSum_uniform_bound_C3d
    (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
    (Φ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hΦ : ∀ c ∈ cols, ∀ d ∈ cols, ‖Φ c d‖ ≤ E) :
    ‖qsPairSum cols z Φ‖ ≤ E * (cols.card : ℝ) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let x : Ideal (𝓞 K) → ℝ := fun c => ‖z c‖
  have hx (c : Ideal (𝓞 K)) : 0 ≤ x c := by positivity
  have hterms (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols) :
      ‖if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ ≤ E * x c * x d := by
    by_cases hcop : IsCoprime c d
    · simp only [if_pos hcop, norm_mul, Complex.norm_conj]
      calc
        ‖z c‖ * ‖z d‖ * ‖Φ c d‖ ≤ ‖z c‖ * ‖z d‖ * E :=
          mul_le_mul_of_nonneg_left (hΦ c hc d hd) (by positivity)
        _ = E * x c * x d := by dsimp [x]; ring
    · simp only [if_neg hcop, norm_zero]
      exact mul_nonneg (mul_nonneg hE (hx c)) (hx d)
  have hdouble :
      ‖∑ c ∈ cols, ∑ d ∈ cols,
        if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ ≤
      ∑ c ∈ cols, ∑ d ∈ cols,
        ‖if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ := by
    calc
      _ ≤ ∑ c ∈ cols, ‖∑ d ∈ cols,
          if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro c hc
        exact norm_sum_le _ _
  have hmajor :
      (∑ c ∈ cols, ∑ d ∈ cols,
        ‖if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖) ≤
      ∑ c ∈ cols, ∑ d ∈ cols, E * x c * x d := by
    apply Finset.sum_le_sum
    intro c hc
    apply Finset.sum_le_sum
    intro d hd
    exact hterms c d hc hd
  have hfactor :
      (∑ c ∈ cols, ∑ d ∈ cols, E * x c * x d) =
        E * (∑ c ∈ cols, x c) * (∑ d ∈ cols, x d) := by
    calc
      _ = ∑ c ∈ cols, E * (∑ d ∈ cols, x c * x d) := by
        apply Finset.sum_congr rfl
        intro c hc
        calc
          _ = ∑ d ∈ cols, E * (x c * x d) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
          _ = E * (∑ d ∈ cols, x c * x d) := by rw [← Finset.mul_sum]
      _ = E * (∑ c ∈ cols, ∑ d ∈ cols, x c * x d) := by rw [← Finset.mul_sum]
      _ = E * ((∑ c ∈ cols, x c) * (∑ d ∈ cols, x d)) := by
        rw [Finset.sum_mul_sum]
      _ = E * (∑ c ∈ cols, x c) * (∑ d ∈ cols, x d) := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq cols x (fun _ => (1 : ℝ))
  have hcs' : (∑ c ∈ cols, x c) ^ 2 ≤
      (∑ c ∈ cols, x c ^ 2) * (cols.card : ℝ) := by
    simpa using hcs
  calc
    ‖qsPairSum cols z Φ‖ =
        ‖∑ c ∈ cols, ∑ d ∈ cols,
          if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ := by
            rfl
    _ ≤ ∑ c ∈ cols, ∑ d ∈ cols,
          ‖if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ := hdouble
    _ ≤ ∑ c ∈ cols, ∑ d ∈ cols, E * x c * x d := hmajor
    _ = E * (∑ c ∈ cols, x c) * (∑ d ∈ cols, x d) := hfactor
    _ = E * (∑ c ∈ cols, x c) ^ 2 := by ring
    _ ≤ E * ((∑ c ∈ cols, x c ^ 2) * (cols.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcs' hE
    _ = E * (cols.card : ℝ) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
      simp only [x]
      ring

private theorem qs_block_cols_card_bound_C3d [IsTotallyComplex K]
    (CI ε : ℝ) (hcount : ∀ X : ℝ, 1 ≤ X →
      (((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset.card : ℕ) : ℝ) ≤
        CI * X ^ (1 + ε))
    (hε : 0 < ε) (n : ℝ) (hn : 1 ≤ n)
    (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
    (hcols : QSBlockCols m qS 𝔮 n cols) :
    (cols.card : ℝ) ≤ CI * 2 ^ (1 + ε) * n ^ (1 + ε) := by
  have hsub : cols ⊆
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊2 * n⌋₊).toFinset := by
    intro c hc
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Nat.le_floor (by exact_mod_cast (hcols.2.2.1 c hc).2.2.2)
  calc
    (cols.card : ℝ) ≤
        ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊2 * n⌋₊).toFinset.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
    _ ≤ CI * (2 * n) ^ (1 + ε) := hcount (2 * n) (by linarith)
    _ = CI * 2 ^ (1 + ε) * n ^ (1 + ε) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ n)]
          ring

private theorem qs_sqfUpTo_card_bound_C3d [IsTotallyComplex K]
    (CI ε : ℝ) (hcount : ∀ X : ℝ, 1 ≤ X →
      (((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset.card : ℕ) : ℝ) ≤
        CI * X ^ (1 + ε))
    (hε : 0 < ε) (κ : ℝ) (hκ : 1 ≤ κ) (𝔮 : Ideal (𝓞 K)) :
    ((qsSqfUpTo κ 𝔮).card : ℝ) ≤ CI * κ ^ (1 + ε) := by
  classical
  have hsub : qsSqfUpTo κ 𝔮 ⊆
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊κ⌋₊).toFinset := by
    intro a ha
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    unfold qsSqfUpTo at ha
    simp only [Finset.mem_filter] at ha
    exact Nat.le_floor (by exact_mod_cast ha.2.2.2.2)
  calc
    ((qsSqfUpTo κ 𝔮).card : ℝ) ≤
        ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊κ⌋₊).toFinset.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
    _ ≤ CI * κ ^ (1 + ε) := hcount κ hκ

private theorem qs_ratio_shift_right_C3d [IsTotallyComplex K] (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℂ, -1/2 ≤ v.re → v.re ≤ 3/2 →
      1 ≤ |v.im| →
      ‖qsGammaRatio K (v + (k : ℂ))‖ ≤
        C * (1 + |v.im|) ^ (2 * InfinitePlace.nrComplexPlaces K * (k + 1)) := by
  obtain ⟨C₀, hC₀, hpoly⟩ := QSP2.exists_ratio_poly_wide (K := K)
  have hbase : ∃ C : ℝ, 0 < C ∧ ∀ v : ℂ, -1/2 ≤ v.re → v.re ≤ 3/2 →
      1 ≤ |v.im| → ‖qsGammaRatio K v‖ ≤
        C * (1 + |v.im|) ^ (2 * InfinitePlace.nrComplexPlaces K) := by
    refine ⟨C₀ + 1, by linarith, ?_⟩
    intro v h₁ h₂ ht
    exact (hpoly v h₁ h₂ (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  induction k with
  | zero =>
      obtain ⟨C, hC, hbound⟩ := hbase
      refine ⟨C, hC, ?_⟩
      intro v h₁ h₂ ht
      simpa using hbound v h₁ h₂ ht
  | succ k ih =>
      obtain ⟨Ck, hCk, hbound⟩ := ih
      let B : ℝ := (k : ℝ) + 4
      let C : ℝ := Ck * dK K * B ^ (2 * InfinitePlace.nrComplexPlaces K)
      have hB : 0 < B := by dsimp [B]; positivity
      have hdK : 0 < dK K := dK_pos
      refine ⟨C, by dsimp [C]; positivity, ?_⟩
      intro v h₁ h₂ ht
      have hvim : (v + (k : ℂ)).im = v.im := by simp
      have hvre : (v + (k : ℂ)).re = v.re + k := by simp
      have hnorm : ‖v + (k : ℂ)‖ ≤ B * (1 + |v.im|) := by
        calc
          ‖v + (k : ℂ)‖ ≤ |(v + (k : ℂ)).re| + |(v + (k : ℂ)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ ≤ B * (1 + |v.im|) := by
            rw [hvre, hvim]
            dsimp [B]
            have hvabs : |v.re| ≤ 3/2 := abs_le.mpr ⟨by linarith, by linarith⟩
            have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
            have hkbound : |v.re + (k : ℝ)| ≤ |v.re| + (k : ℝ) := by
              calc
                |v.re + (k : ℝ)| ≤ |v.re| + |(k : ℝ)| := abs_add_le _ _
                _ = |v.re| + (k : ℝ) := by rw [abs_of_nonneg hk0]
            nlinarith [abs_nonneg v.im]
      have hden : 1 ≤ (4 * Real.pi ^ 2 : ℝ) := by nlinarith [Real.pi_gt_three]
      have hratio :
          ‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2) ≤
            (B * (1 + |v.im|)) ^ 2 := by
        have hsq : ‖v + (k : ℂ)‖ ^ 2 ≤ (B * (1 + |v.im|)) ^ 2 := by
          have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (by positivity)
          simpa [pow_two] using hmul
        rw [div_le_iff₀ (by positivity)]
        calc
          ‖v + (k : ℂ)‖ ^ 2 ≤ (B * (1 + |v.im|)) ^ 2 := hsq
          _ ≤ (B * (1 + |v.im|)) ^ 2 * (4 * Real.pi ^ 2) := by
            calc
              (B * (1 + |v.im|)) ^ 2 = (B * (1 + |v.im|)) ^ 2 * 1 := by ring
              _ ≤ (B * (1 + |v.im|)) ^ 2 * (4 * Real.pi ^ 2) :=
                mul_le_mul_of_nonneg_left hden (sq_nonneg _)
      have hpow :
          (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
              InfinitePlace.nrComplexPlaces K ≤
            (B * (1 + |v.im|)) ^ (2 * InfinitePlace.nrComplexPlaces K) := by
        calc
          _ ≤ ((B * (1 + |v.im|)) ^ 2) ^ InfinitePlace.nrComplexPlaces K :=
            pow_le_pow_left₀ (by positivity) hratio _
          _ = _ := by rw [← pow_mul]
      have hvimne : (v + (k : ℂ)).im ≠ 0 := by
        rw [hvim]
        intro hi
        rw [hi] at ht
        simp at ht
        linarith
      have hv0 : v + (k : ℂ) ≠ 0 := by
        intro hz
        exact hvimne (by simpa using congrArg Complex.im hz)
      have hrec := norm_ratio_add_one (K := K) (v := v + (k : ℂ)) hv0
        (by
          intro n hz
          apply hvimne
          have him := congrArg Complex.im hz
          simpa using him)
        (by
          intro n hz
          apply hvimne
          have him := congrArg Complex.im hz
          simpa using him)
      have hprev := hbound v h₁ h₂ ht
      have hrec' :
          ‖qsGammaRatio K (v + ((k + 1 : ℕ) : ℂ))‖ =
            dK K * (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
              InfinitePlace.nrComplexPlaces K *
              ‖qsGammaRatio K (v + (k : ℂ))‖ := by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hrec
      calc
        ‖qsGammaRatio K (v + ((k + 1 : ℕ) : ℂ))‖ =
            dK K * (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
              InfinitePlace.nrComplexPlaces K *
              ‖qsGammaRatio K (v + (k : ℂ))‖ := hrec'
        _ ≤ dK K * (B * (1 + |v.im|)) ^ (2 * InfinitePlace.nrComplexPlaces K) *
              (Ck * (1 + |v.im|) ^
                (2 * InfinitePlace.nrComplexPlaces K * (k + 1))) := by
          have hp := mul_le_mul hpow hprev (norm_nonneg _) (by positivity)
          calc
            _ = dK K * ((‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
                  InfinitePlace.nrComplexPlaces K *
                  ‖qsGammaRatio K (v + (k : ℂ))‖) := by ring
            _ ≤ _ := by
              simpa [mul_assoc] using
                (mul_le_mul_of_nonneg_left hp (le_of_lt hdK))
        _ = C * (1 + |v.im|) ^
              (2 * InfinitePlace.nrComplexPlaces K * (k + 2)) := by
                dsimp [C, B]
                calc
                  _ = Ck * dK K * ((k : ℝ) + 4) ^
                      (2 * InfinitePlace.nrComplexPlaces K) *
                      ((1 + |v.im|) ^ (2 * InfinitePlace.nrComplexPlaces K) *
                        (1 + |v.im|) ^
                          (2 * InfinitePlace.nrComplexPlaces K * (k + 1))) := by
                    rw [mul_pow]
                    ring_nf
                  _ = Ck * dK K * ((k : ℝ) + 4) ^
                      (2 * InfinitePlace.nrComplexPlaces K) *
                      (1 + |v.im|) ^ (2 * InfinitePlace.nrComplexPlaces K +
                        2 * InfinitePlace.nrComplexPlaces K * (k + 1)) := by
                        rw [← pow_add]
                  _ = _ := by
                    congr 1
                    rw [show 2 * InfinitePlace.nrComplexPlaces K +
                      2 * InfinitePlace.nrComplexPlaces K * (k + 1) =
                        2 * InfinitePlace.nrComplexPlaces K * (k + 2) by ring]

private theorem qs_ratio_shift_left_C3d [IsTotallyComplex K] (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℂ, 1 ≤ |v.im| →
      ‖qsGammaRatio K v‖ ≤ C * ‖qsGammaRatio K (v + (k : ℂ))‖ := by
  let c0 : ℝ := dK K * (1 / (4 * Real.pi ^ 2)) ^ InfinitePlace.nrComplexPlaces K
  let Cstep : ℝ := c0⁻¹
  have hdK : 0 < dK K := dK_pos
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hCstep : 0 < Cstep := by dsimp [Cstep]; positivity
  induction k with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro v hv
      simpa using (le_of_eq (by rfl : ‖qsGammaRatio K (v + (0 : ℂ))‖ =
        ‖qsGammaRatio K v‖))
  | succ k ih =>
      obtain ⟨Ck, hCk, hbound⟩ := ih
      refine ⟨Ck * Cstep, mul_pos hCk hCstep, ?_⟩
      intro v hv
      have hvim (u : ℂ) : (u + (k : ℂ)).im = u.im := by simp
      have huimne (u : ℂ) (hu : 1 ≤ |u.im|) : (u + (k : ℂ)).im ≠ 0 := by
        rw [hvim u]
        intro h0
        rw [h0] at hu
        norm_num at hu
      have hu0 (u : ℂ) (hu : 1 ≤ |u.im|) : u + (k : ℂ) ≠ 0 := by
        intro hz
        exact huimne u hu (by simpa using congrArg Complex.im hz)
      have hrec := norm_ratio_add_one (K := K) (v := v + (k : ℂ)) (hu0 v hv)
        (by
          intro n hz
          have him : (v + (k : ℂ)).im = 0 := by
            have h := congrArg Complex.im hz
            simpa using h
          exact huimne v hv him)
        (by
          intro n hz
          have him : (v + (k : ℂ)).im = 0 := by
            have h := congrArg Complex.im hz
            simpa using h
          exact huimne v hv him)
      have hnorm : 1 ≤ ‖v + (k : ℂ)‖ := by
        have him := Complex.abs_im_le_norm (v + (k : ℂ))
        rw [hvim] at him
        exact hv.trans him
      have hratio : 1 / (4 * Real.pi ^ 2) ≤
          ‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2) := by
        rw [div_le_div_iff_of_pos_right (by positivity)]
        nlinarith
      have hpow : (1 / (4 * Real.pi ^ 2)) ^ InfinitePlace.nrComplexPlaces K ≤
          (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
            InfinitePlace.nrComplexPlaces K :=
        pow_le_pow_left₀ (by positivity) hratio _
      have hfac : dK K * (1 / (4 * Real.pi ^ 2)) ^
          InfinitePlace.nrComplexPlaces K ≤
            dK K * (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
              InfinitePlace.nrComplexPlaces K :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hdK)
      have hprod : 1 ≤ Cstep *
          (dK K * (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
            InfinitePlace.nrComplexPlaces K) := by
        have hone : Cstep * c0 = 1 := by
          dsimp [Cstep]
          exact inv_mul_cancel₀ hc0.ne'
        have hfac' : c0 ≤ dK K * (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
            InfinitePlace.nrComplexPlaces K := by
          simpa [c0] using hfac
        calc
          1 = Cstep * c0 := hone.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hfac' (le_of_lt hCstep)
      have hstep : ‖qsGammaRatio K (v + (k : ℂ))‖ ≤
          Cstep * ‖qsGammaRatio K (v + ((k + 1 : ℕ) : ℂ))‖ := by
        rw [show v + ((k + 1 : ℕ) : ℂ) = (v + (k : ℂ)) + 1 by
          push_cast; ring, hrec]
        calc
          ‖qsGammaRatio K (v + (k : ℂ))‖ =
              1 * ‖qsGammaRatio K (v + (k : ℂ))‖ := by ring
          _ ≤ Cstep * (dK K * (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
                InfinitePlace.nrComplexPlaces K) *
                ‖qsGammaRatio K (v + (k : ℂ))‖ :=
              mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
          _ = Cstep * ((dK K * (‖v + (k : ℂ)‖ ^ 2 / (4 * Real.pi ^ 2)) ^
                InfinitePlace.nrComplexPlaces K) *
                ‖qsGammaRatio K (v + (k : ℂ))‖) := by ring
      have hv0left := hbound v hv
      calc
        ‖qsGammaRatio K v‖ ≤ Ck * ‖qsGammaRatio K (v + (k : ℂ))‖ := hv0left
        _ ≤ Ck * (Cstep * ‖qsGammaRatio K (v + ((k + 1 : ℕ) : ℂ))‖) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hCk)
        _ = Ck * Cstep * ‖qsGammaRatio K (v + ((k + 1 : ℕ) : ℂ))‖ := by ring

private theorem gamma_ne_zero_of_im_C3d {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have him := congrArg Complex.im hn
  simp at him
  exact hz (by linarith)

private noncomputable def qdExt_C3d (s : ℂ) : ℂ :=
  (((dK K : ℝ) : ℂ) ^ (s / 4))⁻¹ *
    ((2 * (Real.pi : ℂ)) ^ (s / 2) * 2 * (2 : ℂ) ^ (-s) *
      (Real.sqrt Real.pi : ℂ) * (Complex.Gamma ((s + 1) / 2))⁻¹) ^
        InfinitePlace.nrComplexPlaces K

private theorem Qd_eq_qdExt_C3d {s : ℂ} (hs : s.im ≠ 0) :
    QSP2.Qd K s = qdExt_C3d (K := K) s := by
  have ha : Complex.Gamma ((s + 1) / 2) ≠ 0 := by
    apply gamma_ne_zero_of_im_C3d
    have him : ((s + 1) / 2).im = s.im / 2 := by simp
    rw [him]
    exact div_ne_zero hs (by norm_num)
  have hb : Complex.Gamma (s + 1) ≠ 0 := by
    apply gamma_ne_zero_of_im_C3d
    simpa using hs
  have hdup := Complex.Gamma_mul_Gamma_add_half ((s + 1) / 2)
  rw [show (s + 1) / 2 + 1 / 2 = s / 2 + 1 by ring,
    show 1 - 2 * ((s + 1) / 2) = -s by ring,
    show 2 * ((s + 1) / 2) = s + 1 by ring] at hdup
  have hratio : Complex.Gamma (s / 2 + 1) * (Complex.Gamma (s + 1))⁻¹ =
      (2 : ℂ) ^ (-s) * (Real.sqrt Real.pi : ℂ) *
        (Complex.Gamma ((s + 1) / 2))⁻¹ := by
    field_simp [ha, hb]
    have hdup' : Complex.Gamma (s / 2 + 1) * Complex.Gamma ((s + 1) / 2) =
        Complex.Gamma (s + 1) * (2 : ℂ) ^ (-s) * (Real.sqrt Real.pi : ℂ) := by
      simpa [mul_comm] using hdup
    rw [show (s + 2) / 2 = s / 2 + 1 by ring, hdup']
  unfold QSP2.Qd qdExt_C3d
  rw [show ((2 * (Real.pi : ℂ)) ^ (s / 2) * 2 * Complex.Gamma (s / 2 + 1) *
      (Complex.Gamma (s + 1))⁻¹) =
      ((2 * (Real.pi : ℂ)) ^ (s / 2) * 2) *
        (Complex.Gamma (s / 2 + 1) * (Complex.Gamma (s + 1))⁻¹) by ring,
    hratio]
  ring

private theorem qdExt_differentiableAt_C3d (s : ℂ) :
    DifferentiableAt ℂ (qdExt_C3d (K := K)) s := by
  have hdK : 0 < dK K := dK_pos
  have hbaseD : ((dK K : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdK.ne'
  have hDpow : DifferentiableAt ℂ
      (fun z : ℂ => ((dK K : ℝ) : ℂ) ^ (z / 4)) s :=
    (differentiableAt_id.div_const 4).const_cpow (Or.inl hbaseD)
  have hDpowne : ((dK K : ℝ) : ℂ) ^ (s / 4) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hbaseD (by exact_mod_cast Complex.ofReal_eq_zero.mp h.1)
  have hDpowInv := hDpow.inv hDpowne
  have hPiBase : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  have hPipow : DifferentiableAt ℂ
      (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (z / 2)) s :=
    (differentiableAt_id.div_const 2).const_cpow (Or.inl hPiBase)
  have hTwoPow : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (-z)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl (by norm_num))
  have hGammaInv : DifferentiableAt ℂ
      (fun z : ℂ => (Complex.Gamma ((z + 1) / 2))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.comp (by fun_prop)).differentiableAt
  have hinner : DifferentiableAt ℂ (fun z : ℂ =>
      (2 * (Real.pi : ℂ)) ^ (z / 2) * 2 * (2 : ℂ) ^ (-z) *
        (Real.sqrt Real.pi : ℂ) * (Complex.Gamma ((z + 1) / 2))⁻¹) s := by
    exact (((hPipow.mul (differentiableAt_const _)).mul hTwoPow).mul
      (differentiableAt_const _)).mul hGammaInv
  unfold qdExt_C3d
  exact hDpowInv.mul (hinner.pow _)

private noncomputable def caseBDualDext_C3d (h : ℝ → ℂ) (u : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Hecke.dedekindPrefactor K u * qdExt_C3d (K := K) (1 - u) *
    (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ *
      QSP2.qsPhiH h ((1 + u) / 2)

private theorem caseBDualDext_differentiableAt_C3d [IsTotallyComplex K] {h : ℝ → ℂ}
    (hh : IsQSWeight h) {u : ℂ} (hu : 3 / 2 ≤ u.re) :
    DifferentiableAt ℂ (caseBDualDext_C3d (K := K) h) u := by
  have hpref : DifferentiableAt ℂ (fun z : ℂ => Hecke.dedekindPrefactor K z) u :=
    differentiableAt_prefactor (not_nonpos_int_of_re_pos (by linarith))
  have hqd : DifferentiableAt ℂ (fun z : ℂ => qdExt_C3d (K := K) (1 - z)) u :=
    (qdExt_differentiableAt_C3d (K := K) (1 - u)).comp u (by fun_prop)
  have hwne : (1 + u) / 2 ≠ 0 := by
    intro hz
    have := congrArg Complex.re hz
    simp at this
    linarith
  have hinv : DifferentiableAt ℂ
      (fun z : ℂ => (Hecke.dedekindPrefactor K z)⁻¹) ((1 + u) / 2) :=
    differentiable_prefactor_inv (K := K) _
  have hphi : DifferentiableAt ℂ (QSP2.qsPhiH h) ((1 + u) / 2) :=
    QSP2.differentiableAt_qsPhiH hh hwne
  unfold caseBDualDext_C3d
  refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
    (DifferentiableAt.mul (differentiableAt_const _) hpref) hqd)
      (DifferentiableAt.comp (g := fun w => (Hecke.dedekindPrefactor K w)⁻¹)
        (f := fun z : ℂ => (1 + z) / 2) u hinv (by fun_prop)))
    (DifferentiableAt.comp (g := QSP2.qsPhiH h)
      (f := fun z : ℂ => (1 + z) / 2) u hphi (by fun_prop))

private theorem caseBDualDext_ratio_C3d [IsTotallyComplex K] {h : ℝ → ℂ} (u : ℂ)
    (hu : u.im ≠ 0) :
    caseBDualDext_C3d (K := K) h u =
      (1 / 2 : ℂ) * qsGammaRatio K u * qsGammaRatio K ((1 - u) / 2) *
        QSP2.qsPhiH h ((1 + u) / 2) := by
  have hs0 : 1 - u ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp at him
    exact hu him
  have hs : ∀ n : ℕ, 1 - u ≠ -(n : ℂ) := by
    intro n hz
    have him := congrArg Complex.im hz
    simp at him
    exact hu him
  have hs2 : ∀ n : ℕ, (1 - u) / 2 ≠ -(n : ℂ) := by
    intro n hz
    have him := congrArg Complex.im hz
    simp at him
    exact hu (by linarith)
  have hq := QSP2.Qd_eq (K := K) hs0 hs hs2
  have hsim : (1 - u).im ≠ 0 := by
    have him : (1 - u).im = -u.im := by simp
    rw [him]
    exact neg_ne_zero.mpr hu
  have hqExt := Qd_eq_qdExt_C3d (K := K) (s := 1 - u) hsim
  unfold caseBDualDext_C3d
  rw [← hqExt, hq]
  unfold qsGammaRatio
  rw [show 1 - (1 - u) / 2 = (1 + u) / 2 by ring]
  ring

set_option maxHeartbeats 50000000 in
private theorem caseBDualDext_decay_large_C3d [IsTotallyComplex K]
    {h : ℝ → ℂ} (hh : IsQSWeight h) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ,
      3 / 2 + 2 * (j : ℝ) ≤ u.re → u.re ≤ 7 / 2 + 2 * (j : ℝ) →
      2 ≤ |u.im| →
      ‖caseBDualDext_C3d (K := K) h u‖ ≤ C / u.im ^ 2 := by
  let k₁ : ℕ := 2 * j + 2
  let k₂ : ℕ := j + 1
  let E₁ : ℕ := 2 * InfinitePlace.nrComplexPlaces K * (k₁ + 1)
  let E₂ : ℕ := 2 * InfinitePlace.nrComplexPlaces K
  let A : ℕ := E₁ + E₂ + 2
  let α : ℝ := 5 / 4 + j
  let β : ℝ := 9 / 4 + j
  obtain ⟨C₁, hC₁, hR₁⟩ := qs_ratio_shift_right_C3d (K := K) k₁
  obtain ⟨C₂, hC₂, hR₂⟩ := qs_ratio_shift_left_C3d (K := K) k₂
  obtain ⟨CR, hCR, hRwide⟩ := QSP2.exists_ratio_poly_wide (K := K)
  obtain ⟨Cφ, hφ⟩ := QSP2.qsPhiH_decay hh A α β
  let C : ℝ := 1 + C₁ * C₂ * (CR + 1) * |Cφ| * 2 ^ (E₁ + E₂ + A)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro u hu₁ hu₂ huim
  have hk₁ : (k₁ : ℝ) = 2 * (j : ℝ) + 2 := by norm_num [k₁]
  have hk₂ : (k₂ : ℝ) = (j : ℝ) + 1 := by norm_num [k₂]
  have ht : 0 < |u.im| := by linarith
  let v : ℂ := u - (k₁ : ℂ)
  have hvim : v.im = u.im := by simp [v]
  have hvre : v.re = u.re - (k₁ : ℝ) := by simp [v]
  have hvlow : -1 / 2 ≤ v.re := by rw [hvre, hk₁]; linarith
  have hvhigh : v.re ≤ 3 / 2 := by rw [hvre, hk₁]; linarith
  have hR₁' : ‖qsGammaRatio K u‖ ≤ C₁ * (1 + |u.im|) ^ E₁ := by
    have hv := hR₁ v hvlow hvhigh (by rw [hvim]; linarith)
    have hmove : v + (k₁ : ℂ) = u := by dsimp [v, k₁]; ring
    calc
      ‖qsGammaRatio K u‖ = ‖qsGammaRatio K (v + (k₁ : ℂ))‖ := by rw [hmove]
      _ ≤ C₁ * (1 + |v.im|) ^ E₁ := by simpa [E₁, k₁] using hv
      _ = C₁ * (1 + |u.im|) ^ E₁ := by rw [hvim]
  let s : ℂ := (1 - u) / 2
  have hsim : s.im = -u.im / 2 := by simp [s]
  have hslarge : 1 ≤ |s.im| := by
    rw [hsim, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  let w : ℂ := s + (k₂ : ℂ)
  have hwim : w.im = s.im := by simp [w]
  have hwre : w.re = s.re + (k₂ : ℝ) := by simp [w]
  have hsre : s.re = (1 - u.re) / 2 := by simp [s]
  have hwlow : -1 / 2 ≤ w.re := by rw [hwre, hsre, hk₂]; nlinarith
  have hwhigh : w.re ≤ 3 / 2 := by rw [hwre, hsre, hk₂]; nlinarith
  have hwlarge : 1 / 2 ≤ |w.im| := by rw [hwim]; linarith
  have hR₂' : ‖qsGammaRatio K s‖ ≤ C₂ * (CR + 1) * (1 + |u.im|) ^ E₂ := by
    have hleft := hR₂ s hslarge
    have hright := hRwide w hwlow hwhigh hwlarge
    have him_le : |w.im| ≤ |u.im| := by
      rw [hwim, hsim, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hpow : (1 + |w.im|) ^ E₂ ≤ (1 + |u.im|) ^ E₂ :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      ‖qsGammaRatio K s‖ ≤ C₂ * ‖qsGammaRatio K w‖ := hleft
      _ ≤ C₂ * (CR * (1 + |w.im|) ^ E₂) :=
        mul_le_mul_of_nonneg_left hright (le_of_lt hC₂)
      _ ≤ C₂ * ((CR + 1) * (1 + |u.im|) ^ E₂) := by
        have hinner : CR * (1 + |w.im|) ^ E₂ ≤
            (CR + 1) * (1 + |u.im|) ^ E₂ := by
          calc
            _ ≤ CR * (1 + |u.im|) ^ E₂ :=
              mul_le_mul_of_nonneg_left hpow hCR
            _ ≤ (CR + 1) * (1 + |u.im|) ^ E₂ := by
              exact mul_le_mul_of_nonneg_right (by linarith [hCR]) (by positivity)
        exact mul_le_mul_of_nonneg_left hinner (le_of_lt hC₂)
      _ = C₂ * (CR + 1) * (1 + |u.im|) ^ E₂ := by ring
  let wp : ℂ := (1 + u) / 2
  have hwpre : α ≤ wp.re := by
    dsimp [α, wp]
    simp
    linarith
  have hwpupper : wp.re ≤ β := by
    dsimp [β, wp]
    simp
    linarith
  have hwpim : 1 ≤ |wp.im| := by
    dsimp [wp]
    simp
    rw [abs_div, abs_two]
    linarith
  have hphi := hφ wp hwpre hwpupper hwpim
  have hphi' : ‖QSP2.qsPhiH h wp‖ ≤ |Cφ| / (|u.im| / 2) ^ A := by
    have him : |wp.im| = |u.im| / 2 := by
      dsimp [wp]
      simp [abs_div, abs_two]
    have hphiAbs : ‖QSP2.qsPhiH h wp‖ ≤ |Cφ| / |wp.im| ^ A :=
      hphi.trans (div_le_div_of_nonneg_right (le_abs_self Cφ) (by positivity))
    rw [him] at hphiAbs
    exact hphiAbs
  have hbase : (1 + |u.im|) ≤ 2 * |u.im| := by linarith
  have hpoly : (1 + |u.im|) ^ (E₁ + E₂) ≤
      2 ^ (E₁ + E₂) * |u.im| ^ (E₁ + E₂) := by
    calc
      _ ≤ (2 * |u.im|) ^ (E₁ + E₂) :=
        pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [mul_pow]
  have hscaled : |Cφ| / (|u.im| / 2) ^ A =
      |Cφ| * 2 ^ A / |u.im| ^ A := by
    rw [div_pow]
    have hu0 : |u.im| ^ A ≠ 0 := pow_ne_zero _ ht.ne'
    field_simp [hu0]
  have hnormD :
      ‖caseBDualDext_C3d (K := K) h u‖ ≤
        (1 / 2 : ℝ) * C₁ * (C₂ * (CR + 1)) * |Cφ| *
          (1 + |u.im|) ^ (E₁ + E₂) / (|u.im| / 2) ^ A := by
    have huimne : u.im ≠ 0 := by
      intro hz
      rw [hz] at huim
      norm_num at huim
    rw [caseBDualDext_ratio_C3d (K := K) (h := h) u huimne]
    rw [norm_mul, norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    calc
      (1 / 2 : ℝ) * ‖qsGammaRatio K u‖ * ‖qsGammaRatio K s‖ *
          ‖QSP2.qsPhiH h wp‖
        ≤ (1 / 2 : ℝ) * (C₁ * (1 + |u.im|) ^ E₁) *
          (C₂ * (CR + 1) * (1 + |u.im|) ^ E₂) *
            (|Cφ| / (|u.im| / 2) ^ A) := by
              gcongr
      _ = _ := by ring
  have htail :
      (1 / 2 : ℝ) * C₁ * (C₂ * (CR + 1)) * |Cφ| *
          (1 + |u.im|) ^ (E₁ + E₂) / (|u.im| / 2) ^ A
        ≤ C / |u.im| ^ 2 := by
    let P : ℝ := (1 / 2 : ℝ) * C₁ * (C₂ * (CR + 1)) * |Cφ|
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hA : E₁ + E₂ + 2 = A := rfl
    have hratio : (1 + |u.im|) ^ (E₁ + E₂) / (|u.im| / 2) ^ A ≤
        2 ^ (E₁ + E₂ + A) / |u.im| ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc
        (1 + |u.im|) ^ (E₁ + E₂) * |u.im| ^ 2
          ≤ 2 ^ (E₁ + E₂) * |u.im| ^ (E₁ + E₂) * |u.im| ^ 2 :=
            mul_le_mul_of_nonneg_right hpoly (sq_nonneg _)
        _ = 2 ^ (E₁ + E₂) * |u.im| ^ A := by
          calc
            _ = 2 ^ (E₁ + E₂) * (|u.im| ^ (E₁ + E₂) * |u.im| ^ 2) := by ring
            _ = 2 ^ (E₁ + E₂) * |u.im| ^ (E₁ + E₂ + 2) := by rw [← pow_add]
            _ = 2 ^ (E₁ + E₂) * |u.im| ^ A := by rw [hA]
        _ = 2 ^ (E₁ + E₂ + A) * (|u.im| / 2) ^ A := by
          rw [div_pow]
          field_simp
          rw [pow_add]
          ring
    have hconst : P * 2 ^ (E₁ + E₂ + A) ≤ C := by
      calc
        P * 2 ^ (E₁ + E₂ + A) =
            (1 / 2 : ℝ) *
              (C₁ * C₂ * (CR + 1) * |Cφ| * 2 ^ (E₁ + E₂ + A)) := by
                dsimp [P]
                ring
        _ ≤ 1 + C₁ * C₂ * (CR + 1) * |Cφ| * 2 ^ (E₁ + E₂ + A) := by
          have hp : 0 ≤ C₁ * C₂ * (CR + 1) * |Cφ| * 2 ^ (E₁ + E₂ + A) := by positivity
          nlinarith
        _ = C := by dsimp [C]
    calc
      _ = P * ((1 + |u.im|) ^ (E₁ + E₂) / (|u.im| / 2) ^ A) := by
        dsimp [P]
        ring
      _ ≤ P * (2 ^ (E₁ + E₂ + A) / |u.im| ^ 2) :=
        mul_le_mul_of_nonneg_left hratio hP
      _ = (P * 2 ^ (E₁ + E₂ + A)) / |u.im| ^ 2 := by ring
      _ ≤ C / |u.im| ^ 2 :=
        div_le_div_of_nonneg_right hconst (by positivity)
  calc
    ‖caseBDualDext_C3d (K := K) h u‖ ≤
        (1 / 2 : ℝ) * C₁ * (C₂ * (CR + 1)) * |Cφ| *
          (1 + |u.im|) ^ (E₁ + E₂) / (|u.im| / 2) ^ A := hnormD
    _ ≤ C / |u.im| ^ 2 := htail
    _ = C / u.im ^ 2 := by rw [sq_abs]

private theorem caseBDualDext_decay_strip_C3d [IsTotallyComplex K]
    {h : ℝ → ℂ} (hh : IsQSWeight h) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ,
      3 / 2 + 2 * (j : ℝ) ≤ u.re → u.re ≤ 7 / 2 + 2 * (j : ℝ) →
      1 ≤ |u.im| →
      ‖caseBDualDext_C3d (K := K) h u‖ ≤ C / u.im ^ 2 := by
  obtain ⟨C₀, hC₀, hlarge⟩ := caseBDualDext_decay_large_C3d (K := K) hh j
  obtain ⟨C₁, hstrip⟩ := QSP2.strip_decay_extend
    (a := 3 / 2 + 2 * (j : ℝ)) (b := 7 / 2 + 2 * (j : ℝ)) (T := 2) (C := C₀)
    (by norm_num)
    (fun u hu₁ hu₂ huT =>
      (caseBDualDext_differentiableAt_C3d (K := K) hh (by linarith)).continuousAt)
    (fun u hu₁ hu₂ huT => hlarge u hu₁ hu₂ huT)
  have hC₁ : 0 ≤ C₁ := by
    let u₀ : ℂ := ((3 / 2 + 2 * (j : ℝ)) : ℂ) + Complex.I
    have hre : u₀.re = 3 / 2 + 2 * (j : ℝ) := by simp [u₀]
    have him : u₀.im = 1 := by simp [u₀]
    have hr : 3 / 2 + 2 * (j : ℝ) ≤ u₀.re := by rw [hre]
    have hr' : u₀.re ≤ 7 / 2 + 2 * (j : ℝ) := by rw [hre]; linarith
    have hi : 1 ≤ |u₀.im| := by rw [him]; norm_num
    have hb := hstrip u₀ hr hr' hi
    rw [him] at hb
    simp at hb
    exact le_trans (norm_nonneg _) hb
  refine ⟨C₁ + 1, by positivity, ?_⟩
  intro u hu₁ hu₂ huim
  exact (hstrip u hu₁ hu₂ huim).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

private theorem caseBData_D_eq_Dext_C3d [IsTotallyComplex K] {h : ℝ → ℂ}
    (hh : IsQSWeight h) {u : ℂ} (hu : u.im ≠ 0) :
    (QSP2.caseBData (K := K) hh).D u = caseBDualDext_C3d (K := K) h u := by
  unfold caseBDualDext_C3d
  change (1 / 2 : ℂ) * Hecke.dedekindPrefactor K u * QSP2.Qd K (1 - u) *
      (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ * QSP2.qsPhiH h ((1 + u) / 2) =
    (1 / 2 : ℂ) * Hecke.dedekindPrefactor K u * qdExt_C3d (K := K) (1 - u) *
      (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ * QSP2.qsPhiH h ((1 + u) / 2)
  have hsim : (1 - u).im ≠ 0 := by
    have him : (1 - u).im = -u.im := by simp
    rw [him]
    exact neg_ne_zero.mpr hu
  rw [Qd_eq_qdExt_C3d (K := K) hsim]

set_option maxHeartbeats 1000000 in
private theorem caseBDualDext_mellinInv_shift_C3d [IsTotallyComplex K]
    {h : ℝ → ℂ} (hh : IsQSWeight h) {x : ℝ} (hx : 0 < x) (j : ℕ) :
    mellinInv (3 / 2 + 2 * (j : ℝ)) (caseBDualDext_C3d (K := K) h) x =
      mellinInv (3 / 2) (caseBDualDext_C3d (K := K) h) x := by
  induction j with
  | zero =>
      norm_num
  | succ j ih =>
      let a : ℝ := 3 / 2 + 2 * (j : ℝ)
      let b : ℝ := 7 / 2 + 2 * (j : ℝ)
      let F : ℂ → ℂ := fun u => (x : ℂ) ^ (-u) * caseBDualDext_C3d (K := K) h u
      obtain ⟨Ctail, hCtail, hDtail⟩ := caseBDualDext_decay_strip_C3d (K := K) hh j
      have hab : a ≤ b := by dsimp [a, b]; linarith
      have hFdiff : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ F s := by
        intro s h₁ h₂
        have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) s :=
          (differentiableAt_id.neg).const_cpow (Or.inl (by exact_mod_cast hx.ne'))
        have ha32 : 3 / 2 ≤ a := by dsimp [a]; linarith
        have hD := caseBDualDext_differentiableAt_C3d (K := K) hh (ha32.trans h₁)
        exact hpow.mul hD
      have hFlineBound : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
          ‖F s‖ ≤ Ctail * (x ^ (-a) + x ^ (-b)) / s.im ^ 2 := by
        intro s h₁ h₂ ht
        have hpow : x ^ (-s.re) ≤ x ^ (-b) + x ^ (-a) :=
          QSP2.rpow_le_add_of_mem hx (by linarith) (by linarith)
        have hD := hDtail s (by dsimp [a] at h₁; exact h₁)
          (by dsimp [b] at h₂; exact h₂) ht
        change ‖(x : ℂ) ^ (-s) * caseBDualDext_C3d (K := K) h s‖ ≤ _
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
        have hmul := mul_le_mul hpow hD (norm_nonneg _) (by positivity)
        calc
          x ^ (-s.re) * ‖caseBDualDext_C3d (K := K) h s‖ ≤
              (x ^ (-b) + x ^ (-a)) * (Ctail / s.im ^ 2) := hmul
          _ = Ctail * (x ^ (-a) + x ^ (-b)) / s.im ^ 2 := by ring
      have hlineCont : ∀ σ : ℝ, a ≤ σ → σ ≤ b →
          Continuous (fun t : ℝ => F (σ + t * I)) := by
        intro σ hσa hσb
        refine continuous_iff_continuousAt.mpr fun t => ?_
        exact ContinuousAt.comp (g := F) (f := fun t : ℝ => σ + t * I)
          (hFdiff (σ + t * I) (by simp; exact hσa) (by simp; exact hσb)).continuousAt
          (by fun_prop)
      have hlineInt : ∀ σ : ℝ, a ≤ σ → σ ≤ b →
          Integrable (fun t : ℝ => F (σ + t * I)) := by
        intro σ hσa hσb
        exact QSP2.integrable_of_cont_decay (hlineCont σ hσa hσb)
          (Ctail * (x ^ (-a) + x ^ (-b))) (fun t ht => by
            have h := hFlineBound (σ + t * I) (by simp; exact hσa) (by simp; exact hσb)
              (by simpa using ht)
            simpa using h)
      have hshift := QSP2.vline_eq_of_differentiable (G := F) (a := a) (b := b) hab
        (fun s h₁ h₂ => hFdiff s h₁ h₂)
        (hlineInt a (by rfl) (by linarith))
        (hlineInt b (by linarith) (by rfl))
        (Ctail * (x ^ (-a) + x ^ (-b))) hFlineBound
      have hstep : mellinInv b (caseBDualDext_C3d (K := K) h) x =
          mellinInv a (caseBDualDext_C3d (K := K) h) x := by
        unfold mellinInv
        simp only [smul_eq_mul]
        rw [hshift]
      have hab' : b = 3 / 2 + 2 * ((j + 1 : ℕ) : ℝ) := by
        dsimp [b]
        push_cast
        ring
      rw [hab'] at hstep
      exact hstep.trans ih


set_option maxHeartbeats 1000000 in
private theorem caseB_doubleTransform_decay_C3d [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖qsTransform K (fun y : ℝ => qsTransform K h (y ^ 2)) x‖ ≤
        C * x ^ (-(A : ℝ)) := by
  let j : ℕ := A
  let σ : ℝ := 3 / 2 + 2 * (j : ℝ)
  let f : ℝ → ℂ := fun y => qsTransform K h (y ^ 2)
  let P := QSP2.caseBData (K := K) (h := h) hh
  obtain ⟨Cdec, hCdec, hdec⟩ := caseBDualDext_decay_strip_C3d (K := K) hh j
  have hσlow : 3 / 2 ≤ σ := by dsimp [σ, j]; nlinarith
  have hcont : Continuous (fun t : ℝ => caseBDualDext_C3d (K := K) h (σ + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hD := caseBDualDext_differentiableAt_C3d (K := K) hh (by
      have : (σ + t * I).re = σ := by simp
      rw [this]
      exact hσlow)
    exact ContinuousAt.comp (g := caseBDualDext_C3d (K := K) h)
      (f := fun t : ℝ => σ + t * I) hD.continuousAt (by fun_prop)
  have hlineBound : ∀ t : ℝ, 1 ≤ |t| →
      ‖caseBDualDext_C3d (K := K) h (σ + t * I)‖ ≤ Cdec / t ^ 2 := by
    intro t ht
    have hre : (σ + t * I).re = σ := by simp
    have him : (σ + t * I).im = t := by simp
    have hsEq : σ = 3 / 2 + 2 * (j : ℝ) := rfl
    have hlower : 3 / 2 + 2 * (j : ℝ) ≤ (σ + t * I).re := by rw [hre, hsEq]
    have hupper : (σ + t * I).re ≤ 7 / 2 + 2 * (j : ℝ) := by
      rw [hre, hsEq]
      linarith
    have h := hdec (σ + t * I) hlower hupper
      (by rw [him]; exact ht)
    simpa [him] using h
  have hInt := QSP2.integrable_of_cont_decay hcont Cdec hlineBound
  let J : ℝ := ∫ t : ℝ, ‖caseBDualDext_C3d (K := K) h (σ + t * I)‖
  have hJ : 0 ≤ J := by dsimp [J]; exact integral_nonneg fun t => norm_nonneg _
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
  have hline : (fun t : ℝ => P.D ((3 / 2 : ℝ) + t * I)) =ᵐ[volume]
      fun t => caseBDualDext_C3d (K := K) h ((3 / 2 : ℝ) + t * I) := by
    filter_upwards [hne] with t ht
    have him : (((3 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
    simpa [him] using caseBData_D_eq_Dext_C3d (K := K) hh (by simpa [him] using ht)
  refine ⟨1 + J, by positivity, ?_⟩
  intro X hX
  have hlineInt :
      ∫ t : ℝ, (((X : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * I))) *
        P.D (((3 / 2 : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, (((X : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * I))) *
        caseBDualDext_C3d (K := K) h (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    apply integral_congr_ae
    filter_upwards [hline] with t ht
    rw [ht]
  have hInv : mellinInv (3 / 2) P.D X =
      mellinInv (3 / 2) (caseBDualDext_C3d (K := K) h) X := by
    unfold mellinInv
    simp only [smul_eq_mul]
    rw [hlineInt]
  have hshift := caseBDualDext_mellinInv_shift_C3d (K := K) hh (x := X)
    (by positivity) j
  have hbound : qsTransform K f X =
      mellinInv σ (caseBDualDext_C3d (K := K) h) X := by
    calc
      qsTransform K f X = mellinInv (3 / 2) P.D X := QSP2.transform_eq P (by positivity)
      _ = mellinInv (3 / 2) (caseBDualDext_C3d (K := K) h) X := hInv
      _ = mellinInv σ (caseBDualDext_C3d (K := K) h) X := hshift.symm
  have hσA : (A : ℝ) ≤ σ := by dsimp [σ, j]; nlinarith
  have hσexp : -σ ≤ -(A : ℝ) := by linarith
  have hpow : X ^ (-σ) ≤ X ^ (-(A : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hX hσexp
  have hcoef : 0 < 1 / (2 * Real.pi) ∧ 1 / (2 * Real.pi) ≤ 1 := by
    constructor
    · positivity
    · have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      simpa using one_div_le_one_div_of_le (by norm_num) hpi
  have hnorm := QSP2.norm_mellinInv_le σ (caseBDualDext_C3d (K := K) h) (by linarith : 0 < X)
  calc
    ‖qsTransform K f X‖ =
        ‖mellinInv σ (caseBDualDext_C3d (K := K) h) X‖ := by rw [hbound]
    _ ≤ (1 / (2 * Real.pi)) * X ^ (-σ) * J := by
      simpa [J] using hnorm
    _ ≤ (1 + J) * X ^ (-(A : ℝ)) := by
      calc
        (1 / (2 * Real.pi)) * X ^ (-σ) * J ≤ X ^ (-σ) * J := by
          have h₁ := mul_le_mul_of_nonneg_right hcoef.2
            (Real.rpow_nonneg (by linarith : 0 ≤ X) (-σ))
          have h₂ := mul_le_mul_of_nonneg_right h₁ hJ
          simpa using h₂
        _ ≤ X ^ (-(A : ℝ)) * J := mul_le_mul_of_nonneg_right hpow hJ
        _ ≤ (1 + J) * X ^ (-(A : ℝ)) := by
          have hXpow : 0 ≤ X ^ (-(A : ℝ)) := Real.rpow_nonneg (by linarith) _
          calc
            X ^ (-(A : ℝ)) * J = J * X ^ (-(A : ℝ)) := by ring
            _ ≤ (1 + J) * X ^ (-(A : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith) hXpow

private theorem qs_scaled_tsum_decay_C3d [IsTotallyComplex K]
    (h : ℝ → ℂ) (CA : ℝ) (A : ℕ) (ε : ℝ)
    (hCA : 0 ≤ CA) (hε : 0 < ε) (hA : 1 + ε ≤ (A : ℝ))
    (hdec : ∀ y : ℝ, 1 ≤ y → ‖h y‖ ≤ CA * y ^ (-(A : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 < X → X ≤ 1 →
      Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ‖h (qsN b.1 / X)‖) ∧
      ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, ‖h (qsN b.1 / X)‖ ≤ C * CA * X ^ A := by
  have hbase₀ : Summable
      (fun I : Ideal (𝓞 K) => ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) I) :=
    ArtinPrimitiveRoots.Hecke.summable_idealNormRpow (K := K) (by linarith)
  let S : ℝ := ∑' I : Ideal (𝓞 K),
    ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) I
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun I => by
      dsimp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
      split_ifs <;> positivity
  let C : ℝ := 1 + S
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro X hX hX1
  let base : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun b =>
    ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) b.1
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun b => ‖h (qsN b.1 / X)‖
  have hbase : Summable base := by
    dsimp [base]
    exact hbase₀.subtype {I : Ideal (𝓞 K) | I ≠ ⊥}
  let factor : ℝ := CA * X ^ A
  have hfactor : 0 ≤ factor := by dsimp [factor]; positivity
  have hpoint : ∀ b, f b ≤ factor * base b := by
    intro b
    have hn : 1 ≤ qsN b.1 := QSC3.one_le_qsN b.2
    have hnpos : 0 < qsN b.1 := lt_of_lt_of_le zero_lt_one hn
    have hratio : 1 ≤ qsN b.1 / X := by
      rw [one_le_div₀ hX]
      exact le_trans hX1 hn
    have hscale : (qsN b.1 / X) ^ (-(A : ℝ)) =
        X ^ (A : ℝ) * qsN b.1 ^ (-(A : ℝ)) := by
      calc
        (qsN b.1 / X) ^ (-(A : ℝ)) = (qsN b.1 / X)⁻¹ ^ (A : ℝ) :=
          Real.rpow_neg_eq_inv_rpow _ _
        _ = (X / qsN b.1) ^ (A : ℝ) := by congr 1 <;> field_simp
        _ = X ^ (A : ℝ) / qsN b.1 ^ (A : ℝ) :=
          Real.div_rpow (x := X) (y := qsN b.1) (by positivity) (by positivity) (A : ℝ)
        _ = X ^ (A : ℝ) * qsN b.1 ^ (-(A : ℝ)) := by
          rw [Real.rpow_neg hnpos.le]
          rw [div_eq_mul_inv]
    have hpowN : qsN b.1 ^ (-(A : ℝ)) ≤ qsN b.1 ^ (-(1 + ε)) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    have hnormNat : Ideal.absNorm b.1 ≠ 0 := by
      intro hz
      exact b.2 (Ideal.absNorm_eq_zero_iff.mp hz)
    have hbaseEq : base b = qsN b.1 ^ (-(1 + ε)) := by
      dsimp [base, ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
      simp [qsN, hnormNat]
    calc
      f b ≤ CA * (qsN b.1 / X) ^ (-(A : ℝ)) := hdec _ hratio
      _ = factor * qsN b.1 ^ (-(A : ℝ)) := by
        dsimp [factor]
        rw [hscale]
        rw [Real.rpow_natCast]
        ac_rfl
      _ ≤ factor * qsN b.1 ^ (-(1 + ε)) :=
        mul_le_mul_of_nonneg_left hpowN hfactor
      _ = factor * base b := by rw [hbaseEq]
  have hmajor : Summable (fun b => factor * base b) := hbase.mul_left factor
  have hsum : Summable f := hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have hbaseSum : (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, base b) ≤ S := by
    calc
      _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) b.1 := by rfl
      _ ≤ S := by
        dsimp [S]
        exact hbase₀.tsum_subtype_le _ {I : Ideal (𝓞 K) | I ≠ ⊥} (fun I => by
          dsimp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
          split_ifs <;> positivity)
  have hsumBound : (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, f b) ≤ factor * S := by
    calc
      _ ≤ ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, factor * base b :=
        hsum.tsum_le_tsum hpoint hmajor
      _ = factor * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, base b := hbase.tsum_mul_left factor
      _ ≤ factor * S := mul_le_mul_of_nonneg_left hbaseSum hfactor
  constructor
  · simpa [f] using hsum
  · calc
      (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, ‖h (qsN b.1 / X)‖) = ∑' b, f b := by rfl
      _ ≤ factor * S := hsumBound
      _ ≤ C * CA * X ^ A := by
        dsimp [factor, C]
        calc
          CA * X ^ A * S = S * (CA * X ^ A) := by ring
          _ ≤ (1 + S) * (CA * X ^ A) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (1 + S) * CA * X ^ A := by ring

set_option maxHeartbeats 1000000 in
private theorem qs_innerTail_bound_C3d [IsTotallyComplex K]
    (h : ℝ → ℂ) (Cdual Cdir : ℝ) (A : ℕ) (ε : ℝ)
    (hCdual : 0 < Cdual) (hCdir : 0 < Cdir) (hε : 0 < ε) (hAε : 1 + ε ≤ (A : ℝ))
    (hA2 : 2 ≤ A)
    (hdual : ∀ y : ℝ, 1 ≤ y →
      ‖qsTransform K h y‖ ≤ Cdual * y ^ (-(A : ℝ)))
    (hdir : ∀ y : ℝ, 1 ≤ y → ‖h y‖ ≤ Cdir * y ^ (-(A : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ (Z : ℝ) (n : Ideal (𝓞 K)) (Ylo Zhi : ℝ),
      n ≠ ⊥ → 0 < Z → Ylo ≤ Z / Λ → Λ * Z ≤ Zhi →
      ‖qsInnerTail K h Z n Ylo Zhi‖ ≤
        C * (qsDivisors n).card * Λ ^ (-((A : ℝ) - 1)) := by
  classical
  obtain ⟨Cd, hCd, hdualScale⟩ :=
    qs_scaled_tsum_decay_C3d (K := K) (qsTransform K h) Cdual A ε
      (le_of_lt hCdual) hε hAε hdual
  obtain ⟨Co, hCo, hdirScale⟩ :=
    qs_scaled_tsum_decay_C3d (K := K) h Cdir A ε
      (le_of_lt hCdir) hε hAε hdir
  let C : ℝ := 2 * (Cd * Cdual + Co * Cdir + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Λ hΛ
  intro Z n Ylo Zhi hn hZ hYlo hZhi
  let low := (qsDivisors n).filter (fun e => qsN e ≤ Ylo)
  let high := (qsDivisors n).filter (fun e => Zhi < qsN e)
  have hΛpos : 0 < Λ := by linarith
  have hdivisor_ne_bot {e : Ideal (𝓞 K)} (he : e ∈ qsDivisors n) : e ≠ ⊥ := by
    intro hebot
    have hdvd : e ∣ n := by
      classical
      unfold qsDivisors at he
      exact (Finset.mem_filter.mp he).2
    have hbotdiv : (⊥ : Ideal (𝓞 K)) ∣ n := by simpa [hebot] using hdvd
    exact hn (le_bot_iff.mp (Ideal.dvd_iff_le.mp hbotdiv))
  have hlowTerm : ∀ e ∈ low,
      ‖(qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          qsTransform K h (Z * qsN b.1 / qsN e)‖ ≤
        (Cd * Cdual) * Λ ^ (-((A : ℝ) - 1)) := by
    intro e he
    have helow := Finset.mem_filter.mp he
    have he0 := hdivisor_ne_bot helow.1
    have heN : 1 ≤ qsN e := QSC3.one_le_qsN he0
    let X : ℝ := qsN e / Z
    have hXpos : 0 < X := div_pos (lt_of_lt_of_le zero_lt_one heN) hZ
    have hXlim : X ≤ 1 / Λ := by
      dsimp [X]
      rw [div_le_iff₀ hZ]
      calc
        qsN e ≤ Z / Λ := le_trans helow.2 hYlo
        _ = (1 / Λ) * Z := by ring
    have hX1 : X ≤ 1 := le_trans hXlim ((div_le_one hΛpos).2 hΛ)
    obtain ⟨hsNorm, hsumNorm⟩ := hdualScale X hXpos hX1
    have hseries : Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        qsTransform K h (Z * qsN b.1 / qsN e)) := by
      apply Summable.of_norm
      apply hsNorm.congr
      intro b
      have harg : qsN b.1 / X = Z * qsN b.1 / qsN e := by
        dsimp [X]
        field_simp
      rw [harg]
    have hsumNorm' :
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ‖qsTransform K h (Z * qsN b.1 / qsN e)‖ ≤ Cd * Cdual * X ^ A := by
      calc
        _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              ‖qsTransform K h (qsN b.1 / X)‖ := by
                apply tsum_congr
                intro b
                have harg : qsN b.1 / X = Z * qsN b.1 / qsN e := by
                  dsimp [X]
                  field_simp
                rw [harg]
        _ ≤ Cd * Cdual * X ^ A := hsumNorm
    have htsum :=
      (norm_tsum_le_tsum_norm hseries.norm).trans hsumNorm'
    have hscale : (Z / qsN e) * X ^ A = X ^ ((A : ℝ) - 1) := by
      have hZX : Z / qsN e = X⁻¹ := by dsimp [X]; field_simp
      have hinv : X⁻¹ = X ^ (-1 : ℝ) := by
        have h := Real.rpow_neg hXpos.le (1 : ℝ)
        simpa using h.symm
      calc
        (Z / qsN e) * X ^ A = X⁻¹ * X ^ (A : ℝ) := by
          rw [hZX, ← Real.rpow_natCast]
        _ = X ^ (-1 : ℝ) * X ^ (A : ℝ) := by rw [hinv]
        _ = X ^ ((A : ℝ) - 1) := by
          rw [← Real.rpow_add hXpos]
          congr 1
          ring
    have hA1 : 1 ≤ (A : ℝ) := by exact_mod_cast (show 1 ≤ A by omega)
    have hposExp : 0 ≤ (A : ℝ) - 1 := by linarith
    have hpowΛ : X ^ ((A : ℝ) - 1) ≤ Λ ^ (-((A : ℝ) - 1)) := by
      have hpowX := Real.rpow_le_rpow hXpos.le hXlim hposExp
      have hpowInv : (1 / Λ) ^ ((A : ℝ) - 1) = Λ ^ (-((A : ℝ) - 1)) := by
        rw [Real.div_rpow (by norm_num) (le_of_lt hΛpos) ((A : ℝ) - 1), Real.one_rpow,
          Real.rpow_neg hΛpos.le]
        simpa [one_div]
      rw [hpowInv] at hpowX
      exact hpowX
    have hnormMu := QSC2.norm_qsMu_le e
    have hZNePos : 0 < Z / qsN e := div_pos hZ (lt_of_lt_of_le zero_lt_one heN)
    have hnormScalar : ‖((Z / qsN e : ℝ) : ℂ)‖ = Z / qsN e := by
      rw [Complex.norm_real]
      exact abs_of_pos hZNePos
    calc
      ‖(qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            qsTransform K h (Z * qsN b.1 / qsN e)‖
        = ‖(qsMu e : ℂ)‖ * (Z / qsN e) *
            ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              qsTransform K h (Z * qsN b.1 / qsN e)‖ := by
                rw [norm_mul, norm_mul, hnormScalar]
      _ ≤ 1 * (Z / qsN e) * (Cd * Cdual * X ^ A) := by
        calc
          ‖(qsMu e : ℂ)‖ * (Z / qsN e) *
              ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
                qsTransform K h (Z * qsN b.1 / qsN e)‖
            ≤ 1 * (Z / qsN e) *
                ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
                  qsTransform K h (Z * qsN b.1 / qsN e)‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hnormMu (by positivity)) (norm_nonneg _)
          _ ≤ 1 * (Z / qsN e) * (Cd * Cdual * X ^ A) := by
              exact mul_le_mul_of_nonneg_left htsum (by positivity)
      _ = Cd * Cdual * ((Z / qsN e) * X ^ A) := by ring
      _ = Cd * Cdual * X ^ ((A : ℝ) - 1) := by rw [hscale]
      _ ≤ Cd * Cdual * Λ ^ (-((A : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hpowΛ (by positivity)
  have hhighTerm : ∀ e ∈ high,
      ‖(qsMu e : ℂ) *
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, h (qsN e * qsN b.1 / Z)‖ ≤
        (Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) := by
    intro e he
    have hehigh := Finset.mem_filter.mp he
    have he0 := hdivisor_ne_bot hehigh.1
    have heN : 1 ≤ qsN e := QSC3.one_le_qsN he0
    let X : ℝ := Z / qsN e
    have hXpos : 0 < X := div_pos hZ (by positivity)
    have hXlim : X ≤ 1 / Λ := by
      dsimp [X]
      have hstrict : Λ * Z < qsN e := lt_of_le_of_lt hZhi hehigh.2
      rw [div_le_iff₀ (by positivity : 0 < qsN e)]
      calc
        Z ≤ qsN e / Λ := (le_div_iff₀ hΛpos).2 (by simpa [mul_comm] using hstrict.le)
        _ = (1 / Λ) * qsN e := by ring
    have hX1 : X ≤ 1 := le_trans hXlim ((div_le_one hΛpos).2 hΛ)
    obtain ⟨hsNorm, hsumNorm⟩ := hdirScale X hXpos hX1
    have harg (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
        qsN b.1 / X = qsN e * qsN b.1 / Z := by
      dsimp [X]
      field_simp
    have hseries : Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        h (qsN e * qsN b.1 / Z)) := by
      apply Summable.of_norm
      apply hsNorm.congr
      intro b
      rw [harg b]
    have hsumNorm' :
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, ‖h (qsN e * qsN b.1 / Z)‖ ≤
          Co * Cdir * X ^ A := by
      calc
        _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, ‖h (qsN b.1 / X)‖ := by
              apply tsum_congr
              intro b
              rw [← harg b]
        _ ≤ Co * Cdir * X ^ A := hsumNorm
    have htsum := (norm_tsum_le_tsum_norm hseries.norm).trans hsumNorm'
    have hXsmallPow : X ^ A ≤ Λ ^ (-((A : ℝ) - 1)) := by
      calc
        X ^ A = X ^ (A : ℝ) := (Real.rpow_natCast X A).symm
        _ ≤ (1 / Λ) ^ (A : ℝ) :=
          Real.rpow_le_rpow hXpos.le hXlim (by positivity)
        _ = Λ ^ (-(A : ℝ)) := by
          rw [Real.div_rpow (by norm_num) (le_of_lt hΛpos) (A : ℝ), Real.one_rpow,
            Real.rpow_neg hΛpos.le]
          simpa [one_div]
        _ ≤ Λ ^ (-((A : ℝ) - 1)) :=
          Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
    have hmu : ‖(qsMu e : ℂ)‖ ≤ 1 := QSC2.norm_qsMu_le e
    calc
      ‖(qsMu e : ℂ) *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, h (qsN e * qsN b.1 / Z)‖
        = ‖(qsMu e : ℂ)‖ *
            ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, h (qsN e * qsN b.1 / Z)‖ := norm_mul _ _
      _ ≤ 1 * (Co * Cdir * X ^ A) := by
        calc
          ‖(qsMu e : ℂ)‖ *
              ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, h (qsN e * qsN b.1 / Z)‖
            ≤ 1 *
                ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, h (qsN e * qsN b.1 / Z)‖ :=
              mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
          _ ≤ 1 * (Co * Cdir * X ^ A) :=
            mul_le_mul_of_nonneg_left htsum (by norm_num)
      _ = Co * Cdir * X ^ A := by ring
      _ ≤ Co * Cdir * Λ ^ (-((A : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hXsmallPow (by positivity)
  unfold qsInnerTail
  let low := (qsDivisors n).filter (fun e => qsN e ≤ Ylo)
  let high := (qsDivisors n).filter (fun e => Zhi < qsN e)
  have hlowCard : (low.card : ℝ) ≤ (qsDivisors n).card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hhighCard : (high.card : ℝ) ≤ (qsDivisors n).card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hsumLow :
      ‖∑ e ∈ low, (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          qsTransform K h (Z * qsN b.1 / qsN e)‖ ≤
        (low.card : ℝ) * (Cd * Cdual) * Λ ^ (-((A : ℝ) - 1)) := by
    calc
      _ ≤ ∑ e ∈ low, ‖(qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              qsTransform K h (Z * qsN b.1 / qsN e)‖ := norm_sum_le _ _
      _ ≤ ∑ _e ∈ low, (Cd * Cdual) * Λ ^ (-((A : ℝ) - 1)) := by
            apply Finset.sum_le_sum
            intro e he
            exact hlowTerm e he
      _ = (low.card : ℝ) * (Cd * Cdual) * Λ ^ (-((A : ℝ) - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hsumHigh :
      ‖∑ e ∈ high, (qsMu e : ℂ) *
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, h (qsN e * qsN b.1 / Z)‖ ≤
        (high.card : ℝ) * (Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) := by
    calc
      _ ≤ ∑ e ∈ high, ‖(qsMu e : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, h (qsN e * qsN b.1 / Z)‖ := norm_sum_le _ _
      _ ≤ ∑ _e ∈ high, (Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) := by
            apply Finset.sum_le_sum
            intro e he
            exact hhighTerm e he
      _ = (high.card : ℝ) * (Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have htotal :
      ‖(∑ e ∈ low, (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            qsTransform K h (Z * qsN b.1 / qsN e)) +
        ∑ e ∈ high, (qsMu e : ℂ) *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, h (qsN e * qsN b.1 / Z)‖ ≤
        C * (qsDivisors n).card * Λ ^ (-((A : ℝ) - 1)) := by
    calc
      _ ≤ (low.card : ℝ) * (Cd * Cdual) * Λ ^ (-((A : ℝ) - 1)) +
          (high.card : ℝ) * (Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) :=
            (norm_add_le _ _).trans (add_le_add hsumLow hsumHigh)
      _ ≤ 2 * ((qsDivisors n).card : ℝ) *
            (Cd * Cdual + Co * Cdir + 1) * Λ ^ (-((A : ℝ) - 1)) := by
          let Ndiv : ℝ := (qsDivisors n).card
          have hNdiv : 0 ≤ Ndiv := by dsimp [Ndiv]; positivity
          have hL : 0 ≤ Λ ^ (-((A : ℝ) - 1)) := Real.rpow_nonneg (le_of_lt hΛpos) _
          have hleft : (low.card : ℝ) * (Cd * Cdual) * Λ ^ (-((A : ℝ) - 1)) ≤
              Ndiv * (Cd * Cdual) * Λ ^ (-((A : ℝ) - 1)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hlowCard (by positivity)) hL
          have hright : (high.card : ℝ) * (Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) ≤
              Ndiv * (Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hhighCard (by positivity)) hL
          have hcoef0 : 0 ≤ Cd * Cdual + Co * Cdir := by positivity
          have hcoef : Cd * Cdual + Co * Cdir ≤
              2 * (Cd * Cdual + Co * Cdir + 1) := by nlinarith
          have hcoeffN : Ndiv * (Cd * Cdual + Co * Cdir) ≤
              2 * Ndiv * (Cd * Cdual + Co * Cdir + 1) := by
            calc
              _ ≤ Ndiv * (2 * (Cd * Cdual + Co * Cdir + 1)) :=
                mul_le_mul_of_nonneg_left hcoef hNdiv
              _ = _ := by ring
          calc
            _ ≤ Ndiv * (Cd * Cdual) * Λ ^ (-((A : ℝ) - 1)) +
                  Ndiv * (Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) := add_le_add hleft hright
            _ = Ndiv * (Cd * Cdual + Co * Cdir) * Λ ^ (-((A : ℝ) - 1)) := by ring
            _ ≤ 2 * Ndiv * (Cd * Cdual + Co * Cdir + 1) *
                  Λ ^ (-((A : ℝ) - 1)) :=
                mul_le_mul_of_nonneg_right hcoeffN hL
      _ = C * (qsDivisors n).card * Λ ^ (-((A : ℝ) - 1)) := by dsimp [C]; ring
  simpa [low, high] using htotal

private theorem capSquare_isQSWeight_C3d (W : ℝ → ℝ) (hW : IsCapWeight W) :
    IsQSWeight (fun y : ℝ => (W (y ^ 2) : ℂ)) := by
  rcases hW.1 with ⟨hcont, hsupport, hnear⟩
  refine ⟨hcont.comp (contDiff_id.pow 2), ?_, ?_⟩
  · refine ⟨Real.sqrt (5 / 2), fun y hy => ?_⟩
    have hy0 : 0 ≤ y := le_trans (Real.sqrt_nonneg _) hy
    have hsquare : (5 / 2 : ℝ) ≤ y ^ 2 := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 2)
      calc
        5 / 2 = Real.sqrt (5 / 2) ^ 2 := hs.symm
        _ ≤ y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy 2
    simp [hW.2.2.2 (y ^ 2) hsquare]
  · obtain ⟨δ, hδ, hconst⟩ := hnear
    refine ⟨Real.sqrt δ, Real.sqrt_pos.2 hδ, ?_⟩
    intro y hy
    have hs := Real.sq_sqrt (le_of_lt hδ)
    have hsquare : y ^ 2 ≤ δ := by
      calc
        y ^ 2 ≤ Real.sqrt δ ^ 2 := pow_le_pow_left₀ hy.1 hy.2 2
        _ = δ := hs
    have hy2 : y ^ 2 ∈ Set.Icc (0 : ℝ) δ := ⟨sq_nonneg _, hsquare⟩
    simpa using hconst (y ^ 2) hy2

set_option maxHeartbeats 1000000 in
private theorem capSquare_decay_C3d (W : ℝ → ℝ) (hW : IsCapWeight W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ y →
      ‖(W (y ^ 2) : ℂ)‖ ≤ C * y ^ (-(A : ℝ)) := by
  let R : ℝ := Real.sqrt (5 / 2)
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact Real.one_le_sqrt.mpr (by norm_num)
  have hsq := capSquare_isQSWeight_C3d W hW
  have hcont : ContinuousOn (fun y : ℝ => (W (y ^ 2) : ℂ)) (Set.Icc (1 : ℝ) R) :=
    hsq.1.continuous.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (1 : ℝ) R) hcont
  let M₀ : ℝ := |B| + 1
  let C : ℝ := M₀ * R ^ A
  refine ⟨C, by dsimp [C, M₀]; positivity, ?_⟩
  intro y hy
  by_cases hlarge : R ≤ y
  · have hsquare : (5 / 2 : ℝ) ≤ y ^ 2 := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 2)
      calc
        5 / 2 = R ^ 2 := by simpa [R] using hs.symm
        _ ≤ y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hlarge 2
    simp [hW.2.2.2 (y ^ 2) hsquare]
    positivity
  · have hyR : y ≤ R := le_of_not_ge hlarge
    have hnorm := hB y ⟨hy, hyR⟩
    have hbound : ‖(W (y ^ 2) : ℂ)‖ ≤ M₀ := by
      calc
        ‖(W (y ^ 2) : ℂ)‖ ≤ B := hnorm
        _ ≤ |B| + 1 := by linarith [le_abs_self B]
        _ = M₀ := by rfl
    have hyPow : y ^ A ≤ R ^ A := pow_le_pow_left₀ (by linarith) hyR _
    have hdenpos : 0 < y ^ A := pow_pos (by linarith) _
    have hdenposR : 0 < y ^ (A : ℝ) := by rw [Real.rpow_natCast]; exact hdenpos
    rw [Real.rpow_neg (by linarith : 0 ≤ y)]
    rw [← div_eq_mul_inv]
    rw [le_div_iff₀ hdenposR]
    rw [Real.rpow_natCast]
    dsimp [C]
    calc
      ‖(W (y ^ 2) : ℂ)‖ * y ^ A ≤ M₀ * y ^ A :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
      _ ≤ M₀ * R ^ A := mul_le_mul_of_nonneg_left hyPow (by positivity)
      _ = C := rfl

private theorem qs_transform_decay_C3d [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (A : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ y →
      ‖qsTransform K h y‖ ≤ C * y ^ (-(A : ℝ)) := by
  obtain ⟨_, ⟨C, hC, hb⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh A 0 η hη
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have h := (hb y hypos).2 hy
  simpa only [iteratedDeriv_zero] using h

private theorem qs_transform_decay_quarter_C3d [IsTotallyComplex K]
    (h : ℝ → ℂ) (hh : IsQSWeight h) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 / 4 ≤ y →
      ‖qsTransform K h y‖ ≤ C * y ^ (-(A : ℝ)) := by
  obtain ⟨_, ⟨C₀, hC₀, hb⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh A 0 (1 / 8) (by norm_num)
  let C : ℝ := C₀ * ((1 / 4 : ℝ) ^ (-(1 / 8 : ℝ)) + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hypos : 0 < y := by linarith
  by_cases hy1 : y ≤ 1
  · have hsmall := (hb y hypos).1 hy1
    have hquarter : y ^ (-(1 / 8 : ℝ)) ≤ (1 / 4 : ℝ) ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hy (by norm_num)
    have hinv : 1 ≤ 1 / y := (one_le_div₀ hypos).2 hy1
    have hpow : 1 ≤ y ^ (-(A : ℝ)) := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact Real.one_le_rpow (by simpa [one_div] using hinv) (Nat.cast_nonneg A)
    calc
      ‖qsTransform K h y‖ ≤ C₀ * y ^ (-(1 / 8 : ℝ)) := by
        simpa [iteratedDeriv_zero] using hsmall
      _ ≤ C₀ * (1 / 4 : ℝ) ^ (-(1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hquarter (le_of_lt hC₀)
      _ ≤ C * y ^ (-(A : ℝ)) := by
        dsimp [C]
        have h₀ : 0 ≤ C₀ * ((1 / 4 : ℝ) ^ (-(1 / 8 : ℝ))) := by positivity
        nlinarith
  · have hlarge := (hb y hypos).2 (le_of_not_ge hy1)
    calc
      ‖qsTransform K h y‖ ≤ C₀ * y ^ (-(A : ℝ)) := by
        simpa only [iteratedDeriv_zero] using hlarge
      _ ≤ C * y ^ (-(A : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
        dsimp [C]
        have hD : 0 ≤ (1 / 4 : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
        nlinarith [hC₀, hD]

private theorem qs_norm_multiset_prod_le_one_C3d {α : Type*} (s : Multiset α)
    (f : α → ℂ) (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) (ih fun x hx =>
        hf x (Multiset.mem_cons_of_mem hx))

private theorem qs_primeValue_norm_le_one_C3d
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (hsq : χ ^ 2 = 1)
    (v : ArtinPrimitiveRoots.A1.FinPlace K) :
    ‖ArtinPrimitiveRoots.A1.HeckeChar.primeValue χ v‖ ≤ 1 := by
  by_cases hu : ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt χ v
  · simp only [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hu, ↓reduceDIte]
    let u : (v.adicCompletion K)ˣ :=
      ArtinPrimitiveRoots.A1.toLoc v (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
        (ArtinPrimitiveRoots.A1.unif_ne_zero v))
    have hloc : (ArtinPrimitiveRoots.A1.HeckeChar.loc χ v u) ^ 2 = 1 := by
      let x := IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u
      have h := congrArg (fun ψ : ArtinPrimitiveRoots.A1.HeckeChar K => ψ x) hsq
      simpa [pow_two, x, ArtinPrimitiveRoots.A1.HeckeChar.loc] using h
    have hpow :
        ((ArtinPrimitiveRoots.A1.HeckeChar.loc χ v u : ℂˣ) : ℂ) ^ 2 = 1 := by
      simpa only [pow_two, Units.val_mul, Units.val_one] using
        congrArg (fun z : ℂˣ => (z : ℂ)) hloc
    have hnorm : ‖((ArtinPrimitiveRoots.A1.HeckeChar.loc χ v u : ℂˣ) : ℂ)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hpow (by norm_num)
    simpa using le_of_eq hnorm
  · simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hu]

private theorem qs_idealValue_norm_le_one_C3d
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (hsq : χ ^ 2 = 1)
    (I : Ideal (𝓞 K)) :
    ‖ArtinPrimitiveRoots.A1.HeckeChar.idealValue χ I‖ ≤ 1 := by
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  apply qs_norm_multiset_prod_le_one_C3d
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using qs_primeValue_norm_le_one_C3d χ hsq ⟨P, h.1, h.2⟩
  · simp [h]

private theorem qs_pairChar_sq_C3d (F : QSFamily m qS)
    {c d : Ideal (𝓞 K)} (hc : QSAdm m qS c) (hd : QSAdm m qS d) :
    (qsPairChar F c d) ^ 2 = 1 := by
  have hc2 := F.character_order_two c hc.1 hc.2.1
  have hd2 := F.character_order_two d hd.1 hd.2.1
  rw [qsPairChar, mul_pow, hc2, inv_pow, hd2]
  simp

private theorem qs_sfNorm_le_qsN_C3d (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (qsSfNorm I : ℝ) ≤ qsN I := by
  obtain ⟨p, hp, -⟩ := qs_squarefree_decomposition_M1 I hI
  rcases p with ⟨a₀, b⟩
  rcases hp with ⟨ha₀, hIeq⟩
  have hb0 : b ≠ ⊥ := by
    intro hb
    apply hI
    rw [hIeq, hb]
    simp
  have hsf : qsSfNorm I = Ideal.absNorm a₀ := by
    rw [hIeq, qs_sfNorm_eq_M1 a₀ b ha₀ hb0]
  have hsfCast : (qsSfNorm I : ℝ) = qsN a₀ := by
    simpa [qsN] using congrArg (fun n : ℕ => (n : ℝ)) hsf
  have hmul : qsN I = qsN a₀ * (qsN b) ^ 2 := by
    simp [qsN, hIeq, map_mul, map_pow]
  have hbn : 1 ≤ qsN b := QSC3.one_le_qsN hb0
  have hbSq : 1 ≤ (qsN b) ^ 2 := one_le_pow₀ hbn
  calc
    (qsSfNorm I : ℝ) = qsN a₀ := hsfCast
    _ ≤ qsN a₀ * (qsN b) ^ 2 := by
      have hna : 0 ≤ qsN a₀ := by positivity
      have := mul_le_mul_of_nonneg_left hbSq hna
      nlinarith
    _ = qsN I := hmul.symm

private noncomputable def qsHigh_tail_constant_C3d (ε : ℝ) : ℝ :=
  1 + ∑' I : Ideal (𝓞 K),
    ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) I

set_option maxHeartbeats 50000000 in
private theorem qsHigh_tail_bound_C3d [IsTotallyComplex K]
    (h : ℝ → ℂ) (CA : ℝ) (A : ℕ) (ε : ℝ)
    (hCA : 0 ≤ CA) (hε : 0 < ε) (hAε : 1 + ε < (A : ℝ)) (hA2 : 2 ≤ A)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (hχ : ∀ I : Ideal (𝓞 K), ‖χ.idealValue I‖ ≤ 1)
    (Y κ : ℝ) (hY : 0 < Y) (hκ : 1 ≤ κ) (hYK : Y ≤ 4 * κ)
    (hdec : ∀ x : ℝ, 1 / 4 ≤ x → ‖h x‖ ≤ CA * x ^ (-(A : ℝ))) :
    ‖qsHigh h Y κ ⊤ χ‖ ≤
      qsHigh_tail_constant_C3d (K := K) ε * CA * κ ^ (1 + ε) * (Y / κ) ^ A := by
  classical
  have hbase₀ : Summable
      (fun I : Ideal (𝓞 K) => ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) I) :=
    ArtinPrimitiveRoots.Hecke.summable_idealNormRpow (K := K) (by linarith)
  let S : ℝ := ∑' I : Ideal (𝓞 K),
    ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) I
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun I => by
      dsimp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
      split_ifs <;> positivity
  let q : ℝ := (A : ℝ) - (1 + ε)
  have hq : 0 < q := by dsimp [q]; exact sub_pos.mpr hAε
  let factor : ℝ := CA * Y ^ A * κ ^ (1 + ε - A)
  have hfactor : 0 ≤ factor := by dsimp [factor]; positivity
  let base : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun a =>
    ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) a.1
  have hbase : Summable base := by
    dsimp [base]
    exact hbase₀.subtype {I : Ideal (𝓞 K) | I ≠ ⊥}
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if IsCoprime a.1 ⊤ ∧ κ < (qsSfNorm a.1 : ℝ) then
      χ.idealValue a.1 * h (qsN a.1 / Y) else 0
  have hpoint : ∀ a, ‖f a‖ ≤ factor * base a := by
    intro a
    by_cases hc : IsCoprime a.1 ⊤ ∧ κ < (qsSfNorm a.1 : ℝ)
    · have hsfN := qs_sfNorm_le_qsN_C3d a.1 a.2
      have hNgt : κ < qsN a.1 := lt_of_lt_of_le hc.2 hsfN
      have hn : 1 ≤ qsN a.1 := QSC3.one_le_qsN a.2
      have hnpos : 0 < qsN a.1 := lt_of_lt_of_le zero_lt_one hn
      have hratio : 1 / 4 ≤ qsN a.1 / Y := by
        rw [le_div_iff₀ hY]
        nlinarith [hYK, hNgt]
      have hscale : (qsN a.1 / Y) ^ (-(A : ℝ)) =
          Y ^ (A : ℝ) * qsN a.1 ^ (-(A : ℝ)) := by
        calc
          (qsN a.1 / Y) ^ (-(A : ℝ)) = (qsN a.1 / Y)⁻¹ ^ (A : ℝ) :=
            Real.rpow_neg_eq_inv_rpow _ _
          _ = (Y / qsN a.1) ^ (A : ℝ) := by congr 1 <;> field_simp
          _ = Y ^ (A : ℝ) / qsN a.1 ^ (A : ℝ) :=
            Real.div_rpow (by positivity) (by positivity) (A : ℝ)
          _ = Y ^ (A : ℝ) * qsN a.1 ^ (-(A : ℝ)) := by
            rw [Real.rpow_neg hnpos.le, div_eq_mul_inv]
      have hsplit : qsN a.1 ^ (-(A : ℝ)) =
          qsN a.1 ^ (-(1 + ε)) * qsN a.1 ^ (-q) := by
        have he : -(A : ℝ) = -(1 + ε) + -q := by dsimp [q]; ring
        rw [he, Real.rpow_add hnpos]
      have hNκ : κ ≤ qsN a.1 := hNgt.le
      have hsmall : qsN a.1 ^ (-q) ≤ κ ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hκ)
          hNκ (neg_nonpos.mpr hq.le)
      have hnormNat : Ideal.absNorm a.1 ≠ 0 := by
        intro hz
        exact a.2 (Ideal.absNorm_eq_zero_iff.mp hz)
      have hbaseEq : base a = qsN a.1 ^ (-(1 + ε)) := by
        dsimp [base, ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
        simp [qsN, hnormNat]
      simp [f, hc]
      have hW := hdec (qsN a.1 / Y) hratio
      calc
        ‖χ.idealValue a.1‖ * ‖h (qsN a.1 / Y)‖ ≤
            1 * (CA * (qsN a.1 / Y) ^ (-(A : ℝ))) :=
          mul_le_mul (hχ a.1) hW (norm_nonneg _) (by positivity)
        _ = CA * Y ^ (A : ℝ) *
              (qsN a.1 ^ (-(1 + ε)) * qsN a.1 ^ (-q)) := by
          rw [hscale, hsplit]
          ring
        _ ≤ factor * base a := by
          rw [hbaseEq]
          have hcoef : 0 ≤ CA * Y ^ (A : ℝ) * qsN a.1 ^ (-(1 + ε)) := by positivity
          calc
            CA * Y ^ (A : ℝ) *
                (qsN a.1 ^ (-(1 + ε)) * qsN a.1 ^ (-q))
              = (CA * Y ^ (A : ℝ) * qsN a.1 ^ (-(1 + ε))) * qsN a.1 ^ (-q) := by ring
            _ ≤ (CA * Y ^ (A : ℝ) * qsN a.1 ^ (-(1 + ε))) * κ ^ (-q) :=
              mul_le_mul_of_nonneg_left hsmall hcoef
            _ = factor * qsN a.1 ^ (-(1 + ε)) := by
              dsimp [factor]
              rw [show 1 + ε - (A : ℝ) = -q by dsimp [q]; ring]
              rw [Real.rpow_natCast]
              ac_rfl
    · simp [f, hc]
      have hbase0 : 0 ≤ base a := by
        dsimp [base, ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
        split_ifs <;> positivity
      exact mul_nonneg hfactor hbase0
  have hmajor : Summable (fun a => factor * base a) := hbase.mul_left factor
  have hnormf : Summable (fun a => ‖f a‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have hsum : Summable f := Summable.of_norm hnormf
  have hbaseSum : (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, base a) ≤ S := by
    calc
      _ = ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
            ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + ε) a.1 := by rfl
      _ ≤ S := by
        dsimp [S]
        exact hbase₀.tsum_subtype_le _ {I : Ideal (𝓞 K) | I ≠ ⊥} (fun I => by
          dsimp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
          split_ifs <;> positivity)
  have hsumBound : (∑' a, ‖f a‖) ≤ factor * S := by
    calc
      _ ≤ ∑' a, factor * base a := hnormf.tsum_le_tsum hpoint hmajor
      _ = factor * ∑' a, base a := hbase.tsum_mul_left factor
      _ ≤ factor * S := mul_le_mul_of_nonneg_left hbaseSum hfactor
  have hEq : qsHigh h Y κ ⊤ χ = ∑' a, f a := by
    unfold qsHigh f
    apply tsum_congr
    intro a
    have htop : IsCoprime a.1 ⊤ := by
      rw [Ideal.isCoprime_iff_sup_eq]
      simp
    simp [htop]
  rw [hEq]
  calc
    ‖∑' a, f a‖ ≤ ∑' a, ‖f a‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ factor * S := hsumBound
    _ ≤ (1 + S) * factor := by
      calc
        factor * S = S * factor := by ring
        _ ≤ (1 + S) * factor := mul_le_mul_of_nonneg_right (by linarith) hfactor
    _ = qsHigh_tail_constant_C3d (K := K) ε * CA * κ ^ (1 + ε) * (Y / κ) ^ A := by
      dsimp [qsHigh_tail_constant_C3d, S, factor]
      rw [← Real.rpow_natCast Y A, ← Real.rpow_natCast (Y / κ) A,
        Real.div_rpow (by positivity) (by positivity) (A : ℝ),
        Real.rpow_sub (lt_of_lt_of_le zero_lt_one hκ) (1 + ε) (A : ℝ)]
      ring

private theorem qs_norm_finset_sum_bound_C3d {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → E) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x ∈ s, ‖f x‖ ≤ B) :
    ‖∑ x ∈ s, f x‖ ≤ (s.card : ℝ) * B := by
  calc
    ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ s, B := by
      apply Finset.sum_le_sum
      intro x hx
      exact hf x hx
    _ = (s.card : ℝ) * B := by simp [nsmul_eq_mul]

private theorem qs_high_ratio_pow_bound_C3d (A : ℕ) (θ X κ Y : ℝ)
    (hX : 1 ≤ X) (hXpos : 0 < X) (hκpos : 0 < κ) (hκX : κ ≤ X) (hY : 0 ≤ Y)
    (hRatio : Y / κ ≤ 4 / X ^ θ) (hθA : 8 ≤ θ * (A : ℝ)) :
    κ ^ 2 * (Y / κ) ^ A ≤ 4 ^ A * X ^ (-(6 : ℝ)) := by
  have hκsq : κ ^ 2 ≤ X ^ 2 := by
    have hprod : 0 ≤ (X - κ) * (X + κ) :=
      mul_nonneg (sub_nonneg.mpr hκX) (by linarith)
    nlinarith [hprod]
  have hratioPow : (Y / κ) ^ A ≤ (4 / X ^ θ) ^ A :=
    pow_le_pow_left₀ (div_nonneg hY (le_of_lt hκpos)) hRatio A
  have hpow : (4 / X ^ θ) ^ A = 4 ^ A * X ^ (-(θ * (A : ℝ))) := by
    calc
      (4 / X ^ θ) ^ A = (4 : ℝ) ^ (A : ℝ) / (X ^ θ) ^ (A : ℝ) := by
        rw [← Real.rpow_natCast (4 / X ^ θ) A,
          Real.div_rpow (by norm_num) (by positivity) (A : ℝ)]
      _ = 4 ^ A / X ^ (θ * (A : ℝ)) := by
        rw [← Real.rpow_natCast 4 A, ← Real.rpow_mul hXpos.le]
      _ = 4 ^ A * X ^ (-(θ * (A : ℝ))) := by
        rw [Real.rpow_neg hXpos.le]
        ring
  have hXtail : X ^ 2 * X ^ (-(θ * (A : ℝ))) ≤ X ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_natCast X 2, ← Real.rpow_add hXpos]
    apply Real.rpow_le_rpow_of_exponent_le hX
    calc
      (2 : ℝ) + (-(θ * (A : ℝ))) = (-(θ * (A : ℝ))) + 2 := by ring
      _ ≤ (-8) + 2 := by
        have h := add_le_add_right (neg_le_neg hθA) 2
        simpa [add_comm] using h
      _ = -6 := by norm_num
  calc
    κ ^ 2 * (Y / κ) ^ A ≤ X ^ 2 * (Y / κ) ^ A :=
      mul_le_mul_of_nonneg_right hκsq (by positivity)
    _ ≤ X ^ 2 * (4 / X ^ θ) ^ A :=
      mul_le_mul_of_nonneg_left hratioPow (by positivity)
    _ = 4 ^ A * (X ^ 2 * X ^ (-(θ * (A : ℝ)))) := by rw [hpow]; ring
    _ ≤ 4 ^ A * X ^ (-(6 : ℝ)) :=
      mul_le_mul_of_nonneg_left hXtail (by positivity)

set_option maxHeartbeats 50000000 in
/-- C3d (IMPL): rapid tails (both inner tails and the dual high-core kernel), under the margin
`N𝔮 n² (Mn)^θ ≤ κ M`. -/
theorem qs_tails_C3d [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (θ : ℝ) (hθ : 0 < θ) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        qsN 𝔮 * n ^ 2 * (M * n) ^ θ ≤ κ * M →
        ‖qsPairSum cols z (fun c d =>
            qsDualKernel (qsInnerTail K) F W M κ ((M * n) ^ η) n 𝔮 c d -
              qsOrigKernel (qsInnerTail K) F W M κ ((M * n) ^ η) 𝔮 c d +
              qsDualHighKernel F W M κ 𝔮 c d)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ (-1 : ℝ) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let R : ℝ := 9 / η + 9 / θ + 10
  obtain ⟨A, hRA⟩ := exists_nat_gt R
  have hRA' : R < (A : ℝ) := by exact_mod_cast hRA
  have hRη : 8 / η + 1 < R := by
    dsimp [R]
    have hηi : 0 < 1 / η := one_div_pos.mpr hη
    have hθi : 0 < 1 / θ := one_div_pos.mpr hθ
    have hpos9θ : 0 < 9 / θ := div_pos (by norm_num) hθ
    have heq : 9 / η = 8 / η + 1 / η := by ring
    rw [heq]
    linarith
  have hRθ : 8 / θ < R := by
    dsimp [R]
    have hηi : 0 < 1 / η := one_div_pos.mpr hη
    have hθi : 0 < 1 / θ := one_div_pos.mpr hθ
    have hpos9η : 0 < 9 / η := div_pos (by norm_num) hη
    have heq : 9 / θ = 8 / θ + 1 / θ := by ring
    rw [heq]
    linarith
  have hηA₀ : 8 / η + 1 < (A : ℝ) := lt_trans hRη hRA'
  have hθA₀ : 8 / θ < (A : ℝ) := lt_trans hRθ hRA'
  have hηmul := mul_lt_mul_of_pos_left hηA₀ hη
  have hθmul := mul_lt_mul_of_pos_left hθA₀ hθ
  have hηcancel : η * (8 / η) = 8 := by
    calc
      η * (8 / η) = (η / η) * 8 := by ring
      _ = 8 := by rw [div_self (ne_of_gt hη), one_mul]
  have hθcancel : θ * (8 / θ) = 8 := by
    calc
      θ * (8 / θ) = (θ / θ) * 8 := by ring
      _ = 8 := by rw [div_self (ne_of_gt hθ), one_mul]
  have hηL : 8 ≤ η * ((A : ℝ) - 1) := by nlinarith [hηmul, hηcancel]
  have hθA : 8 ≤ θ * (A : ℝ) := by nlinarith [hθmul, hθcancel]
  have hA2 : 2 ≤ A := by
    have hRbig : 10 ≤ R := by
      dsimp [R]
      have hηi : 0 < 9 / η := div_pos (by norm_num) hη
      have hθi : 0 < 9 / θ := div_pos (by norm_num) hθ
      linarith
    have : (2 : ℝ) ≤ (A : ℝ) := by linarith [hRA', hRbig]
    exact_mod_cast this
  have hAε : 1 + 1 ≤ (A : ℝ) := by exact_mod_cast hA2
  let H : ℝ → ℂ := fun y => (W (y ^ 2) : ℂ)
  let G : ℝ → ℂ := fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)
  have hHQS : IsQSWeight H := capSquare_isQSWeight_C3d W hW
  obtain ⟨CdirO, hCdirO, hdirO⟩ := capSquare_decay_C3d W hW A
  obtain ⟨CdualO, hCdualO, hdualO⟩ :=
    qs_transform_decay_C3d (K := K) H hHQS A (1 / 8) (by norm_num)
  obtain ⟨Ctw, hCtw, htwdec⟩ :=
    qs_transform_decay_C3d (K := K) (fun x => (W x : ℂ)) hW.1 A (1 / 8) (by norm_num)
  obtain ⟨CdualD, hCdualD, hdualD⟩ :=
    caseB_doubleTransform_decay_C3d (K := K) (fun x => (W x : ℂ)) hW.1 A
  have hdirD : ∀ y : ℝ, 1 ≤ y → ‖G y‖ ≤ Ctw * y ^ (-(A : ℝ)) := by
    intro y hy
    have hy2 : 1 ≤ y ^ 2 := one_le_pow₀ hy
    have h := htwdec (y ^ 2) hy2
    have hpow : (y ^ 2) ^ (-(A : ℝ)) ≤ y ^ (-(A : ℝ)) := by
      apply Real.rpow_le_rpow_of_nonpos (by linarith : 0 < y)
      · nlinarith [sq_nonneg (y - 1)]
      · exact neg_nonpos.mpr (Nat.cast_nonneg A)
    calc
      ‖G y‖ ≤ Ctw * (y ^ 2) ^ (-(A : ℝ)) := by simpa [G] using h
      _ ≤ Ctw * y ^ (-(A : ℝ)) := mul_le_mul_of_nonneg_left hpow (le_of_lt hCtw)
  obtain ⟨CtailO, hCtailO, hinnerO⟩ :=
    qs_innerTail_bound_C3d (K := K) H CdualO CdirO A 1
      hCdualO hCdirO (by norm_num) hAε hA2 hdualO hdirO
  obtain ⟨CtailD, hCtailD, hinnerD⟩ :=
    qs_innerTail_bound_C3d (K := K) G CdualD Ctw A 1
      hCdualD hCtw (by norm_num) hAε hA2 hdualD hdirD
  obtain ⟨Ctrans, hCtrans, htransDec⟩ :=
    qs_transform_decay_quarter_C3d (K := K) (fun x => (W x : ℂ)) hW.1 A
  obtain ⟨CI, hCI, hcount⟩ := qs_ideal_count_M1 (K := K) 1 (by norm_num)
  obtain ⟨Cdiv, hCdiv, hdiv⟩ := qs_divisor_bound_M1 (K := K) 1 (by norm_num)
  have hnormTsum : 0 ≤ ∑' I : Ideal (𝓞 K),
      ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + 1) I := by
    apply tsum_nonneg
    intro I
    dsimp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
    split_ifs <;> positivity
  have hChigh : 0 < qsHigh_tail_constant_C3d (K := K) 1 := by
    dsimp [qsHigh_tail_constant_C3d]
    linarith
  let CO : ℝ := 4 * CI * Cdiv * CtailO
  let CD : ℝ := 4 * CI * Cdiv ^ 2 * CtailD
  let CH : ℝ := Cdiv * qsHigh_tail_constant_C3d (K := K) 1 * Ctrans * 4 ^ A
  let Cker : ℝ := CO + CD + CH + 1
  let Ccols : ℝ := CI * (2 : ℝ) ^ (2 : ℝ)
  let C : ℝ := Cker * Ccols
  have hCker : 0 < Cker := by dsimp [Cker, CO, CD, CH]; positivity
  have hCcols : 0 < Ccols := by dsimp [Ccols]; positivity
  refine ⟨C, by dsimp [C]; exact mul_pos hCker hCcols, ?_⟩
  intro M n κ 𝔮 cols z hn hκ hM hcols hmargin
  let X : ℝ := M * n
  let Λ : ℝ := X ^ η
  have hMpos : 0 < M := by nlinarith
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκleM : κ ≤ M := by nlinarith
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hX : 1 ≤ X := by dsimp [X]; nlinarith
  have hnX : n ≤ X := by dsimp [X]; nlinarith
  have hMleX : M ≤ X := by
    dsimp [X]
    calc
      M = M * 1 := by ring
      _ ≤ M * n := mul_le_mul_of_nonneg_left hn (le_of_lt hMpos)
  have hκX : κ ≤ X := le_trans hκleM hMleX
  have hΛ : 1 ≤ Λ := by
    dsimp [Λ]
    exact Real.one_le_rpow hX hη.le
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hq0 : 𝔮 ≠ ⊥ := by
    intro hqbot
    have hqzero : 𝔮 = 0 := by simpa using hqbot
    exact (Squarefree.ne_zero hcols.1) hqzero
  have hqN : 1 ≤ qsN 𝔮 := QSC3.one_le_qsN hq0
  have hqNpos : 0 < qsN 𝔮 := lt_of_lt_of_le zero_lt_one hqN
  have hdivBound (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
      ((qsDivisors I).card : ℝ) ≤ Cdiv * qsN I := by
    have h := hdiv I hI
    simpa [qsN, Real.rpow_one] using h
  have hsfCount : ((qsSqfUpTo κ 𝔮).card : ℝ) ≤ CI * κ ^ (2 : ℝ) := by
    have h := qs_sqfUpTo_card_bound_C3d (K := K) CI 1 hcount (by norm_num) κ hκ 𝔮
    have hexp : (1 + 1 : ℝ) = 2 := by norm_num
    rw [hexp] at h
    exact h
  have hsfCountTop : ((qsSqfUpTo κ (⊤ : Ideal (𝓞 K))).card : ℝ) ≤ CI * κ ^ (2 : ℝ) := by
    have h := qs_sqfUpTo_card_bound_C3d (K := K) CI 1 hcount (by norm_num) κ hκ
      (⊤ : Ideal (𝓞 K))
    have hexp : (1 + 1 : ℝ) = 2 := by norm_num
    rw [hexp] at h
    exact h
  have hcolsCount : (cols.card : ℝ) ≤ Ccols * n ^ (2 : ℝ) := by
    have h := qs_block_cols_card_bound_C3d (K := K) CI 1 hcount (by norm_num)
      n hn 𝔮 cols hcols
    have hexp : (1 + 1 : ℝ) = 2 := by norm_num
    rw [hexp] at h
    simpa [Ccols] using h
  have hcolumn (c : Ideal (𝓞 K)) (hc : c ∈ cols) :
      QSAdm m qS c ∧ IsCoprime c 𝔮 ∧ n < qsN c ∧ qsN c ≤ 2 * n :=
    hcols.2.2.1 c hc
  have hcdNorm (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols) :
      n ^ (2 : ℝ) ≤ qsN (c * d) ∧ qsN (c * d) ≤ 4 * n ^ (2 : ℝ) := by
    have hcNlow := (hcolumn c hc).2.2.1
    have hdNlow := (hcolumn d hd).2.2.1
    have hcNhigh := (hcolumn c hc).2.2.2
    have hdNhigh := (hcolumn d hd).2.2.2
    have hmul : qsN (c * d) = qsN c * qsN d := by simp [qsN, map_mul]
    have hnPow : n ^ (2 : ℝ) = n ^ 2 := Real.rpow_natCast n 2
    constructor
    · rw [hnPow, hmul]
      have h := mul_le_mul_of_nonneg hcNlow.le hdNlow.le (by linarith) (by linarith)
      nlinarith
    · rw [hmul, hnPow]
      have h := mul_le_mul_of_nonneg hcNhigh hdNhigh (by positivity) (by positivity)
      nlinarith
  have hcdNormNat (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols) :
      n ^ 2 ≤ qsN (c * d) ∧ qsN (c * d) ≤ 4 * n ^ 2 := by
    have hnPow : n ^ (2 : ℝ) = n ^ 2 := Real.rpow_natCast n 2
    constructor
    · calc
        n ^ 2 = n ^ (2 : ℝ) := hnPow.symm
        _ ≤ qsN (c * d) := (hcdNorm c d hc hd).1
    · calc
        qsN (c * d) ≤ 4 * n ^ (2 : ℝ) := (hcdNorm c d hc hd).2
        _ = 4 * n ^ 2 := by rw [hnPow]
  have hpowκ2 : κ ^ (2 : ℝ) ≤ X ^ (2 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt hκpos) hκX (by norm_num)
  have hpowN2 : n ^ (2 : ℝ) ≤ X ^ (2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hnX (by norm_num)
  have hpowProd : κ ^ (2 : ℝ) * n ^ (2 : ℝ) ≤ X ^ (4 : ℝ) := by
    calc
      κ ^ (2 : ℝ) * n ^ (2 : ℝ) ≤ X ^ (2 : ℝ) * X ^ (2 : ℝ) :=
        mul_le_mul hpowκ2 hpowN2 (by positivity) (by positivity)
      _ = X ^ (4 : ℝ) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        norm_num
  have hX4m8 : X ^ (4 : ℝ) * X ^ (-(8 : ℝ)) = X ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hX5m8 : X ^ (5 : ℝ) * X ^ (-(8 : ℝ)) = X ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hΛdec : Λ ^ (-((A : ℝ) - 1)) ≤ X ^ (-(8 : ℝ)) := by
    have hpowEq : Λ ^ (-((A : ℝ) - 1)) =
        X ^ (-(η * ((A : ℝ) - 1))) := by
      dsimp [Λ]
      rw [← Real.rpow_mul hXpos.le]
      congr 1
      ring
    rw [hpowEq]
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith [hηL])
  have hNqcdBound (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols)
      (hc0 : c ≠ ⊥) (hd0 : d ≠ ⊥) :
      ((qsDivisors (𝔮 * (c * d))).card : ℝ) ≤ Cdiv * qsN 𝔮 * 4 * n ^ (2 : ℝ) := by
    have hqcd0 : 𝔮 * (c * d) ≠ ⊥ := mul_ne_zero hq0 (mul_ne_zero hc0 hd0)
    have hNormMul : qsN (𝔮 * (c * d)) = qsN 𝔮 * qsN (c * d) := by
      simp [qsN, map_mul]
    calc
      ((qsDivisors (𝔮 * (c * d))).card : ℝ) ≤ Cdiv * qsN (𝔮 * (c * d)) :=
        hdivBound _ hqcd0
      _ = Cdiv * (qsN 𝔮 * qsN (c * d)) := by rw [hNormMul]
      _ ≤ Cdiv * (qsN 𝔮 * (4 * n ^ (2 : ℝ))) := by
        gcongr
        exact (hcdNorm c d hc hd).2
      _ = Cdiv * qsN 𝔮 * 4 * n ^ (2 : ℝ) := by ring
  have hDivCD (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols)
      (hc0 : c ≠ ⊥) (hd0 : d ≠ ⊥) :
      ((qsDivisors (c * d)).card : ℝ) ≤ Cdiv * 4 * n ^ (2 : ℝ) := by
    calc
      ((qsDivisors (c * d)).card : ℝ) ≤ Cdiv * qsN (c * d) := hdivBound _ (mul_ne_zero hc0 hd0)
      _ ≤ Cdiv * (4 * n ^ (2 : ℝ)) := by gcongr; exact (hcdNorm c d hc hd).2
      _ = Cdiv * 4 * n ^ (2 : ℝ) := by ring
  have hDivQ : ((qsDivisors 𝔮).card : ℝ) ≤ Cdiv * qsN 𝔮 := hdivBound 𝔮 hq0
  have hcolNormPos (c : Ideal (𝓞 K)) (hc : c ∈ cols) : c ≠ ⊥ := by
    intro hc0
    have hcn := (hcolumn c hc).2.2.1
    have hnorm0 : qsN c = 0 := by simp [qsN, hc0]
    rw [hnorm0] at hcn
    linarith [hn]
  have hmulNorm (c d : Ideal (𝓞 K)) : qsN (c * d) = qsN c * qsN d := by
    simp [qsN, map_mul]
  have hcharNorm (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols)
      (I : Ideal (𝓞 K)) :
      ‖(qsPairChar F c d).idealValue I‖ ≤ 1 := by
    apply qs_idealValue_norm_le_one_C3d
    exact qs_pairChar_sq_C3d F (hcolumn c hc).1 (hcolumn d hd).1
  have hneDiv (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
      {e : Ideal (𝓞 K)} (he : e ∈ qsDivisors I) : e ≠ ⊥ := by
    intro hebot
    have hediv : e ∣ I := by
      unfold qsDivisors at he
      exact (Finset.mem_filter.mp he).2
    have hbotdiv : (⊥ : Ideal (𝓞 K)) ∣ I := by simpa [hebot] using hediv
    exact hI (le_bot_iff.mp (Ideal.dvd_iff_le.mp hbotdiv))
  have heNormLe (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) : qsN e ≤ qsN 𝔮 := by
    have hediv : e ∣ 𝔮 := by
      unfold qsDivisors at he
      exact (Finset.mem_filter.mp he).2
    have hnormQ : 0 < Ideal.absNorm 𝔮 := by
      apply Nat.pos_iff_ne_zero.mpr
      intro hz
      exact hq0 (Ideal.absNorm_eq_zero_iff.mp hz)
    have hdvd : Ideal.absNorm e ∣ Ideal.absNorm 𝔮 := map_dvd Ideal.absNorm hediv
    have hle : Ideal.absNorm e ≤ Ideal.absNorm 𝔮 := Nat.le_of_dvd hnormQ hdvd
    exact_mod_cast hle
  have hOrigPairBound (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols) :
      ‖qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d‖ ≤
        CO * qsN 𝔮 * X ^ (-(3 : ℝ)) := by
    have hc0 := hcolNormPos c hc
    have hd0 := hcolNormPos d hd
    have hqcd0 : 𝔮 * (c * d) ≠ ⊥ := mul_ne_zero hq0 (mul_ne_zero hc0 hd0)
    let χ := qsPairChar F c d
    let B : ℝ := CtailO * ((qsDivisors (𝔮 * (c * d))).card : ℝ) *
      Λ ^ (-((A : ℝ) - 1))
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hterm (a : Ideal (𝓞 K)) (ha : a ∈ qsSqfUpTo κ 𝔮) :
        ‖χ.idealValue a * qsInnerTail K H (Real.sqrt (M / qsN a))
          (𝔮 * (c * d)) (Real.sqrt (M / qsN a) / Λ)
          (Λ * Real.sqrt (M / qsN a))‖ ≤ B := by
      have ha0 : a ≠ ⊥ := by
        unfold qsSqfUpTo at ha
        simp only [Finset.mem_filter] at ha
        exact ha.2.1
      have hNa : 1 ≤ qsN a := QSC3.one_le_qsN ha0
      have hZ : 0 < Real.sqrt (M / qsN a) := by
        apply Real.sqrt_pos.2
        exact div_pos hMpos (lt_of_lt_of_le zero_lt_one hNa)
      have htail := hinnerO Λ hΛ (Real.sqrt (M / qsN a)) (𝔮 * (c * d))
        (Real.sqrt (M / qsN a) / Λ) (Λ * Real.sqrt (M / qsN a))
        hqcd0 hZ le_rfl le_rfl
      calc
        _ = ‖χ.idealValue a‖ *
            ‖qsInnerTail K H (Real.sqrt (M / qsN a)) (𝔮 * (c * d))
              (Real.sqrt (M / qsN a) / Λ) (Λ * Real.sqrt (M / qsN a))‖ := norm_mul _ _
        _ ≤ 1 * (CtailO * (qsDivisors (𝔮 * (c * d))).card *
              Λ ^ (-((A : ℝ) - 1)) ) :=
          mul_le_mul (hcharNorm c d hc hd a) htail (norm_nonneg _) (by positivity)
        _ = B := by dsimp [B, χ]; ring
    have hOrigRaw :
        ‖qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d‖ ≤
          (qsSqfUpTo κ 𝔮).card * B := by
      unfold qsOrigKernel
      exact qs_norm_finset_sum_bound_C3d (qsSqfUpTo κ 𝔮)
        (fun a => (qsPairChar F c d).idealValue a *
          qsInnerTail K H (Real.sqrt (M / qsN a)) (𝔮 * (c * d))
            (Real.sqrt (M / qsN a) / Λ) (Λ * Real.sqrt (M / qsN a)))
        B hB (by simpa [χ] using hterm)
    have hBbound : B ≤ CtailO * Cdiv * qsN 𝔮 * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ)) := by
      have hcard := hNqcdBound c d hc hd hc0 hd0
      have hcard' : CtailO * ((qsDivisors (𝔮 * (c * d))).card : ℝ) ≤
          CtailO * (Cdiv * qsN 𝔮 * 4 * n ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcard (le_of_lt hCtailO)
      calc
        B = (CtailO * ((qsDivisors (𝔮 * (c * d))).card : ℝ)) *
              Λ ^ (-((A : ℝ) - 1)) := by dsimp [B]
        _ ≤ (CtailO * (Cdiv * qsN 𝔮 * 4 * n ^ (2 : ℝ))) *
              Λ ^ (-((A : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right hcard' (Real.rpow_nonneg (le_of_lt hΛpos) _)
        _ ≤ CtailO * (Cdiv * qsN 𝔮 * 4 * n ^ (2 : ℝ)) * X ^ (-(8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hΛdec (by positivity)
        _ = CtailO * Cdiv * qsN 𝔮 * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ)) := by ring
    calc
      _ ≤ (qsSqfUpTo κ 𝔮).card * B := hOrigRaw
      _ ≤ (CI * κ ^ (2 : ℝ)) *
            (CtailO * Cdiv * qsN 𝔮 * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ)) ) :=
        mul_le_mul hsfCount hBbound (by positivity) (by positivity)
      _ = CO * qsN 𝔮 * (κ ^ (2 : ℝ) * n ^ (2 : ℝ)) * X ^ (-(8 : ℝ)) := by
        dsimp [CO]
        ring
      _ ≤ CO * qsN 𝔮 * X ^ (4 : ℝ) * X ^ (-(8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowProd (by positivity)) (Real.rpow_nonneg (le_of_lt hXpos) _)
      _ = CO * qsN 𝔮 * (X ^ (4 : ℝ) * X ^ (-(8 : ℝ))) := by ring
      _ = CO * qsN 𝔮 * X ^ (-(4 : ℝ)) := by rw [hX4m8]
      _ ≤ CO * qsN 𝔮 * X ^ (-(3 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX (by norm_num)) (by positivity)
  have hDualPairBound (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols) :
      ‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d‖ ≤
        CD * qsN 𝔮 * X ^ (-(3 : ℝ)) := by
    have hc0 := hcolNormPos c hc
    have hd0 := hcolNormPos d hd
    have hcd0 : c * d ≠ ⊥ := mul_ne_zero hc0 hd0
    have hNcdpos : 0 < qsN (c * d) := by
      have hn2 : 0 < n ^ 2 := pow_pos (lt_of_lt_of_le zero_lt_one hn) 2
      have hNlow := (hcdNormNat c d hc hd).1
      exact lt_of_lt_of_le hn2 hNlow
    let χ := qsPairChar F c d
    let S : Finset (Ideal (𝓞 K)) := qsSqfUpTo κ (⊤ : Ideal (𝓞 K))
    let Bcore : ℝ := CtailD * ((qsDivisors (c * d)).card : ℝ) *
      Λ ^ (-((A : ℝ) - 1))
    have hBcore : 0 ≤ Bcore := by dsimp [Bcore]; positivity
    have hcoreBound (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) :
        ‖∑ a ∈ S, χ.idealValue a *
          qsInnerTail K G
            (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
            (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
            (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))‖ ≤
          (S.card : ℝ) * Bcore := by
      have he0 := hneDiv 𝔮 hq0 he
      have hNe : 1 ≤ qsN e := QSC3.one_le_qsN he0
      have hNePos : 0 < qsN e := lt_of_lt_of_le zero_lt_one hNe
      have hterm (a : Ideal (𝓞 K)) (ha : a ∈ S) :
          ‖χ.idealValue a *
            qsInnerTail K G
              (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
              (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
              (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))‖ ≤ Bcore := by
        have ha0 : a ≠ ⊥ := by
          change a ∈ qsSqfUpTo κ (⊤ : Ideal (𝓞 K)) at ha
          unfold qsSqfUpTo at ha
          exact (Finset.mem_filter.mp ha).2.1
        have hNa : 1 ≤ qsN a := QSC3.one_le_qsN ha0
        have hNaPos : 0 < qsN a := lt_of_lt_of_le zero_lt_one hNa
        have hden : 0 < M * qsN a := mul_pos hMpos hNaPos
        let Z : ℝ := Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))
        let Zc : ℝ := Real.sqrt (qsN e * n ^ 2 / (M * qsN a))
        have hargLow : qsN e * n ^ 2 / (M * qsN a) ≤
            qsN e * qsN (c * d) / (M * qsN a) := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left (hcdNormNat c d hc hd).1 (by positivity)
          · exact hden.le
        have hZcZ : Zc ≤ Z := by
          dsimp [Z, Zc]
          exact Real.sqrt_le_sqrt hargLow
        have hnumHi : qsN e * qsN (c * d) ≤ qsN e * (4 * n ^ 2) := by
          exact mul_le_mul_of_nonneg_left (hcdNormNat c d hc hd).2 (by positivity)
        have hargHi : qsN e * qsN (c * d) / (M * qsN a) ≤
            4 * (qsN e * n ^ 2 / (M * qsN a)) := by
          calc
            qsN e * qsN (c * d) / (M * qsN a) ≤
                (qsN e * (4 * n ^ 2)) / (M * qsN a) :=
              div_le_div_of_nonneg_right hnumHi hden.le
            _ = 4 * (qsN e * n ^ 2 / (M * qsN a)) := by ring
        have hZupper : Z ≤ 2 * Zc := by
          dsimp [Z, Zc]
          calc
            Real.sqrt (qsN e * qsN (c * d) / (M * qsN a)) ≤
                Real.sqrt (4 * (qsN e * n ^ 2 / (M * qsN a))) :=
              Real.sqrt_le_sqrt hargHi
            _ = 2 * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
              norm_num
        have hZpos : 0 < Z := by
          dsimp [Z]
          apply Real.sqrt_pos.2
          exact div_pos (mul_pos hNePos hNcdpos) hden
        have hYlo : Zc / (2 * Λ) ≤ Z / Λ := by
          calc
            Zc / (2 * Λ) ≤ Z / (2 * Λ) :=
              div_le_div_of_nonneg_right hZcZ (by positivity)
            _ ≤ Z / Λ := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [mul_pos hZpos hΛpos]
        have hZhi : Λ * Z ≤ 2 * Λ * Zc := by
          calc
            Λ * Z ≤ Λ * (2 * Zc) := mul_le_mul_of_nonneg_left hZupper (le_of_lt hΛpos)
            _ = 2 * Λ * Zc := by ring
        have htail := hinnerD Λ hΛ Z (c * d) (Zc / (2 * Λ)) (2 * Λ * Zc)
          hcd0 hZpos hYlo hZhi
        calc
          _ = ‖χ.idealValue a‖ *
              ‖qsInnerTail K G Z (c * d) (Zc / (2 * Λ)) (2 * Λ * Zc)‖ := norm_mul _ _
          _ ≤ 1 * (CtailD * (qsDivisors (c * d)).card *
                Λ ^ (-((A : ℝ) - 1)) ) :=
            mul_le_mul (hcharNorm c d hc hd a) htail (norm_nonneg _) (by positivity)
          _ = Bcore := by dsimp [Bcore]; ring
      exact qs_norm_finset_sum_bound_C3d S
        (fun a => χ.idealValue a *
          qsInnerTail K G
            (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
            (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
            (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a))))
        Bcore hBcore hterm
    let Bdual : ℝ := X * (S.card : ℝ) * Bcore
    have hBdual : 0 ≤ Bdual := by dsimp [Bdual]; positivity
    have hNeGlobal (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) :
        1 ≤ qsN e := QSC3.one_le_qsN (hneDiv 𝔮 hq0 he)
    have hNsqrt : n ≤ Real.sqrt (qsN (c * d)) := by
      have hn2 : n ^ 2 ≤ qsN (c * d) := (hcdNormNat c d hc hd).1
      exact Real.le_sqrt_of_sq_le hn2
    have hdenom (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) :
        n ≤ qsN e * Real.sqrt (qsN (c * d)) := by
      have hNe := hNeGlobal e he
      calc
        n ≤ Real.sqrt (qsN (c * d)) := hNsqrt
        _ ≤ qsN e * Real.sqrt (qsN (c * d)) := by
          nlinarith [mul_le_mul_of_nonneg_right hNe (Real.sqrt_nonneg (qsN (c * d)))]
    have hdenomPos (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) :
        0 < qsN e * Real.sqrt (qsN (c * d)) :=
      mul_pos (lt_of_lt_of_le zero_lt_one (hNeGlobal e he)) (Real.sqrt_pos.2 hNcdpos)
    have hpref (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) :
        M / (qsN e * Real.sqrt (qsN (c * d))) ≤ X := by
      have hdenomPos := hdenomPos e he
      have hpref₁ : M / (qsN e * Real.sqrt (qsN (c * d))) ≤ M / n := by
        rw [div_le_div_iff₀ hdenomPos (lt_of_lt_of_le zero_lt_one hn)]
        exact mul_le_mul_of_nonneg_left (hdenom e he) (le_of_lt hMpos)
      have hpref₂ : M / n ≤ X := by
        calc
          M / n ≤ M := div_le_self (le_of_lt hMpos) hn
          _ ≤ X := hMleX
      exact hpref₁.trans hpref₂
    have houter (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) :
        ‖(qsMu e : ℂ) * χ.idealValue e *
          ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ) *
          (∑ a ∈ S, χ.idealValue a *
            qsInnerTail K G
              (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
              (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
              (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a))))‖ ≤ Bdual := by
      have hmu := QSC2.norm_qsMu_le e
      have hchar := hcharNorm c d hc hd e
      have hcore := hcoreBound e he
      have hscalarpos : 0 < M / (qsN e * Real.sqrt (qsN (c * d))) :=
        div_pos hMpos (hdenomPos e he)
      have hscalar : ‖((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ)‖ =
          M / (qsN e * Real.sqrt (qsN (c * d))) := by
        rw [Complex.norm_real]
        exact abs_of_pos hscalarpos
      calc
        _ = ‖(qsMu e : ℂ)‖ * ‖χ.idealValue e‖ *
              (M / (qsN e * Real.sqrt (qsN (c * d)))) *
              ‖∑ a ∈ S, χ.idealValue a *
                qsInnerTail K G
                  (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
                  (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
              (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))‖ := by
              rw [norm_mul, norm_mul, norm_mul, hscalar]
        _ ≤ X * (S.card : ℝ) * Bcore := by
              have hstep1 : ‖(qsMu e : ℂ)‖ * ‖χ.idealValue e‖ ≤ 1 := by
                exact mul_le_one₀ hmu (norm_nonneg _) hchar
              calc
                _ ≤ 1 * (M / (qsN e * Real.sqrt (qsN (c * d)))) *
                      ‖∑ a ∈ S, χ.idealValue a *
                        qsInnerTail K G
                          (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
                          (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
                          (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hstep1 (by positivity)) (norm_nonneg _)
                _ ≤ X * (S.card : ℝ) * Bcore := by
                  calc
                    _ ≤ 1 * X * ‖∑ a ∈ S, χ.idealValue a *
                          qsInnerTail K G
                            (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
                            (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
                            (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))‖ := by
                      exact mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left (hpref e he) (by norm_num))
                        (norm_nonneg _)
                    _ ≤ X * ((S.card : ℝ) * Bcore) := by
                      calc
                        1 * X * ‖∑ a ∈ S, χ.idealValue a *
                              qsInnerTail K G
                                (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
                                (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
                                (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))‖
                          = X * ‖∑ a ∈ S, χ.idealValue a *
                              qsInnerTail K G
                                (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
                                (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
                                (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))‖ := by ring
                        _ ≤ X * ((S.card : ℝ) * Bcore) :=
                          mul_le_mul_of_nonneg_left hcore (by positivity)
                    _ = Bdual := by dsimp [Bdual]; ring
    have hDualRaw :
        ‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d‖ ≤
          (qsDivisors 𝔮).card * Bdual := by
      unfold qsDualKernel
      exact qs_norm_finset_sum_bound_C3d (qsDivisors 𝔮)
        (fun e => (qsMu e : ℂ) * χ.idealValue e *
          ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ) *
          (∑ a ∈ S, χ.idealValue a *
            qsInnerTail K G
              (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
              (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
              (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))))
        Bdual hBdual houter
    have hBcoreBound : Bcore ≤ CtailD * Cdiv * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ)) := by
      have hcard := hDivCD c d hc hd hc0 hd0
      have hcard' : CtailD * ((qsDivisors (c * d)).card : ℝ) ≤
          CtailD * (Cdiv * 4 * n ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcard (le_of_lt hCtailD)
      calc
        Bcore = (CtailD * ((qsDivisors (c * d)).card : ℝ)) *
              Λ ^ (-((A : ℝ) - 1)) := by dsimp [Bcore]
        _ ≤ (CtailD * (Cdiv * 4 * n ^ (2 : ℝ))) *
              Λ ^ (-((A : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right hcard' (Real.rpow_nonneg (le_of_lt hΛpos) _)
        _ ≤ CtailD * (Cdiv * 4 * n ^ (2 : ℝ)) * X ^ (-(8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hΛdec (by positivity)
        _ = CtailD * Cdiv * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ)) := by ring
    have hDualMain :
        ‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d‖ ≤
          CD * qsN 𝔮 * X ^ (-(3 : ℝ)) := by
      calc
        _ ≤ (qsDivisors 𝔮).card * Bdual := hDualRaw
        _ ≤ (Cdiv * qsN 𝔮) * (X * (S.card : ℝ) * Bcore) := by
          dsimp [Bdual]
          exact mul_le_mul_of_nonneg_right hDivQ hBdual
        _ ≤ (Cdiv * qsN 𝔮) * (X * (CI * κ ^ (2 : ℝ)) *
              (CtailD * Cdiv * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ)))) := by
          have hcoreprod : (S.card : ℝ) * Bcore ≤
              (CI * κ ^ (2 : ℝ)) *
                (CtailD * Cdiv * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ))) :=
            mul_le_mul hsfCountTop hBcoreBound
              (by positivity) (by positivity)
          calc
            (Cdiv * qsN 𝔮) * (X * (S.card : ℝ) * Bcore) =
                (Cdiv * qsN 𝔮) * (X * ((S.card : ℝ) * Bcore)) := by ring
            _ ≤ (Cdiv * qsN 𝔮) *
                  (X * ((CI * κ ^ (2 : ℝ)) *
                    (CtailD * Cdiv * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ)))) ) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hcoreprod (by positivity)) (by positivity)
            _ = (Cdiv * qsN 𝔮) * (X * (CI * κ ^ (2 : ℝ)) *
                  (CtailD * Cdiv * 4 * n ^ (2 : ℝ) * X ^ (-(8 : ℝ)))) := by ring
        _ = CD * qsN 𝔮 * (X * (κ ^ (2 : ℝ) * n ^ (2 : ℝ)) * X ^ (-(8 : ℝ))) := by
          dsimp [CD]
          ring
        _ ≤ CD * qsN 𝔮 * (X * X ^ (4 : ℝ) * X ^ (-(8 : ℝ))) := by
          gcongr
        _ = CD * qsN 𝔮 * (X ^ (5 : ℝ) * X ^ (-(8 : ℝ))) := by
          have hXmul4 : X * X ^ (4 : ℝ) = X ^ (5 : ℝ) := by
            have h4 : X ^ (4 : ℝ) = X ^ 4 := Real.rpow_natCast X 4
            have h5 : X ^ (5 : ℝ) = X ^ 5 := Real.rpow_natCast X 5
            rw [h4, h5]
            ring
          rw [hXmul4]
        _ = CD * qsN 𝔮 * X ^ (-(3 : ℝ)) := by rw [hX5m8]
    simpa [χ] using hDualMain
  have hRge10 : 10 ≤ R := by
    dsimp [R]
    have hηp : 0 < 9 / η := div_pos (by norm_num) hη
    have hθp : 0 < 9 / θ := div_pos (by norm_num) hθ
    linarith
  have hAgt2 : (2 : ℝ) < (A : ℝ) := by linarith [hRA', hRge10]
  have hXθpos : 0 < X ^ θ := Real.rpow_pos_of_pos hXpos θ
  have hXθ : 1 ≤ X ^ θ := Real.one_le_rpow hX hθ.le
  have hmarginX : qsN 𝔮 * n ^ 2 * X ^ θ ≤ κ * M := by simpa [X] using hmargin
  have hHighPairBound (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols) :
      ‖qsDualHighKernel F W M κ 𝔮 c d‖ ≤ CH * qsN 𝔮 * X ^ (-(3 : ℝ)) := by
    have hc0 := hcolNormPos c hc
    have hd0 := hcolNormPos d hd
    have hNcdpos : 0 < qsN (c * d) := by
      have hNcd := (hcdNormNat c d hc hd).1
      have hn2 : 0 < n ^ 2 := pow_pos (lt_of_lt_of_le zero_lt_one hn) 2
      exact lt_of_lt_of_le hn2 hNcd
    let χ := qsPairChar F c d
    let Bhigh : ℝ := X * qsHigh_tail_constant_C3d (K := K) 1 * Ctrans * 4 ^ A *
      X ^ (-(6 : ℝ))
    have hBhigh : 0 ≤ Bhigh := by dsimp [Bhigh]; positivity
    have hhighTerm (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) :
        ‖(qsMu e : ℂ) * χ.idealValue e *
          ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ) *
          qsHigh (qsTransform K (fun x => (W x : ℂ)))
            (qsN e * qsN (c * d) / M) κ ⊤ χ‖ ≤ Bhigh := by
      have he0 := hneDiv 𝔮 hq0 he
      have hNe : 1 ≤ qsN e := QSC3.one_le_qsN he0
      have hNePos : 0 < qsN e := lt_of_lt_of_le zero_lt_one hNe
      let Y : ℝ := qsN e * qsN (c * d) / M
      have hYpos : 0 < Y := by
        dsimp [Y]
        exact div_pos (mul_pos hNePos hNcdpos) hMpos
      have hYnum : qsN e * qsN (c * d) ≤ qsN 𝔮 * (4 * n ^ 2) := by
        have hEe := heNormLe e he
        have hcd := (hcdNormNat c d hc hd).2
        exact mul_le_mul hEe hcd (by positivity) (by positivity)
      have hYleBase : Y ≤ (qsN 𝔮 * (4 * n ^ 2)) / M := by
        dsimp [Y]
        exact div_le_div_of_nonneg_right hYnum (le_of_lt hMpos)
      have hmargin4 : (qsN 𝔮 * (4 * n ^ 2)) * X ^ θ ≤ (4 * κ) * M := by
        calc
          (qsN 𝔮 * (4 * n ^ 2)) * X ^ θ = 4 * (qsN 𝔮 * n ^ 2 * X ^ θ) := by ring
          _ ≤ 4 * (κ * M) := mul_le_mul_of_nonneg_left hmarginX (by norm_num)
          _ = (4 * κ) * M := by ring
      have hYbound : Y ≤ (4 * κ) / (X ^ θ) := by
        calc
          Y ≤ (qsN 𝔮 * (4 * n ^ 2)) / M := hYleBase
          _ ≤ (4 * κ) / (X ^ θ) := by
            rw [div_le_div_iff₀ hMpos hXθpos]
            exact hmargin4
      have hYratio : Y / κ ≤ 4 / (X ^ θ) := by
        rw [div_le_div_iff₀ hκpos hXθpos]
        exact (le_div_iff₀ hXθpos).mp hYbound
      have hYK : Y ≤ 4 * κ := by
        calc
          Y ≤ (4 * κ) / (X ^ θ) := hYbound
          _ ≤ 4 * κ := div_le_self (by positivity) hXθ
      have hχ : ∀ I : Ideal (𝓞 K), ‖χ.idealValue I‖ ≤ 1 :=
        fun I => hcharNorm c d hc hd I
      have hAepsStrict : 1 + 1 < (A : ℝ) := by
        have heq : (1 + 1 : ℝ) = 2 := by norm_num
        rw [heq]
        exact hAgt2
      have hhigh := qsHigh_tail_bound_C3d (K := K)
        (qsTransform K (fun x => (W x : ℂ))) Ctrans A 1 (le_of_lt hCtrans)
        (by norm_num) hAepsStrict hA2 χ hχ Y κ hYpos hκ hYK htransDec
      have hhigh' :
          ‖qsHigh (qsTransform K (fun x => (W x : ℂ))) Y κ ⊤ χ‖ ≤
            qsHigh_tail_constant_C3d (K := K) 1 * Ctrans * κ ^ 2 * (Y / κ) ^ A := by
        have hhigh₂ := hhigh
        rw [show (1 + 1 : ℝ) = 2 by norm_num] at hhigh₂
        have hκpow : κ ^ (2 : ℝ) = κ ^ 2 := Real.rpow_natCast κ 2
        rw [hκpow] at hhigh₂
        exact hhigh₂
      have hratioPow := qs_high_ratio_pow_bound_C3d A θ X κ Y hX hXpos
        hκpos hκX (le_of_lt hYpos) hYratio hθA
      have hhighBound :
          ‖qsHigh (qsTransform K (fun x => (W x : ℂ))) Y κ ⊤ χ‖ ≤
            qsHigh_tail_constant_C3d (K := K) 1 * Ctrans * 4 ^ A *
              X ^ (-(6 : ℝ)) := by
        calc
          _ ≤ qsHigh_tail_constant_C3d (K := K) 1 * Ctrans *
                (κ ^ 2 * (Y / κ) ^ A) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hhigh'
          _ ≤ qsHigh_tail_constant_C3d (K := K) 1 * Ctrans *
                (4 ^ A * X ^ (-(6 : ℝ))) :=
              mul_le_mul_of_nonneg_left hratioPow (by positivity)
          _ = qsHigh_tail_constant_C3d (K := K) 1 * Ctrans * 4 ^ A *
                X ^ (-(6 : ℝ)) := by ring
      have hNsqrt : n ≤ Real.sqrt (qsN (c * d)) :=
        Real.le_sqrt_of_sq_le (hcdNormNat c d hc hd).1
      have hdenom : n ≤ qsN e * Real.sqrt (qsN (c * d)) := by
        have hNeN := QSC3.one_le_qsN he0
        calc
          n ≤ Real.sqrt (qsN (c * d)) := hNsqrt
          _ ≤ qsN e * Real.sqrt (qsN (c * d)) := by
            nlinarith [mul_le_mul_of_nonneg_right hNeN (Real.sqrt_nonneg (qsN (c * d)))]
      have hdenomPos : 0 < qsN e * Real.sqrt (qsN (c * d)) :=
        mul_pos hNePos (Real.sqrt_pos.2 hNcdpos)
      have hpref : M / (qsN e * Real.sqrt (qsN (c * d))) ≤ X := by
        have hpref₁ : M / (qsN e * Real.sqrt (qsN (c * d))) ≤ M / n := by
          rw [div_le_div_iff₀ hdenomPos (lt_of_lt_of_le zero_lt_one hn)]
          exact mul_le_mul_of_nonneg_left hdenom (le_of_lt hMpos)
        have hpref₂ : M / n ≤ X := by
          calc
            M / n ≤ M := div_le_self (le_of_lt hMpos) hn
            _ ≤ X := hMleX
        exact hpref₁.trans hpref₂
      have hscalarpos : 0 < M / (qsN e * Real.sqrt (qsN (c * d))) :=
        div_pos hMpos hdenomPos
      have hscalar : ‖((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ)‖ =
          M / (qsN e * Real.sqrt (qsN (c * d))) := by
        calc
          ‖((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ)‖ =
              |M / (qsN e * Real.sqrt (qsN (c * d)))| := Complex.norm_real _
          _ = M / (qsN e * Real.sqrt (qsN (c * d))) := abs_of_pos hscalarpos
      have hmu := QSC2.norm_qsMu_le e
      have hχe := hcharNorm c d hc hd e
      have hmulChar : ‖(qsMu e : ℂ)‖ * ‖χ.idealValue e‖ ≤ 1 :=
        mul_le_one₀ hmu (norm_nonneg _) hχe
      have hrem :
          (M / (qsN e * Real.sqrt (qsN (c * d)))) *
              ‖qsHigh (qsTransform K (fun x => (W x : ℂ))) Y κ ⊤ χ‖ ≤
            X * (qsHigh_tail_constant_C3d (K := K) 1 * Ctrans * 4 ^ A *
              X ^ (-(6 : ℝ))) :=
        mul_le_mul hpref hhighBound (by positivity) (by positivity)
      have hnormProduct :
          ‖(qsMu e : ℂ) * χ.idealValue e *
            ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ) *
            qsHigh (qsTransform K (fun x => (W x : ℂ))) Y κ ⊤ χ‖ =
          (‖(qsMu e : ℂ)‖ * ‖χ.idealValue e‖) *
            ((M / (qsN e * Real.sqrt (qsN (c * d)))) *
              ‖qsHigh (qsTransform K (fun x => (W x : ℂ))) Y κ ⊤ χ‖) := by
        calc
          _ = ‖(qsMu e : ℂ)‖ * ‖χ.idealValue e‖ *
              ‖((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ)‖ *
              ‖qsHigh (qsTransform K (fun x => (W x : ℂ))) Y κ ⊤ χ‖ := by
                simp only [norm_mul]
          _ = _ := by rw [hscalar]; ring
      calc
        _ = (‖(qsMu e : ℂ)‖ * ‖χ.idealValue e‖) *
              ((M / (qsN e * Real.sqrt (qsN (c * d)))) *
                ‖qsHigh (qsTransform K (fun x => (W x : ℂ))) Y κ ⊤ χ‖) := hnormProduct
        _ ≤ 1 * (X *
              (qsHigh_tail_constant_C3d (K := K) 1 * Ctrans * 4 ^ A *
                X ^ (-(6 : ℝ)))) := by
              exact mul_le_mul hmulChar hrem (by positivity) (by positivity)
        _ = Bhigh := by dsimp [Bhigh]; ring
    have hHighRaw :
        ‖qsDualHighKernel F W M κ 𝔮 c d‖ ≤ (qsDivisors 𝔮).card * Bhigh := by
      unfold qsDualHighKernel
      exact qs_norm_finset_sum_bound_C3d (qsDivisors 𝔮)
        (fun e => (qsMu e : ℂ) * χ.idealValue e *
          ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ) *
          qsHigh (qsTransform K (fun x => (W x : ℂ)))
            (qsN e * qsN (c * d) / M) κ ⊤ χ)
        Bhigh hBhigh hhighTerm
    calc
      _ ≤ (qsDivisors 𝔮).card * Bhigh := hHighRaw
      _ ≤ (Cdiv * qsN 𝔮) * Bhigh :=
        mul_le_mul_of_nonneg_right hDivQ hBhigh
      _ = CH * qsN 𝔮 * (X * X ^ (-(6 : ℝ))) := by dsimp [CH, Bhigh]; ring
      _ = CH * qsN 𝔮 * X ^ (-(5 : ℝ)) := by
        have hXone : X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        have hX1m6 : X * X ^ (-(6 : ℝ)) = X ^ (-(5 : ℝ)) := by
          calc
            X * X ^ (-(6 : ℝ)) = X ^ (1 : ℝ) * X ^ (-(6 : ℝ)) :=
              congrArg (fun t : ℝ => t * X ^ (-(6 : ℝ))) hXone
            _ = X ^ ((1 : ℝ) + (-(6 : ℝ))) := by rw [← Real.rpow_add hXpos]
            _ = X ^ (-(5 : ℝ)) := by congr 1 <;> norm_num
        rw [hX1m6]
      _ ≤ CH * qsN 𝔮 * X ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX (by norm_num)) (by positivity)
  let Φ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun c d =>
    qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d -
      qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d +
      qsDualHighKernel F W M κ 𝔮 c d
  have hE : 0 ≤ Cker * qsN 𝔮 * X ^ (-(3 : ℝ)) := by positivity
  have hPoint : ∀ c ∈ cols, ∀ d ∈ cols, ‖Φ c d‖ ≤ Cker * qsN 𝔮 * X ^ (-(3 : ℝ)) := by
    intro c hc d hd
    have hnormsum : ‖Φ c d‖ ≤
        (‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d‖ +
          ‖qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d‖) +
          ‖qsDualHighKernel F W M κ 𝔮 c d‖ := by
      dsimp [Φ]
      calc
        _ ≤ ‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d -
              qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d‖ +
              ‖qsDualHighKernel F W M κ 𝔮 c d‖ := norm_add_le _ _
        _ ≤ (‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d‖ +
              ‖qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d‖) +
              ‖qsDualHighKernel F W M κ 𝔮 c d‖ := by
          calc
            _ = ‖qsDualHighKernel F W M κ 𝔮 c d‖ +
                  ‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d -
                    qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d‖ := by ring
            _ ≤ ‖qsDualHighKernel F W M κ 𝔮 c d‖ +
                  (‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d‖ +
                    ‖qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d‖) :=
              add_le_add_right (norm_sub_le _ _) _
            _ = _ := by ring
    have hterms :
        (‖qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d‖ +
          ‖qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d‖) +
          ‖qsDualHighKernel F W M κ 𝔮 c d‖ ≤
        (CD + CO + CH) * qsN 𝔮 * X ^ (-(3 : ℝ)) := by
      calc
        _ ≤ (CD * qsN 𝔮 * X ^ (-(3 : ℝ)) +
              CO * qsN 𝔮 * X ^ (-(3 : ℝ))) +
              CH * qsN 𝔮 * X ^ (-(3 : ℝ)) := by
          gcongr
          · exact hDualPairBound c d hc hd
          · exact hOrigPairBound c d hc hd
          · exact hHighPairBound c d hc hd
        _ = (CD + CO + CH) * qsN 𝔮 * X ^ (-(3 : ℝ)) := by ring
    have hsumcoef : CD + CO + CH ≤ Cker := by
      dsimp [Cker]
      nlinarith
    calc
      ‖Φ c d‖ ≤ (CD + CO + CH) * qsN 𝔮 * X ^ (-(3 : ℝ)) := hnormsum.trans hterms
      _ ≤ Cker * qsN 𝔮 * X ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsumcoef (by positivity))
          (Real.rpow_nonneg (by positivity) _)
  have hPair := qs_pairSum_uniform_bound_C3d cols z Φ
      (Cker * qsN 𝔮 * X ^ (-(3 : ℝ))) hE hPoint
  have hcolsBound : (cols.card : ℝ) ≤ Ccols * X ^ (2 : ℝ) := by
    calc
      (cols.card : ℝ) ≤ Ccols * n ^ (2 : ℝ) := hcolsCount
      _ ≤ Ccols * X ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpowN2 (by positivity)
  have henergy : 0 ≤ ∑ c ∈ cols, ‖z c‖ ^ 2 :=
    Finset.sum_nonneg fun c hc => sq_nonneg _
  have hX3m1 : X ^ (-(3 : ℝ)) * X ^ (2 : ℝ) = X ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hXpos]
    congr 1
    norm_num
  have hqpow : qsN 𝔮 ≤ qsN 𝔮 ^ 8 := by
    have hq7 : 1 ≤ qsN 𝔮 ^ 7 := one_le_pow₀ hqN
    calc
      qsN 𝔮 = qsN 𝔮 * 1 := by ring
      _ ≤ qsN 𝔮 * qsN 𝔮 ^ 7 :=
        mul_le_mul_of_nonneg_left hq7 (le_of_lt hqNpos)
      _ = qsN 𝔮 ^ 8 := by rw [pow_succ]; ring
  have hcoef : Cker * Ccols * qsN 𝔮 ≤ C * qsN 𝔮 ^ 8 := by
    calc
      Cker * Ccols * qsN 𝔮 = C * qsN 𝔮 := by dsimp [C]
      _ ≤ C * qsN 𝔮 ^ 8 := mul_le_mul_of_nonneg_left hqpow (by positivity)
  calc
    ‖qsPairSum cols z Φ‖ ≤
        (Cker * qsN 𝔮 * X ^ (-(3 : ℝ))) * (cols.card : ℝ) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := hPair
    _ ≤ (Cker * qsN 𝔮 * X ^ (-(3 : ℝ))) *
          (Ccols * X ^ (2 : ℝ)) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcolsBound (by positivity)) henergy
    _ = (Cker * Ccols * qsN 𝔮) *
          (X ^ (-(3 : ℝ)) * X ^ (2 : ℝ)) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
    _ = (Cker * Ccols * qsN 𝔮) * X ^ (-(1 : ℝ)) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by rw [hX3m1]
    _ ≤ (C * qsN 𝔮 ^ 8) * X ^ (-(1 : ℝ)) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (le_of_lt hXpos) _)) henergy
    _ = C * qsN 𝔮 ^ 8 * X ^ (-(1 : ℝ)) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
    _ = C * qsN 𝔮 ^ 8 * (M * n) ^ (-1 : ℝ) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by dsimp [X]

end ArtinPrimitiveRoots.A2
