import ArtinPrimitiveRoots.Hecke.Defs

/-!
# Hecke L-function package: elementary statements (Re s > 1)

Frozen interface (§2 of the design, and (D3)). Design: `research/design/A2-HeckeAPI.lean` and `A2-DESIGN.md` (Opus A2 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open scoped NumberField ComplexOrder
open NumberField IsDedekindDomain
open Filter Asymptotics
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

open ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

private theorem idealUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIJ : I * J ≠ ⊥) :
    idealUnit (I * J) hIJ = idealUnit I hI * idealUnit J hJ := by
  apply Units.ext
  simp [idealUnit, FractionalIdeal.coeIdeal_mul]

private theorem isCoprimeTo_mul_iff (m : RayClassModulus K) (I J : Ideal (𝓞 K)) :
    IsCoprimeTo m (I * J) ↔ IsCoprimeTo m I ∧ IsCoprimeTo m J := by
  classical
  by_cases hI : I = ⊥
  · subst I
    simp [IsCoprimeTo]
  by_cases hJ : J = ⊥
  · subst J
    simp [IsCoprimeTo]
  constructor
  · rintro ⟨hIJ0, hIJ⟩
    constructor
    · refine ⟨hI, ?_⟩
      intro v hv
      have hsum :
          FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) +
            FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
        have hx := hIJ v hv
        have hval := congrArg (fun u : NumberFieldFractionalIdealGroup K =>
          (u : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
          (idealUnit_mul I J hI hJ hIJ0)
        rw [hval, Units.val_mul,
          FractionalIdeal.count_mul K v (Units.ne_zero (idealUnit I hI))
            (Units.ne_zero (idealUnit J hJ))] at hx
        simpa [idealUnit] using hx
      have hI' := FractionalIdeal.count_coe_nonneg K v I
      have hJ' := FractionalIdeal.count_coe_nonneg K v J
      have : FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
        omega
      simpa [idealUnit] using this
    · refine ⟨hJ, ?_⟩
      intro v hv
      have hsum :
          FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) +
            FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
        have hx := hIJ v hv
        have hval := congrArg (fun u : NumberFieldFractionalIdealGroup K =>
          (u : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
          (idealUnit_mul I J hI hJ hIJ0)
        rw [hval, Units.val_mul,
          FractionalIdeal.count_mul K v (Units.ne_zero (idealUnit I hI))
            (Units.ne_zero (idealUnit J hJ))] at hx
        simpa [idealUnit] using hx
      have hI' := FractionalIdeal.count_coe_nonneg K v I
      have hJ' := FractionalIdeal.count_coe_nonneg K v J
      have : FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
        omega
      simpa [idealUnit] using this
  · rintro ⟨⟨_, hI'⟩, ⟨_, hJ'⟩⟩
    refine ⟨mul_ne_zero hI hJ, ?_⟩
    have hmul : idealUnit I hI * idealUnit J hJ ∈ rayClassPrimeToIdeals m :=
      (rayClassPrimeToIdeals m).mul_mem hI' hJ'
    simpa [idealUnit_mul I J hI hJ (mul_ne_zero hI hJ)] using hmul

private theorem rayClass_mul {m : RayClassModulus K} (I J : Ideal (𝓞 K))
    (hI : IsCoprimeTo m I) (hJ : IsCoprimeTo m J) :
    rayClass m (I * J) ((isCoprimeTo_mul_iff m I J).2 ⟨hI, hJ⟩) =
      rayClass m I hI * rayClass m J hJ := by
  rcases hI with ⟨hI0, hI'⟩
  rcases hJ with ⟨hJ0, hJ'⟩
  have hIJ0 : I * J ≠ ⊥ := mul_ne_zero hI0 hJ0
  have hIJ' : idealUnit (I * J) hIJ0 ∈ rayClassPrimeToIdeals m := by
    simpa [idealUnit_mul I J hI0 hJ0 hIJ0] using
      (rayClassPrimeToIdeals m).mul_mem hI' hJ'
  change QuotientGroup.mk (⟨idealUnit (I * J) hIJ0, hIJ'⟩ : rayClassPrimeToIdeals m) =
    QuotientGroup.mk (⟨idealUnit I hI0, hI'⟩ : rayClassPrimeToIdeals m) *
      QuotientGroup.mk (⟨idealUnit J hJ0, hJ'⟩ : rayClassPrimeToIdeals m)
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (idealUnit_mul I J hI0 hJ0 hIJ0)

private def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

private theorem idealCount_sum_eq (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} =
      ∑ k ∈ Finset.Icc 0 n, idealCount (K := K) k := by
  classical
  unfold idealCount
  rw [← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k)]
  simp [Set.coe_eq_subtype]

/-! ## §2 Elementary statements (Re s > 1)

All `sorry`; Mathlib-level.  Sizes in `A2-DESIGN.md` §2. -/

/-- `charValue` is completely multiplicative (zero extension included).
Consumers: A2 `def:zf-detector` (`L·D_U = Σ α_U η`), A2 `po:H-product`; B `sp:upstairs-factor`. -/
theorem charValue_mul {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (I J : Ideal (𝓞 K)) : charValue η (I * J) = charValue η I * charValue η J := by
  classical
  by_cases hprod : IsCoprimeTo m (I * J)
  · rcases (isCoprimeTo_mul_iff m I J).1 hprod with ⟨hI, hJ⟩
    simp [charValue, hprod, hI, hJ, rayClass_mul, map_mul]
  · have hpair : ¬ (IsCoprimeTo m I ∧ IsCoprimeTo m J) := by
      intro h
      exact hprod ((isCoprimeTo_mul_iff m I J).2 h)
    rcases not_and_or.mp hpair with hI | hJ
    · simp [charValue, hprod, hI]
    · simp [charValue, hprod, hJ]

/-- Characters of the finite group `Cl_𝔪` have unimodular values.
Consumers: every bound below; A2 `lem:conductor-sieve`. -/
theorem norm_charValue_le_one {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (I : Ideal (𝓞 K)) : ‖charValue η I‖ ≤ 1 := by
  classical
  by_cases h : IsCoprimeTo m I
  · simp only [charValue, dite_eq_left h]
    have hpow : (η (rayClass m I h)) ^ Nat.card (RayClassGroup m) = 1 := by
      rw [← map_pow, pow_card_eq_one']
      simp
    have hpow' := congrArg (fun z : ℂˣ => (z : ℂ)) hpow
    have hnorm := Complex.norm_eq_one_of_pow_eq_one (by simpa using hpow')
      (Nat.card_pos.ne' : Nat.card (RayClassGroup m) ≠ 0)
    simpa using hnorm.le
  · simp [charValue, h]

private theorem coeff_norm_le_idealCount {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (n : ℕ) :
    ‖coeff η n‖ ≤ (idealCount (K := K) n : ℝ) := by
  classical
  unfold coeff
  let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  let S := F.toFinset
  have hcard : S.card = idealCount (K := K) n := by
    dsimp [S, idealCount]
    exact (Nat.card_eq_card_finite_toFinset F).symm
  calc
    ‖∑ I ∈ S, charValue η I‖ ≤ ∑ I ∈ S, ‖charValue η I‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ S, (1 : ℝ) := Finset.sum_le_sum fun I hI ↦ norm_charValue_le_one η I
    _ = (idealCount (K := K) n : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard

/-- Absolute convergence for `Re s > 1`.  Consumers: all. -/
theorem LSeriesSummable_coeff {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (coeff η) s := by
  have hcountLim : Tendsto
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) /
        (n : ℝ)) atTop (𝓝 (dedekindZeta_residue K)) := by
    have h := (Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
    convert h using 1
    · funext n
      congr 1
      exact_mod_cast (Nat.card_congr
        (Equiv.subtypeEquivRight (fun _ ↦ by norm_cast)))
    · simp [dedekindZeta_residue]
  have hcountLim' : Tendsto
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) /
        (n : ℝ) ^ (1 : ℝ)) atTop (𝓝 (dedekindZeta_residue K)) := by
    simpa only [Real.rpow_one] using hcountLim
  have hcount :
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (r := 1) hcountLim'
  have hpartial :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖coeff η k‖) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    apply (isBigO_of_le (l := atTop) ?_).trans hcount
    intro n
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k hk => norm_nonneg (coeff η k)),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      ∑ k ∈ Finset.Icc 1 n, ‖coeff η k‖ ≤
          ∑ k ∈ Finset.Icc 1 n, (idealCount (K := K) k : ℝ) :=
        Finset.sum_le_sum fun k hk => coeff_norm_le_idealCount η k
      _ ≤ ∑ k ∈ Finset.Icc 0 n, (idealCount (K := K) k : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
          (fun k _ _ ↦ by positivity)
      _ = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ n} : ℝ) := by
        exact_mod_cast (idealCount_sum_eq (K := K) n).symm
  exact LSeriesSummable_of_sum_norm_bigO hpartial zero_le_one hs

private theorem charValue_one_modulus (I : Ideal (𝓞 K)) :
    charValue (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) I =
      if I = ⊥ then 0 else 1 := by
  classical
  by_cases hI : I = ⊥
  · simp [charValue, IsCoprimeTo, hI]
  · have hcop : IsCoprimeTo (⟨0, ∅⟩ : RayClassModulus K) I := by
      change ∃ h' : I ≠ ⊥, idealUnit I h' ∈
        rayClassPrimeToIdeals (⟨0, ∅⟩ : RayClassModulus K)
      refine ⟨hI, ?_⟩
      change ∀ v, v ∈ (0 : HeightOneSpectrum (𝓞 K) →₀ ℕ).support → _
      intro v hv
      simp at hv
    simp only [charValue, dite_eq_left hcop]
    simp [hI]

private theorem coeff_one_modulus_eq_idealCount {n : ℕ} (hn : n ≠ 0) :
    coeff (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) n =
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) := by
  classical
  unfold coeff
  let F := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  calc
    ∑ I ∈ F.toFinset,
        charValue (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) I =
      ∑ I ∈ F.toFinset, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [charValue_one_modulus]
        have hIn : Ideal.absNorm I = n := F.mem_toFinset.mp hI
        have hI0 : I ≠ ⊥ := by
          intro h
          subst I
          simp at hIn
          exact hn hIn.symm
        simp [hI0]
    _ = (F.toFinset.card : ℂ) := by simp
    _ = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) := by
      exact_mod_cast (Nat.card_eq_card_finite_toFinset F).symm

private theorem idealCount_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (idealCount (K := K) n : ℂ)) s := by
  apply (LSeriesSummable_congr s
    (f := fun n ↦ (idealCount (K := K) n : ℂ))
    (g := coeff (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ))
    (fun {n} hn ↦ (coeff_one_modulus_eq_idealCount (K := K) hn).symm)).mpr
  exact LSeriesSummable_coeff (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) hs

private theorem idealCount_norm_tsum_eq_dedekindZeta_re {σ : ℝ} (hσ : 1 < σ) :
    (dedekindZeta K (σ : ℂ)).re =
      ∑' n, ‖LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n‖ := by
  have hs := idealCount_LSeriesSummable (K := K) (s := (σ : ℂ)) (by simpa using hσ)
  have hnonneg (n : ℕ) :
      0 ≤ LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n := by
    exact LSeries.term_nonneg (by positivity) σ
  calc
    (dedekindZeta K (σ : ℂ)).re =
        (∑' n, LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n).re := rfl
    _ = ∑' n, (LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n).re :=
      Complex.re_tsum hs
    _ = ∑' n, ‖LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (σ : ℂ) n‖ := by
      apply tsum_congr
      intro n
      exact congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (hnonneg n))

private theorem norm_LSeriesRay_upper {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeriesRay η s‖ ≤ (dedekindZeta K s.re).re := by
  have hη := (LSeriesSummable_coeff η hs).norm
  have hζ := (idealCount_LSeriesSummable (K := K) (s := s.re) hs).norm
  have hterm (n : ℕ) :
      ‖LSeries.term (coeff η) s n‖ ≤
        ‖LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (s.re : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · rfl
    · simp only [Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (coeff_norm_le_idealCount η n) (by positivity)
  calc
    ‖LSeriesRay η s‖ = ‖∑' n, LSeries.term (coeff η) s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term (coeff η) s n‖ := norm_tsum_le_tsum_norm hη
    _ ≤ ∑' n, ‖LSeries.term (fun n ↦ (idealCount (K := K) n : ℂ)) (s.re : ℂ) n‖ :=
      hη.tsum_le_tsum hterm hζ
    _ = (dedekindZeta K s.re).re :=
      (idealCount_norm_tsum_eq_dedekindZeta_re (K := K) hs).symm

/-- Euler product, as a convergent product over the finite primes.
Consumers: A2 `def:zf-detector`, `zf:reciprocal-bound`; B `sp:upstairs-factor`,
`sp:quotient-factor`. -/
theorem LSeriesRay_eulerProduct {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - charValue η v.asIdeal * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeriesRay η s) := sorry

/-- Size bounds on `Re s > 1`: `‖L‖ ≤ ζ_K(σ)` and `‖L⁻¹‖ ≤ ζ_K(σ)`, `σ = Re s`.
Consumers: A2 `zf:height-decay`, `zf:small-rows`, `zf:far-rows`, `zf:f-bounds`. -/
theorem norm_LSeriesRay_le {m : RayClassModulus K} (η : RayClassGroup m →* ℂˣ) {s : ℂ}
    (hs : 1 < s.re) :
    ‖LSeriesRay η s‖ ≤ (dedekindZeta K s.re).re ∧
      LSeriesRay η s ≠ 0 ∧ ‖(LSeriesRay η s)⁻¹‖ ≤ (dedekindZeta K s.re).re := by
  refine ⟨norm_LSeriesRay_upper η hs, ?_⟩
  sorry

/-- **Change of modulus.**  If `η` (mod `𝔪`) and `η'` (mod `𝔫`) agree on every prime coprime
to `𝔪`, the two L-series differ by the finitely many Euler factors at the primes of `𝔪`:
`L^{(𝔪)}(s,η) = L^{(𝔫)}(s,η') · ∏_{v ∈ supp 𝔪} (1 - η'(𝔭_v) N𝔭_v^{-s})`.
Consumers: B `thm:hecke-zero-free` note ("choice of modulus harmless"), `sp:upstairs-factor`;
A2 passage between `L^S` (paper) and `L^{(𝔪)}` in `zf:convexity`, `prop:zero-density`. -/
theorem LSeriesRay_change_modulus {m n : RayClassModulus K} (η : RayClassGroup m →* ℂˣ)
    (η' : RayClassGroup n →* ℂˣ)
    (hagree : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
      charValue η v.asIdeal = charValue η' v.asIdeal)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesRay η s = LSeriesRay η' s * ∏ v ∈ m.finitePart.support,
      (1 - charValue η' v.asIdeal * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := sorry

/-- Trivial modulus and trivial character give Mathlib's Dedekind zeta function.
Consumers: B `ext:dedekind-fe` (dictionary), A2 `zf:principal-row`. -/
theorem LSeriesRay_trivial_eq_dedekindZeta (s : ℂ) :
    LSeriesRay (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ) s =
      dedekindZeta K s := by
  change LSeries (coeff (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus K) →* ℂˣ)) s =
    LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) s
  apply LSeries_congr
  intro n hn
  exact coeff_one_modulus_eq_idealCount (K := K) hn



/-- **(D3) Uniform Jensen inputs** (constants absolute; degree `n = [K:ℚ]`): for `σ > 1`,
`(ζ(2σ)/ζ(σ))^n ≤ ‖ζ_K(σ+it)‖ ≤ ζ(σ)^n`.  With (D1) and Stirling these are the only
field-dependent inputs of the unit-window zero count.
Consumers: B `ext:dedekind-zero-count`, `spl:left-line` (Euler bound at `Re = 3/2`). -/
theorem dedekindZeta_norm_bounds (K : Type*) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    ((riemannZeta (2 * σ)).re / (riemannZeta σ).re) ^ Module.finrank ℚ K ≤
        ‖dedekindZeta K (σ + t * Complex.I)‖ ∧
      ‖dedekindZeta K (σ + t * Complex.I)‖ ≤ (riemannZeta σ).re ^ Module.finrank ℚ K := sorry


end ArtinPrimitiveRoots.Hecke
