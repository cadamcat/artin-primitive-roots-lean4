import ArtinPrimitiveRoots.Splitting.Analytic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# §7 transfer from prime ideals to rational primes

Blueprint node `sp:count-from-theta`; source `07-splitting.tex:227-246`.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Ext.SplittingInputs

private def thetaSummand {K : Type*} [Field K] [NumberField K]
    (f : ℝ → ℝ) (x : ℝ)
    (w : HeightOneSpectrum (𝓞 K) × ℕ) : ℝ :=
  if 0 < w.2 then
    Real.log (Ideal.absNorm w.1.asIdeal : ℝ) *
      f (((Ideal.absNorm w.1.asIdeal) ^ w.2 : ℕ) / x)
  else 0

private theorem thetaSummand_summable {K : Type*} [Field K] [NumberField K]
    (f : ℝ → ℝ) (x : ℝ) (hx : 2 ≤ x)
    (hsupport : Function.support f ⊆ Set.Ioo 0 3) :
    Summable (thetaSummand (K := K) f x) := by
  classical
  obtain ⟨B, hB⟩ := exists_nat_gt (3 * x)
  have hBreal : 3 * x ≤ (B : ℝ) := hB.le
  have hBtwo : 2 ≤ B := by
    have h : (2 : ℝ) < B := by nlinarith
    exact_mod_cast h.le
  have hBne : B ≠ 0 := by omega
  let U : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | Ideal.absNorm v.asIdeal ≤ B}
  let J : Set ℕ := Set.Iio (Nat.log2 B + 1)
  have hU : U.Finite := by
    exact (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
      (S := 𝓞 K) B)
  have hJ : J.Finite := Set.finite_Iio _
  have hSupport : Function.support (thetaSummand (K := K) f x) ⊆ U ×ˢ J := by
    intro w hw
    change thetaSummand (K := K) f x w ≠ 0 at hw
    have hj : 0 < w.2 := by
      by_contra h
      simp [thetaSummand, not_lt.mp h] at hw
    have hprod :
        Real.log (Ideal.absNorm w.1.asIdeal : ℝ) *
          f (((Ideal.absNorm w.1.asIdeal) ^ w.2 : ℕ) / x) ≠ 0 := by
      simpa [thetaSummand, hj] using hw
    have hfne : f (((Ideal.absNorm w.1.asIdeal) ^ w.2 : ℕ) / x) ≠ 0 :=
      (mul_ne_zero_iff.mp hprod).2
    have hargSupport :
        (((Ideal.absNorm w.1.asIdeal) ^ w.2 : ℕ) / x) ∈ Function.support f := hfne
    have hargLt :
        (((Ideal.absNorm w.1.asIdeal) ^ w.2 : ℕ) : ℝ) / x < 3 :=
      (hsupport hargSupport).2
    have hpowLt :
        ((Ideal.absNorm w.1.asIdeal) ^ w.2 : ℕ) < 3 * x :=
      (div_lt_iff₀ (by linarith : 0 < x)).mp hargLt
    have hpowLe : (Ideal.absNorm w.1.asIdeal) ^ w.2 ≤ B := by
      exact_mod_cast hpowLt.le.trans hBreal
    have hNtwo : 2 ≤ Ideal.absNorm w.1.asIdeal := by
      have hN := NumberField.HeightOneSpectrum.one_lt_absNorm w.1
      omega
    have hNle : Ideal.absNorm w.1.asIdeal ≤ B := by
      exact (le_self_pow₀ (by omega : 1 ≤ Ideal.absNorm w.1.asIdeal)
        (by omega : w.2 ≠ 0)).trans hpowLe
    have h2pow : 2 ^ w.2 ≤ B := by
      calc
        2 ^ w.2 ≤ (Ideal.absNorm w.1.asIdeal) ^ w.2 := by
          gcongr
        _ ≤ B := hpowLe
    have hjlog : w.2 ≤ Nat.log2 B := (Nat.le_log2 hBne).2 h2pow
    change w.1 ∈ U ∧ w.2 ∈ J
    exact ⟨hNle, Nat.lt_succ_of_le hjlog⟩
  exact summable_of_hasFiniteSupport ((hU.prod hJ).subset hSupport)

private theorem finite_sum_le_tsum_of_injective {α β : Type*} [DecidableEq β]
    (s : Finset α) (e : α → β) (f : β → ℝ) (he : Set.InjOn e s)
    (hs : Summable f) (hnonneg : ∀ b, 0 ≤ f b) :
    (∑ a ∈ s, f (e a)) ≤ ∑' b, f b := by
  calc
    _ = ∑ b ∈ s.image e, f b := (Finset.sum_image he).symm
    _ ≤ ∑' b, f b := hs.sum_le_tsum _ (fun b _ => hnonneg b)

set_option maxHeartbeats 1000000

/-- **`sp:count-from-theta`**, `07-splitting.tex:227-246`. The smooth estimate and `spl:field-bounds`
bound primes that split completely in `K_q`, with constants independent of `q` in the range
`q ≤ exp((log x)^(3/10))`. The frozen elementary proposition follows by `alg:splitting-test` and
the short exclusion of primes dividing `a q`. -/
theorem sp_count_from_theta (a : ℤ) (ha : 1 < |a|) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, 5 ≤ q₀ ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ (q : ℕ) [NeZero q], q.Prime → q₀ ≤ q →
        (q : ℝ) ≤ Real.exp (Real.log x ^ (3 / 10 : ℝ)) →
          (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
              splitsCompletely (kummerField a q) p} : Set ℕ).ncard : ℝ) ≤
            C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) +
              x ^ (1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀)) := by
  have hδ : 0 < ArtinPrimitiveRoots.HeckeBoundary.δ₀ := by
    norm_num [ArtinPrimitiveRoots.HeckeBoundary.δ₀]
  have hδ' : ArtinPrimitiveRoots.HeckeBoundary.δ₀ < 1 / 2 := by
    norm_num [ArtinPrimitiveRoots.HeckeBoundary.δ₀]
  obtain ⟨f, hfSmooth, hfCompact, hfSupport, hfLower, hfNonneg⟩ := smooth_bump_exists
  have hfTest : IsSmoothPositiveTestFunction f := by
    refine ⟨hfSmooth, hfCompact, ?_⟩
    exact hfSupport.trans Set.Ioo_subset_Ioi_self
  obtain ⟨Cf, hCf, hSmooth⟩ :=
    spl_smooth_estimate ArtinPrimitiveRoots.HeckeBoundary.δ₀ hδ hδ' f hfTest hfNonneg
  obtain ⟨qₐ, Ca, hqₐ, hCa, hBounds⟩ := spl_field_bounds a ha
  let C : ℝ := Cf * (1 + 2 * Ca)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let Xval : ℝ := Real.exp 2 + 2
  have hXval : 2 ≤ Xval := by
    dsimp [Xval]
    nlinarith [Real.exp_pos (2 : ℝ)]
  refine ⟨C, hC, qₐ, hqₐ, Xval, hXval, ?_⟩
  intro x hx q _ hq hqa hqexp
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlogx : 2 ≤ Real.log x := by
    have hExpX : Real.exp 2 ≤ Xval := by
      dsimp [Xval]
      linarith
    have hExp : Real.exp 2 ≤ x := hExpX.trans hx
    have h := Real.log_le_log (Real.exp_pos 2) hExp
    simpa using h
  have hlogxpos : 0 < Real.log x := by linarith
  have hlogxOne : 1 ≤ Real.log x := by linarith
  have hlog2le : Real.log 2 ≤ Real.log x := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hq5 : 5 ≤ q := hqₐ.trans hqa
  have hqpos : 0 < q := hq.pos
  have hqRealPos : 0 < (q : ℝ) := Nat.cast_pos.mpr hqpos
  have hqSubPos : 0 < (q : ℝ) - 1 := by
    have hqRealGt : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
    linarith
  have hdegreeNat : kummerDegree a q = q * (q - 1) :=
    (hBounds q hq hqa).1
  have hfieldBound := (hBounds q hq hqa).2.2.1
  have hGalois := (hBounds q hq hqa).2.2.2.1
  have hzero := (hBounds q hq hqa).2.2.2.2.2
  let K := kummerField a q
  haveI : IsGalois ℚ K := hGalois
  have hdegreeReal : (Module.finrank ℚ K : ℝ) =
      (q : ℝ) * ((q : ℝ) - 1) := by
    calc
      (Module.finrank ℚ K : ℝ) = (kummerDegree a q : ℝ) := by
        simp [K, kummerDegree]
      _ = ((q * (q - 1) : ℕ) : ℝ) := by rw [hdegreeNat]
      _ = (q : ℝ) * ((q : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q)]
        ring
  have hfieldBound' :
      Real.log (absoluteDiscriminant K) + (Module.finrank ℚ K : ℝ) ≤
        Ca * ((q : ℝ) * ((q : ℝ) - 1)) * Real.log (2 * (q : ℝ)) := by
    calc
      _ ≤ Ca * (Module.finrank ℚ K : ℝ) * Real.log (2 * (q : ℝ)) := by
        simpa [K, kummerDegree] using hfieldBound
      _ = _ := by rw [hdegreeReal]
  have hpow : 0 < Real.rpow x (1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀) :=
    Real.rpow_pos_of_pos hxpos _
  have hTheta := hSmooth K hzero x (hXval.trans hx)
  have hThetaBound :
      primeIdealTheta K f x ≤
        Cf * (x + Real.rpow x (1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀) *
          (Ca * ((q : ℝ) * ((q : ℝ) - 1)) * Real.log (2 * (q : ℝ)))) := by
    calc
      _ ≤ Cf * (x + Real.rpow x (1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀) *
          (Real.log (absoluteDiscriminant K) + Module.finrank ℚ K)) := hTheta
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hCf.le
        have hmul := mul_le_mul_of_nonneg_left hfieldBound' (le_of_lt hpow)
        nlinarith [hmul]

  let Pset : Set ℕ := {p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
    splitsCompletely K p}
  have hPfinite : Pset.Finite := by
    obtain ⟨B, hB⟩ := exists_nat_gt (2 * x)
    refine (Set.finite_Iio B).subset ?_
    intro p hp
    rcases hp with ⟨_, _, hp2x, _⟩
    exact_mod_cast lt_of_le_of_lt hp2x hB

  classical
  let P : Type := {p : ℕ // p ∈ Pset}
  letI : Fintype P := hPfinite.fintype
  let pIdeal : P → Ideal ℤ := fun p => Ideal.span {(p.1 : ℤ)}
  have hPprop (p : P) : p.1.Prime ∧ x < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * x ∧
      splitsCompletely K p.1 := by
    cases p with
    | mk p hp =>
      change p ∈ Pset at hp
      simpa [Pset] using hp
  have hpPrime (p : P) : p.1.Prime := by
    exact (hPprop p).1
  have hpIdealNeBot (p : P) : pIdeal p ≠ ⊥ := by
    have hpz : (p.1 : ℤ) ≠ 0 := by exact_mod_cast (hpPrime p).ne_zero
    intro h
    apply hpz
    exact Ideal.span_singleton_eq_bot.mp (by simpa [pIdeal] using h)
  have hpIdealMax (p : P) : (pIdeal p).IsMaximal := by
    have hpz : (p.1 : ℤ) ≠ 0 := by exact_mod_cast (hpPrime p).ne_zero
    have hpInt : Prime (p.1 : ℤ) := Int.prime_iff_natAbs_prime.mpr (hpPrime p)
    have hpIdealPrime : (pIdeal p).IsPrime := by
      simpa [pIdeal] using (Ideal.span_singleton_prime hpz).mpr hpInt
    exact hpIdealPrime.isMaximal (hpIdealNeBot p)
  let Vset : P → Set (HeightOneSpectrum (𝓞 K)) := fun p =>
    {v | v.asIdeal ∣ (pIdeal p).map (algebraMap ℤ (𝓞 K))}
  have hVcard (p : P) : (Vset p).ncard = Module.finrank ℚ K := by
    let e : {v : HeightOneSpectrum (𝓞 K) // v ∈ Vset p} ≃
        (pIdeal p).primesOver (𝓞 K) :=
      letI : (pIdeal p).IsMaximal := hpIdealMax p
      IsDedekindDomain.HeightOneSpectrum.equivPrimesOver
        (B := 𝓞 K) (p := pIdeal p) (hpIdealNeBot p)
    rw [Set.ncard_congr' e]
    simpa [splitsCompletely, pIdeal] using (hPprop p).2.2.2
  have hVfinite (p : P) : (Vset p).Finite :=
    Set.finite_of_ncard_ne_zero (by
      rw [hVcard p]
      exact Nat.ne_of_gt Module.finrank_pos)
  let V : P → Type := fun p => {v : HeightOneSpectrum (𝓞 K) // v ∈ Vset p}
  letI : ∀ p : P, Fintype (V p) := fun p => (hVfinite p).fintype
  have hVcardF (p : P) : Fintype.card (V p) = Module.finrank ℚ K := by
    calc
      Fintype.card (V p) = (Vset p).ncard := by
        simpa [V] using Set.fintypeCard_eq_ncard (Vset p)
      _ = Module.finrank ℚ K := hVcard p
  have hNormV (p : P) (v : V p) : Ideal.absNorm v.1.asIdeal = p.1 := by
    rcases hPprop p with ⟨hp, _, _, hsplit⟩
    letI : Fact p.1.Prime := ⟨hp⟩
    let e : {w : HeightOneSpectrum (𝓞 K) // w ∈ Vset p} ≃
        (pIdeal p).primesOver (𝓞 K) :=
      letI : (pIdeal p).IsMaximal := hpIdealMax p
      IsDedekindDomain.HeightOneSpectrum.equivPrimesOver
        (B := 𝓞 K) (p := pIdeal p) (hpIdealNeBot p)
    have hOver : v.1.asIdeal ∈ (pIdeal p).primesOver (𝓞 K) :=
      (e ⟨v.1, v.2⟩).property
    exact ext_split_prime_norm K p.1 v.1.asIdeal hOver hsplit

  have hPcard : Pset.ncard = Fintype.card P := by
    calc
      Pset.ncard = Nat.card P := by
        symm
        simpa [P] using Nat.card_coe_set_eq Pset
      _ = Fintype.card P := Nat.card_eq_fintype_card

  have hThetaPairSummable : Summable (thetaSummand (K := K) f x) :=
    thetaSummand_summable f x (hXval.trans hx) hfSupport
  have hThetaPairNonneg (w : HeightOneSpectrum (𝓞 K) × ℕ) :
      0 ≤ thetaSummand (K := K) f x w := by
    by_cases hj : 0 < w.2
    · have hN : 1 ≤ (Ideal.absNorm w.1.asIdeal : ℝ) := by
        exact_mod_cast (Nat.le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm w.1))
      simp only [thetaSummand, if_pos hj]
      exact mul_nonneg (Real.log_nonneg hN) (hfNonneg _)
    · simp [thetaSummand, hj]
  have hThetaEq : primeIdealTheta K f x =
      ∑' w : HeightOneSpectrum (𝓞 K) × ℕ, thetaSummand (K := K) f x w := by
    unfold primeIdealTheta
    exact (hThetaPairSummable.tsum_prod).symm

  let Pair : Type := Σ p : P, V p
  let toTheta : Pair → HeightOneSpectrum (𝓞 K) × ℕ := fun z => (z.2.1, 1)
  have htoThetaInj : Function.Injective toTheta := by
    intro z z'
    cases z with
    | mk p v =>
      cases z' with
      | mk p' v' =>
        intro heq
        rcases Prod.mk.inj heq with ⟨hv, _⟩
        have hpval : p.1 = p'.1 := by
          calc
            p.1 = Ideal.absNorm v.1.asIdeal := (hNormV p v).symm
            _ = Ideal.absNorm v'.1.asIdeal := by rw [hv]
            _ = p'.1 := hNormV p' v'
        have hpEq : p = p' := Subtype.ext hpval
        subst p'
        have hvEq : v = v' := Subtype.ext hv
        subst v'
        rfl
  have hSelectedLe :
      (∑ z : Pair, thetaSummand (K := K) f x (toTheta z)) ≤ primeIdealTheta K f x := by
    calc
      _ ≤ ∑' w : HeightOneSpectrum (𝓞 K) × ℕ, thetaSummand (K := K) f x w := by
        simpa [toTheta] using
          finite_sum_le_tsum_of_injective (s := Finset.univ) toTheta
            (thetaSummand (K := K) f x) htoThetaInj.injOn
            hThetaPairSummable hThetaPairNonneg
      _ = primeIdealTheta K f x := hThetaEq.symm

  have hSelectedTermLower (p : P) (v : V p) :
      Real.log x ≤ thetaSummand (K := K) f x (v.1, 1) := by
    rcases hPprop p with ⟨_, hpx, hp2x, _⟩
    have hNormReal : (Ideal.absNorm v.1.asIdeal : ℝ) = (p.1 : ℝ) := by
      exact_mod_cast hNormV p v
    have hinterval : (p.1 : ℝ) / x ∈ Set.Icc 1 2 := by
      constructor
      · rw [one_le_div₀ hxpos]
        exact hpx.le
      · rw [div_le_iff₀ hxpos]
        exact hp2x
    have hfAt : 1 ≤ f ((p.1 : ℝ) / x) := hfLower _ hinterval
    have hlogP : Real.log x ≤ Real.log (p.1 : ℝ) :=
      Real.log_le_log hxpos hpx.le
    have hlogPnonneg : 0 ≤ Real.log (p.1 : ℝ) :=
      Real.log_nonneg (by linarith)
    have hprod : Real.log x ≤ Real.log (p.1 : ℝ) * f ((p.1 : ℝ) / x) := by
      calc
        _ ≤ Real.log (p.1 : ℝ) := hlogP
        _ = Real.log (p.1 : ℝ) * 1 := by ring
        _ ≤ Real.log (p.1 : ℝ) * f ((p.1 : ℝ) / x) :=
          mul_le_mul_of_nonneg_left hfAt hlogPnonneg
    simpa [thetaSummand, hNormReal] using hprod

  have hSelectedSumLower :
      (Fintype.card Pair : ℝ) * Real.log x ≤
        ∑ z : Pair, thetaSummand (K := K) f x (toTheta z) := by
    calc
      _ = ∑ z : Pair, Real.log x := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro z hz
        exact hSelectedTermLower z.1 z.2
  have hPairCard : Fintype.card Pair = Fintype.card P * Module.finrank ℚ K := by
    calc
      Fintype.card Pair = ∑ p : P, Fintype.card (V p) := by
        simp [Pair, Fintype.card_sigma]
      _ = ∑ p : P, Module.finrank ℚ K := by simp_rw [hVcardF]
      _ = Fintype.card P * Module.finrank ℚ K := by simp
  have hPairCardReal : (Fintype.card Pair : ℝ) =
      (Pset.ncard : ℝ) * ((q : ℝ) * ((q : ℝ) - 1)) := by
    calc
      _ = (Fintype.card P : ℝ) * (Module.finrank ℚ K : ℝ) := by
        exact_mod_cast hPairCard
      _ = (Pset.ncard : ℝ) * ((q : ℝ) * ((q : ℝ) - 1)) := by
        rw [← hPcard, hdegreeReal]
  have hThetaLower :
      (Pset.ncard : ℝ) * ((q : ℝ) * ((q : ℝ) - 1)) * Real.log x ≤
        primeIdealTheta K f x := by
    calc
      _ = (Fintype.card Pair : ℝ) * Real.log x := by
        rw [hPairCardReal]
      _ ≤ ∑ z : Pair, thetaSummand (K := K) f x (toTheta z) := hSelectedSumLower
      _ ≤ primeIdealTheta K f x := hSelectedLe

  have hqLog : Real.log (q : ℝ) ≤ Real.rpow (Real.log x) (3 / 10 : ℝ) := by
    have h := Real.log_le_log hqRealPos hqexp
    simpa using h
  have hlogPow : Real.rpow (Real.log x) (3 / 10 : ℝ) ≤ Real.log x := by
    calc
      _ ≤ Real.rpow (Real.log x) (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogxOne (by norm_num)
      _ = Real.log x := by simp
  have hlogqLe : Real.log (q : ℝ) ≤ Real.log x := hqLog.trans hlogPow
  have hlogMul : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have hlog2q : Real.log (2 * (q : ℝ)) ≤ 2 * Real.log x := by
    rw [hlogMul]
    linarith [hlog2le, hlogqLe]
  let n : ℝ := (q : ℝ) * ((q : ℝ) - 1)
  let xpow : ℝ := Real.rpow x (1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀)
  have hnpos : 0 < n := by dsimp [n]; positivity
  have hxpowPos : 0 < xpow := by dsimp [xpow]; exact hpow
  have hdenomPos : 0 < n * Real.log x := mul_pos hnpos hlogxpos
  have hcountNumerator :
      (Pset.ncard : ℝ) * (n * Real.log x) ≤
        Cf * (x + xpow * (Ca * n * Real.log (2 * (q : ℝ)))) := by
    calc
      _ = (Pset.ncard : ℝ) * n * Real.log x := by ring
      _ ≤ primeIdealTheta K f x := by
        simpa [n] using hThetaLower
      _ ≤ Cf * (x + xpow * (Ca * n * Real.log (2 * (q : ℝ)))) := by
        simpa [n, xpow, mul_assoc] using hThetaBound
  have hcountBound : (Pset.ncard : ℝ) ≤
      Cf * (x + xpow * (Ca * n * Real.log (2 * (q : ℝ)))) / (n * Real.log x) := by
    rw [le_div_iff₀ hdenomPos]
    exact hcountNumerator
  have hfracEq :
      Cf * (x + xpow * (Ca * n * Real.log (2 * (q : ℝ)))) / (n * Real.log x) =
        Cf * (x / (n * Real.log x)) + Cf * Ca * xpow *
          (Real.log (2 * (q : ℝ)) / Real.log x) := by
    field_simp [ne_of_gt hnpos, ne_of_gt hlogxpos]
  have hcountExpanded :
      (Pset.ncard : ℝ) ≤ Cf * (x / (n * Real.log x)) + 2 * Cf * Ca * xpow := by
    calc
      _ ≤ Cf * (x + xpow * (Ca * n * Real.log (2 * (q : ℝ)))) /
          (n * Real.log x) := hcountBound
      _ = Cf * (x / (n * Real.log x)) + Cf * Ca * xpow *
          (Real.log (2 * (q : ℝ)) / Real.log x) := hfracEq
      _ ≤ _ := by
        have hratio : Real.log (2 * (q : ℝ)) / Real.log x ≤ 2 :=
          (div_le_iff₀ hlogxpos).2 hlog2q
        have hsecond := mul_le_mul_of_nonneg_left hratio (by positivity :
          0 ≤ Cf * Ca * xpow)
        nlinarith [hsecond]
  have hcoeffFirst : Cf ≤ C := by
    dsimp [C]
    calc
      Cf ≤ Cf + 2 * Cf * Ca := by
        have hprod : 0 ≤ 2 * Cf * Ca := by positivity
        linarith
      _ = Cf * (1 + 2 * Ca) := by ring
  have hcoeffSecond : 2 * Cf * Ca ≤ C := by
    dsimp [C]
    calc
      2 * Cf * Ca ≤ Cf + 2 * Cf * Ca := by linarith [hCf]
      _ = Cf * (1 + 2 * Ca) := by ring
  have hxdivNonneg : 0 ≤ x / (n * Real.log x) :=
    div_nonneg hxpos.le (le_of_lt hdenomPos)
  have hfinal : (Pset.ncard : ℝ) ≤
      C * (x / (n * Real.log x) + xpow) := by
    calc
      _ ≤ Cf * (x / (n * Real.log x)) + 2 * Cf * Ca * xpow := hcountExpanded
      _ = Cf * (x / (n * Real.log x)) + (2 * Cf * Ca) * xpow := by ring
      _ ≤ C * (x / (n * Real.log x)) + C * xpow := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hcoeffFirst hxdivNonneg)
          (mul_le_mul_of_nonneg_right hcoeffSecond (le_of_lt hxpowPos))
      _ = C * (x / (n * Real.log x) + xpow) := by ring
  simpa [Pset, n, xpow] using hfinal

end ArtinPrimitiveRoots.Splitting

end
