import Mathlib
import PrimeNumberTheoremAnd.Erdos970.MertensClassical

/-! Prime estimates for the density comparison, using the frozen Type II inputs. -/

namespace ArtinPrimitiveRoots.Proofs.b_density_sol

open MeasureTheory Filter
open scoped Topology

/-- Reciprocal-prime mass up to a real cutoff. -/
noncomputable def primeReciprocalSumLE (y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, 1 / (p : ℝ)

/-- The integer interval used in the sieve comparison, represented by its natural endpoints. -/
noncomputable def roughIntegerInterval (x : ℝ) : Finset ℕ :=
  Finset.Icc (⌊x⌋₊ + 1) ⌊2 * x⌋₊

/-- The primes up to the sieve level `z`. -/
noncomputable def roughSievePrimes (z : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊z⌋₊).filter Nat.Prime

lemma roughSievePrimes_eq_Ioc (z : ℝ) :
    roughSievePrimes z = (Finset.Ioc 0 ⌊z⌋₊).filter Nat.Prime := by
  ext p
  simp only [roughSievePrimes, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h2, hz⟩, hp⟩
    exact ⟨⟨by omega, hz⟩, hp⟩
  · rintro ⟨⟨_, hz⟩, hp⟩
    exact ⟨⟨hp.two_le, hz⟩, hp⟩

/-- The reciprocal error has a limit; a quantitative error rate is unnecessary. -/
lemma exists_tendsto_primeReciprocalMertens_error :
    ∃ M : ℝ, Tendsto (fun y : ℝ =>
      primeReciprocalSumLE y - Real.log (Real.log y) - M) atTop (𝓝 0) := by
  refine ⟨Erdos970.Mertens.M, ?_⟩
  have hE : Tendsto Erdos970.Mertens.E₂p atTop (𝓝 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Erdos970.Mertens.E₂p.bound'
  apply hE.congr'
  filter_upwards [] with y
  change Erdos970.Mertens.E₂p y =
    (∑ p ∈ roughSievePrimes y, 1 / (p : ℝ)) -
      Real.log (Real.log y) - Erdos970.Mertens.M
  rw [roughSievePrimes_eq_Ioc]

/-- The prime product has the classical normalized constant. -/
lemma primeProductMertens :
    Tendsto (fun x : ℝ => Real.log x *
      ∏ p ∈ roughSievePrimes x, (1 - 1 / (p : ℝ)))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hE : Tendsto Erdos970.Mertens.E₃ atTop (𝓝 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Erdos970.Mertens.E₃.bound'
  have hexp : Tendsto (fun y => Real.exp (Erdos970.Mertens.E₃ y))
      atTop (𝓝 1) := by
    change Tendsto (Real.exp ∘ Erdos970.Mertens.E₃) atTop (𝓝 1)
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hE
  have hbase : Tendsto (fun y => Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Erdos970.Mertens.E₃ y)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa using hexp.const_mul (Real.exp (-Real.eulerMascheroniConstant))
  apply hbase.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  rw [roughSievePrimes_eq_Ioc, Erdos970.Mertens.prod_one_minus_div_prime_eq hy]
  have hlog : Real.log y ≠ 0 := (Real.log_pos hy).ne'
  field_simp [hlog]
  <;> ring

lemma tendsto_roughSieveProduct_scaled {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.log x *
      ∏ p ∈ roughSievePrimes (Real.rpow x b), (1 - 1 / (p : ℝ))) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / b)) := by
  let V : ℝ → ℝ := fun x =>
    ∏ p ∈ roughSievePrimes (Real.rpow x b), (1 - 1 / (p : ℝ))
  have hmertens := primeProductMertens.comp (tendsto_rpow_atTop hb)
  have hmain : Tendsto (fun x : ℝ => (1 / b) *
      (Real.log (Real.rpow x b) * V x)) atTop
      (𝓝 ((1 / b) * Real.exp (-Real.eulerMascheroniConstant))) :=
    tendsto_const_nhds.mul hmertens
  have hlogPow (x : ℝ) (hx : 0 < x) :
      Real.log (Real.rpow x b) = b * Real.log x := Real.log_rpow hx b
  have heq : ∀ᶠ x : ℝ in atTop,
      Real.log x * V x = (1 / b) * (Real.log (Real.rpow x b) * V x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [hlogPow x hx]
    field_simp [ne_of_gt hb]
    <;> ring
  have hscaled : Tendsto (fun x : ℝ => Real.log x * V x) atTop
      (𝓝 ((1 / b) * Real.exp (-Real.eulerMascheroniConstant))) :=
    hmain.congr' (heq.mono fun x h => h.symm)
  simpa [V, roughSievePrimes, div_eq_mul_inv, mul_comm] using hscaled

lemma tendsto_log_mul_rpow_sub_one {α : ℝ} (hα : α < 1) :
    Tendsto (fun x : ℝ => Real.log x * Real.rpow x (α - 1)) atTop (𝓝 0) := by
  have hsmall :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hα)).tendsto_div_nhds_zero
  have heq : ∀ᶠ x : ℝ in atTop,
      Real.log x * Real.rpow x (α - 1) =
        Real.log x / Real.rpow x (1 - α) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show α - 1 = -(1 - α) by ring]
    have hpow : Real.rpow x (-(1 - α)) = (Real.rpow x (1 - α))⁻¹ :=
      Real.rpow_neg hx.le (1 - α)
    rw [hpow, div_eq_mul_inv]
  exact hsmall.congr' (heq.mono fun x h => h.symm)

/-- Reciprocal-prime mass between the logarithmic cutoffs `x^a` and `x^b`. -/
noncomputable def primeReciprocalBand (x a b : ℝ) : ℝ :=
  ∑ p ∈ (roughSievePrimes (Real.rpow x b)).filter
      (fun p : ℕ => Real.rpow x a < (p : ℝ)),
    1 / (p : ℝ)

/-- Mertens' theorem gives the limiting reciprocal-prime mass of every fixed exponent band. -/
lemma tendsto_primeReciprocalBand {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ => primeReciprocalBand x a b) atTop
      (𝓝 (Real.log (b / a))) := by
  have hb : 0 < b := lt_trans ha hab
  obtain ⟨M, hM⟩ := exists_tendsto_primeReciprocalMertens_error
  let E : ℝ → ℝ := fun y => primeReciprocalSumLE y - Real.log (Real.log y) - M
  have hE : Tendsto E atTop (𝓝 0) := by simpa [E] using hM
  have haPow : Tendsto (fun x : ℝ => Real.rpow x a) atTop atTop :=
    tendsto_rpow_atTop ha
  have hbPow : Tendsto (fun x : ℝ => Real.rpow x b) atTop atTop :=
    tendsto_rpow_atTop hb
  have hEa := hE.comp haPow
  have hEb := hE.comp hbPow
  have hconst : Tendsto (fun _ : ℝ => Real.log (b / a)) atTop
      (𝓝 (Real.log (b / a))) := tendsto_const_nhds
  have hlimit : Tendsto (fun x : ℝ => Real.log (b / a) +
      (E (Real.rpow x b) - E (Real.rpow x a))) atTop (𝓝 (Real.log (b / a))) := by
    simpa using hconst.add (hEb.sub hEa)
  have hEq : ∀ᶠ x : ℝ in atTop,
      primeReciprocalBand x a b = Real.log (b / a) +
        (E (Real.rpow x b) - E (Real.rpow x a)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    let y₁ := Real.rpow x a
    let y₂ := Real.rpow x b
    let P₁ := roughSievePrimes y₁
    let P₂ := roughSievePrimes y₂
    let B := P₂.filter (fun p : ℕ => y₁ < (p : ℝ))
    have hxpos : 0 < x := by linarith
    have hxone : 1 ≤ x := by linarith
    have hy₁ : 0 ≤ y₁ := Real.rpow_nonneg hxpos.le a
    have hy₁₂ : y₁ ≤ y₂ := Real.rpow_le_rpow_of_exponent_le hxone hab.le
    have hfloor : ⌊y₁⌋₊ ≤ ⌊y₂⌋₊ := Nat.floor_mono hy₁₂
    have hlow : P₂.filter (fun p : ℕ => (p : ℝ) ≤ y₁) = P₁ := by
      ext p
      simp only [P₂, P₁, roughSievePrimes, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hp2, hpf₂⟩, hpPrime⟩, hpLE⟩
        refine ⟨⟨hp2, ?_⟩, hpPrime⟩
        exact (Nat.le_floor_iff hy₁).2 hpLE
      · rintro ⟨⟨hp2, hpf₁⟩, hpPrime⟩
        refine ⟨⟨⟨hp2, le_trans hpf₁ hfloor⟩, hpPrime⟩, ?_⟩
        exact le_trans (Nat.cast_le.mpr hpf₁) (Nat.floor_le hy₁)
    have hsplit :
        (∑ p ∈ B, 1 / (p : ℝ)) + primeReciprocalSumLE y₁ =
          primeReciprocalSumLE y₂ := by
      have hsplit' := Finset.sum_filter_add_sum_filter_not P₂
        (fun p : ℕ => y₁ < (p : ℝ)) (fun p : ℕ => 1 / (p : ℝ))
      simpa [B, P₁, P₂, roughSievePrimes, primeReciprocalSumLE, hlow, not_lt] using hsplit'
    have hformula :
        (∑ p ∈ B, 1 / (p : ℝ)) =
          Real.log (Real.log y₂) - Real.log (Real.log y₁) + E y₂ - E y₁ := by
      dsimp [E] at hsplit ⊢
      linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogy₁ : Real.log y₁ = a * Real.log x := by
      simp [y₁, Real.log_rpow hxpos]
    have hlogy₂ : Real.log y₂ = b * Real.log x := by
      simp [y₂, Real.log_rpow hxpos]
    have hlogdiff :
        Real.log (Real.log y₂) - Real.log (Real.log y₁) = Real.log (b / a) := by
      rw [hlogy₁, hlogy₂]
      calc
        Real.log (b * Real.log x) - Real.log (a * Real.log x) =
            Real.log b - Real.log a := by
              rw [Real.log_mul hb.ne' hlogx.ne', Real.log_mul ha.ne' hlogx.ne']
              ring
        _ = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
    rw [primeReciprocalBand, hformula, hlogdiff]
    ring
  exact hlimit.congr' (hEq.mono fun x hx => hx.symm)

/-- Finite products of reciprocal-prime exponent-band masses converge to the corresponding
product measure. -/
lemma tendsto_primeReciprocalBand_prod {k : ℕ} (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) :
    Tendsto (fun x : ℝ => ∏ i : Fin k, primeReciprocalBand x (a i) (b i)) atTop
      (𝓝 (∏ i : Fin k, Real.log (b i / a i))) := by
  apply tendsto_finsetProd Finset.univ
  intro i hi
  exact tendsto_primeReciprocalBand (ha i) (hab i)

/-- Prime count in the dyadic interval `(y,2y]`. -/
noncomputable def primeDyadicCount (y : ℝ) : ℝ :=
  ((Nat.primeCounting ⌊2 * y⌋₊ - Nat.primeCounting ⌊y⌋₊ : ℕ) : ℝ)

/-- The primes in `(y,2y]`, represented by natural endpoints. -/
noncomputable def primeDyadicPrimes (y : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊2 * y⌋₊ \ Nat.primesLE ⌊y⌋₊

/-- The cardinality of the natural prime interval agrees with `primeDyadicCount`. -/
lemma primeDyadicPrimes_card (y : ℝ) (hy : 0 ≤ y) :
    ((primeDyadicPrimes y).card : ℝ) = primeDyadicCount y := by
  let lo := ⌊y⌋₊
  let hi := ⌊2 * y⌋₊
  have hfloor : lo ≤ hi := by
    dsimp [lo, hi]
    apply Nat.floor_mono
    nlinarith
  have hsub : Nat.primesLE lo ⊆ Nat.primesLE hi :=
    Nat.primesLE_mono hfloor
  have hset :
      Nat.primesLE hi \ Nat.primesLE lo = (Finset.Ioc lo hi).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hhi, hp⟩, hnlo⟩
      refine ⟨⟨?_, hhi⟩, hp⟩
      by_contra hnot
      exact hnlo ⟨le_of_not_gt hnot, hp⟩
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      refine ⟨⟨hhi, hp⟩, ?_⟩
      rintro ⟨hlo', _⟩
      exact (not_le_of_gt hlo) hlo'
  have hcard :
      ((Nat.primesLE hi \ Nat.primesLE lo).card : ℝ) =
        ((Nat.primeCounting hi - Nat.primeCounting lo : ℕ) : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub]
    rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hcard' :
      (((Finset.Ioc lo hi).filter Nat.Prime).card : ℝ) =
        ((Nat.primeCounting hi - Nat.primeCounting lo : ℕ) : ℝ) := by
    rw [← hset]
    exact hcard
  rw [primeDyadicPrimes, hset]
  simpa [primeDyadicCount, lo, hi] using hcard'

lemma primeDyadicPrimes_mem {y : ℝ} (hy : 0 ≤ y) {p : ℕ}
    (hp : p ∈ primeDyadicPrimes y) :
    p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y := by
  have hp' := Finset.mem_sdiff.mp hp
  have hhi : p ∈ Nat.primesLE ⌊2 * y⌋₊ := hp'.1
  have hhi' := Nat.mem_primesLE.mp hhi
  have hprime : p.Prime := hhi'.2
  have hnot : p ∉ Nat.primesLE ⌊y⌋₊ := hp'.2
  have hfloor : ⌊y⌋₊ < p := by
    by_contra h
    exact hnot (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt h, hprime⟩)
  have hylt : y < (p : ℝ) := (Nat.floor_lt hy).1 hfloor
  have hpcast : (p : ℝ) ≤ (⌊2 * y⌋₊ : ℝ) := Nat.cast_le.mpr hhi'.1
  have hfloor2 : (⌊2 * y⌋₊ : ℝ) ≤ 2 * y := Nat.floor_le (mul_nonneg (by norm_num) hy)
  exact ⟨hprime, hylt, hpcast.trans hfloor2⟩

/-- The dyadic PNT required by the comparison, isolated from downstream Type II definitions. -/
def DyadicPrimeInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y →
    |primeDyadicCount y - y / Real.log y| ≤ ε * y / Real.log y

/-- A dyadic PNT input directly supplies the lower estimate. -/
lemma eventually_primeDyadicCount_lower (hPNT : DyadicPrimeInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, (1 - ε) * y / Real.log y ≤ primeDyadicCount y := by
  obtain ⟨Y, _, hY⟩ := hPNT ε hε
  filter_upwards [eventually_ge_atTop Y] with y hy
  have hlow := (abs_le.mp (hY y hy)).1
  rw [show (1 - ε) * y / Real.log y =
    y / Real.log y - ε * y / Real.log y by ring]
  linarith

/-- The dyadic PNT lower bound holds uniformly for all interval bases above `x^η`. -/
lemma eventually_uniform_primeDyadicCount_lower (hPNT : DyadicPrimeInput) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, Real.rpow x η ≤ y →
      (1 - ε) * y / Real.log y ≤ primeDyadicCount y := by
  obtain ⟨Y, hY⟩ := eventually_atTop.1 (eventually_primeDyadicCount_lower hPNT hε)
  filter_upwards [(tendsto_rpow_atTop hη).eventually_ge_atTop Y] with x hx
  intro y hy
  exact hY y (le_trans hx hy)

/-- Prime values whose logarithmic exponents lie in a fixed half-open band. -/
noncomputable def primeExponentBand (x a b : ℝ) : Finset ℕ :=
  (roughSievePrimes (Real.rpow x b)).filter (fun p : ℕ => Real.rpow x a < (p : ℝ))

lemma primeExponentBand_mem {x a b : ℝ} {p : ℕ} (hx : 0 ≤ x)
    (hp : p ∈ primeExponentBand x a b) :
    p.Prime ∧ Real.rpow x a < (p : ℝ) ∧ (p : ℝ) ≤ Real.rpow x b := by
  simp only [primeExponentBand, roughSievePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
  refine ⟨hp.1.2, hp.2, ?_⟩
  exact (Nat.cast_le.mpr hp.1.1.2).trans (Nat.floor_le (Real.rpow_nonneg hx _))

/-- One constant bounds the reciprocal-prime mass in every multiplicative band. -/
lemma exists_prime_reciprocal_band_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ v : ℝ, 1 < v →
      ∑ p ∈ ((Finset.Icc 2 ⌊v ^ 2⌋₊).filter Nat.Prime).filter
        (fun p : ℕ => v < (p : ℝ)), 1 / (p : ℝ) ≤ C₀ := by
  classical
  have hlim : Tendsto (fun v : ℝ =>
      ∑ p ∈ ((Finset.Icc 2 ⌊v ^ 2⌋₊).filter Nat.Prime).filter
        (fun p : ℕ => v < (p : ℝ)), 1 / (p : ℝ))
      atTop (𝓝 (Real.log 2)) := by
    simpa [primeReciprocalBand, roughSievePrimes, Real.rpow_two] using
      (tendsto_primeReciprocalBand (a := 1) (b := 2) (by norm_num) (by norm_num))
  have hev := hlim.eventually (Iio_mem_nhds (by linarith : Real.log 2 < Real.log 2 + 1))
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hev
  let Y : ℝ := max 2 Y₀
  let C₀ : ℝ := max (primeReciprocalSumLE (Y ^ 2)) (Real.log 2 + 1)
  have hY : 2 ≤ Y := le_max_left _ _
  have hC₀ : 0 < C₀ := by
    exact lt_of_lt_of_le (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
      (le_max_right _ _)
  refine ⟨C₀, hC₀, ?_⟩
  intro v hv
  by_cases hvY : Y ≤ v
  · have hbound := hY₀ v ((le_max_right 2 Y₀).trans hvY)
    exact (le_of_lt hbound).trans (le_max_right _ _)
  · have hvY' : v ≤ Y := (lt_of_not_ge hvY).le
    have hsq : v ^ 2 ≤ Y ^ 2 := by
      simpa [pow_two] using
        (mul_le_mul hvY' hvY' (by linarith : 0 ≤ v) (by linarith : 0 ≤ Y))
    have hfloor := Nat.floor_mono hsq
    have hsub :
        (((Finset.Icc 2 ⌊v ^ 2⌋₊).filter Nat.Prime).filter
          (fun p : ℕ => v < (p : ℝ))) ⊆
        (Finset.Icc 2 ⌊Y ^ 2⌋₊).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1.1, hp.1.1.2.trans hfloor⟩, hp.1.2⟩
    have hbound :
        (∑ p ∈ ((Finset.Icc 2 ⌊v ^ 2⌋₊).filter Nat.Prime).filter
          (fun p : ℕ => v < (p : ℝ)), 1 / (p : ℝ)) ≤
        primeReciprocalSumLE (Y ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _
      exact one_div_nonneg.mpr (Nat.cast_nonneg p)
    exact hbound.trans (le_max_left _ _)

end ArtinPrimitiveRoots.Proofs.b_density_sol
