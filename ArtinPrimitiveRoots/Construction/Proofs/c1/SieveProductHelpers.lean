import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.c1.SupportHelpers
import OAI.NumberTheory.PrimeGaps.SingularSeries

set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.Construction

open Classical
open Filter
open ArtinPrimitiveRoots.TypeII
open scoped Topology

noncomputable def twinEulerFactor (p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

private lemma pair_residue_count {p : ℕ} (hp : p.Prime) (h2 : 2 < p) :
    OAI.LargePrimeGaps.residueCount ({0, 2} : Finset ℤ) p = 2 := by
  have hrem : (0 : ℤ) % (p : ℤ) ≠ (2 : ℤ) % (p : ℤ) := by
    intro he
    have hzero : ((0 : ℤ) - 2) % (p : ℤ) = 0 :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he
    have hd : (p : ℤ) ∣ (0 : ℤ) - 2 := Int.dvd_of_emod_eq_zero hzero
    have hdNat : p ∣ 2 := by
      have hnat := Int.natAbs_dvd_natAbs.mpr hd
      simpa using hnat
    have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdNat
    omega
  unfold OAI.LargePrimeGaps.residueCount
  have hinj : Set.InjOn (fun z : ℤ => z % (p : ℤ)) ({0, 2} : Finset ℤ) := by
    intro z hz w hw he
    have hz' : z = 0 ∨ z = 2 := by
      have hz'' : z ∈ ({0, 2} : Finset ℤ) := Finset.mem_coe.mp hz
      simpa using hz''
    have hw' : w = 0 ∨ w = 2 := by
      have hw'' : w ∈ ({0, 2} : Finset ℤ) := Finset.mem_coe.mp hw
      simpa using hw''
    rcases hz' with rfl | rfl <;> rcases hw' with rfl | rfl
    · rfl
    · exact False.elim (hrem he)
    · exact False.elim (hrem he.symm)
    · rfl
  rw [Finset.card_image_of_injOn hinj]
  norm_num

private lemma pair_singular_local (p : Nat.Primes) :
    OAI.LargePrimeGaps.singularLocal ({0, 2} : Finset ℤ) p =
      if p.val = 2 then 2 else twinEulerFactor p.val := by
  by_cases h2 : p.val = 2
  · have hpEq : p = ⟨2, Nat.prime_two⟩ := Subtype.ext h2
    subst p
    norm_num [twinEulerFactor, OAI.LargePrimeGaps.singularLocal,
      OAI.LargePrimeGaps.residueCount]
  · have hp := p.property
    have hgt : 2 < p.val := by have := hp.two_le; omega
    rw [OAI.LargePrimeGaps.singularLocal, pair_residue_count hp hgt]
    have hpR : (2 : ℝ) < (p.val : ℝ) := by exact_mod_cast hgt
    have hp0 : (p.val : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hp1 : (p.val : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    simp [twinEulerFactor, hp, hgt, h2]
    field_simp [hp0, hp1]
    <;> ring

private lemma twinEulerFactor_lower (n : ℕ) : (3 / 4 : ℝ) ≤ twinEulerFactor n := by
  by_cases h : n.Prime ∧ 2 < n
  · have hn3 : 3 ≤ n := by omega
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hsquare : (4 : ℝ) ≤ ((n : ℝ) - 1) ^ 2 := by nlinarith [hnR]
    have hinv : 1 / ((n : ℝ) - 1) ^ 2 ≤ (1 / 4 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hsquare
    rw [twinEulerFactor, if_pos h]
    nlinarith [hinv]
  · rw [twinEulerFactor, if_neg h]
    norm_num

private lemma twinEulerFactor_diff_summable :
    Summable (fun n : ℕ => twinEulerFactor n - 1) := by
  let loc (n : ℕ) := OAI.LargePrimeGaps.singularLocal ({0, 2} : Finset ℤ) n
  let d (n : ℕ) := if n.Prime then loc n - 1 else 0
  have hd : Summable d := by
    simpa [d, loc] using
      (OAI.LargePrimeGaps.singularLocal_summable_error ({0, 2} : Finset ℤ))
  have hdnorm := hd.norm
  apply hdnorm.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  by_cases hp : n.Prime
  · have hlocal : loc n = twinEulerFactor n := by
      have h := pair_singular_local (⟨n, hp⟩ : Nat.Primes)
      have hn2 : n ≠ 2 := by omega
      simpa [loc, hn2] using h
    simp [d, hp, hlocal]
  · simp [d, hp, twinEulerFactor]

private lemma twinEulerFactor_multipliable : Multipliable twinEulerFactor := by
  have h := Real.multipliable_one_add_of_summable twinEulerFactor_diff_summable
  have heq : (fun n : ℕ => 1 + (twinEulerFactor n - 1)) = twinEulerFactor := by
    funext n
    ring
  rw [heq] at h
  exact h

private lemma twinPartial_tendsto :
    Tendsto (fun y : ℝ => ∏ p ∈ primesUpTo y, twinEulerFactor p) atTop
      (𝓝 (∏' n : ℕ, twinEulerFactor n)) := by
  have hindex : Tendsto (fun y : ℝ => ⌊y⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun y => by omega) tendsto_nat_floor_atTop
  have hprod : Tendsto (fun k : ℕ => ∏ n ∈ Finset.range k, twinEulerFactor n) atTop
      (𝓝 (∏' n : ℕ, twinEulerFactor n)) :=
    twinEulerFactor_multipliable.tendsto_prod_tprod_nat
  have hcomp := hprod.comp hindex
  have hfinite (y : ℝ) :
      (∏ p ∈ primesUpTo y, twinEulerFactor p) =
        ∏ n ∈ Finset.range (⌊y⌋₊ + 1), twinEulerFactor n := by
    unfold primesUpTo
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp [hp, twinEulerFactor]
    · simp [hp, twinEulerFactor]
  exact hcomp.congr' (Filter.Eventually.of_forall fun y => (hfinite y).symm)

private noncomputable def progressionFactor (M p : ℕ) : ℝ :=
  if 2 < p ∧ ¬ p ∣ M then 1 - 1 / ((p : ℝ) - 1) else 1

private noncomputable def roughFactor (p : ℕ) : ℝ := 1 - 1 / (p : ℝ)

private noncomputable def correctionFactor (M p : ℕ) : ℝ :=
  if p ∣ M ∧ 2 < p then (1 - 1 / ((p : ℝ) - 1))⁻¹ else 1

private noncomputable def twoFactor (p : ℕ) : ℝ := if p = 2 then 2 else 1

private noncomputable def twinPartial (y : ℝ) : ℝ :=
  ∏ p ∈ primesUpTo y, twinEulerFactor p

private noncomputable def correctionPartial (M : ℕ) (y : ℝ) : ℝ :=
  ∏ p ∈ primesUpTo y, correctionFactor M p

private noncomputable def correctionFull (M : ℕ) : ℝ :=
  ∏ p ∈ (primesUpTo (M : ℝ)).filter (fun p => p ∣ M ∧ 2 < p),
    (1 - 1 / ((p : ℝ) - 1))⁻¹

private lemma progressionFactor_identity (M p : ℕ) (hp : p.Prime) :
    progressionFactor M p =
      twoFactor p * roughFactor p * twinEulerFactor p * correctionFactor M p := by
  by_cases htwo : p = 2
  · subst p
    simp [progressionFactor, twoFactor, roughFactor, twinEulerFactor, correctionFactor,
      Nat.prime_two]
    norm_num
  · have hgt : 2 < p := by have hp₂ := hp.two_le; omega
    have hpR : (2 : ℝ) < p := by exact_mod_cast hgt
    have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    have hp2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
    have hp2add : -2 + (p : ℝ) ≠ 0 := by linarith
    have hfactor : 1 - 1 / ((p : ℝ) - 1) ≠ 0 := by
      have hlt : 1 / ((p : ℝ) - 1) < 1 :=
        (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2 (by linarith)
      linarith
    have hfactorInv : 1 - ((p : ℝ) - 1)⁻¹ ≠ 0 := by
      simpa [one_div] using hfactor
    have hbaseDiv : 1 - 1 / ((p : ℝ) - 1) =
        (1 - 1 / (p : ℝ)) * (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
      field_simp [hp0, hp1, hp2]
      <;> ring
    have hbase : 1 - ((p : ℝ) - 1)⁻¹ =
        (1 - (p : ℝ)⁻¹) * (1 - (((p : ℝ) - 1) ^ 2)⁻¹) := by
      simpa only [one_div] using hbaseDiv
    by_cases hdiv : p ∣ M
    · simp [progressionFactor, twoFactor, roughFactor, twinEulerFactor,
        correctionFactor, htwo, hgt, hp, hdiv]
      rw [← hbase]
      exact (mul_inv_cancel₀ hfactorInv).symm
    · simp [progressionFactor, twoFactor, roughFactor, twinEulerFactor,
        correctionFactor, htwo, hgt, hp, hdiv]
      exact hbase

private noncomputable def progressionForFactor (M r p : ℕ) : ℝ :=
  if 2 < p then 1 - localSieveDensity M r p else 1

private noncomputable def rExtraFactor (M r p : ℕ) : ℝ :=
  if p ∣ r ∧ ¬ p ∣ M ∧ 2 < p then (1 - 1 / ((p : ℝ) - 1))⁻¹ else 1

noncomputable def rExtraPartial (M r : ℕ) (y : ℝ) : ℝ :=
  ∏ p ∈ primesUpTo y, rExtraFactor M r p

noncomputable def rExtraFull (M r : ℕ) : ℝ :=
  ∏ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ M ∧ 2 < p),
    (1 - 1 / ((p : ℝ) - 1))⁻¹

private lemma localSieveDensity_prime (M r p : ℕ) (hp : p.Prime) :
    localSieveDensity M r p =
      if p ∣ M ∨ p ∣ r then 0 else 1 / ((p : ℝ) - 1) := by
  by_cases hM : p ∣ M
  · have hnot : ¬ Nat.Coprime p (M * r) := by
      intro hcop
      exact (hp.coprime_iff_not_dvd.mp hcop) (dvd_mul_of_dvd_left hM r)
    simp [localSieveDensity, hM, hnot]
  · by_cases hr : p ∣ r
    · have hnot : ¬ Nat.Coprime p (M * r) := by
        intro hcop
        exact (hp.coprime_iff_not_dvd.mp hcop) (dvd_mul_of_dvd_right hr M)
      simp [localSieveDensity, hM, hr, hnot]
    · have hcop : Nat.Coprime p (M * r) := by
        rw [hp.coprime_iff_not_dvd]
        intro hprod
        rcases hp.dvd_mul.mp hprod with h | h
        · exact hM h
        · exact hr h
      simp [localSieveDensity, hM, hr, hcop, Nat.totient_prime hp,
        Nat.cast_sub hp.one_le]

private lemma progressionForFactor_identity (M r p : ℕ) (hp : p.Prime) :
    progressionForFactor M r p = progressionFactor M p * rExtraFactor M r p := by
  by_cases htwo : p = 2
  · subst p
    simp [progressionForFactor, progressionFactor, rExtraFactor]
  · have hgt : 2 < p := by have hp₂ := hp.two_le; omega
    have hpR : (2 : ℝ) < p := by exact_mod_cast hgt
    have hbase : 0 < 1 - 1 / ((p : ℝ) - 1) := by
      have hlt : 1 / ((p : ℝ) - 1) < 1 :=
        (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2 (by linarith)
      linarith
    have hbaseInv : 1 - ((p : ℝ) - 1)⁻¹ ≠ 0 := by
      simpa [one_div] using hbase.ne'
    by_cases hM : p ∣ M
    · unfold progressionForFactor
      rw [if_pos hgt, localSieveDensity_prime M r p hp]
      simp [progressionFactor, rExtraFactor, htwo, hgt, hM]
    · by_cases hr : p ∣ r
      · unfold progressionForFactor
        rw [if_pos hgt, localSieveDensity_prime M r p hp]
        simp [progressionFactor, rExtraFactor, htwo, hgt, hM, hr]
        exact (mul_inv_cancel₀ hbaseInv).symm
      · unfold progressionForFactor
        rw [if_pos hgt, localSieveDensity_prime M r p hp]
        simp [progressionFactor, rExtraFactor, htwo, hgt, hM, hr]

theorem progressionSieveProductFor_factorization (M r : ℕ) {y : ℝ} :
    progressionSieveProductFor M r y =
      progressionSieveProduct M y * rExtraPartial M r y := by
  let S := primesUpTo y
  have hfor : progressionSieveProductFor M r y =
      ∏ p ∈ S, progressionForFactor M r p := by
    unfold progressionSieveProductFor progressionForFactor
    rw [Finset.prod_filter]
  have hprog : progressionSieveProduct M y =
      ∏ p ∈ S, progressionFactor M p := by
    unfold progressionSieveProduct progressionFactor
    rw [Finset.prod_filter]
  have hlocal : ∀ p ∈ S,
      progressionForFactor M r p = progressionFactor M p * rExtraFactor M r p := by
    intro p hp
    have hpPrime : p.Prime := by
      change p ∈ primesUpTo y at hp
      unfold primesUpTo at hp
      exact (Finset.mem_filter.mp hp).2
    exact progressionForFactor_identity M r p hpPrime
  rw [hfor]
  calc
    _ = ∏ p ∈ S, (progressionFactor M p * rExtraFactor M r p) :=
      Finset.prod_congr rfl (fun p hp => hlocal p hp)
    _ = (∏ p ∈ S, progressionFactor M p) * (∏ p ∈ S, rExtraFactor M r p) :=
      Finset.prod_mul_distrib
    _ = progressionSieveProduct M y * rExtraPartial M r y := by
      rw [hprog]
      rfl

theorem rExtraPartial_le_full {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {r M : ℕ} {y : ℝ}
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x) (ha : ValidBands K a)
    (hr : IsGroupInteger x K a r) :
    rExtraPartial M r y ≤ rExtraFull M r := by
  have hnot2 : 2 ∉ markedPrimes x K a := by
    intro htwo
    have hs := markedPrime_scale_bounds hxpos hL ha htwo
    have hslo := hs.1
    norm_num at hslo
  have hrne : r ≠ 0 := by
    intro hr0
    apply hnot2
    have hdiv : 2 ∣ r := by simpa [hr0] using (dvd_zero 2)
    exact hr 2 Nat.prime_two hdiv
  let S := (primesUpTo y).filter (fun p => p ∣ r ∧ ¬ p ∣ M ∧ 2 < p)
  have hpartial : rExtraPartial M r y =
      ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    unfold rExtraPartial rExtraFactor
    rw [Finset.prod_filter]
  have hsub : S ⊆ r.primeFactors.filter (fun p => ¬ p ∣ M ∧ 2 < p) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSet, ⟨hpDiv, hpM, hp2⟩⟩
    have hpPrime : p.Prime := by
      have hpSet' := (Finset.mem_filter.mp hpSet).2
      exact hpSet'
    have hpf : p ∈ r.primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero hrne).mpr ⟨hpPrime, hpDiv⟩
    exact Finset.mem_filter.mpr ⟨hpf, ⟨hpM, hp2⟩⟩
  have hmono :
      (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
        ∏ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ M ∧ 2 < p),
          (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    · intro p hp
      have hpCond := (Finset.mem_filter.mp hp).2
      have hpR : (2 : ℝ) < p := by exact_mod_cast hpCond.2.2
      have hbasePos : 0 < 1 - 1 / ((p : ℝ) - 1) := by
        have hlt : 1 / ((p : ℝ) - 1) < 1 :=
          (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2 (by linarith)
        linarith
      exact (inv_pos.mpr hbasePos).le
    · intro p hp hpnot
      have hp2 := (Finset.mem_filter.mp hp).2.2
      have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
      have hbasePos : 0 < 1 - 1 / ((p : ℝ) - 1) := by
        have hlt : 1 / ((p : ℝ) - 1) < 1 :=
          (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2 (by linarith)
        linarith
      have hbaseLe : 1 - 1 / ((p : ℝ) - 1) ≤ 1 := by
        have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) :=
          div_nonneg (by norm_num) (by linarith)
        linarith
      exact (one_le_inv₀ hbasePos).2 hbaseLe
  rw [hpartial]
  exact hmono

private lemma correctionLog_tail_eventually {β : ℝ} (hβ : 1 / 10 < β) :
    ∀ᶠ L : ℝ in atTop,
      (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) *
        Real.exp (-Real.rpow L β + Real.rpow L (1 / 10 : ℝ)) < 1 / 2 := by
  have hβpos : 0 < β := lt_trans (by norm_num) hβ
  have hratio : Tendsto (fun L : ℝ => Real.rpow L (1 / 10 - β)) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg] using tendsto_rpow_neg_atTop (sub_pos.mpr hβ)
  have hratioEvent : ∀ᶠ L : ℝ in atTop, Real.rpow L (1 / 10 - β) < 1 / 2 :=
    hratio.eventually (Iio_mem_nhds (by norm_num))
  let s := (9 / 10 : ℝ) / β
  have hbase : Tendsto (fun L : ℝ => Real.rpow L β) atTop atTop :=
    tendsto_rpow_atTop hβpos
  have hdecay : Tendsto (fun L : ℝ =>
      Real.rpow (Real.rpow L β) s * Real.exp (-(1 / 2 : ℝ) * Real.rpow L β))
      atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (1 / 2 : ℝ) (by norm_num)).comp hbase
  have hpowEq : ∀ᶠ L : ℝ in atTop,
      Real.rpow (Real.rpow L β) s = Real.rpow L (9 / 10 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hLpos
    have hs : β * s = (9 / 10 : ℝ) := by
      dsimp [s]
      field_simp [ne_of_gt hβpos]
    calc
      Real.rpow (Real.rpow L β) s = Real.rpow L (β * s) :=
        (Real.rpow_mul hLpos.le β s).symm
      _ = Real.rpow L (9 / 10 : ℝ) := by rw [hs]
  have hdecayScaled : Tendsto (fun L : ℝ =>
      (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * Real.rpow L β)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => (11 / 50 : ℝ)) atTop (𝓝 (11 / 50 : ℝ)) :=
      tendsto_const_nhds
    have h : Tendsto (fun L : ℝ => (11 / 50 : ℝ) *
        (Real.rpow (Real.rpow L β) s * Real.exp (-(1 / 2 : ℝ) * Real.rpow L β)))
        atTop (𝓝 0) := by
      simpa using hconst.mul hdecay
    have heq : (fun L : ℝ => (11 / 50 : ℝ) *
        (Real.rpow (Real.rpow L β) s * Real.exp (-(1 / 2 : ℝ) * Real.rpow L β))) =ᶠ[atTop]
        (fun L => (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * Real.rpow L β)) := by
      filter_upwards [hpowEq] with L hLpow
      rw [hLpow]
      ring
    exact h.congr' heq
  have hdecayEvent : ∀ᶠ L : ℝ in atTop,
      (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * Real.rpow L β) < 1 / 2 :=
    hdecayScaled.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hratioEvent, hdecayEvent]
    with L hLone hratioL hdecayL
  have hLpos : 0 < L := by linarith
  have hpowSub : Real.rpow L (1 / 10 - β) =
      Real.rpow L (1 / 10 : ℝ) / Real.rpow L β :=
    Real.rpow_sub hLpos (1 / 10 : ℝ) β
  have hpow : Real.rpow L (1 / 10 : ℝ) <
      (1 / 2 : ℝ) * Real.rpow L β := by
    have h := hratioL
    rw [hpowSub] at h
    exact (div_lt_iff₀ (Real.rpow_pos_of_pos hLpos β)).mp h
  have hexp : Real.exp (-Real.rpow L β + Real.rpow L (1 / 10 : ℝ)) ≤
      Real.exp (-(1 / 2 : ℝ) * Real.rpow L β) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    _ ≤ (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * Real.rpow L β) := by
          have hcoef : 0 ≤ (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) :=
            mul_nonneg (by norm_num)
              (Real.rpow_nonneg (le_of_lt hLpos) (9 / 10 : ℝ))
          exact mul_le_mul_of_nonneg_left hexp hcoef
    _ < 1 / 2 := hdecayL

private lemma progressionProduct_factorization (M : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    progressionSieveProduct M y =
      roughSieveProduct y * (2 * twinPartial y * correctionPartial M y) := by
  let S := primesUpTo y
  have htwoMem : 2 ∈ S := by
    have hyfloor : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
    change 2 ∈ primesUpTo y
    unfold primesUpTo
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hyfloor), Nat.prime_two⟩
  have htwoProd : (∏ p ∈ S, twoFactor p) = 2 := by
    calc
      _ = twoFactor 2 := Finset.prod_eq_single_of_mem 2 htwoMem
        (by
          intro p hp hne
          simp [twoFactor, hne])
      _ = 2 := by simp [twoFactor]
  have hprog : progressionSieveProduct M y = ∏ p ∈ S, progressionFactor M p := by
    unfold progressionSieveProduct progressionFactor
    rw [Finset.prod_filter]
  have hrough : roughSieveProduct y = ∏ p ∈ S, roughFactor p := by
    rfl
  have hlocal : ∀ p ∈ S,
      progressionFactor M p =
        twoFactor p * roughFactor p * twinEulerFactor p * correctionFactor M p := by
    intro p hp
    have hpPrime : p.Prime := by
      change p ∈ primesUpTo y at hp
      unfold primesUpTo at hp
      exact (Finset.mem_filter.mp hp).2
    exact progressionFactor_identity M p hpPrime
  rw [hprog]
  calc
    _ = ∏ p ∈ S,
        (twoFactor p * roughFactor p * twinEulerFactor p * correctionFactor M p) :=
          Finset.prod_congr rfl (fun p hp => hlocal p hp)
    _ = (∏ p ∈ S, twoFactor p) * (∏ p ∈ S, roughFactor p) *
          (∏ p ∈ S, twinEulerFactor p) * (∏ p ∈ S, correctionFactor M p) := by
            simp_rw [Finset.prod_mul_distrib]
    _ = roughSieveProduct y * (2 * twinPartial y * correctionPartial M y) := by
      rw [htwoProd, hrough]
      dsimp [twinPartial, correctionPartial]
      ring

private lemma twinEulerProduct_pos : 0 < (∏' n : ℕ, twinEulerFactor n) := by
  have hdiff := twinEulerFactor_diff_summable
  have hInvBound : ∀ n, ‖(twinEulerFactor n)⁻¹ - 1‖ ≤
      (4 / 3 : ℝ) * ‖twinEulerFactor n - 1‖ := by
    intro n
    have hlower := twinEulerFactor_lower n
    have hpos : 0 < twinEulerFactor n := lt_of_lt_of_le (by norm_num) hlower
    have hinv : 1 / twinEulerFactor n ≤ (4 / 3 : ℝ) := by
      apply (div_le_iff₀ hpos).2
      nlinarith [hlower]
    have heq : (twinEulerFactor n)⁻¹ - 1 =
        -((twinEulerFactor n - 1) / twinEulerFactor n) := by
      field_simp [ne_of_gt hpos]
      ring
    rw [heq, norm_neg, norm_div]
    have hnorm : ‖twinEulerFactor n‖ = twinEulerFactor n := by
      rw [Real.norm_eq_abs, abs_of_pos hpos]
    rw [hnorm]
    calc
      ‖twinEulerFactor n - 1‖ / twinEulerFactor n =
          ‖twinEulerFactor n - 1‖ * (1 / twinEulerFactor n) := by ring
      _ ≤ ‖twinEulerFactor n - 1‖ * (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = (4 / 3 : ℝ) * ‖twinEulerFactor n - 1‖ := by ring
  have hInvDiff : Summable (fun n : ℕ => (twinEulerFactor n)⁻¹ - 1) := by
    apply (twinEulerFactor_diff_summable.norm.mul_left (4 / 3)).of_norm_bounded_eventually_nat
    exact Filter.Eventually.of_forall hInvBound
  have hprod := twinEulerFactor_multipliable
  have hInvProd : Multipliable (fun n : ℕ => (twinEulerFactor n)⁻¹) := by
    have h := Real.multipliable_one_add_of_summable hInvDiff
    have heq : (fun n : ℕ => 1 + ((twinEulerFactor n)⁻¹ - 1)) =
        fun n => (twinEulerFactor n)⁻¹ := by
      funext n
      ring
    rw [heq] at h
    exact h
  have hpoint : (fun n : ℕ => twinEulerFactor n * (twinEulerFactor n)⁻¹) =
      fun _ => (1 : ℝ) := by
    funext n
    exact mul_inv_cancel₀ (ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (twinEulerFactor_lower n)))
  have hprodOne : (∏' n : ℕ, twinEulerFactor n) *
      (∏' n : ℕ, (twinEulerFactor n)⁻¹) = 1 := by
    rw [← hprod.tprod_mul hInvProd, hpoint]
    simp
  have hne : (∏' n : ℕ, twinEulerFactor n) ≠ 0 := by
    intro hz
    rw [hz] at hprodOne
    norm_num at hprodOne
  have hnonneg : 0 ≤ ∏' n : ℕ, twinEulerFactor n :=
    tprod_nonneg fun n => le_trans (by norm_num : (0 : ℝ) ≤ 3 / 4) (twinEulerFactor_lower n)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem singularProduct_pos (M : ℕ) : 0 < singularProduct M := by
  have hcorrection :
      0 < ∏ p ∈ (primesUpTo (M : ℝ)).filter (fun p => p ∣ M ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_pos
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSet, hpcond⟩
    have hpPrime : p.Prime := by
      change p ∈ (Finset.range (⌊(M : ℝ)⌋₊ + 1)).filter Nat.Prime at hpSet
      exact (Finset.mem_filter.mp hpSet).2
    have hpR : (2 : ℝ) < p := by exact_mod_cast hpcond.2
    have hden : 0 < (p : ℝ) - 1 := by linarith
    have hfrac : 1 / ((p : ℝ) - 1) < 1 := (div_lt_one hden).2 (by linarith)
    exact inv_pos.mpr (by linarith)
  change 0 <
    (2 * (∏' p : ℕ, twinEulerFactor p)) *
      (∏ p ∈ (primesUpTo (M : ℝ)).filter (fun p => p ∣ M ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))⁻¹)
  exact mul_pos (mul_pos (by norm_num) twinEulerProduct_pos) hcorrection

private lemma correctionPartial_stable (M : ℕ) (hM : 0 < M) {y : ℝ} (hy : (M : ℝ) ≤ y) :
    correctionPartial M y = correctionFull M := by
  have hfloor : ⌊(M : ℝ)⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hy
  have hsub : primesUpTo (M : ℝ) ⊆ primesUpTo y := by
    intro p hp
    unfold primesUpTo at hp ⊢
    rcases Finset.mem_filter.mp hp with ⟨hpRange, hpPrime⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hpRange)
        (Nat.add_le_add_right hfloor 1)), hpPrime⟩
  have hout : ∀ p ∈ primesUpTo y, p ∉ primesUpTo (M : ℝ) → correctionFactor M p = 1 := by
    intro p hp hyMem
    have hpPrime : p.Prime := by
      unfold primesUpTo at hp
      exact (Finset.mem_filter.mp hp).2
    have hpDivFalse : ¬ p ∣ M := by
      intro hpDiv
      have hpLe : p ≤ M := Nat.le_of_dvd hM hpDiv
      have hpCast : (p : ℝ) ≤ (M : ℝ) := by exact_mod_cast hpLe
      have hpFloor : p ≤ ⌊(M : ℝ)⌋₊ := Nat.le_floor hpCast
      have hpMem : p ∈ primesUpTo (M : ℝ) := by
        unfold primesUpTo
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpFloor), hpPrime⟩
      exact hyMem hpMem
    simp [correctionFactor, hpDivFalse]
  have hprod :
      (∏ p ∈ primesUpTo (M : ℝ), correctionFactor M p) =
        (∏ p ∈ primesUpTo y, correctionFactor M p) := Finset.prod_subset hsub hout
  have hfilter :
      (∏ p ∈ primesUpTo (M : ℝ), correctionFactor M p) = correctionFull M := by
    unfold correctionFull correctionFactor
    rw [Finset.prod_filter]
  unfold correctionPartial
  exact hprod.symm.trans hfilter

private lemma sieveRatio_tendsto (M : ℕ) (hM : 0 < M) :
    Tendsto (fun y : ℝ => 2 * twinPartial y * correctionPartial M y) atTop
      (𝓝 (singularProduct M)) := by
  have hbase : Tendsto (fun y : ℝ => 2 * twinPartial y * correctionFull M) atTop
      (𝓝 (2 * (∏' n : ℕ, twinEulerFactor n) * correctionFull M)) := by
    have h2 : Tendsto (fun y : ℝ => 2 * twinPartial y) atTop
        (𝓝 (2 * (∏' n : ℕ, twinEulerFactor n))) :=
      tendsto_const_nhds.mul twinPartial_tendsto
    exact h2.mul tendsto_const_nhds
  have hevent : (fun y : ℝ => 2 * twinPartial y * correctionFull M) =ᶠ[atTop]
      (fun y : ℝ => 2 * twinPartial y * correctionPartial M y) := by
    filter_upwards [eventually_ge_atTop (M : ℝ)] with y hy
    rw [correctionPartial_stable M hM hy]
  have hsingular : 2 * (∏' n : ℕ, twinEulerFactor n) * correctionFull M =
      singularProduct M := rfl
  simpa only [hsingular] using hbase.congr' hevent

private lemma roughSieveProduct_nonneg (y : ℝ) : 0 ≤ roughSieveProduct y := by
  unfold roughSieveProduct
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime : p.Prime := by
    unfold primesUpTo at hp
    exact (Finset.mem_filter.mp hp).2
  have hp₂ : 2 ≤ p := hpPrime.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp₂
  have hInv : 1 / (p : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hpR
  linarith

theorem progressionSieveProduct_relative (M : ℕ) (hM : 0 < M) :
    ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        |progressionSieveProduct M y - singularProduct M * roughSieveProduct y| ≤
          ε * singularProduct M * roughSieveProduct y := by
  intro ε hε
  have hS : 0 < singularProduct M := singularProduct_pos M
  have hRadius : 0 < ε * singularProduct M := mul_pos hε hS
  have hnear : ∀ᶠ y : ℝ in atTop,
      2 * twinPartial y * correctionPartial M y ∈ Metric.ball
        (singularProduct M) (ε * singularProduct M) :=
    (sieveRatio_tendsto M hM).eventually (Metric.ball_mem_nhds _ hRadius)
  obtain ⟨y₁, hy₁⟩ := Filter.eventually_atTop.mp hnear
  let y₀ := max y₁ (max 2 (M : ℝ))
  have hy₀₂ : 2 ≤ y₀ := le_trans (le_max_left 2 (M : ℝ)) (le_max_right y₁ _)
  refine ⟨y₀, hy₀₂, ?_⟩
  intro y hy
  have hy₁y : y₁ ≤ y := le_trans (le_max_left y₁ _ ) hy
  have hcloseBall := hy₁ y hy₁y
  have hclose :
      |2 * twinPartial y * correctionPartial M y - singularProduct M| ≤
        ε * singularProduct M := by
    have hlt := Metric.mem_ball.mp hcloseBall
    simpa [Real.dist_eq, abs_sub_comm] using hlt.le
  have hy₂ : 2 ≤ y := le_trans hy₀₂ hy
  have hrough : 0 ≤ roughSieveProduct y := roughSieveProduct_nonneg y
  rw [progressionProduct_factorization M hy₂]
  calc
    |roughSieveProduct y *
        (2 * twinPartial y * correctionPartial M y) -
          singularProduct M * roughSieveProduct y| =
        |roughSieveProduct y *
          (2 * twinPartial y * correctionPartial M y - singularProduct M)| := by
            congr 1 <;> ring
    _ = |roughSieveProduct y| *
        |2 * twinPartial y * correctionPartial M y - singularProduct M| := abs_mul _ _
    _ ≤ roughSieveProduct y * (ε * singularProduct M) := by
      rw [abs_of_nonneg hrough]
      exact mul_le_mul_of_nonneg_left hclose hrough
    _ = ε * singularProduct M * roughSieveProduct y := by ring

private lemma markedPrime_lower_exp {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p : ℕ}
    (hL : (4 : ℝ) ^ 10 ≤ Real.log x) (ha : ValidBands K a)
    (hp : p ∈ markedPrimes x K a) :
    Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤ (p : ℝ) := by
  have hLone : 1 ≤ Real.log x := by norm_num at hL ⊢; linarith
  simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
  obtain ⟨i, hpi⟩ := hp
  rcases Finset.mem_filter.mp hpi with ⟨_, hpband⟩
  rcases hpband with ⟨hpprime, hplow, _⟩
  have hpow : Real.rpow (Real.log x) (1 / 10 : ℝ) ≤
      Real.rpow (Real.log x) (a i) :=
    Real.rpow_le_rpow_of_exponent_le hLone (ha.2.1 i).1.le
  exact (Real.exp_le_exp.mpr hpow).trans hplow

private lemma markedPrime_lower_exp_general {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {p : ℕ} {β : ℝ} (hL : (4 : ℝ) ^ 10 ≤ Real.log x)
    (hβ : ∀ i : Fin K, β ≤ a i) (hp : p ∈ markedPrimes x K a) :
    Real.exp (Real.rpow (Real.log x) β) ≤ (p : ℝ) := by
  have hLone : 1 ≤ Real.log x := by norm_num at hL ⊢; linarith
  simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
  obtain ⟨i, hpi⟩ := hp
  rcases Finset.mem_filter.mp hpi with ⟨_, hpband⟩
  rcases hpband with ⟨_, hplow, _⟩
  have hpow : Real.rpow (Real.log x) β ≤ Real.rpow (Real.log x) (a i) :=
    Real.rpow_le_rpow_of_exponent_le hLone (hβ i)
  exact (Real.exp_le_exp.mpr hpow).trans hplow

private lemma groupPrimeFactorCount_bound {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {r : ℕ}
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x) (ha : ValidBands K a)
    (hr : IsGroupInteger x K a r)
    (hrbound : (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ)) :
    (r.primeFactors.card : ℝ) ≤
      (11 / 100 : ℝ) * Real.rpow (Real.log x) (9 / 10 : ℝ) := by
  let L := Real.log x
  let t := Real.rpow L (1 / 10 : ℝ)
  have hLpos : 0 < L := by have := hL; dsimp [L]; linarith
  have hnot2 : 2 ∉ markedPrimes x K a := by
    intro htwo
    have hs := markedPrime_scale_bounds hxpos hL ha htwo
    have hslo := hs.1
    norm_num at hslo
  have hrne : r ≠ 0 := by
    intro hr0
    apply hnot2
    have hdiv : 2 ∣ r := by simpa [hr0] using (dvd_zero 2)
    exact hr 2 Nat.prime_two hdiv
  let F := r.factorization.support
  have hmemFactor : ∀ p ∈ F, p.Prime ∧ p ∣ r := by
    intro p hp
    have hpf : p ∈ r.primeFactors := by simpa [F] using hp
    exact (Nat.mem_primeFactors_of_ne_zero hrne).mp hpf
  have hlogp : ∀ p ∈ F, t ≤ Real.log (p : ℝ) := by
    intro p hp
    have ⟨hpPrime, hpDiv⟩ := hmemFactor p hp
    have hgroup := hr p hpPrime hpDiv
    have hplow := markedPrime_lower_exp hL ha hgroup
    have hlog := Real.log_le_log (Real.exp_pos _) hplow
    simpa [L, t] using hlog
  have hval : ∀ p ∈ F, (1 : ℝ) ≤ (r.factorization p : ℝ) := by
    intro p hp
    have hp' : p ∈ r.factorization.support := by simpa [F] using hp
    have hpos : 0 < r.factorization p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp')
    exact_mod_cast (Nat.succ_le_iff.mpr hpos)
  have htpos : 0 < t := Real.rpow_pos_of_pos hLpos _
  have htNonneg : 0 ≤ t := htpos.le
  have hlogLower : t * (F.card : ℝ) ≤ Real.log (r : ℝ) := by
    have hsumLower : t * (F.card : ℝ) ≤
        ∑ p ∈ F, (r.factorization p : ℝ) * Real.log (p : ℝ) := by
      calc
        t * (F.card : ℝ) = ∑ p ∈ F, t := by simp [mul_comm]
        _ ≤ ∑ p ∈ F, (r.factorization p : ℝ) * Real.log (p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          calc
            t = 1 * t := by ring
            _ ≤ (r.factorization p : ℝ) * t :=
              mul_le_mul_of_nonneg_right (hval p hp) htNonneg
            _ ≤ (r.factorization p : ℝ) * Real.log (p : ℝ) :=
              mul_le_mul_of_nonneg_left (hlogp p hp) (by positivity)
    have hlogFact : Real.log (r : ℝ) =
        ∑ p ∈ F, (r.factorization p : ℝ) * Real.log (p : ℝ) := by
      simpa [F, Finsupp.sum, mul_comm] using Real.log_nat_eq_sum_factorization r
    rw [hlogFact]
    exact hsumLower
  have hlogUpper : Real.log (r : ℝ) ≤ (11 / 100 : ℝ) * L := by
    have hrpos : 0 < (r : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hrne)
    have h := Real.log_le_log hrpos hrbound
    simpa [L, Real.log_rpow hxpos] using h
  have hcount : (F.card : ℝ) ≤ ((11 / 100 : ℝ) * L) / t := by
    apply (le_div_iff₀ htpos).2
    calc
      (F.card : ℝ) * t = t * (F.card : ℝ) := by ring
      _ ≤ Real.log (r : ℝ) := hlogLower
      _ ≤ (11 / 100 : ℝ) * L := hlogUpper
  have hcard : (F.card : ℝ) = (r.primeFactors.card : ℝ) := by
    simp [F, Nat.support_factorization]
  rw [← hcard]
  have hpower : Real.rpow L (1 / 10 : ℝ) * Real.rpow L (9 / 10 : ℝ) = L := by
    calc
      _ = Real.rpow L ((1 / 10 : ℝ) + 9 / 10) := (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L 1 := by congr 1 <;> norm_num
      _ = L := by simp [Real.rpow_one]
  have hquot : L / t = Real.rpow L (9 / 10 : ℝ) := by
    apply (div_eq_iff (ne_of_gt htpos)).2
    calc
      L = t * Real.rpow L (9 / 10 : ℝ) := by simpa [t] using hpower.symm
      _ = Real.rpow L (9 / 10 : ℝ) * t := by ring
  calc
    (F.card : ℝ) ≤ ((11 / 100 : ℝ) * L) / t := hcount
    _ = (11 / 100 : ℝ) * Real.rpow L (9 / 10 : ℝ) := by
      calc
        _ = (11 / 100 : ℝ) * (L / t) := by ring
        _ = (11 / 100 : ℝ) * Real.rpow L (9 / 10 : ℝ) := by rw [hquot]

theorem groupPrimeReciprocal_sum_bound {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {r : ℕ}
    (hxpos : 0 < x) (hL : (4 : ℝ) ^ 10 ≤ Real.log x) (ha : ValidBands K a)
    (hr : IsGroupInteger x K a r)
    (hrbound : (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ)) :
    (∑ p ∈ (primesUpTo (Real.rpow x (1 / 5 : ℝ))).filter (fun p => p ∣ r),
      1 / (p : ℝ)) ≤
        (11 / 100 : ℝ) * Real.rpow (Real.log x) (9 / 10 : ℝ) *
          Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) := by
  let t := Real.rpow (Real.log x) (1 / 10 : ℝ)
  have hnot2 : 2 ∉ markedPrimes x K a := by
    intro htwo
    have hs := markedPrime_scale_bounds hxpos hL ha htwo
    have hslo := hs.1
    norm_num at hslo
  have hrne : r ≠ 0 := by
    intro hr0
    apply hnot2
    have hdiv : 2 ∣ r := by simpa [hr0] using (dvd_zero 2)
    exact hr 2 Nat.prime_two hdiv
  let S := (primesUpTo (Real.rpow x (1 / 5 : ℝ))).filter (fun p => p ∣ r)
  have hsub : S ⊆ r.primeFactors := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSet, hpDiv⟩
    have hpPrime : p.Prime := by
      unfold primesUpTo at hpSet
      exact (Finset.mem_filter.mp hpSet).2
    exact (Nat.mem_primeFactors_of_ne_zero hrne).mpr ⟨hpPrime, hpDiv⟩
  have hcardS : (S.card : ℝ) ≤ (r.primeFactors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hsum :
      (∑ p ∈ S, 1 / (p : ℝ)) ≤ (S.card : ℝ) * Real.exp (-t) := by
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul S (fun p => 1 / (p : ℝ)) (Real.exp (-t)) (by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨_, hpDiv⟩
        have hpPrime : p.Prime := by
          have hpSet := (Finset.mem_filter.mp hp).1
          unfold primesUpTo at hpSet
          exact (Finset.mem_filter.mp hpSet).2
        have hgroup := hr p hpPrime hpDiv
        have hplow := markedPrime_lower_exp hL ha hgroup
        have hrecip : 1 / (p : ℝ) ≤ 1 / Real.exp t :=
          one_div_le_one_div_of_le (Real.exp_pos _) hplow
        calc
          _ ≤ 1 / Real.exp t := hrecip
          _ = _ := by rw [one_div, ← Real.exp_neg]))
  have hcount : (r.primeFactors.card : ℝ) ≤
      (11 / 100 : ℝ) * Real.rpow (Real.log x) (9 / 10 : ℝ) :=
    groupPrimeFactorCount_bound hxpos hL ha hr hrbound
  have hExpNonneg : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  calc
    _ ≤ (S.card : ℝ) * Real.exp (-t) := hsum
    _ ≤ (r.primeFactors.card : ℝ) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hcardS hExpNonneg
    _ ≤ ((11 / 100 : ℝ) * Real.rpow (Real.log x) (9 / 10 : ℝ)) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hcount hExpNonneg
    _ = (11 / 100 : ℝ) * Real.rpow (Real.log x) (9 / 10 : ℝ) *
        Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) := by rfl

theorem rExtraFull_close_eventually (M K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∀ᶠ x : ℝ in atTop, ∀ r : ℕ, IsGroupInteger x K a r →
      (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) →
        rExtraFull M r ≤ 1 + Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) := by
  let i₀ : Fin K := ⟨0, by have := ha.1; omega⟩
  let a₀ := a i₀
  let β := (a₀ + 1 / 10) / 2
  have ha₀ : (1 / 10 : ℝ) < a₀ := (ha.2.1 i₀).1
  have hβ₀ : (1 / 10 : ℝ) < β := by dsimp [β]; linarith
  have hβa₀ : β < a₀ := by dsimp [β]; linarith
  have hamin : ∀ i : Fin K, a₀ ≤ a i := by
    intro i
    by_cases hzero : i.val = 0
    · have hi : i = i₀ := Fin.ext (by simpa [i₀] using hzero)
      simp [a₀, hi]
    · have hlt : i₀.val < i.val := by simp [i₀]; omega
      exact (ha.2.2 i₀ i hlt).le
  have hβall : ∀ i : Fin K, β ≤ a i := by
    intro i
    exact (le_of_lt hβa₀).trans (hamin i)
  have hlogLarge : ∀ᶠ x : ℝ in atTop, (4 : ℝ) ^ 10 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((4 : ℝ) ^ 10))
  have htail : ∀ᶠ x : ℝ in atTop,
      (11 / 50 : ℝ) * Real.rpow (Real.log x) (9 / 10 : ℝ) *
        Real.exp (-Real.rpow (Real.log x) β + Real.rpow (Real.log x) (1 / 10 : ℝ)) < 1 / 2 :=
    Real.tendsto_log_atTop.eventually (correctionLog_tail_eventually hβ₀)
  have hdomain : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hall : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ (4 : ℝ) ^ 10 ≤ Real.log x ∧
        (11 / 50 : ℝ) * Real.rpow (Real.log x) (9 / 10 : ℝ) *
          Real.exp (-Real.rpow (Real.log x) β + Real.rpow (Real.log x) (1 / 10 : ℝ)) < 1 / 2 := by
    filter_upwards [hdomain, hlogLarge, htail] with x hx hL hxTail
    exact ⟨hx, hL, hxTail⟩
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hall
  let x₀ := max X 2
  refine Filter.eventually_atTop.2 ⟨x₀, ?_⟩
  intro x hx r hr hrbound
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨_, hL, htailx⟩ := hX x hxX
  have hxpos : 0 < x := by linarith
  let L := Real.log x
  let η := Real.exp (-Real.rpow L (1 / 10 : ℝ))
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hEta : 0 < η := Real.exp_pos _
  have hExpFactor : Real.exp (-Real.rpow L β) =
      η * Real.exp (-Real.rpow L β + Real.rpow L (1 / 10 : ℝ)) := by
    dsimp [η]
    rw [← Real.exp_add]
    congr 1 <;> ring
  let R : Finset ℕ := r.primeFactors.filter (fun p => ¬ p ∣ M ∧ 2 < p)
  have hnot2 : 2 ∉ markedPrimes x K a := by
    intro htwo
    have hs := markedPrime_scale_bounds hxpos hL ha htwo
    have hslo := hs.1
    norm_num at hslo
  have hrne : r ≠ 0 := by
    intro hr0
    apply hnot2
    have hdiv : 2 ∣ r := by simpa [hr0] using (dvd_zero 2)
    exact hr 2 Nat.prime_two hdiv
  have htermPos : ∀ p ∈ R,
      0 < (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    intro p hp
    have hpcond := (Finset.mem_filter.mp hp).2
    have hpR : (2 : ℝ) < p := by exact_mod_cast hpcond.2
    have hbase : 0 < 1 - 1 / ((p : ℝ) - 1) := by
      have hlt : 1 / ((p : ℝ) - 1) < 1 :=
        (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2 (by linarith)
      linarith
    exact inv_pos.mpr hbase
  have hCpos : 0 < rExtraFull M r := by
    unfold rExtraFull
    exact Finset.prod_pos htermPos
  have hlogProd : Real.log (rExtraFull M r) =
      ∑ p ∈ R, Real.log ((1 - 1 / ((p : ℝ) - 1))⁻¹) := by
    unfold rExtraFull
    exact Real.log_prod (fun p hp => (htermPos p hp).ne')
  have hlogEach : ∀ p ∈ R,
      Real.log ((1 - 1 / ((p : ℝ) - 1))⁻¹) ≤ 1 / ((p : ℝ) - 2) := by
    intro p hp
    have hpcond := (Finset.mem_filter.mp hp).2
    have hpR : (4 : ℝ) < p := by
      have hgroup := hr p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
        (Nat.mem_primeFactors_of_ne_zero hrne |>.mp (Finset.mem_filter.mp hp).1 |>.2)
      exact (markedPrime_scale_bounds hxpos hL ha hgroup).1
    have hpminus : 0 < (p : ℝ) - 2 := by linarith
    have hpminusNe : (p : ℝ) - 2 ≠ 0 := ne_of_gt hpminus
    have hpminusAddNe : -2 + (p : ℝ) ≠ 0 := by linarith
    have hpminusOneNe : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    have hbase : 0 < 1 - 1 / ((p : ℝ) - 1) := by
      have hlt : 1 / ((p : ℝ) - 1) < 1 :=
        (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2 (by linarith)
      linarith
    have hbaseEq : 1 - 1 / ((p : ℝ) - 1) =
        ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
      field_simp [hpminusOneNe]
      <;> ring
    have hfactor :
        (1 - 1 / ((p : ℝ) - 1))⁻¹ = 1 + 1 / ((p : ℝ) - 2) := by
      rw [hbaseEq]
      field_simp [hpminusNe, hpminusOneNe]
      <;> ring_nf
    rw [hfactor]
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((p : ℝ) - 2))
    linarith
  have hlogToSum : Real.log (rExtraFull M r) ≤
      ∑ p ∈ R, 1 / ((p : ℝ) - 2) := by
    rw [hlogProd]
    exact Finset.sum_le_sum (fun p hp => hlogEach p hp)
  have hRecipSum :
      (∑ p ∈ R, 1 / (p : ℝ)) ≤
        (R.card : ℝ) * Real.exp (-Real.rpow L β) := by
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul R (fun p => 1 / (p : ℝ))
        (Real.exp (-Real.rpow L β)) (by
          intro p hp
          have hpPrime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
          have hdiv := (Nat.mem_primeFactors_of_ne_zero hrne).mp (Finset.mem_filter.mp hp).1 |>.2
          have hgroup := hr p hpPrime hdiv
          have hrecip : 1 / (p : ℝ) ≤ 1 / Real.exp (Real.rpow L β) :=
            one_div_le_one_div_of_le (Real.exp_pos _) (markedPrime_lower_exp_general hL hβall hgroup)
          have hExpRecip : 1 / Real.exp (Real.rpow L β) =
              Real.exp (-Real.rpow L β) := by
            rw [one_div, ← Real.exp_neg]
          calc
            _ ≤ 1 / Real.exp (Real.rpow L β) := hrecip
            _ = _ := hExpRecip))
  have hrecipFactor : ∀ p ∈ R,
      1 / ((p : ℝ) - 2) ≤ 2 / (p : ℝ) := by
    intro p hp
    have hpR : (4 : ℝ) ≤ p := by
      have hpPrime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      have hdiv := (Nat.mem_primeFactors_of_ne_zero hrne).mp (Finset.mem_filter.mp hp).1 |>.2
      have hgroup := hr p hpPrime hdiv
      have hs := markedPrime_scale_bounds hxpos hL ha hgroup
      exact le_of_lt hs.1
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith [hpR]
  have hSumDen :
      (∑ p ∈ R, 1 / ((p : ℝ) - 2)) ≤ 2 * (∑ p ∈ R, 1 / (p : ℝ)) := by
    calc
      _ ≤ ∑ p ∈ R, 2 / (p : ℝ) := Finset.sum_le_sum (fun p hp => hrecipFactor p hp)
      _ = 2 * (∑ p ∈ R, 1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hcount : (R.card : ℝ) ≤
      (11 / 100 : ℝ) * Real.rpow L (9 / 10 : ℝ) := by
    apply le_trans ?_ (groupPrimeFactorCount_bound hxpos hL ha hr hrbound)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hlogUpper : Real.log (rExtraFull M r) ≤
      (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) * Real.exp (-Real.rpow L β) := by
    calc
      _ ≤ 2 * (∑ p ∈ R, 1 / (p : ℝ)) := hlogToSum.trans hSumDen
      _ ≤ 2 * ((R.card : ℝ) * Real.exp (-Real.rpow L β)) :=
        mul_le_mul_of_nonneg_left hRecipSum (by norm_num)
      _ ≤ 2 * (((11 / 100 : ℝ) * Real.rpow L (9 / 10 : ℝ)) *
          Real.exp (-Real.rpow L β)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
      _ = (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) * Real.exp (-Real.rpow L β) := by ring
  have hTail : (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) *
      Real.exp (-Real.rpow L β + Real.rpow L (1 / 10 : ℝ)) ≤ 1 / 2 := by
    simpa [L] using htailx.le
  have hlogC : Real.log (rExtraFull M r) ≤ (1 / 2 : ℝ) * η := by
    calc
      _ ≤ (11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) * Real.exp (-Real.rpow L β) := hlogUpper
      _ = η * ((11 / 50 : ℝ) * Real.rpow L (9 / 10 : ℝ) *
          Real.exp (-Real.rpow L β + Real.rpow L (1 / 10 : ℝ))) := by rw [hExpFactor]; ring
      _ ≤ η * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hTail hEta.le
      _ = (1 / 2 : ℝ) * η := by ring
  have hEtaLe : η ≤ 2 := by
    have hnonneg : 0 ≤ Real.rpow L (1 / 10 : ℝ) := Real.rpow_nonneg (le_of_lt hLpos) _
    calc
      η = Real.exp (-Real.rpow L (1 / 10 : ℝ)) := rfl
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := by simp
      _ ≤ 2 := by norm_num
  have hEtaLog : (1 / 2 : ℝ) * η ≤ Real.log (1 + η) := by
    have hlog := Real.le_log_one_add_of_nonneg hEta.le
    have hfrac : η / 2 ≤ 2 * η / (η + 2) := by
      apply (div_le_div_iff₀ (by norm_num) (by linarith)).2
      nlinarith [hEtaLe, hEta.le]
    have hlog' : 2 * η / (η + 2) ≤ Real.log (1 + η) := by simpa [div_eq_mul_inv, add_comm] using hlog
    calc
      (1 / 2 : ℝ) * η = η / 2 := by ring
      _ ≤ Real.log (1 + η) := hfrac.trans hlog'
  have hLogBound : Real.log (rExtraFull M r) ≤ Real.log (1 + η) := hlogC.trans hEtaLog
  have hExpBound := Real.exp_le_exp.mpr hLogBound
  rw [Real.exp_log hCpos, Real.exp_log (by positivity : 0 < 1 + η)] at hExpBound
  exact hExpBound

theorem progressionSieveProductFor_relative (M K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ r : ℕ, IsGroupInteger x K a r → (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) →
        ∀ y : ℝ, 2 ≤ y →
          |progressionSieveProductFor M r y - progressionSieveProduct M y| ≤
            Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) * progressionSieveProduct M y := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    (rExtraFull_close_eventually M K a ha)
  let Xscale := Real.exp ((4 : ℝ) ^ 10)
  let x₀ := max X (max Xscale 2)
  have hXscale₂ : 2 ≤ Xscale := by
    have h₂ : 2 ≤ Real.exp (1 : ℝ) := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      norm_num at hh ⊢
      linarith
    exact h₂.trans (Real.exp_le_exp.mpr (by norm_num))
  have hx₀₂ : 2 ≤ x₀ := by
    exact le_trans hXscale₂ (le_trans (le_max_left _ _) (le_max_right _ _))
  refine ⟨x₀, hx₀₂, ?_⟩
  intro x hx r hr hrbound y hy
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hxScale : Xscale ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxScale
  have hL : (4 : ℝ) ^ 10 ≤ Real.log x := by
    have hlog := Real.log_le_log (Real.exp_pos _) hxScale
    simpa [Xscale, Real.log_exp] using hlog
  have hFull := hX x hxX r hr hrbound
  have hExtraUpper : rExtraPartial M r y ≤
      1 + Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) :=
    (rExtraPartial_le_full hxpos hL ha hr).trans hFull
  have hExtraLower : 1 ≤ rExtraPartial M r y := by
    unfold rExtraPartial
    apply Finset.one_le_prod₀
    intro p hp
    have hpPrime : p.Prime := by
      unfold primesUpTo at hp
      exact (Finset.mem_filter.mp hp).2
    by_cases hcond : p ∣ r ∧ ¬ p ∣ M ∧ 2 < p
    · rw [rExtraFactor, if_pos hcond]
      have hgroup := hr p hpPrime hcond.1
      have hs := markedPrime_scale_bounds hxpos hL ha hgroup
      have hpR : (2 : ℝ) < p := by exact_mod_cast hcond.2.2
      have hbase : 0 < 1 - 1 / ((p : ℝ) - 1) := by
        have hlt : 1 / ((p : ℝ) - 1) < 1 :=
          (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2 (by linarith)
        linarith
      have hbaseLe : 1 - 1 / ((p : ℝ) - 1) ≤ 1 := by
        have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
        linarith
      exact (one_le_inv₀ hbase).2 hbaseLe
    · rw [rExtraFactor, if_neg hcond]
  have hProgNonneg : 0 ≤ progressionSieveProduct M y := by
    unfold progressionSieveProduct
    apply Finset.prod_nonneg
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpcond⟩
    have hpR : (2 : ℝ) < p := by exact_mod_cast hpcond.1
    have hInv : 1 / ((p : ℝ) - 1) ≤ 1 :=
      (div_le_one (by linarith)).2 (by linarith)
    linarith
  have hDeltaNonneg : 0 ≤ rExtraPartial M r y - 1 := sub_nonneg.mpr hExtraLower
  have hDeltaBound :
      rExtraPartial M r y - 1 ≤ Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) := by
    linarith
  rw [progressionSieveProductFor_factorization M r (y := y)]
  calc
    |progressionSieveProduct M y * rExtraPartial M r y - progressionSieveProduct M y| =
        |progressionSieveProduct M y * (rExtraPartial M r y - 1)| := by
          congr 1 <;> ring
    _ = progressionSieveProduct M y * (rExtraPartial M r y - 1) := by
      rw [abs_mul, abs_of_nonneg hProgNonneg, abs_of_nonneg hDeltaNonneg]
    _ ≤ progressionSieveProduct M y * Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hDeltaBound hProgNonneg
    _ = _ := by ring

theorem progressionPrimeSum_trivial_bound (x : ℝ) (M c : ℕ) (u : ℤ)
    (Ψ : ℝ → ℝ) (K : ℕ) (a : Fin K → ℝ) (r : ℕ)
    (hc : 0 < c) (ha : ValidBands K a) (hΨ : IsTestFunction Ψ)
    (hL : (4 : ℝ) ^ 10 ≤ Real.log x) (hx4 : 4 ≤ x)
    (hr : IsGroupInteger x K a r) :
    progressionPrimeSum x M c u Ψ r 1 ≤ 3 * x / (r : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hnot2 : 2 ∉ markedPrimes x K a := by
    intro htwo
    have hs := markedPrime_scale_bounds hxpos hL ha htwo
    have hslo := hs.1
    norm_num at hslo
  have hrne : r ≠ 0 := by
    intro hr0
    apply hnot2
    have hdiv : 2 ∣ r := by simpa [hr0] using (dvd_zero 2)
    exact hr 2 Nat.prime_two hdiv
  have hrpos : 0 < (r : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hrne)
  have hcOne : (1 : ℝ) ≤ c := by exact_mod_cast (Nat.succ_le_of_lt hc)
  let B : Finset ℕ := (Finset.range (⌊2 * x⌋₊ + 1)).filter fun Q =>
    Q.Prime ∧ Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
      (((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M]) ∧ 1 ∣ c * r * Q + 1
  let f (Q : ℕ) := Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x)
  let S := B.filter fun Q => f Q ≠ 0
  have hsumEq : progressionPrimeSum x M c u Ψ r 1 = ∑ Q ∈ S, f Q := by
    unfold progressionPrimeSum
    have hEq : (∑ Q ∈ B, f Q) = ∑ Q ∈ S, f Q := by
      unfold S
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro Q hQ hnot
      by_contra hnonzero
      exact hnot (Finset.mem_filter.mpr ⟨hQ, hnonzero⟩)
    simpa [B, f] using hEq
  let A := 2 * x / ((c * r : ℕ) : ℝ)
  have hSrange : S ⊆ Finset.range (⌊A⌋₊ + 1) := by
    intro Q hQ
    rcases Finset.mem_filter.mp hQ with ⟨hQin, hΨnz⟩
    rcases Finset.mem_filter.mp hQin with ⟨_, hconds⟩
    rcases hconds with ⟨hprime, hQlarge, _, _⟩
    have hargMem : ((c * r * Q + 1 : ℕ) : ℝ) / x ∈ Function.support Ψ := by
      simpa [Function.support, f] using hΨnz
    have harg := hΨ.2.1 hargMem
    have hDcast : ((c * r * Q + 1 : ℕ) : ℝ) =
        (c : ℝ) * (r : ℝ) * (Q : ℝ) + 1 := by push_cast; ring
    have hDdiv : ((c : ℝ) * (r : ℝ) * (Q : ℝ) + 1) / x < 2 := by
      simpa [hDcast] using harg.2
    have hDupper : (c : ℝ) * (r : ℝ) * (Q : ℝ) + 1 < 2 * x :=
      (div_lt_iff₀ hxpos).mp hDdiv
    have hprodUpper : (c : ℝ) * (r : ℝ) * (Q : ℝ) < 2 * x := by linarith
    have hcrPos : 0 < (c : ℝ) * (r : ℝ) :=
      mul_pos (Nat.cast_pos.mpr hc) hrpos
    have hQupper : (Q : ℝ) < A := by
      have hQupper' : (Q : ℝ) < 2 * x / ((c : ℝ) * (r : ℝ)) :=
        (lt_div_iff₀ hcrPos).2 (by simpa [mul_assoc, mul_comm, mul_left_comm] using hprodUpper)
      simpa [A, Nat.cast_mul] using hQupper'
    have hA0 : 0 ≤ A := by dsimp [A]; positivity
    have hQfloor : Q ≤ ⌊A⌋₊ := Nat.le_floor hQupper.le
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hQfloor)
  have hsumCard : (∑ Q ∈ S, f Q) ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ Q ∈ S, (1 : ℝ) := Finset.sum_le_sum fun Q hQ => hΨ.2.2.2.1 _
      _ = (S.card : ℝ) := by simp
  have hcardNat : S.card ≤ ⌊A⌋₊ + 1 := by
    calc
      S.card ≤ (Finset.range (⌊A⌋₊ + 1)).card := Finset.card_le_card hSrange
      _ = ⌊A⌋₊ + 1 := by simp
  have hcard : (S.card : ℝ) ≤ (⌊A⌋₊ + 1 : ℝ) := by exact_mod_cast hcardNat
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hfloor : (⌊A⌋₊ : ℝ) ≤ A := Nat.floor_le hA0
  have hsumA : progressionPrimeSum x M c u Ψ r 1 ≤ A + 1 := by
    rw [hsumEq]
    calc
      _ ≤ (S.card : ℝ) := hsumCard
      _ ≤ (⌊A⌋₊ + 1 : ℝ) := hcard
      _ ≤ A + 1 := by linarith [hfloor]
  have hcR : (r : ℝ) ≤ (c * r : ℕ) := by
    exact_mod_cast (Nat.le_mul_of_pos_left r hc)
  have hrecip : 1 / ((c * r : ℕ) : ℝ) ≤ 1 / (r : ℝ) :=
    one_div_le_one_div_of_le hrpos (by exact_mod_cast hcR)
  have hA : A ≤ 2 * x / (r : ℝ) := by
    calc
      A = 2 * x * (1 / ((c * r : ℕ) : ℝ)) := by dsimp [A]; ring
      _ ≤ 2 * x * (1 / (r : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 2 * x / (r : ℝ) := by ring
  have hpow9 : 2 ≤ Real.rpow x (9 / 10 : ℝ) := by
    have hxone : 1 ≤ x := by linarith
    have hroot : 2 ≤ Real.sqrt x := by
      exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) hxpos.le).2 (by nlinarith [hx4])
    calc
      2 ≤ Real.sqrt x := hroot
      _ = Real.rpow x (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
      _ ≤ Real.rpow x (9 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
  have hpoweq : Real.rpow x (1 / 10 : ℝ) * Real.rpow x (9 / 10 : ℝ) = x := by
    calc
      _ = Real.rpow x ((1 / 10 : ℝ) + 9 / 10) := (Real.rpow_add hxpos _ _).symm
      _ = Real.rpow x 1 := by congr 1 <;> norm_num
      _ = x := by simp [Real.rpow_one]
  by_cases hSempty : S = ∅
  · have hsumZero : progressionPrimeSum x M c u Ψ r 1 = 0 := by
      rw [hsumEq, hSempty]
      simp
    rw [hsumZero]
    positivity
  · obtain ⟨Q, hQ⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
    have hrSmall : (r : ℝ) < 2 * Real.rpow x (1 / 10 : ℝ) := by
      have hqData := Finset.mem_filter.mp hQ
      rcases Finset.mem_filter.mp hqData.1 with ⟨_, hconds⟩
      rcases hconds with ⟨hqPrime, hqLarge, _, _⟩
      have hargMem : ((c * r * Q + 1 : ℕ) : ℝ) / x ∈ Function.support Ψ := by
        simpa [Function.support, f] using hqData.2
      have harg := hΨ.2.1 hargMem
      have hDcast : ((c * r * Q + 1 : ℕ) : ℝ) =
          (c : ℝ) * (r : ℝ) * (Q : ℝ) + 1 := by push_cast; ring
      have hDupper : (c : ℝ) * (r : ℝ) * (Q : ℝ) < 2 * x := by
        have hDdiv : ((c : ℝ) * (r : ℝ) * (Q : ℝ) + 1) / x < 2 := by
          simpa [hDcast] using harg.2
        have h := (div_lt_iff₀ hxpos).mp hDdiv
        linarith
      have hlower : (r : ℝ) * Real.rpow x (9 / 10 : ℝ) <
          (c : ℝ) * (r : ℝ) * (Q : ℝ) := by
        have hcr : (r : ℝ) ≤ (c : ℝ) * (r : ℝ) := by
          calc
            (r : ℝ) = 1 * (r : ℝ) := by ring
            _ ≤ (c : ℝ) * (r : ℝ) :=
              mul_le_mul_of_nonneg_right hcOne (Nat.cast_nonneg r)
        calc
          (r : ℝ) * Real.rpow x (9 / 10 : ℝ) ≤
              ((c : ℝ) * (r : ℝ)) * Real.rpow x (9 / 10 : ℝ) :=
                mul_le_mul_of_nonneg_right hcr (Real.rpow_nonneg hxpos.le _)
          _ < ((c : ℝ) * (r : ℝ)) * (Q : ℝ) :=
            mul_lt_mul_of_pos_left hqLarge (mul_pos (Nat.cast_pos.mpr hc) hrpos)
          _ = (c : ℝ) * (r : ℝ) * (Q : ℝ) := by ring
      have hprod : (r : ℝ) * Real.rpow x (9 / 10 : ℝ) < 2 * x := hlower.trans hDupper
      have htpos : 0 < Real.rpow x (9 / 10 : ℝ) := Real.rpow_pos_of_pos hxpos _
      have hrDiv : (r : ℝ) < 2 * x / Real.rpow x (9 / 10 : ℝ) :=
        (lt_div_iff₀ htpos).2 (by simpa [mul_comm] using hprod)
      have hquot : x / Real.rpow x (9 / 10 : ℝ) = Real.rpow x (1 / 10 : ℝ) := by
        apply (div_eq_iff (ne_of_gt htpos)).2
        exact hpoweq.symm
      calc
        (r : ℝ) < 2 * x / Real.rpow x (9 / 10 : ℝ) := hrDiv
        _ = 2 * Real.rpow x (1 / 10 : ℝ) := by
          calc
            _ = 2 * (x / Real.rpow x (9 / 10 : ℝ)) := by ring
            _ = 2 * Real.rpow x (1 / 10 : ℝ) := by rw [hquot]
    have hxpowle : 2 * Real.rpow x (1 / 10 : ℝ) ≤ x := by
      calc
        2 * Real.rpow x (1 / 10 : ℝ) ≤
            Real.rpow x (9 / 10 : ℝ) * Real.rpow x (1 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_right hpow9 (Real.rpow_nonneg hxpos.le _)
        _ = x := by rw [mul_comm, hpoweq]
    have hrle : (r : ℝ) ≤ x := hrSmall.le.trans hxpowle
    have hxr : 1 ≤ x / (r : ℝ) := (one_le_div₀ hrpos).2 hrle
    calc
      progressionPrimeSum x M c u Ψ r 1 ≤ A + 1 := hsumA
      _ ≤ 2 * x / (r : ℝ) + 1 := add_le_add hA le_rfl
      _ ≤ 2 * x / (r : ℝ) + x / (r : ℝ) := add_le_add le_rfl hxr
      _ = 3 * x / (r : ℝ) := by ring

set_option maxHeartbeats 200000

end ArtinPrimitiveRoots.Construction
