import ArtinPrimitiveRoots.Sieve.RoughDensity
import ArtinPrimitiveRoots.TypeII.Rough
import ArtinPrimitiveRoots.Construction.Defs

namespace ArtinPrimitiveRoots.Construction.Proofs.C4

open MeasureTheory

theorem primesUpTo_subset_of_le {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    ArtinPrimitiveRoots.TypeII.primesUpTo y ⊆ ArtinPrimitiveRoots.TypeII.primesUpTo z := by
  intro p hp
  simp only [ArtinPrimitiveRoots.TypeII.primesUpTo, Finset.mem_filter, Finset.mem_range] at hp
  rcases hp with ⟨hprange, hprime⟩
  have hpFloor : p ≤ ⌊y⌋₊ := by omega
  have hpReal : (p : ℝ) ≤ y := (Nat.le_floor_iff hy).1 hpFloor
  have hz : 0 ≤ z := le_trans hy hyz
  have hpZFloor : p ≤ ⌊z⌋₊ := (Nat.le_floor_iff hz).2 (hpReal.trans hyz)
  simp only [ArtinPrimitiveRoots.TypeII.primesUpTo, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hprime⟩

theorem finite_sum_le_superset_of_injective {α β : Type*} [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → β) (wa : α → ℝ) (wb : β → ℝ)
    (hinj : Set.InjOn f A) (hmap : ∀ a ∈ A, f a ∈ B)
    (hbound : ∀ a ∈ A, wa a ≤ wb (f a)) (hnonneg : ∀ b ∈ B, 0 ≤ wb b) :
    (∑ a ∈ A, wa a) ≤ ∑ b ∈ B, wb b := by
  classical
  let I := A.image f
  have hI : I ⊆ B := Finset.image_subset_iff.mpr hmap
  have hdisj : Disjoint (B \ I) I := by
    rw [Finset.disjoint_left]
    intro b hbDiff hbI
    exact (Finset.mem_sdiff.mp hbDiff).2 hbI
  have hunion : B \ I ∪ I = B := Finset.sdiff_union_of_subset hI
  have hsumI : (∑ b ∈ I, wb b) = ∑ a ∈ A, wb (f a) := Finset.sum_image hinj
  have hsumB :
      (∑ b ∈ B, wb b) = (∑ b ∈ B \ I, wb b) + ∑ b ∈ I, wb b := by
    have hsumSet : (∑ b ∈ B, wb b) = ∑ b ∈ B \ I ∪ I, wb b := by
      exact congrArg (fun s : Finset β => ∑ b ∈ s, wb b) hunion.symm
    calc
      _ = ∑ b ∈ B \ I ∪ I, wb b := hsumSet
      _ = (∑ b ∈ B \ I, wb b) + ∑ b ∈ I, wb b := Finset.sum_union hdisj
  have hnonnegI : 0 ≤ ∑ b ∈ B \ I, wb b :=
    Finset.sum_nonneg fun b hb => hnonneg b (Finset.mem_sdiff.mp hb).1
  calc
    _ ≤ ∑ a ∈ A, wb (f a) := Finset.sum_le_sum fun a ha => hbound a ha
    _ = ∑ b ∈ I, wb b := hsumI.symm
    _ ≤ ∑ b ∈ B, wb b := by rw [hsumB]; linarith

theorem exists_strict_partition_mesh (b e δ : ℝ) (hbe : b < e)
    (hδ : 0 < δ) :
    ∃ J : ℕ, ∃ γ : Fin (J + 1) → ℝ,
      0 < J ∧ γ 0 = b ∧ γ (Fin.last J) = e ∧
      (∀ i, b ≤ γ i ∧ γ i ≤ e) ∧
      (∀ i j, i.val < j.val → γ i < γ j) ∧
      (∀ j : Fin J, γ j.castSucc < γ j.succ ∧ γ j.succ - γ j.castSucc < δ) := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ((e - b) / δ)
  have hJpos : 0 < J := by
    have hratio : 0 < (e - b) / δ := div_pos (sub_pos.mpr hbe) hδ
    exact_mod_cast Nat.cast_pos.mp (lt_trans hratio hJ)
  have hJreal : 0 < (J : ℝ) := Nat.cast_pos.mpr hJpos
  have hL : e - b < δ * (J : ℝ) := by
    nlinarith [(div_lt_iff₀ hδ).1 hJ]
  let γ : Fin (J + 1) → ℝ := fun i => b + (e - b) * (i.val : ℝ) / (J : ℝ)
  refine ⟨J, γ, hJpos, ?_, ?_, ?_, ?_, ?_⟩
  · simp [γ]
  · simp [γ]
    have hJne : (J : ℝ) ≠ 0 := ne_of_gt hJreal
    field_simp
    ring
  · intro i
    constructor
    · dsimp [γ]
      have hfrac : 0 ≤ (i.val : ℝ) / (J : ℝ) := div_nonneg (Nat.cast_nonneg _) hJreal.le
      have hLpos : 0 < e - b := sub_pos.mpr hbe
      have hprod : 0 ≤ (e - b) * ((i.val : ℝ) / (J : ℝ)) := mul_nonneg hLpos.le hfrac
      calc
        b ≤ b + (e - b) * ((i.val : ℝ) / (J : ℝ)) := le_add_of_nonneg_right hprod
        _ = b + (e - b) * (i.val : ℝ) / (J : ℝ) := by ring
    · dsimp [γ]
      have hi : (i.val : ℝ) ≤ (J : ℝ) := by
        exact_mod_cast (Nat.le_of_lt_succ i.isLt)
      have hfrac : (i.val : ℝ) / (J : ℝ) ≤ 1 :=
        (div_le_one₀ hJreal).2 hi
      have hLpos : 0 < e - b := sub_pos.mpr hbe
      have hprod : (e - b) * ((i.val : ℝ) / (J : ℝ)) ≤ e - b :=
        calc
          (e - b) * ((i.val : ℝ) / (J : ℝ)) ≤ (e - b) * 1 :=
            mul_le_mul_of_nonneg_left hfrac hLpos.le
          _ = e - b := by ring
      calc
        b + (e - b) * (i.val : ℝ) / (J : ℝ) =
            b + (e - b) * ((i.val : ℝ) / (J : ℝ)) := by ring
        _ ≤ b + (e - b) := by simpa [add_comm] using add_le_add_left hprod b
        _ = e := by ring
  · intro i j hij
    have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    have hq : (i.val : ℝ) / (J : ℝ) < (j.val : ℝ) / (J : ℝ) :=
      (div_lt_div_iff₀ hJreal hJreal).2 (by nlinarith)
    dsimp [γ]
    have hbe' : 0 < e - b := sub_pos.mpr hbe
    have hprod := mul_lt_mul_of_pos_left hq hbe'
    calc
      b + (e - b) * (i.val : ℝ) / (J : ℝ) =
          b + (e - b) * ((i.val : ℝ) / (J : ℝ)) := by ring
      _ < b + (e - b) * ((j.val : ℝ) / (J : ℝ)) := by
        simpa [add_comm] using add_lt_add_left hprod b
      _ = b + (e - b) * (j.val : ℝ) / (J : ℝ) := by ring
  · intro j
    have hstep : γ j.succ - γ j.castSucc = (e - b) / (J : ℝ) := by
      simp [γ, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      ring
    constructor
    ·
      have hstepPos : 0 < (e - b) / (J : ℝ) := div_pos (sub_pos.mpr hbe) hJreal
      have hstepPos' : 0 < γ j.succ - γ j.castSucc := by rw [hstep]; exact hstepPos
      exact sub_pos.mp hstepPos'
    ·
      have hmesh : (e - b) / (J : ℝ) < δ :=
        (div_lt_iff₀ hJreal).2 (by nlinarith [hL])
      rw [hstep]
      exact hmesh

theorem exists_partition_cell {J : ℕ} (hJ : 0 < J) (γ : Fin (J + 1) → ℝ)
    (b e t : ℝ) (hγ0 : γ 0 = b) (hγend : γ (Fin.last J) = e)
    (hγstrict : ∀ i j, i.val < j.val → γ i < γ j)
    (hbt : b < t) (hte : t ≤ e) :
    ∃ j : Fin J, γ j.castSucc < t ∧ t ≤ γ j.succ := by
  classical
  let S : Finset (Fin (J + 1)) := Finset.univ.filter fun i => t ≤ γ i
  have hS : S.Nonempty := by
    refine ⟨Fin.last J, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hγend]
    exact hte
  let i : Fin (J + 1) := S.min' hS
  have hiMem : i ∈ S := S.min'_mem hS
  have hiPos : 0 < i.val := by
    by_contra h
    have hizero : i.val = 0 := by omega
    have hi0 : i = 0 := Fin.ext hizero
    have hit := (Finset.mem_filter.mp hiMem).2
    rw [hi0, hγ0] at hit
    linarith
  have hiPred : i.val - 1 < J := by omega
  let j : Fin J := ⟨i.val - 1, hiPred⟩
  have hpred : Fin.castSucc j = ⟨i.val - 1, by omega⟩ := Fin.ext rfl
  have hsucc : Fin.succ j = i := by
    apply Fin.ext
    simp [j]
    omega
  have hprevNot : ¬ t ≤ γ (Fin.castSucc j) := by
    intro h
    have hpMem : Fin.castSucc j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hmin := S.min'_le (Fin.castSucc j) hpMem
    have hval : i.val ≤ (Fin.castSucc j).val := by exact_mod_cast hmin
    have : i.val ≤ i.val - 1 := by simpa [j] using hval
    omega
  have hlow : γ (Fin.castSucc j) < t := lt_of_not_ge hprevNot
  have hup : t ≤ γ (Fin.succ j) := by
    simpa [hsucc] using (Finset.mem_filter.mp hiMem).2
  exact ⟨j, hlow, hup⟩

theorem exists_pow_partition_cell {J : ℕ} (hJ : 0 < J) (γ : Fin (J + 1) → ℝ)
    (x b e : ℝ) (hx : 1 < x) (hb : 0 < b) (hbe : b < e)
    (hγ0 : γ 0 = b) (hγend : γ (Fin.last J) = e)
    (hγstrict : ∀ i j, i.val < j.val → γ i < γ j)
    (q : ℕ) (hq : q.Prime) (hqlower : Real.rpow x b < (q : ℝ))
    (hqupper : (q : ℝ) ≤ Real.rpow x e) :
    ∃ j : Fin J, Real.rpow x (γ j.castSucc) < (q : ℝ) ∧
      (q : ℝ) ≤ Real.rpow x (γ j.succ) := by
  have hxpos : 0 < x := by linarith
  have hxne : x ≠ 1 := ne_of_gt hx
  have hxlog : 0 < Real.log x := Real.log_pos hx
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hloglo : b * Real.log x < Real.log (q : ℝ) := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos b) hqlower
    rw [Real.log_rpow hxpos b] at h
    simpa [mul_comm] using h
  have hloghi : Real.log (q : ℝ) ≤ e * Real.log x := by
    calc
      Real.log (q : ℝ) ≤ Real.log (Real.rpow x e) := Real.log_le_log hqpos hqupper
      _ = e * Real.log x := Real.log_rpow hxpos e
  let t : ℝ := Real.log (q : ℝ) / Real.log x
  have htlower : b < t := by
    dsimp [t]
    exact (lt_div_iff₀ hxlog).2 hloglo
  have htupper : t ≤ e := by
    dsimp [t]
    exact (div_le_iff₀ hxlog).2 hloghi
  obtain ⟨j, hjlo, hjhi⟩ := exists_partition_cell hJ γ b e t hγ0 hγend
    hγstrict htlower htupper
  have hqeq : Real.rpow x t = (q : ℝ) := by
    simpa [t, Real.logb] using Real.rpow_logb hxpos hxne hqpos
  refine ⟨j, ?_, ?_⟩
  · rw [← hqeq]
    exact Real.rpow_lt_rpow_of_exponent_lt hx hjlo
  · rw [← hqeq]
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) hjhi

theorem minFac_bin_factorization {J : ℕ} (hJ : 0 < J) (γ : Fin (J + 1) → ℝ)
    (x b e : ℝ) (hx : 1 < x) (hb : 0 < b) (hbe : b < e)
    (hγ0 : γ 0 = b) (hγend : γ (Fin.last J) = e)
    (hγstrict : ∀ i j, i.val < j.val → γ i < γ j)
    (d : ℕ) (hd : 1 < d)
    (hrough : ArtinPrimitiveRoots.TypeII.roughAbove d (Real.rpow x b))
    (hnot : ¬ ArtinPrimitiveRoots.TypeII.roughAbove d (Real.rpow x e)) :
    ∃ j : Fin J, ∃ q m : ℕ,
      q.Prime ∧ q ∣ d ∧ m = d / q ∧ d = m * q ∧
      Real.rpow x (γ j.castSucc) < (q : ℝ) ∧
      (q : ℝ) ≤ Real.rpow x (γ j.succ) ∧
      ArtinPrimitiveRoots.TypeII.roughAbove m (Real.rpow x (γ j.castSucc)) := by
  let q : ℕ := Nat.minFac d
  have hqprime : q.Prime := Nat.minFac_prime (by omega)
  have hqdvd : q ∣ d := by dsimp [q]; exact Nat.minFac_dvd d
  have hqlower : Real.rpow x b < (q : ℝ) := hrough q hqprime hqdvd
  have hbad : ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ (p : ℝ) ≤ Real.rpow x e := by
    by_contra h
    apply hnot
    intro p hp hpd
    by_contra hlt
    exact h ⟨p, hp, hpd, le_of_not_gt hlt⟩
  obtain ⟨p, hp, hpd, hple⟩ := hbad
  have hqle : q ≤ p := Nat.minFac_le_of_dvd hp.two_le (by simpa [q] using hpd)
  have hqupper : (q : ℝ) ≤ Real.rpow x e := by
    exact (Nat.cast_le.mpr hqle).trans hple
  have hxpos : 0 < x := by linarith
  have hxne : x ≠ 1 := ne_of_gt hx
  have hxlog : 0 < Real.log x := Real.log_pos hx
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqprime.pos
  have hloglo : b * Real.log x < Real.log (q : ℝ) := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos b) hqlower
    rw [Real.log_rpow hxpos b] at h
    simpa [mul_comm] using h
  have hloghi : Real.log (q : ℝ) ≤ e * Real.log x := by
    calc
      Real.log (q : ℝ) ≤ Real.log (Real.rpow x e) := Real.log_le_log hqpos hqupper
      _ = e * Real.log x := Real.log_rpow hxpos e
  let t : ℝ := Real.log (q : ℝ) / Real.log x
  have htlower : b < t := by
    dsimp [t]
    exact (lt_div_iff₀ hxlog).2 hloglo
  have htupper : t ≤ e := by
    dsimp [t]
    exact (div_le_iff₀ hxlog).2 hloghi
  obtain ⟨j, hjlo, hjhi⟩ := exists_partition_cell hJ γ b e t hγ0 hγend
    hγstrict htlower htupper
  have hqeq : Real.rpow x t = (q : ℝ) := by
    simpa [t, Real.logb] using Real.rpow_logb hxpos hxne hqpos
  let m : ℕ := d / q
  have hfactor : d = m * q := by
    dsimp [m]
    exact (Nat.div_mul_cancel hqdvd).symm
  have hqlo : Real.rpow x (γ j.castSucc) < (q : ℝ) := by
    rw [← hqeq]
    exact Real.rpow_lt_rpow_of_exponent_lt hx hjlo
  have hqhi : (q : ℝ) ≤ Real.rpow x (γ j.succ) := by
    rw [← hqeq]
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) hjhi
  have hmrough : ArtinPrimitiveRoots.TypeII.roughAbove m
      (Real.rpow x (γ j.castSucc)) := by
    intro r hr hrdvd
    have hmd : m ∣ d := by
      dsimp [m]
      exact Nat.div_dvd_of_dvd hqdvd
    have hrd : r ∣ d := dvd_trans hrdvd hmd
    have hqleR : q ≤ r := Nat.minFac_le_of_dvd hr.two_le hrd
    have hqleR' : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hqleR
    exact lt_of_lt_of_le hqlo hqleR'
  exact ⟨j, q, m, hqprime, hqdvd, rfl, hfactor, hqlo, hqhi, hmrough⟩

theorem roughDensityTerm_nonneg (γ w : ℝ) (hγ : 0 < γ) (hw : 0 < w) (j : ℕ) :
    0 ≤ ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j := by
  by_cases hj0 : j = 0
  · simp [ArtinPrimitiveRoots.Sieve.roughDensityTerm, hj0]
  by_cases hj1 : j = 1
  · simp [ArtinPrimitiveRoots.Sieve.roughDensityTerm, hj1]
    positivity
  rw [ArtinPrimitiveRoots.Sieve.roughDensityTerm]
  simp only [if_neg hj0, if_neg hj1]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro t
  by_cases ht : t ∈ {t : Fin (j - 1) → ℝ |
      (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}
  · have ht' : (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ := ht
    simp only [Set.indicator_of_mem ht]
    have hden : 0 < w - ∑ i, t i := by linarith [ht'.2]
    have hprod : 0 ≤ ∏ i, (1 / t i) := by
      apply Finset.prod_nonneg
      intro i hi
      have hi' : 0 < t i := lt_of_lt_of_le hγ (ht'.1 i)
      positivity
    exact mul_nonneg (div_nonneg (by norm_num) hden.le) hprod
  · simp [Set.indicator_of_notMem ht]

theorem roughDensity_nonneg (γ w : ℝ) (hγ : 0 < γ) (hw : 0 < w) :
    0 ≤ ArtinPrimitiveRoots.Sieve.roughDensity γ w := by
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  apply tsum_nonneg
  intro j
  exact roughDensityTerm_nonneg γ w hγ hw j

theorem roughDensityTerm_zero_of_width (γ w : ℝ) (hγ : 0 < γ) (hw : w < 2 * γ)
    {j : ℕ} (hj : 2 ≤ j) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j = 0 := by
  unfold ArtinPrimitiveRoots.Sieve.roughDensityTerm
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  rw [if_neg hj0, if_neg hj1]
  let S : Set (Fin (j - 1) → ℝ) :=
    {t | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}
  let f : (Fin (j - 1) → ℝ) → ℝ :=
    fun t => (1 / (w - ∑ i, t i)) * ∏ i, (1 / t i)
  have hfun : S.indicator f = 0 := by
    funext t
    by_cases ht : t ∈ S
    · have ht' : (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ := ht
      have hi : Fin (j - 1) := ⟨0, by omega⟩
      have hsum : t hi ≤ ∑ i, t i := by
        apply Finset.single_le_sum
        · intro i _
          exact le_trans hγ.le (ht'.1 i)
        · exact Finset.mem_univ hi
      have hden : w - γ < γ := by nlinarith
      have : False := by linarith [ht'.2, ht'.1 hi, hsum]
      exact this.elim
    · rw [Set.indicator_of_notMem ht]
      rfl
  have hfun' : (fun t => Set.indicator
      {t : Fin (j - 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}
      (fun t => (1 / (w - ∑ i, t i)) * ∏ i, (1 / t i)) t) = 0 := by
    simpa [S, f] using hfun
  rw [hfun']
  simp

theorem roughDensity_eq_one_div (γ w : ℝ) (hγ : 0 < γ) (hw : w < 2 * γ) :
    ArtinPrimitiveRoots.Sieve.roughDensity γ w = 1 / w := by
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  calc
    (∑' j : ℕ, ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j) =
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w 1 :=
      tsum_eq_single 1 (fun j hj => by
        by_cases hj0 : j = 0
        · simp [ArtinPrimitiveRoots.Sieve.roughDensityTerm, hj0]
        by_cases hj1 : j = 1
        · exact (hj hj1).elim
        · have hj' : 2 ≤ j := by omega
          exact roughDensityTerm_zero_of_width γ w hγ hw hj')
    _ = 1 / w := by simp [ArtinPrimitiveRoots.Sieve.roughDensityTerm]

theorem roughDensity_integrand_continuous (b κ : ℝ) (hb : 0 < b)
    (hκ : 0 < κ) (hκsmall : κ < 1 / 100) (hbκ : b < 1 / 2 - κ) :
    ContinuousOn (fun t : ℝ =>
      ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t) (Set.Icc b (1 / 2)) := by
  let c : ℝ := 1 / 2 - κ / 2
  let f : ℝ → ℝ := fun t => ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t
  have hbc : b ≤ c := by dsimp [c]; linarith
  have hcHalf : c ≤ 1 / 2 := by dsimp [c]; linarith
  have hcThird : 1 / 3 < c := by dsimp [c]; linarith
  have hleft : ContinuousOn f (Set.Icc b c) := by
    have hD := ArtinPrimitiveRoots.TypeII.Rough.density_regularity.1
    have hpair : ContinuousOn (fun t : ℝ => (t, 1 - t)) (Set.Icc b c) := by fun_prop
    have hmap : Set.MapsTo (fun t : ℝ => (t, 1 - t)) (Set.Icc b c)
        {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
      intro t ht
      rcases ht with ⟨htlo, hthi⟩
      constructor
      · exact lt_of_lt_of_le hb htlo
      · have htc : t ≤ c := hthi
        dsimp [c] at htc
        linarith
    have hcomp : ContinuousOn (fun t : ℝ =>
        ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t)) (Set.Icc b c) := by
      change ContinuousOn
        ((fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2) ∘
          (fun t : ℝ => (t, 1 - t))) (Set.Icc b c)
      exact hD.comp hpair hmap
    have hden : ∀ t ∈ Set.Icc b c, t ≠ 0 := by
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le hb ht.1)
    have hdiv := hcomp.div continuousOn_id hden
    change ContinuousOn (fun t : ℝ =>
      ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t) (Set.Icc b c)
    exact hdiv
  have hright : ContinuousOn f (Set.Icc c (1 / 2)) := by
    have heq : ∀ t ∈ Set.Icc c (1 / 2), f t = 1 / (t * (1 - t)) := by
      intro t ht
      rcases ht with ⟨htlo, hthi⟩
      have htpos : 0 < t := lt_trans (by norm_num) (lt_of_lt_of_le hcThird htlo)
      have hwidth : 1 - t < 2 * t := by linarith
      have hwpos : 0 < 1 - t := by linarith
      dsimp [f]
      rw [roughDensity_eq_one_div t (1 - t) htpos hwidth]
      have hden : 1 - t ≠ 0 := by linarith
      have htne : t ≠ 0 := ne_of_gt htpos
      field_simp
    have hrat : ContinuousOn (fun t : ℝ => 1 / (t * (1 - t)))
        (Set.Icc c (1 / 2)) := by
      apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      intro t ht
      rcases ht with ⟨htlo, hthi⟩
      apply mul_ne_zero
      · exact ne_of_gt (lt_trans (by norm_num) (lt_of_lt_of_le hcThird htlo))
      · have hpos : 0 < 1 - t := by nlinarith [hthi]
        exact ne_of_gt hpos
    exact hrat.congr heq
  have hunion : Set.Icc b (1 / 2) = Set.Icc b c ∪ Set.Icc c (1 / 2) := by
    ext t
    simp only [Set.mem_Icc, Set.mem_union]
    constructor
    · rintro ⟨htb, ht⟩
      by_cases htc : t ≤ c
      · exact Or.inl ⟨htb, htc⟩
      · exact Or.inr ⟨le_of_not_ge htc, ht⟩
    · rintro (⟨htb, htc⟩ | ⟨htc, ht⟩) <;> constructor <;> linarith
  rw [hunion]
  exact hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc

theorem roughDensity_integral_le (b κ : ℝ) (hb : 0 < b) (hκ : 0 < κ)
    (hκsmall : κ < 1 / 100) (hbκ : b < 1 / 2 - κ) :
    (∫ t in b..(1 / 2 - κ),
      ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t) ≤
      ArtinPrimitiveRoots.Sieve.roughDensity b 1 - 1 := by
  have hbHalf : b < 1 / 2 := by linarith
  have hright : b ≤ 1 / 2 - κ := le_of_lt hbκ
  have htop : 1 / 2 - κ ≤ 1 / 2 := by linarith
  have hcont := roughDensity_integrand_continuous b κ hb hκ hκsmall hbκ
  have hfi : IntervalIntegrable
      (fun t : ℝ => ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t)
      volume b (1 / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hbHalf) hcont
  have hnonneg : ∀ t ∈ Set.Icc b (1 / 2),
      0 ≤ ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hb ht.1
    have hwpos : 0 < 1 - t := by linarith [ht.2]
    exact div_nonneg (roughDensity_nonneg t (1 - t) htpos hwpos) htpos.le
  have hnonnegAE :
      0 ≤ᵐ[volume.restrict (Set.Ioc b (1 / 2))]
        (fun t : ℝ => ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hnonneg t (Set.Ioc_subset_Icc_self ht)
  have hmono := intervalIntegral.integral_mono_interval le_rfl hright htop hnonnegAE hfi
  calc
    (∫ t in b..(1 / 2 - κ),
        ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t) ≤
        ∫ t in b..(1 / 2), ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t := hmono
    _ = ArtinPrimitiveRoots.Sieve.roughDensity b 1 - 1 :=
      ArtinPrimitiveRoots.Sieve.lem_density.1 b hb hbHalf

theorem exists_roughDensity_partition_budget (b e : ℝ) (hb : 0 < b)
    (hbe : b < e) (he : e < 1 / 2) :
    ∃ J : ℕ, ∃ γ : Fin (J + 1) → ℝ,
      0 < J ∧ γ 0 = b ∧ γ (Fin.last J) = e ∧
      (∀ i, b ≤ γ i ∧ γ i ≤ e) ∧
      (∀ i j, i.val < j.val → γ i < γ j) ∧
      (∑ j : Fin J,
        sSup ((fun t : ℝ => ArtinPrimitiveRoots.Sieve.roughDensity
          (γ j.castSucc) (1 - t)) '' Set.Icc (γ j.castSucc) (γ j.succ)) *
          Real.log (γ j.succ / γ j.castSucc)) ≤
        ∫ t in b..e, ArtinPrimitiveRoots.Sieve.roughDensity t (1 - t) / t + 1 / 10 := by
  let D : ℝ × ℝ → ℝ := fun p => ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2
  let F : ℝ → ℝ := fun t => D (t, 1 - t) / t
  have hratio : 1 < e / b := (one_lt_div hb).2 hbe
  have hlog : 0 < Real.log (e / b) := Real.log_pos hratio
  let ε : ℝ := (e - b) / (100 * (Real.log (e / b) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let K : Set (ℝ × ℝ) := Set.Icc b e ×ˢ Set.Icc (1 - e) (1 - b)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKsub : K ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rcases hx with ⟨hxlo, hxhi⟩
    rcases hy with ⟨hylo, hyhi⟩
    change 0 < x ∧ x < y
    constructor
    · exact lt_of_lt_of_le hb hxlo
    · have hmid : e < 1 - e := by linarith
      linarith
  have hDcont : ContinuousOn D K := by
    have h := ArtinPrimitiveRoots.TypeII.Rough.density_regularity.1
    exact h.mono hKsub
  have hUC : UniformContinuousOn D K := hK.uniformContinuousOn_of_continuous hDcont
  obtain ⟨δ, hδ, hδmod⟩ := (Metric.uniformContinuousOn_iff.mp hUC) ε hε
  have hgap : 0 < 1 / 2 - e := by linarith
  let κ₀ : ℝ := min (1 / 200) ((1 / 2 - e) / 2)
  have hκ₀ : 0 < κ₀ := lt_min (by norm_num) (by positivity)
  have hκ₀small : κ₀ < 1 / 100 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have heκ₀ : e < 1 / 2 - κ₀ := by
    have hκ₀right : κ₀ ≤ (1 / 2 - e) / 2 := min_le_right _ _
    dsimp [κ₀] at hκ₀right
    linarith
  have hbκ₀ : b < 1 / 2 - κ₀ := hbe.trans heκ₀
  have hFcont := roughDensity_integrand_continuous b κ₀ hb hκ₀ hκ₀small hbκ₀
  have hepsmesh : 0 < δ / 4 := by positivity
  obtain ⟨J, γ, hJ, hγ0, hγend, hγrange, hγstrict, hmesh⟩ :=
    exists_strict_partition_mesh b e (δ / 4) hbe hepsmesh
  let grid : ℕ → ℝ := fun k => if hk : k ≤ J then γ ⟨k, by omega⟩ else e
  have hgrid0 : grid 0 = b := by simp [grid, hγ0]
  have hlast : (⟨J, Nat.lt_succ_self J⟩ : Fin (J + 1)) = Fin.last J := by
    apply Fin.ext
    rfl
  have hgridJ : grid J = e := by
    have hidx : (⟨J, Nat.lt_succ_self J⟩ : Fin (J + 1)) = Fin.last J := hlast
    have hgrid : grid J = γ ⟨J, Nat.lt_succ_self J⟩ := by simp [grid]
    rw [hgrid, hidx, hγend]
  have hgridCast (j : Fin J) : grid j.val = γ j.castSucc := by
    have hjle : j.val ≤ J := le_of_lt j.isLt
    have hfin : (⟨j.val, by omega⟩ : Fin (J + 1)) = j.castSucc := by
      apply Fin.ext
      rfl
    have hgrid : grid j.val = γ ⟨j.val, by omega⟩ := by simp [grid, hjle]
    rw [hgrid, hfin]
  have hgridSucc (j : Fin J) : grid (j.val + 1) = γ j.succ := by
    have hjle : j.val + 1 ≤ J := Nat.succ_le_of_lt j.isLt
    have hfin : (⟨j.val + 1, by omega⟩ : Fin (J + 1)) = j.succ := by
      apply Fin.ext
      rfl
    have hgrid : grid (j.val + 1) = γ ⟨j.val + 1, by omega⟩ := by simp [grid, hjle]
    rw [hgrid, hfin]
  refine ⟨J, γ, hJ, hγ0, hγend, hγrange, hγstrict, ?_⟩
  have hFint (a z : ℝ) (ha : b ≤ a) (hz : z ≤ e) (haz : a ≤ z) :
      IntervalIntegrable F volume a z := by
    apply ContinuousOn.intervalIntegrable_of_Icc haz
    apply hFcont.mono
    intro t ht
    exact ⟨le_trans ha ht.1, le_trans ht.2 (by linarith [hz, he])⟩
  have hInvint (a z : ℝ) (ha : 0 < a) (hz : 0 < z) (haz : a ≤ z) :
      IntervalIntegrable (fun t : ℝ => 1 / t) volume a z := by
    apply ContinuousOn.intervalIntegrable_of_Icc haz
    apply continuousOn_const.div continuousOn_id
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le ha ht.1)
  have hFadj (k : ℕ) (hk : k < J) :
      IntervalIntegrable F volume (grid k) (grid (k + 1)) := by
    let j : Fin J := ⟨k, hk⟩
    have hm := hmesh j
    have hleft := hgridCast j
    have hright := hgridSucc j
    have hrangeL := hγrange j.castSucc
    have hrangeR := hγrange j.succ
    have hF' := hFint (γ j.castSucc) (γ j.succ) hrangeL.1 hrangeR.2 hm.1.le
    rw [hleft, hright]
    exact hF'
  have hInvadj (k : ℕ) (hk : k < J) :
      IntervalIntegrable (fun t : ℝ => 1 / t) volume (grid k) (grid (k + 1)) := by
    let j : Fin J := ⟨k, hk⟩
    have hm := hmesh j
    have hleft := hgridCast j
    have hright := hgridSucc j
    have hrangeL := hγrange j.castSucc
    have hrangeR := hγrange j.succ
    have hInv' := hInvint (γ j.castSucc) (γ j.succ)
      (lt_of_lt_of_le hb hrangeL.1) (lt_of_lt_of_le hb hrangeR.1) hm.1.le
    rw [hleft, hright]
    exact hInv'
  have hPairMem (x : ℝ) (hx : x ∈ Set.Icc b e) : (x, 1 - x) ∈ K := by
    change x ∈ Set.Icc b e ∧ 1 - x ∈ Set.Icc (1 - e) (1 - b)
    constructor
    · exact hx
    · constructor <;> linarith [hx.1, hx.2]
  have hBounds (j : Fin J) :
      let a := γ j.castSucc
      let z := γ j.succ
      a < z ∧ z - a < δ := by
    have hm := hmesh j
    constructor
    · exact hm.1
    · linarith [hm.2, hδ]
  have hCell (j : Fin J) :
      let a := γ j.castSucc
      let z := γ j.succ
      let S := sSup ((fun t : ℝ => D (a, 1 - t)) '' Set.Icc a z)
      S * Real.log (z / a) ≤
        (∫ t in a..z, F t) + 2 * ε * Real.log (z / a) := by
    dsimp
    let a : ℝ := γ j.castSucc
    let z : ℝ := γ j.succ
    have haz : a < z := (hBounds j).1
    have hwidth : z - a < δ := (hBounds j).2
    have haRange : a ∈ Set.Icc b e := hγrange j.castSucc
    have hzRange : z ∈ Set.Icc b e := hγrange j.succ
    have hSne : ((fun t : ℝ => D (a, 1 - t)) '' Set.Icc a z).Nonempty := by
      refine ⟨D (a, 1 - a), ?_⟩
      exact ⟨a, ⟨le_rfl, haz.le⟩, rfl⟩
    have hval : ∀ s ∈ Set.Icc a z, ∀ t ∈ Set.Icc a z,
        D (a, 1 - s) ≤ D (t, 1 - t) + 2 * ε := by
      intro s hs t ht
      have hsRange : s ∈ Set.Icc b e :=
        ⟨le_trans haRange.1 hs.1, le_trans hs.2 hzRange.2⟩
      have htRange : t ∈ Set.Icc b e :=
        ⟨le_trans haRange.1 ht.1, le_trans ht.2 hzRange.2⟩
      have hcrossMem : (a, 1 - s) ∈ K := by
        change a ∈ Set.Icc b e ∧ 1 - s ∈ Set.Icc (1 - e) (1 - b)
        exact ⟨haRange, by constructor <;> linarith [hsRange.1, hsRange.2]⟩
      have hsmem := hPairMem s hsRange
      have htmem := hPairMem t htRange
      have hcrossDist : dist (a, 1 - s) (s, 1 - s) < δ := by
        calc
          dist (a, 1 - s) (s, 1 - s) = dist a s := dist_prod_same_right
          _ = s - a := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.1)]; ring
          _ ≤ z - a := sub_le_sub_right hs.2 a
          _ < δ := hwidth
      have hdiagEq : dist (s, 1 - s) (t, 1 - t) = dist s t := by
        rw [Prod.dist_eq]
        have hsecond : dist (1 - s) (1 - t) = dist s t := by
          rw [Real.dist_eq, Real.dist_eq]
          have hsub : (1 - s) - (1 - t) = t - s := by ring
          rw [hsub, abs_sub_comm]
        rw [hsecond, max_self]
      have hstAbs : |s - t| ≤ z - a := by
        apply abs_le.mpr
        constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      have hdiagDist : dist (s, 1 - s) (t, 1 - t) < δ := by
        rw [hdiagEq, Real.dist_eq]
        exact hstAbs.trans_lt (by linarith [hwidth])
      have hc := hδmod (a, 1 - s) hcrossMem (s, 1 - s) hsmem hcrossDist
      have hd := hδmod (s, 1 - s) hsmem (t, 1 - t) htmem hdiagDist
      have hc' : |D (a, 1 - s) - D (s, 1 - s)| < ε := by
        simpa [Real.dist_eq] using hc
      have hd' : |D (s, 1 - s) - D (t, 1 - t)| < ε := by
        simpa [Real.dist_eq] using hd
      linarith [abs_le.mp hc'.le, abs_le.mp hd'.le]
    have hsup : ∀ t ∈ Set.Icc a z,
        sSup ((fun s : ℝ => D (a, 1 - s)) '' Set.Icc a z) ≤
          D (t, 1 - t) + 2 * ε := by
      intro t ht
      apply csSup_le hSne
      intro y hy
      rcases hy with ⟨s, hs, rfl⟩
      exact hval s hs t ht
    let G₁ : ℝ → ℝ := fun t => sSup ((fun s : ℝ => D (a, 1 - s)) '' Set.Icc a z) / t
    let G₂ : ℝ → ℝ := fun t => F t + 2 * ε / t
    have hG₁cont : ContinuousOn G₁ (Set.Icc a z) := by
      apply continuousOn_const.div continuousOn_id
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le hb haRange.1) ht.1)
    have hFcell : ContinuousOn F (Set.Icc a z) := by
      apply hFcont.mono
      intro t ht
      exact ⟨le_trans haRange.1 ht.1, le_trans ht.2 (by linarith [hzRange.2, he])⟩
    have hTwocont : ContinuousOn (fun t : ℝ => 2 * ε / t) (Set.Icc a z) := by
      apply continuousOn_const.div continuousOn_id
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le hb haRange.1) ht.1)
    have hG₂cont : ContinuousOn G₂ (Set.Icc a z) := by
      dsimp [G₂]
      exact hFcell.add hTwocont
    have hG₁int : IntervalIntegrable G₁ volume a z :=
      ContinuousOn.intervalIntegrable_of_Icc haz.le hG₁cont
    have hG₂int : IntervalIntegrable G₂ volume a z :=
      ContinuousOn.intervalIntegrable_of_Icc haz.le hG₂cont
    have hFcellInt : IntervalIntegrable F volume a z :=
      hFint a z haRange.1 hzRange.2 haz.le
    have hInvcellInt : IntervalIntegrable (fun t : ℝ => 1 / t) volume a z :=
      hInvint a z (lt_of_lt_of_le hb haRange.1) (lt_of_lt_of_le hb hzRange.1) haz.le
    have hpoint : ∀ t ∈ Set.Icc a z, G₁ t ≤ G₂ t := by
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le hb haRange.1) ht.1
      dsimp [G₁, G₂]
      calc
        _ ≤ (D (t, 1 - t) + 2 * ε) / t := div_le_div_of_nonneg_right (hsup t ht) htpos.le
        _ = F t + 2 * ε / t := by dsimp [F]; ring
    have hmono := intervalIntegral.integral_mono_on haz.le hG₁int hG₂int hpoint
    have hinv := integral_one_div_of_pos
      (lt_of_lt_of_le hb haRange.1) (lt_of_lt_of_le hb hzRange.1)
    have hleftEq : (∫ t in a..z, G₁ t) =
        sSup ((fun s : ℝ => D (a, 1 - s)) '' Set.Icc a z) * Real.log (z / a) := by
      calc
        (∫ t in a..z, G₁ t) =
            ∫ t in a..z, sSup ((fun s : ℝ => D (a, 1 - s)) '' Set.Icc a z) * (1 / t) := by
              apply intervalIntegral.integral_congr
              intro t ht
              dsimp [G₁]
              ring
        _ = sSup ((fun s : ℝ => D (a, 1 - s)) '' Set.Icc a z) *
              (∫ t in a..z, 1 / t) := intervalIntegral.integral_const_mul _ _
        _ = _ := by rw [hinv]
    have hrightEq : (∫ t in a..z, G₂ t) =
        (∫ t in a..z, F t) + 2 * ε * Real.log (z / a) := by
      calc
        (∫ t in a..z, G₂ t) =
            (∫ t in a..z, F t) + (∫ t in a..z, 2 * ε * (1 / t)) := by
              calc
                (∫ t in a..z, G₂ t) =
                    ∫ t in a..z, F t + 2 * ε * (1 / t) := by
                      apply intervalIntegral.integral_congr
                      intro t ht
                      dsimp [G₂]
                      ring
                _ = (∫ t in a..z, F t) + (∫ t in a..z, 2 * ε * (1 / t)) :=
                  intervalIntegral.integral_add hFcellInt
                    (hInvcellInt.const_mul (2 * ε))
        _ = (∫ t in a..z, F t) +
              2 * ε * (∫ t in a..z, 1 / t) := by
              rw [intervalIntegral.integral_const_mul]
        _ = _ := by rw [hinv]
    calc
      sSup ((fun s : ℝ => D (a, 1 - s)) '' Set.Icc a z) * Real.log (z / a) =
          ∫ t in a..z, G₁ t := hleftEq.symm
      _ ≤ ∫ t in a..z, G₂ t := hmono
      _ = _ := hrightEq
  have hsumF :
      (∑ j : Fin J, ∫ t in γ j.castSucc..γ j.succ, F t) = ∫ t in b..e, F t := by
    let g : ℕ → ℝ := fun k => ∫ t in grid k..grid (k + 1), F t
    have hconvert :
        (∑ j : Fin J, ∫ t in γ j.castSucc..γ j.succ, F t) =
          ∑ j : Fin J, g j.val := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [g, hgridCast, hgridSucc]
    have hsum : (∑ j : Fin J, g j.val) = ∑ k ∈ Finset.range J, g k :=
      Fin.sum_univ_eq_sum_range g J
    have hadj := intervalIntegral.sum_integral_adjacent_intervals
      (f := F) (μ := volume) (a := grid) (n := J) hFadj
    calc
      _ = ∑ j : Fin J, g j.val := hconvert
      _ = ∑ k ∈ Finset.range J, g k := hsum
      _ = ∫ t in b..e, F t := by simpa [g, hgrid0, hgridJ] using hadj
  have hsumInv :
      (∑ j : Fin J, ∫ t in γ j.castSucc..γ j.succ, 1 / t) =
        ∫ t in b..e, 1 / t := by
    let g : ℕ → ℝ := fun k => ∫ t in grid k..grid (k + 1), 1 / t
    have hconvert :
        (∑ j : Fin J, ∫ t in γ j.castSucc..γ j.succ, 1 / t) =
          ∑ j : Fin J, g j.val := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [g, hgridCast, hgridSucc]
    have hsum : (∑ j : Fin J, g j.val) = ∑ k ∈ Finset.range J, g k :=
      Fin.sum_univ_eq_sum_range g J
    have hadj := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun t : ℝ => 1 / t) (μ := volume) (a := grid) (n := J) hInvadj
    calc
      _ = ∑ j : Fin J, g j.val := hconvert
      _ = ∑ k ∈ Finset.range J, g k := hsum
      _ = ∫ t in b..e, 1 / t := by simpa [g, hgrid0, hgridJ] using hadj
  have hlogsum :
      (∑ j : Fin J, Real.log (γ (Fin.succ j) / γ (Fin.castSucc j))) = Real.log (e / b) := by
    calc
      _ = ∑ j : Fin J, ∫ t in γ j.castSucc..γ j.succ, 1 / t := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_one_div_of_pos
          (lt_of_lt_of_le hb (hγrange (Fin.castSucc j)).1)
          (lt_of_lt_of_le hb (hγrange (Fin.succ j)).1)]
      _ = ∫ t in b..e, 1 / t := hsumInv
      _ = Real.log (e / b) := integral_one_div_of_pos hb (lt_of_lt_of_le hb hbe.le)
  have hsumle :
      (∑ j : Fin J,
        sSup ((fun t : ℝ => ArtinPrimitiveRoots.Sieve.roughDensity
          (γ (Fin.castSucc j)) (1 - t)) '' Set.Icc (γ (Fin.castSucc j)) (γ (Fin.succ j))) *
          Real.log (γ (Fin.succ j) / γ (Fin.castSucc j))) ≤
      (∑ j : Fin J,
        ((∫ t in γ (Fin.castSucc j)..γ (Fin.succ j), F t) +
          2 * ε * Real.log (γ (Fin.succ j) / γ (Fin.castSucc j)))) := by
    apply Finset.sum_le_sum
    intro j hj
    simpa [D] using hCell j
  have hErr : 2 * ε * Real.log (e / b) ≤ (e - b) / 10 := by
    dsimp [ε]
    have hden : 0 < 100 * (Real.log (e / b) + 1) := by positivity
    have hnum : 2 * Real.log (e / b) ≤
        (1 / 10) * (100 * (Real.log (e / b) + 1)) := by nlinarith [hlog]
    calc
      2 * ((e - b) / (100 * (Real.log (e / b) + 1))) * Real.log (e / b) =
          (e - b) * ((2 * Real.log (e / b)) / (100 * (Real.log (e / b) + 1))) := by ring
      _ ≤ (e - b) * (1 / 10) :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hden).2 hnum) (sub_nonneg.mpr hbe.le)
      _ = (e - b) / 10 := by ring
  calc
    _ ≤ ∑ j : Fin J,
        ((∫ t in γ j.castSucc..γ j.succ, F t) +
          2 * ε * Real.log (γ j.succ / γ j.castSucc)) := hsumle
    _ = (∑ j : Fin J, ∫ t in γ j.castSucc..γ j.succ, F t) +
        2 * ε * (∑ j : Fin J, Real.log (γ j.succ / γ j.castSucc)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (∫ t in b..e, F t) + 2 * ε * Real.log (e / b) := by rw [hsumF, hlogsum]
    _ ≤ (∫ t in b..e, F t) + (e - b) / 10 := by
      simpa [add_comm] using add_le_add_right hErr (∫ t in b..e, F t)
    _ = ∫ t in b..e, F t + 1 / 10 := by
      have hFintbe : IntervalIntegrable F volume b e := hFint b e le_rfl le_rfl hbe.le
      have hcint : IntervalIntegrable (fun _ : ℝ => (1 / 10 : ℝ)) volume b e := by
        exact continuousOn_const.intervalIntegrable
      have hcval : (∫ t in b..e, (1 / 10 : ℝ)) = (e - b) / 10 := by
        simp [intervalIntegral.integral_const]
        ring
      calc
        _ = (∫ t in b..e, F t) + (∫ t in b..e, (1 / 10 : ℝ)) := by rw [hcval]
        _ = ∫ t in b..e, F t + 1 / 10 := (intervalIntegral.integral_add hFintbe hcint).symm

end ArtinPrimitiveRoots.Construction.Proofs.C4
