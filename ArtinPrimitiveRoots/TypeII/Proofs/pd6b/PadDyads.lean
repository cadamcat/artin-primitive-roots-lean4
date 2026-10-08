import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.Damping

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical Filter

noncomputable section

/-- The strict band exponent gap supplies a fixed small coefficient in prime log bounds. -/
theorem markedPrimeLogs_small_eventually {K : ℕ} (a : Fin K → ℝ) (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → 1 ≤ Real.log x ∧
      ∀ i : Fin K, ∀ p ∈ primeBand x (a i),
        Real.log (p : ℝ) ≤ (Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hEvent : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K, ∀ p ∈ primeBand x (a i),
      Real.log (p : ℝ) ≤ (Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
    rw [Filter.eventually_all]
    intro i
    have hgap : 0 < (1 / 5 : ℝ) - a i := sub_pos.mpr (ha.2.1 i).2
    have ht : Tendsto (fun x : ℝ => Real.rpow (Real.log x) ((1 / 5 : ℝ) - a i))
        atTop atTop := (tendsto_rpow_atTop hgap).comp Real.tendsto_log_atTop
    filter_upwards [ht.eventually_ge_atTop (4 / Real.log 2), eventually_ge_atTop (2 : ℝ)] with x hg hx
    intro p hp
    have hL : 0 < Real.log x := Real.log_pos (by linarith)
    have hpa : 0 < Real.rpow (Real.log x) (a i) := Real.rpow_pos_of_pos hL _
    have hprod : Real.rpow (Real.log x) (1 / 5 : ℝ) =
        Real.rpow (Real.log x) (a i) * Real.rpow (Real.log x) ((1 / 5 : ℝ) - a i) := by
      calc
        _ = Real.rpow (Real.log x) (a i + ((1 / 5 : ℝ) - a i)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hL _ _
    have hsep : 2 * Real.rpow (Real.log x) (a i) ≤
        (Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
      rw [hprod]
      calc
        _ = (Real.log 2 / 2) * ((4 / Real.log 2) * Real.rpow (Real.log x) (a i)) := by
          field_simp [hlog2.ne']
          <;> ring
        _ ≤ (Real.log 2 / 2) *
            (Real.rpow (Real.log x) (a i) * Real.rpow (Real.log x) ((1 / 5 : ℝ) - a i)) :=
          mul_le_mul_of_nonneg_left
            (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hg hpa.le) (by positivity)
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hlogUpper := Real.log_le_log hpPos (Finset.mem_filter.mp hp).2.2.2
    have hlogP : Real.log (p : ℝ) ≤ 2 * Real.rpow (Real.log x) (a i) := by
      simpa only [Real.log_exp] using hlogUpper
    exact hlogP.trans hsep
  have hBoth : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      ∀ i : Fin K, ∀ p ∈ primeBand x (a i),
        Real.log (p : ℝ) ≤ (Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
    filter_upwards [hEvent, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
    exact ⟨hL, hx⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hBoth
  exact ⟨max 2 x₁, le_max_left _ _, fun x hx => hx₁ x ((le_max_right _ _).trans hx)⟩

/-- The small prime-log bound leaves room for every shared pad product's dyad. -/
theorem padChoicePrimeProduct_log_bound {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hL : 1 ≤ Real.log x)
    (hprimes : ∀ i : Fin K, ∀ p ∈ primeBand x (a i),
      Real.log (p : ℝ) ≤ (Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ))
    (d : PadChoice x K a) :
    Real.log (padChoicePrimeProduct x d : ℝ) ≤
      Real.log 2 * ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : Real.log (padChoicePrimeProduct x d : ℝ) =
      ∑ q : Fin K × Fin (momentJ x), Real.log ((d q).val : ℝ) := by
    unfold padChoicePrimeProduct
    rw [Nat.cast_prod, Real.log_prod]
    intro q hq
    have hp : (d q).val.Prime := (Finset.mem_filter.mp (d q).property).2.1
    exact (Nat.cast_pos.mpr hp.pos).ne'
  have hsum : Real.log (padChoicePrimeProduct x d : ℝ) ≤
      (K : ℝ) * (momentJ x : ℝ) *
        ((Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ)) := by
    rw [hprod]
    calc
      _ ≤ ∑ q : Fin K × Fin (momentJ x),
          (Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ) :=
        Finset.sum_le_sum (fun q hq => hprimes q.1 (d q).val (d q).property)
      _ = _ := by simp [mul_assoc]
  have hJ : (momentJ x : ℝ) ≤ Real.rpow (Real.log x) (1 / 100 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hLpos.le _)
  have hJoin : Real.rpow (Real.log x) (1 / 100 : ℝ) *
      Real.rpow (Real.log x) (1 / 5 : ℝ) = Real.rpow (Real.log x) (21 / 100 : ℝ) := by
    calc
      _ = Real.rpow (Real.log x) ((1 / 100 : ℝ) + (1 / 5 : ℝ)) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by norm_num
  have hPow : 0 ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hCoeff : (K : ℝ) * (Real.log 2 / 2) ≤ Real.log 2 * ((K : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) K]
  calc
    _ ≤ (K : ℝ) * (momentJ x : ℝ) *
        ((Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ)) := hsum
    _ ≤ (K : ℝ) * Real.rpow (Real.log x) (1 / 100 : ℝ) *
        ((Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg K))
        (mul_nonneg (by positivity) hPow)
    _ = (K : ℝ) * (Real.log 2 / 2) * Real.rpow (Real.log x) (21 / 100 : ℝ) := by
      rw [← hJoin]
      ring
    _ ≤ _ := by
      push_cast
      exact mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg hLpos.le (21 / 100 : ℝ))

private theorem dyad_pow_unique (k l : ℕ) (D : ℝ)
    (hklo : ((2 ^ k : ℕ) : ℝ) ≤ D) (hkhi : D < 2 * ((2 ^ k : ℕ) : ℝ))
    (hllo : ((2 ^ l : ℕ) : ℝ) ≤ D) (hlhi : D < 2 * ((2 ^ l : ℕ) : ℝ)) : k = l := by
  have hnotkl : ¬ k < l := by
    intro hkl
    have hp : 2 ^ (k + 1) ≤ (2 ^ l : ℕ) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpR : 2 * ((2 ^ k : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := by
      have hp' : 2 * (2 ^ k : ℕ) ≤ 2 ^ l := by simpa [pow_succ, Nat.mul_comm] using hp
      exact_mod_cast hp'
    linarith
  have hnotlk : ¬ l < k := by
    intro hlk
    have hp : 2 ^ (l + 1) ≤ (2 ^ k : ℕ) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpR : 2 * ((2 ^ l : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      have hp' : 2 * (2 ^ l : ℕ) ≤ 2 ^ k := by simpa [pow_succ, Nat.mul_comm] using hp
      exact_mod_cast hp'
    linarith
  omega

/-- The dyads in the frozen finite set cover a small positive pad product exactly once. -/
theorem padDyad_exists_unique (x : ℝ) (K D : ℕ) (hD : 0 < D) (hL : 0 ≤ Real.log x)
    (hLog : Real.log (D : ℝ) ≤
      Real.log 2 * ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)) :
    ∃! d₀ : ℕ, d₀ ∈ padScales x K ∧
      (d₀ : ℝ) ≤ (D : ℝ) ∧ (D : ℝ) < 2 * (d₀ : ℝ) := by
  let k := Nat.log 2 D
  have hLo : 2 ^ k ≤ D := Nat.pow_log_le_self 2 hD.ne'
  have hHi : D < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  have hLoR : ((2 ^ k : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hLo
  have hHiR : (D : ℝ) < 2 * ((2 ^ k : ℕ) : ℝ) := by
    have hHi' : D < 2 * (2 ^ k : ℕ) := by simpa [pow_succ, Nat.mul_comm] using hHi
    exact_mod_cast hHi'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogLo := Real.log_le_log (by positivity : 0 < ((2 ^ k : ℕ) : ℝ)) hLoR
  have hmul : (k : ℝ) * Real.log 2 ≤
      (((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)) * Real.log 2 := by
    have h := hlogLo.trans hLog
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_assoc, mul_comm, mul_left_comm] using h
  have hkR : (k : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) :=
    (mul_le_mul_iff_of_pos_right hlog2).mp hmul
  have hmem : 2 ^ k ∈ padScales x K := by
    unfold padScales
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), rfl⟩
    exact (Nat.le_floor_iff
      (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL (21 / 100 : ℝ)))).mpr hkR
  refine ⟨2 ^ k, ⟨hmem, hLoR, hHiR⟩, ?_⟩
  intro d₀ hd₀
  obtain ⟨l, hl, hd₀eq⟩ := Finset.mem_image.mp hd₀.1
  have hle : ((2 ^ l : ℕ) : ℝ) ≤ (D : ℝ) := by simpa only [hd₀eq] using hd₀.2.1
  have hlt : (D : ℝ) < 2 * ((2 ^ l : ℕ) : ℝ) := by simpa only [hd₀eq] using hd₀.2.2
  have hkl := dyad_pow_unique k l (D : ℝ) hLoR hHiR hle hlt
  simpa only [hkl] using hd₀eq.symm

/-- Small prime logs also leave room to double an eta-supported product dyad. -/
theorem doubleDyad_mem_of_marked_eta_support {x Y : ℝ} {K : ℕ}
    (F : PDFix K) (hF : F.Valid) (hL : 1 ≤ Real.log x)
    (hprimes : ∀ i : Fin K, ∀ p ∈ primeBand x (F.a i),
      Real.log (p : ℝ) ≤ (Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ))
    (hY : Y ∈ dyadicScales x K) (t : Fin K → ℕ)
    (ht : IsMarkedPrimeTuple x K F.a t) (heta : F.eta ((tupleProduct t : ℝ) / Y) ≠ 0) :
    2 * Y ∈ dyadicScales x K := by
  obtain ⟨hYImage, hYBounds⟩ := Finset.mem_filter.mp hY
  obtain ⟨k, hk, hkY⟩ := Finset.mem_image.mp hYImage
  have hYpos : 0 < Y := by rw [← hkY]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hPow : 1 ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hProductPos : 0 < tupleProduct t := by
    unfold tupleProduct
    exact Finset.prod_pos (fun i hi => (Finset.mem_filter.mp (ht i)).2.1.pos)
  have hProductLog : Real.log (tupleProduct t : ℝ) ≤
      (K : ℝ) * ((Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ)) := by
    unfold tupleProduct
    rw [Nat.cast_prod, Real.log_prod]
    · calc
        _ ≤ ∑ i : Fin K, (Real.log 2 / 2) * Real.rpow (Real.log x) (1 / 5 : ℝ) :=
          Finset.sum_le_sum (fun i hi => hprimes i (t i) (ht i))
        _ = _ := by simp
    · intro i hi
      exact (Nat.cast_pos.mpr (Finset.mem_filter.mp (ht i)).2.1.pos).ne'
  have hYprod : Y ≤ (tupleProduct t : ℝ) := by
    have hsupport := hF.2.2.2.2.1.2.1 heta
    have h := (le_div_iff₀ hYpos).mp hsupport.1
    simpa using h
  have hlogY := Real.log_le_log hYpos hYprod
  have hUpper : Real.log (2 * Y) ≤ ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYpos.ne']
    have hcoef : (K : ℝ) * (Real.log 2 / 2) ≤ (K : ℝ) := by
      have hk0 := Nat.cast_nonneg (α := ℝ) K
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hLpos.le (1 / 5 : ℝ))
    push_cast
    nlinarith [hlogY.trans hProductLog]
  have hdoubleEq : (2 : ℝ) ^ (k + 1) = 2 * Y := by rw [pow_succ, hkY]; ring
  have hIndex : (k + 1 : ℕ) ≤
      ⌊((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ) / Real.log 2⌋₊ := by
    apply (Nat.le_floor_iff (div_nonneg (by positivity) hlog2.le)).mpr
    apply (le_div_iff₀ hlog2).mpr
    have h := hUpper
    rw [← hdoubleEq, Real.log_pow] at h
    exact h
  have hLower : (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ Real.log (2 * Y) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYpos.ne']
    linarith [hYBounds.1]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr (Nat.lt_succ_of_le hIndex), hdoubleEq⟩,
    hLower, hUpper⟩

end
end ArtinPrimitiveRoots.TypeII.PD
