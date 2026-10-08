import ArtinPrimitiveRoots.Construction.Proofs.crp.Survivors
import ArtinPrimitiveRoots.Construction.Defs

/-! Assembly lemmas for `con_rough_pairs` (PROOFS.md §13, steps 7–9). The construction inputs
(`support`, `con_harmonic`, `con_distribution`) enter only as hypotheses, so this file does not
depend on `Results.lean`. -/

namespace ArtinPrimitiveRoots.Construction.Proofs.CRP

open Classical
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.Construction.Proofs.C4

theorem markedWeight_nonneg' (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (h : ℕ) :
    0 ≤ markedWeight x K a (1 / 2 : ℝ) h := by
  unfold markedWeight
  split_ifs
  · apply mul_nonneg (pow_nonneg (by norm_num) _)
    apply Finset.prod_nonneg
    intro i _
    apply div_nonneg (Nat.cast_nonneg _)
    unfold bandMass
    apply Finset.sum_nonneg
    intro p _
    positivity
  · exact le_refl 0

theorem conWeight_le_markedWeight (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (d : ℕ) :
    conWeight x M c u K a Ψ d ≤ markedWeight x K a (1 / 2 : ℝ) (d - 1) := by
  have hmw := markedWeight_nonneg' x K a (d - 1)
  unfold conWeight
  split_ifs
  · have hF : 0 ≤ conFactor x c K a (d - 1) ∧ conFactor x c K a (d - 1) ≤ 1 := by
      unfold conFactor
      split_ifs <;> norm_num
    have hΨ := hΨ1 ((d : ℝ) / x)
    have hΨ' := hΨ0 ((d : ℝ) / x)
    have h1 : Ψ ((d : ℝ) / x) * conFactor x c K a (d - 1) ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul hΨ hF.2 hF.1 (by norm_num)
        _ = 1 := by norm_num
    calc Ψ ((d : ℝ) / x) * conFactor x c K a (d - 1) * markedWeight x K a (1 / 2) (d - 1)
        ≤ 1 * markedWeight x K a (1 / 2) (d - 1) := mul_le_mul_of_nonneg_right h1 hmw
      _ = _ := one_mul _
  · exact hmw

/-- Positive group integers up to `x^0.11`. -/
noncomputable def crpGroupSet (x : ℝ) (K : ℕ) (a : Fin K → ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.rpow x (11 / 100 : ℝ)⌋₊ + 1)).filter
    (fun r => 0 < r ∧ IsGroupInteger x K a r)

/-- The pair-sieve survivors attached to the group integer `r`. -/
noncomputable def crpSurvivors (x H₁ H₂ : ℝ) (c r : ℕ) : Finset (ℕ × ℕ) :=
  pairSieveSurvivors H₁ H₂ (c * r)
    ((primesUpTo (Real.rpow x (1 / 500 : ℝ))).filter (fun p : ℕ => 2 < p ∧ ¬ p ∣ r))
    (roughCutoff x)

theorem mem_crpGroupSet {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {r : ℕ} (hr : r ∈ crpGroupSet x K a) :
    0 < r ∧ IsGroupInteger x K a r ∧ (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) := by
  have hx0 : 0 ≤ Real.rpow x (11 / 100 : ℝ) ∨ Real.rpow x (11 / 100 : ℝ) < 0 :=
    le_or_gt 0 _
  simp only [crpGroupSet, Finset.mem_filter, Finset.mem_range] at hr
  obtain ⟨hlt, hr0, hgrp⟩ := hr
  refine ⟨hr0, hgrp, ?_⟩
  rcases hx0 with h0 | hneg
  · exact le_trans (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hlt)) (Nat.floor_le h0)
  · have : ⌊Real.rpow x (11 / 100 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega

/-- Steps 7: every positive term of the pair sum is a survivor for its own group integer. -/
theorem roughPairBoxSum_le_groupSum (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (H₁ H₂ : ℝ) (hc : c = 2 ∨ c = 4)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1)
    (hx : 1 ≤ x) (hzQ : Real.rpow x (1 / 500 : ℝ) ≤ Real.rpow x (9 / 10 : ℝ))
    (hsupp : ∀ d, conWeight x M c u K a Ψ d ≠ 0 →
          x < (d : ℝ) ∧ (d : ℝ) < 2 * x ∧
            ∃ r Q : ℕ, d - 1 = c * r * Q ∧ Q.Prime ∧
              Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
              IsGroupInteger x K a r ∧ (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) ∧
              markedWeight x K a (1 / 2 : ℝ) (d - 1) =
                markedWeight x K a (1 / 2 : ℝ) r) :
    roughPairBoxSum x M c u K a Ψ H₁ H₂ ≤
      ∑ r ∈ crpGroupSet x K a,
        markedWeight x K a (1 / 2 : ℝ) r * ((crpSurvivors x H₁ H₂ c r).card : ℝ) := by
  classical
  set A₁ := dyadicIntegers H₁ with hA₁
  set A₂ := dyadicIntegers H₂ with hA₂
  set R := crpGroupSet x K a with hR
  set w : ℕ → ℝ := fun r => markedWeight x K a (1 / 2 : ℝ) r with hwdef
  set F : ℕ → ℕ → ℕ → ℝ := fun m n r =>
    w r * (if (m, n) ∈ crpSurvivors x H₁ H₂ c r then (1 : ℝ) else 0) with hFdef
  have hw : ∀ r, 0 ≤ w r := fun r => markedWeight_nonneg' x K a r
  have hF0 : ∀ m n r, 0 ≤ F m n r := by
    intro m n r
    apply mul_nonneg (hw r)
    split_ifs <;> norm_num
  have hpt : ∀ m ∈ A₁, ∀ n ∈ A₂,
      (if roughAbove m (roughCutoff x) ∧ roughAbove n (roughCutoff x) then
        conWeight x M c u K a Ψ (m * n) else 0) ≤ ∑ r ∈ R, F m n r := by
    intro m hm n hn
    have hRHS : 0 ≤ ∑ r ∈ R, F m n r := Finset.sum_nonneg (fun r _ => hF0 m n r)
    split_ifs with hrough
    · by_cases hcw : conWeight x M c u K a Ψ (m * n) = 0
      · rw [hcw]
        exact hRHS
      obtain ⟨hdx, -, r, Q, hdec, hQ, hQbig, hgrp, hrle, hmw⟩ := hsupp (m * n) hcw
      have hmn2 : 2 ≤ m * n := by
        have h1 : (1 : ℝ) < ((m * n : ℕ) : ℝ) := lt_of_le_of_lt hx hdx
        have h2 : 1 < m * n := by exact_mod_cast h1
        omega
      have hr0 : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · exfalso
          rw [h] at hdec
          simp only [mul_zero, zero_mul] at hdec
          omega
        · exact h
      have hrR : r ∈ R := by
        simp only [hR, crpGroupSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le (Nat.le_floor hrle), hr0, hgrp⟩
      have hmem : (m, n) ∈ crpSurvivors x H₁ H₂ c r := by
        apply mem_pairSieveSurvivors_of_factor hc hm hn hrough.1 hrough.2 hQ
          (lt_of_le_of_lt hzQ hQbig)
        omega
      have hle : conWeight x M c u K a Ψ (m * n) ≤ w r := by
        have h := conWeight_le_markedWeight x M c u K a Ψ hΨ0 hΨ1 (m * n)
        rw [hmw] at h
        exact h
      calc conWeight x M c u K a Ψ (m * n) ≤ w r := hle
        _ = F m n r := by
          simp only [hFdef, if_pos hmem, mul_one]
        _ ≤ ∑ r ∈ R, F m n r :=
          Finset.single_le_sum (f := fun r => F m n r) (fun r _ => hF0 m n r) hrR
    · exact hRHS
  calc roughPairBoxSum x M c u K a Ψ H₁ H₂
      = ∑ m ∈ A₁, ∑ n ∈ A₂,
          (if roughAbove m (roughCutoff x) ∧ roughAbove n (roughCutoff x) then
            conWeight x M c u K a Ψ (m * n) else 0) := rfl
    _ ≤ ∑ m ∈ A₁, ∑ n ∈ A₂, ∑ r ∈ R, F m n r := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        exact hpt m hm n hn
    _ = ∑ m ∈ A₁, ∑ r ∈ R, ∑ n ∈ A₂, F m n r := by
        apply Finset.sum_congr rfl
        intro m _
        exact Finset.sum_comm
    _ = ∑ r ∈ R, ∑ m ∈ A₁, ∑ n ∈ A₂, F m n r := Finset.sum_comm
    _ = ∑ r ∈ R, w r * ∑ m ∈ A₁, ∑ n ∈ A₂,
          (if (m, n) ∈ crpSurvivors x H₁ H₂ c r then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ R, w r * ((crpSurvivors x H₁ H₂ c r).card : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        apply mul_le_mul_of_nonneg_left _ (hw r)
        rw [← Finset.sum_product' A₁ A₂
          (fun m n => if (m, n) ∈ crpSurvivors x H₁ H₂ c r then (1 : ℝ) else 0)]
        have hb := Finset.sum_boole (R := ℝ) (fun p : ℕ × ℕ => p ∈ crpSurvivors x H₁ H₂ c r)
          (A₁ ×ˢ A₂)
        simp only [Prod.mk.eta] at hb ⊢
        rw [hb]
        exact_mod_cast Finset.card_le_card (fun p hp => (Finset.mem_filter.mp hp).2)

/-- Summing the group weights against the harmonic mass. -/
theorem groupSum_le_harmonic (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (R : Finset ℕ)
    (hR : ∀ r ∈ R, IsGroupInteger x K a r)
    (hJ : 1 ≤ groupHarmonicMass x K a) :
    ∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ) ≤ groupHarmonicMass x K a := by
  set f : ℕ → ℝ := fun r => if IsGroupInteger x K a r then
    markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ) else 0 with hfdef
  have hf0 : ∀ r, 0 ≤ f r := by
    intro r
    simp only [hfdef]
    split_ifs
    · exact div_nonneg (markedWeight_nonneg' x K a r) (Nat.cast_nonneg r)
    · exact le_refl 0
  have hJdef : groupHarmonicMass x K a = ∑' r, f r := rfl
  have hsum : Summable f := by
    by_contra hns
    have h0 := tsum_eq_zero_of_not_summable hns
    rw [hJdef, h0] at hJ
    norm_num at hJ
  calc ∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ) = ∑ r ∈ R, f r := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [hfdef, if_pos (hR r hr)]
    _ ≤ ∑' r, f r := hsum.sum_le_tsum R (fun r _ => hf0 r)
    _ = groupHarmonicMass x K a := hJdef.symm

/-- Steps 7, combined: the absolute pair bound `Csv·x·J₀·V²/L`. -/
theorem roughPairBoxSum_le_harmonic (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (H₁ H₂ Csv V L : ℝ) (hCsv : 0 < Csv) (hx : 0 ≤ x) (hL : 0 < L)
    (hgs : roughPairBoxSum x M c u K a Ψ H₁ H₂ ≤
      ∑ r ∈ crpGroupSet x K a,
        markedWeight x K a (1 / 2 : ℝ) r * ((crpSurvivors x H₁ H₂ c r).card : ℝ))
    (hper : ∀ r ∈ crpGroupSet x K a,
      ((crpSurvivors x H₁ H₂ c r).card : ℝ) ≤ Csv * (x / r) * V ^ 2 / L)
    (hJ : 1 ≤ groupHarmonicMass x K a) :
    roughPairBoxSum x M c u K a Ψ H₁ H₂ ≤ Csv * x * groupHarmonicMass x K a / L * V ^ 2 := by
  have hR : ∀ r ∈ crpGroupSet x K a, IsGroupInteger x K a r :=
    fun r hr => (mem_crpGroupSet hr).2.1
  have hharm := groupSum_le_harmonic x K a (crpGroupSet x K a) hR hJ
  have hconst : 0 ≤ Csv * x * V ^ 2 / L := by positivity
  calc roughPairBoxSum x M c u K a Ψ H₁ H₂
      ≤ ∑ r ∈ crpGroupSet x K a,
          markedWeight x K a (1 / 2 : ℝ) r * ((crpSurvivors x H₁ H₂ c r).card : ℝ) := hgs
    _ ≤ ∑ r ∈ crpGroupSet x K a,
          markedWeight x K a (1 / 2 : ℝ) r * (Csv * (x / r) * V ^ 2 / L) := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (hper r hr) (markedWeight_nonneg' x K a r)
    _ = (Csv * x * V ^ 2 / L) *
          ∑ r ∈ crpGroupSet x K a, markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
    _ ≤ (Csv * x * V ^ 2 / L) * groupHarmonicMass x K a :=
        mul_le_mul_of_nonneg_left hharm hconst
    _ = Csv * x * groupHarmonicMass x K a / L * V ^ 2 := by ring

theorem primesUpTo_mono {y y' : ℝ} (h : y ≤ y') : primesUpTo y ⊆ primesUpTo y' := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ (Nat.floor_mono h)), hp.2⟩

/-- Step 8: the residue of an actual construction integer modulo `N` is an admissible
progression for `con_distribution`, once all prime factors of `d`, of `r` and `Q` exceed `N`. -/
theorem lift_admissible {N c d r Q : ℕ} (hN : 0 < N) (hc : c = 2 ∨ c = 4) (hcN : c ∣ N)
    (hd : d = c * r * Q + 1)
    (hdN : ∀ p, p.Prime → p ∣ d → N < p)
    (hrN : ∀ p, p.Prime → p ∣ r → N < p) (hQ : Q.Prime) (hQN : N < Q) :
    Int.gcd ((d % N : ℕ) : ℤ) (N : ℤ) = 1 ∧ (c : ℤ) ∣ ((d % N : ℕ) : ℤ) - 1 ∧
      Int.gcd ((((d % N : ℕ) : ℤ) - 1) / c) ((N / c : ℕ) : ℤ) = 1 := by
  set v : ℤ := ((d % N : ℕ) : ℤ) with hv
  have hcpos : 0 < c := by rcases hc with h | h <;> omega
  have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hcop : Nat.Coprime d N := Nat.coprime_of_dvd (fun p hp hpd hpN => by
    have h1 := hdN p hp hpd
    have h2 := Nat.le_of_dvd hN hpN
    omega)
  have h1 : Int.gcd v (N : ℤ) = 1 := by
    rw [hv, Int.gcd_natCast_natCast, ← Nat.gcd_rec N d]
    exact Nat.Coprime.symm hcop
  have hvd : v ≡ (d : ℤ) [ZMOD N] := by
    rw [hv, Int.natCast_mod]
    exact Int.mod_modEq _ _
  have hdZ : (d : ℤ) = c * ((r * Q : ℕ) : ℤ) + 1 := by
    rw [hd]
    push_cast
    ring
  have hcN' : (c : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hcN
  have h2 : (c : ℤ) ∣ v - 1 := by
    have hmod : v ≡ (d : ℤ) [ZMOD c] := Int.ModEq.of_dvd hcN' hvd
    have h' : (c : ℤ) ∣ (d : ℤ) - v := Int.ModEq.dvd hmod
    have h'' : (c : ℤ) ∣ (d : ℤ) - 1 := ⟨((r * Q : ℕ) : ℤ), by rw [hdZ]; ring⟩
    have heq : v - 1 = ((d : ℤ) - 1) - ((d : ℤ) - v) := by ring
    rw [heq]
    exact dvd_sub h'' h'
  obtain ⟨t, ht⟩ := h2
  have htdiv : (v - 1) / c = t := by
    rw [ht]
    exact Int.mul_ediv_cancel_left _ hcZ
  set n : ℕ := N / c with hn
  have hNn : N = c * n := (Nat.mul_div_cancel' hcN).symm
  have hnpos : 0 < n := Nat.div_pos (Nat.le_of_dvd hN hcN) hcpos
  have hnN : n ≤ N := Nat.div_le_self N c
  have hdiff : (N : ℤ) ∣ (d : ℤ) - v := Int.ModEq.dvd hvd
  have hdiff' : (n : ℤ) ∣ ((r * Q : ℕ) : ℤ) - t := by
    have heq : (d : ℤ) - v = (c : ℤ) * (((r * Q : ℕ) : ℤ) - t) := by
      have hv' : v = c * t + 1 := by linarith [ht]
      rw [hv', hdZ]
      ring
    rw [heq, hNn] at hdiff
    push_cast at hdiff
    exact (mul_dvd_mul_iff_left hcZ).mp hdiff
  have hrQn : Nat.Coprime (r * Q) n := by
    refine Nat.coprime_mul_iff_left.2 ⟨?_, ?_⟩
    · exact Nat.coprime_of_dvd (fun p hp hpr hpn => by
        have h1 := hrN p hp hpr
        have h2 := Nat.le_of_dvd hnpos hpn
        omega)
    · rw [Nat.Prime.coprime_iff_not_dvd hQ]
      intro hQn
      have := Nat.le_of_dvd hnpos hQn
      omega
  have hIsC : IsCoprime ((r * Q : ℕ) : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr hrQn
  obtain ⟨w, hw⟩ := hdiff'
  have htw : t = ((r * Q : ℕ) : ℤ) + (n : ℤ) * (-w) := by
    rw [mul_neg]
    linarith [hw]
  have hIsC' : IsCoprime t (n : ℤ) := by
    rw [htw]
    exact hIsC.add_mul_left_left (-w)
  refine ⟨h1, ⟨t, ht⟩, ?_⟩
  rw [htdiv]
  exact Int.isCoprime_iff_gcd_eq_one.mp hIsC'

/-- Step 9: restricting the progression modulo `M` to a residue class modulo a multiple `N`
can only lower the total mass. -/
theorem conTotalMass_le_of_lift (x : ℝ) (M N c : ℕ) (u v : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (hMN : (M : ℤ) ∣ (N : ℤ)) (d : ℕ) (hdu : (d : ℤ) ≡ u [ZMOD M])
    (hdv : (d : ℤ) ≡ v [ZMOD N]) (hnn : ∀ e, 0 ≤ conWeight x M c u K a Ψ e) :
    conTotalMass x N c v K a Ψ ≤ conTotalMass x M c u K a Ψ := by
  unfold conTotalMass
  apply Finset.sum_le_sum
  intro e _
  by_cases h : 1 < e ∧ (e : ℤ) ≡ v [ZMOD N]
  · have h' : 1 < e ∧ (e : ℤ) ≡ u [ZMOD M] := by
      refine ⟨h.1, ?_⟩
      have hed : (e : ℤ) ≡ d [ZMOD N] := h.2.trans hdv.symm
      exact (Int.ModEq.of_dvd hMN hed).trans hdu
    simp only [conWeight, if_pos h, if_pos h', le_refl]
  · have h0 : conWeight x N c v K a Ψ e = 0 := by simp only [conWeight, if_neg h]
    rw [h0]
    exact hnn e

end ArtinPrimitiveRoots.Construction.Proofs.CRP
