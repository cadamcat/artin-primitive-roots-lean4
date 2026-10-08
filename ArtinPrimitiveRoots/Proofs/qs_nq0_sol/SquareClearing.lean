import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Admissibility

/-!
# Integral representatives by an S-supported square

The planned clearing statement is:
```
theorem qs_nq0_integral_square_clearing
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) :
    ∀ c : Kˣ, (c : K) ∈ Sd.R → ∃ b : 𝓞 K, b ≠ 0 ∧
      (∀ v : FinPlace K, v ∉ Sd.Sf → residue v (b : K) ≠ 0) ∧
      ∃ c₀ : 𝓞 K, (c₀ : K) = (c : K) * (b : K) ^ 2
```
The class-group-power argument also proves the downstream NQ2 endpoint.
Here the count and valuation steps are local, so NQ0 can use the argument
without importing its own containing module.
-/

set_option autoImplicit false

open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- An S-integer becomes integral after multiplication by the square of an S-supported integer. -/
theorem qs_nq0_integral_square_clearing
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) :
    ∀ c : Kˣ, (c : K) ∈ Sd.R → ∃ b : 𝓞 K, b ≠ 0 ∧
      (∀ v : FinPlace K, v ∉ Sd.Sf → residue v (b : K) ≠ 0) ∧
      ∃ c₀ : 𝓞 K, (c₀ : K) = (c : K) * (b : K) ^ 2 := by
  classical
  have hcount_power
      (v w : HeightOneSpectrum (𝓞 K)) (n : ℕ) {a : 𝓞 K}
      (ha : Ideal.span {a} = v.asIdeal ^ n) :
      FractionalIdeal.count K w (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) =
        if w = v then n else 0 := by
    classical
    rw [ha, FractionalIdeal.coeIdeal_pow]
    by_cases hwv : w = v
    · subst w
      simpa using (FractionalIdeal.count_pow_self K v n)
    · have hvw : v ≠ w := Ne.symm hwv
      rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime K w hvw]
      simp [hwv]

  have hvaluation
      (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ≠ 0) :
      v.valuation K (a : K) =
        WithZero.exp (-FractionalIdeal.count K v
          (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K)) := by
    rw [v.valuation_of_algebraMap, v.intValuation_if_neg ha]
    congr 1
    have hspan : Ideal.span {a} ≠ ⊥ := by
      intro h
      exact ha (Ideal.span_singleton_eq_bot.mp h)
    have hfrac : (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hspan
    rw [FractionalIdeal.count_well_defined K v hfrac (a := 1)
      (J := Ideal.span {a}) (by simp)]
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one,
      Associates.factors_one, Associates.count_zero v.associates_irreducible]
    ring

  intro c hR
  let h : ℕ := Fintype.card (ClassGroup (𝓞 K))
  have hh : 0 < h := by
    dsimp [h]
    exact (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 K)))
  have hpower (v : ArtinPrimitiveRoots.A1.FinPlace K) :
      ∃ a : 𝓞 K, Ideal.span {a} = v.asIdeal ^ h := by
    let p₀ : (Ideal (𝓞 K))⁰ :=
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
    have hClass : ClassGroup.mk0 p₀ ^ h = 1 := by
      simpa [h, p₀] using (pow_card_eq_one (x := ClassGroup.mk0 p₀))
    have hpow0 : v.asIdeal ^ h ≠ ⊥ := pow_ne_zero _ v.ne_bot
    have hClassPow :
        ClassGroup.mk0 ⟨v.asIdeal ^ h, mem_nonZeroDivisors_iff_ne_zero.mpr hpow0⟩ = 1 := by
      change ClassGroup.mk0 (p₀ ^ h) = 1
      rw [map_pow]
      exact hClass
    have hPrincipal : (v.asIdeal ^ h).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hpow0)).mp hClassPow
    obtain ⟨a, ha⟩ := hPrincipal.principal
    exact ⟨a, ha.symm⟩
  let π : ArtinPrimitiveRoots.A1.FinPlace K → 𝓞 K := fun v => Classical.choose (hpower v)
  have hπ (v : ArtinPrimitiveRoots.A1.FinPlace K) : Ideal.span {π v} = v.asIdeal ^ h :=
    Classical.choose_spec (hpower v)
  have hπ_ne (v : ArtinPrimitiveRoots.A1.FinPlace K) : π v ≠ 0 := by
    intro hz
    have hpow0 : v.asIdeal ^ h ≠ ⊥ := pow_ne_zero _ v.ne_bot
    apply hpow0
    calc
      v.asIdeal ^ h = Ideal.span {π v} := (hπ v).symm
      _ = ⊥ := by simp [hz]
  let e : ℕ := ∑ v ∈ Sd.Sf, (WithZero.log (v.valuation K (c : K))).toNat
  let b : 𝓞 K := ∏ v ∈ Sd.Sf, (π v) ^ e
  have hb_ne : b ≠ 0 := by
    dsimp [b]
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact pow_ne_zero _ (hπ_ne v)
  have hvalπ (w v : ArtinPrimitiveRoots.A1.FinPlace K) :
      w.valuation K (π v : K) = if w = v then WithZero.exp (-(h : ℤ)) else 1 := by
    rw [hvaluation w (hπ_ne v),
      hcount_power v w h (hπ v)]
    by_cases hwv : w = v <;> simp [hwv]
  have hvalb (w : ArtinPrimitiveRoots.A1.FinPlace K) :
      w.valuation K (b : K) =
        if w ∈ Sd.Sf then WithZero.exp ((e : ℕ) • (-(h : ℤ))) else 1 := by
    dsimp [b]
    change w.valuation K
      (algebraMap (𝓞 K) K (∏ v ∈ Sd.Sf, (π v) ^ e)) = _
    rw [map_prod, map_prod]
    simp_rw [map_pow]
    by_cases hw : w ∈ Sd.Sf
    · rw [if_pos hw, Finset.prod_eq_single w]
      · rw [hvalπ]
        by_cases hEq : w = w
        · rw [if_pos hEq]
          rw [← WithZero.exp_nsmul]
          congr 1
        · exact False.elim (hEq rfl)
      · intro v hv hne
        rw [hvalπ]
        have hwv : w ≠ v := by
          intro hEq
          exact hne hEq.symm
        simp [hwv]
      · intro hnot
        exact (hnot hw).elim
    · rw [if_neg hw, Finset.prod_eq_one]
      intro v hv
      rw [hvalπ]
      have hwv : w ≠ v := by
        intro hEq
        exact hw (hEq ▸ hv)
      simp [hwv]
  have htoNat (z : ℤ) : z ≤ (z.toNat : ℤ) := by
    by_cases hz : 0 ≤ z
    · rw [Int.toNat_of_nonneg hz]
    · have hneg : z < 0 := lt_of_not_ge hz
      have hzNat : z.toNat = 0 := by omega
      rw [hzNat]
      omega
  have heBound (v : ArtinPrimitiveRoots.A1.FinPlace K) (hv : v ∈ Sd.Sf) :
      WithZero.log (v.valuation K (c : K)) ≤ (e : ℤ) := by
    let z := WithZero.log (v.valuation K (c : K))
    have hsum := Finset.single_le_sum
      (s := Sd.Sf) (f := fun w => (WithZero.log (w.valuation K (c : K))).toNat)
      (fun _ _ => Nat.zero_le _) hv
    dsimp [e, z]
    calc
      z ≤ (z.toNat : ℤ) := htoNat z
      _ ≤ (e : ℤ) := by exact_mod_cast hsum
  have hvalCorrected (v : ArtinPrimitiveRoots.A1.FinPlace K) :
      v.valuation K ((c : K) * (b : K) ^ 2) ≤ 1 := by
    have hc_ne : v.valuation K (c : K) ≠ 0 := by simp [c.ne_zero]
    have hbval_ne : v.valuation K (b : K) ≠ 0 := by
      rw [hvalb]
      split_ifs <;> simp
    have hx_ne : v.valuation K ((c : K) * (b : K) ^ 2) ≠ 0 := by
      have hx : (c : K) * (b : K) ^ 2 ≠ 0 := mul_ne_zero c.ne_zero (pow_ne_zero _ (by exact_mod_cast hb_ne))
      simp [hx, hb_ne]
    have hlog : WithZero.log (v.valuation K ((c : K) * (b : K) ^ 2)) =
        WithZero.log (v.valuation K (c : K)) +
          2 * WithZero.log (v.valuation K (b : K)) := by
      rw [map_mul, map_pow, WithZero.log_mul hc_ne (pow_ne_zero _ hbval_ne), WithZero.log_pow]
      norm_num
    by_cases hv : v ∈ Sd.Sf
    · rw [← WithZero.exp_log hx_ne, ← WithZero.exp_zero, WithZero.exp_le_exp]
      rw [hlog, hvalb, if_pos hv]
      simp only [WithZero.log_exp]
      have he_nonneg : (0 : ℤ) ≤ (e : ℤ) := by exact_mod_cast Nat.zero_le e
      have hh_ge : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
      have hprod : (0 : ℤ) ≤ (e : ℤ) * ((h : ℤ) - 1) :=
        mul_nonneg he_nonneg (by omega)
      have hbound := heBound v hv
      simp only [nsmul_eq_mul]
      nlinarith
    · have hc_int : v.valuation K (c : K) ≤ 1 := by
        change (c : K) ∈ ((Sd.Sf : Set (ArtinPrimitiveRoots.A1.FinPlace K)).integer K) at hR
        exact hR v hv
      calc
        v.valuation K ((c : K) * (b : K) ^ 2) =
            v.valuation K (c : K) * v.valuation K (b : K) ^ 2 := by rw [map_mul, map_pow]
        _ = v.valuation K (c : K) := by rw [hvalb, if_neg hv]; simp
        _ ≤ 1 := hc_int
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K
    ((c : K) * (b : K) ^ 2) hvalCorrected
  refine ⟨b, hb_ne, ?_, a, ha⟩
  intro v hv
  have hbval : v.valuation K (b : K) = 1 := by rw [hvalb, if_neg hv]
  exact (qs_nq0_residue_ne_zero_iff_valuation_one v (b : K)).mpr hbval

end ArtinPrimitiveRoots.A2
