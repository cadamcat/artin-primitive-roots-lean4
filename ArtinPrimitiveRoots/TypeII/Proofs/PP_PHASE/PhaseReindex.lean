import ArtinPrimitiveRoots.TypeII.PP.Defs

namespace ArtinPrimitiveRoots.Proofs.pp_phase_p

open ArtinPrimitiveRoots.TypeII.PP

/-- Reindex a residue-class phase sum by the quotient coordinate. -/
theorem phase_reindex_identity (N' : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (a : ZMod q) (v N₁ N₂ : ℝ) (hN' : 0 < N') :
    residuePhaseSum N' q a v {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂} =
      Complex.exp (Complex.I * v * Real.log (q : ℝ)) *
        ∑ b ∈ (Finset.range (⌊2 * N' / (q : ℝ)⌋₊ + 1)).filter
          (fun b : ℕ => N' ≤ (q : ℝ) * b + a.val ∧
            (q : ℝ) * b + a.val ≤ 2 * N' ∧
            N₁ ≤ (q : ℝ) * b + a.val ∧
            (q : ℝ) * b + a.val ≤ N₂),
          Complex.exp (Complex.I * v * Real.log ((b : ℝ) + (a.val : ℝ) / q)) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let S : Finset ℕ :=
    (Finset.range (⌊2 * N'⌋₊ + 1)).filter
      (fun n : ℕ => N' ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N' ∧
        n ∈ {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂} ∧ (n : ZMod q) = a)
  let T : Finset ℕ :=
    (Finset.range (⌊2 * N' / (q : ℝ)⌋₊ + 1)).filter
      (fun b : ℕ => N' ≤ (q : ℝ) * b + a.val ∧
        (q : ℝ) * b + a.val ≤ 2 * N' ∧
        N₁ ≤ (q : ℝ) * b + a.val ∧
        (q : ℝ) * b + a.val ≤ N₂)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have haq : a.val < q := a.val_lt
  have hprops (n : ℕ) (hn : n ∈ S) :
      N' ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N' ∧
        N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂ ∧ (n : ZMod q) = a := by
    rcases (Finset.mem_filter.mp hn).2 with ⟨hN, hN2, hI, hres⟩
    rcases hI with ⟨hI1, hI2⟩
    exact ⟨hN, hN2, hI1, hI2, hres⟩
  have hres (n : ℕ) (hn : n ∈ S) : n % q = a.val := by
    have hz := congrArg ZMod.val (hprops n hn).2.2.2.2
    simpa [ZMod.val_natCast] using hz
  have hrepr (n : ℕ) (hn : n ∈ S) : n = q * (n / q) + a.val := by
    have hd := Nat.mod_add_div n q
    rw [hres n hn] at hd
    omega
  have hlogFactor (n : ℕ) (hn : n ∈ S) :
      Complex.exp (Complex.I * v * Real.log (n : ℝ)) =
        Complex.exp (Complex.I * v * Real.log (q : ℝ)) *
          Complex.exp (Complex.I * v *
            Real.log ((n / q : ℕ) + (a.val : ℝ) / q)) := by
    have hnreal : (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) + (a.val : ℝ) := by
      exact_mod_cast hrepr n hn
    have harg : (n : ℝ) = (q : ℝ) *
        (((n / q : ℕ) : ℝ) + (a.val : ℝ) / q) := by
      calc
        (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) + (a.val : ℝ) := hnreal
        _ = (q : ℝ) * (((n / q : ℕ) : ℝ) + (a.val : ℝ) / q) := by
          field_simp [hqR.ne']
          <;> ring
    have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le hN' (hprops n hn).1
    have hdpos : 0 < (n / q : ℕ) + (a.val : ℝ) / q := by
      by_contra hnot
      have hle : (n / q : ℕ) + (a.val : ℝ) / q ≤ 0 := le_of_not_gt hnot
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hqR.le hle
      rw [← harg] at hnonpos
      linarith
    have hlog : Real.log (n : ℝ) = Real.log (q : ℝ) +
      Real.log (((n / q : ℕ) : ℝ) + (a.val : ℝ) / q) := by
      rw [harg, Real.log_mul hqR.ne' hdpos.ne']
    rw [hlog]
    push_cast
    rw [mul_add, Complex.exp_add]
  have hsum :
      (∑ n ∈ S, Complex.exp (Complex.I * v * Real.log (n : ℝ))) =
        ∑ b ∈ T,
          Complex.exp (Complex.I * v * Real.log (q : ℝ)) *
            Complex.exp (Complex.I * v * Real.log ((b : ℝ) + (a.val : ℝ) / q)) := by
    refine Finset.sum_nbij' (fun n => n / q) (fun b => q * b + a.val)
      ?_ ?_ ?_ ?_ ?_
    · intro n hn
      have hp := hprops n hn
      have hr := hrepr n hn
      have hrR : (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) + (a.val : ℝ) := by
        exact_mod_cast hr
      have hbReal : ((n / q : ℕ) : ℝ) ≤ 2 * N' / q := by
        apply (le_div_iff₀ hqR).2
        have ha0 : (0 : ℝ) ≤ (a.val : ℝ) := Nat.cast_nonneg _
        nlinarith [hp.2.1, hrR]
      have hbFloor : n / q ≤ ⌊2 * N' / (q : ℝ)⌋₊ := Nat.le_floor hbReal
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [← hrR]
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
    · intro b hb
      rcases (Finset.mem_filter.mp hb).2 with ⟨hN, hN2, hI1, hI2⟩
      have hnreal : ((q * b + a.val : ℕ) : ℝ) = (q : ℝ) * b + (a.val : ℝ) := by
        exact_mod_cast (show q * b + a.val = q * b + a.val from rfl)
      have hnle : (q * b + a.val : ℕ) ≤ ⌊2 * N'⌋₊ := by
        apply Nat.le_floor
        rw [hnreal]
        exact hN2
      have hmod : (q * b + a.val) % q = a.val := by
        simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt haq]
      have hres' : ((q * b + a.val : ℕ) : ZMod q) = a := by
        conv_rhs => rw [← ZMod.natCast_zmod_val a]
        exact (ZMod.natCast_eq_natCast_iff' (q * b + a.val) a.val q).2 (by
          rw [hmod, Nat.mod_eq_of_lt haq])
      have hNcast : N' ≤ ((q * b + a.val : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_mul] using hN
      have hN2cast : ((q * b + a.val : ℕ) : ℝ) ≤ 2 * N' := by
        simpa only [Nat.cast_add, Nat.cast_mul] using hN2
      have hI1cast : N₁ ≤ ((q * b + a.val : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_mul] using hI1
      have hI2cast : ((q * b + a.val : ℕ) : ℝ) ≤ N₂ := by
        simpa only [Nat.cast_add, Nat.cast_mul] using hI2
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      exact ⟨hNcast, hN2cast, ⟨hI1cast, hI2cast⟩, hres'⟩
    · intro n hn
      have h := hrepr n hn
      rw [← h]
    · intro b hb
      rcases (Finset.mem_filter.mp hb).2 with ⟨hN, hN2, hI1, hI2⟩
      have hmod : (q * b + a.val) % q = a.val := by
        simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt haq]
      have hdivEq := Nat.mod_add_div (q * b + a.val) q
      rw [hmod] at hdivEq
      have hmul : q * ((q * b + a.val) / q) = q * b := by omega
      have hdiv : (q * b + a.val) / q = b :=
        Nat.mul_left_cancel (Nat.pos_of_ne_zero (by omega)) hmul
      simpa [hdiv]
    · intro n hn
      have hval : (a.val : ℝ) = a.cast := ZMod.natCast_val (R := ℝ) a
      simpa only [← hval] using hlogFactor n hn
  calc
    residuePhaseSum N' q a v {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂} =
        ∑ n ∈ S, Complex.exp (Complex.I * v * Real.log (n : ℝ)) := by
          simp [residuePhaseSum, S, Set.mem_setOf_eq]
    _ = Complex.exp (Complex.I * v * Real.log (q : ℝ)) *
          ∑ b ∈ T, Complex.exp (Complex.I * v *
            Real.log ((b : ℝ) + (a.val : ℝ) / q)) := by
          rw [hsum, Finset.mul_sum]
    _ = _ := by
          rfl

end ArtinPrimitiveRoots.Proofs.pp_phase_p
