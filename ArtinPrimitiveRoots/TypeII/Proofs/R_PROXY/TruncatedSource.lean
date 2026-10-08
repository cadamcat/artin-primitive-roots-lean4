import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.SieveAlgebra

/-!
Finite reindexing tools for the truncated rough-prime source sum.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical

/-- Quotients of the members of `I` that are divisible by `d`. -/
noncomputable def divisorQuotients (I : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (I.filter (fun m => d ∣ m)).image (fun m => m / d)

/-- Reindex a divisibility-restricted sum by writing every member as `d*h`. -/
theorem sum_filter_dvd_reindex (d : ℕ) (I : Finset ℕ)
    (f : ℕ → ℂ) :
    (∑ m ∈ I, (if d ∣ m then f m else 0)) =
      ∑ h ∈ divisorQuotients I d, f (d * h) := by
  classical
  let J : Finset ℕ := I.filter (fun m => d ∣ m)
  have hinj : Set.InjOn (fun m : ℕ => m / d) (↑J : Set ℕ) := by
    intro m hm n hn hmn
    have hmd : d ∣ m := (Finset.mem_filter.mp hm).2
    have hnd : d ∣ n := (Finset.mem_filter.mp hn).2
    have hmeq : d * (m / d) = m := Nat.mul_div_cancel' hmd
    have hneq : d * (n / d) = n := Nat.mul_div_cancel' hnd
    change m / d = n / d at hmn
    calc
      m = d * (m / d) := hmeq.symm
      _ = d * (n / d) := by rw [hmn]
      _ = n := hneq
  calc
    (∑ m ∈ I, (if d ∣ m then f m else 0)) = ∑ m ∈ J, f m := by
      rw [← Finset.sum_filter]
    _ = ∑ m ∈ J, f (d * (m / d)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmd : d ∣ m := (Finset.mem_filter.mp hm).2
      rw [Nat.mul_div_cancel' hmd]
    _ = ∑ h ∈ divisorQuotients I d, f (d * h) := by
      dsimp [divisorQuotients]
      exact (Finset.sum_image (f := fun h => f (d * h)) hinj).symm

/-- Factor the character and oscillatory phase of a product, leaving the
reciprocal-log weight on the product. -/
theorem source_term_factorization (k : ℕ) (χ : DirichletCharacter ℂ k)
    (u : ℝ) (d h : ℕ) (hd : 0 < d) (hh : 0 < h) :
    (χ ((d * h : ℕ) : ZMod k) : ℂ) *
        Complex.exp (Complex.I * u * Real.log ((d * h : ℕ) : ℝ)) /
          Real.log ((d * h : ℕ) : ℝ) =
      ((χ (d : ZMod k) : ℂ) * Complex.exp (Complex.I * u * Real.log (d : ℝ))) *
        ((χ (h : ZMod k) : ℂ) * Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
          Real.log ((d * h : ℕ) : ℝ)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hcast : ((d * h : ℕ) : ℝ) = (d : ℝ) * (h : ℝ) := by norm_cast
  have hlog : Real.log ((d * h : ℕ) : ℝ) =
      Real.log (d : ℝ) + Real.log (h : ℝ) := by
    rw [hcast, Real.log_mul hdR.ne' hhR.ne']
  have hchar : (χ ((d * h : ℕ) : ZMod k) : ℂ) =
      (χ (d : ZMod k) : ℂ) * (χ (h : ZMod k) : ℂ) := by
    simp only [Nat.cast_mul, map_mul]
  have hphase : Complex.exp (Complex.I * u *
        Real.log ((d * h : ℕ) : ℝ)) =
        Complex.exp (Complex.I * u * Real.log (d : ℝ)) *
        Complex.exp (Complex.I * u * Real.log (h : ℝ)) := by
    rw [hlog]
    calc
      _ = Complex.exp (Complex.I * ↑u * Real.log (d : ℝ) +
          Complex.I * ↑u * Real.log (h : ℝ)) := by
        congr 1
        push_cast
        ring
      _ = _ := Complex.exp_add _ _
  rw [hchar, hphase]
  ring

/-- Expand the truncated inclusion-exclusion sum against an arbitrary complex
weight and interchange its two finite sums. -/
theorem smallPrimeTruncation_weighted_sum_expand
    (x : ℝ) (r : ℕ) (I : Finset ℕ) (f : ℕ → ℂ) :
    (∑ m ∈ I, (smallPrimeTruncation x r m : ℂ) * f m) =
      ∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card < r),
        ((-1 : ℂ) ^ S.card) *
          ∑ m ∈ I,
            (if (∏ p ∈ S, p) ∣ m then f m else 0) := by
  classical
  let Q := (primesUpTo (roughCutoff x)).powerset.filter (fun S => S.card < r)
  have hcast (m : ℕ) :
      (smallPrimeTruncation x r m : ℂ) =
        ∑ S ∈ Q, ((-1 : ℂ) ^ S.card) *
          (if (∏ p ∈ S, p) ∣ m then (1 : ℂ) else 0) := by
    unfold smallPrimeTruncation
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hdiv : (∏ p ∈ S, p) ∣ m <;>
      simp [Q, hdiv, Complex.ofReal_mul, Complex.ofReal_pow]
  calc
    _ = ∑ m ∈ I,
        (∑ S ∈ Q, ((-1 : ℂ) ^ S.card) *
          (if (∏ p ∈ S, p) ∣ m then (1 : ℂ) else 0)) * f m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hcast]
    _ = ∑ m ∈ I, ∑ S ∈ Q,
        (((-1 : ℂ) ^ S.card) *
          (if (∏ p ∈ S, p) ∣ m then (1 : ℂ) else 0)) * f m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]
    _ = ∑ S ∈ Q, ∑ m ∈ I,
        (((-1 : ℂ) ^ S.card) *
          (if (∏ p ∈ S, p) ∣ m then (1 : ℂ) else 0)) * f m := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ Q, ((-1 : ℂ) ^ S.card) *
        ∑ m ∈ I, (if (∏ p ∈ S, p) ∣ m then f m else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      calc
        ∑ m ∈ I,
            (((-1 : ℂ) ^ S.card) *
              (if (∏ p ∈ S, p) ∣ m then (1 : ℂ) else 0)) * f m =
          ∑ m ∈ I, ((-1 : ℂ) ^ S.card) *
            (if (∏ p ∈ S, p) ∣ m then f m else 0) := by
              apply Finset.sum_congr rfl
              intro m hm
              by_cases hdiv : (∏ p ∈ S, p) ∣ m <;> simp [hdiv, mul_assoc]
        _ = ((-1 : ℂ) ^ S.card) *
            ∑ m ∈ I, (if (∏ p ∈ S, p) ∣ m then f m else 0) := by
              rw [Finset.mul_sum]
    _ = ∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card < r),
        ((-1 : ℂ) ^ S.card) *
          ∑ m ∈ I,
            (if (∏ p ∈ S, p) ∣ m then f m else 0) := by rfl

/-- Expand the truncated source sum and reindex each divisibility class by
writing `m = d*h`. -/
theorem truncated_source_reindex
    (x u : ℝ) (r k : ℕ) (χ : DirichletCharacter ℂ k)
    (I : Finset ℕ) (hI : ∀ m ∈ I, 0 < m) :
    (∑ m ∈ I,
      (smallPrimeTruncation x r m : ℂ) *
        ((χ (m : ZMod k) : ℂ) *
          Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
            Real.log (m : ℝ))) =
      ∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card < r),
        ((-1 : ℂ) ^ S.card) *
          ((χ ((∏ p ∈ S, p : ℕ) : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u *
              Real.log ((∏ p ∈ S, p : ℕ) : ℝ))) *
          ∑ h ∈ divisorQuotients I (∏ p ∈ S, p),
            (χ (h : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                Real.log (((∏ p ∈ S, p) * h : ℕ) : ℝ) := by
  classical
  let P := primesUpTo (roughCutoff x)
  let Q := P.powerset.filter (fun S => S.card < r)
  let F : ℕ → ℂ := fun m =>
    (χ (m : ZMod k) : ℂ) *
      Complex.exp (Complex.I * u * Real.log (m : ℝ)) / Real.log (m : ℝ)
  calc
    _ = ∑ S ∈ Q, ((-1 : ℂ) ^ S.card) *
          ∑ m ∈ I,
            (if (∏ p ∈ S, p) ∣ m then F m else 0) := by
      simpa [F, P, Q] using
        smallPrimeTruncation_weighted_sum_expand x r I F
    _ = ∑ S ∈ Q, ((-1 : ℂ) ^ S.card) *
          (((χ ((∏ p ∈ S, p : ℕ) : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u *
                Real.log ((∏ p ∈ S, p : ℕ) : ℝ))) *
            ∑ h ∈ divisorQuotients I (∏ p ∈ S, p),
              (χ (h : ZMod k) : ℂ) *
                Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                  Real.log (((∏ p ∈ S, p) * h : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro S hS
      let d : ℕ := ∏ p ∈ S, p
      have hSP : S ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := by
        have hpP : p ∈ P := hSP hp
        dsimp [P, primesUpTo] at hpP
        exact (Finset.mem_filter.mp hpP).2
      have hd : 0 < d := by
        dsimp [d]
        exact Finset.prod_pos (fun p hp => (hprime p hp).pos)
      have hquotient_pos (h : ℕ) (hh : h ∈ divisorQuotients I d) : 0 < h := by
        rcases Finset.mem_image.mp hh with ⟨m, hm, hEq⟩
        rcases Finset.mem_filter.mp hm with ⟨hmI, hdvd⟩
        rw [← hEq]
        exact Nat.div_pos (Nat.le_of_dvd (hI m hmI) hdvd) hd
      have hinner :
          (∑ m ∈ I, (if d ∣ m then F m else 0)) =
            ((χ (d : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (d : ℝ))) *
              ∑ h ∈ divisorQuotients I d,
                (χ (h : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                    Real.log ((d * h : ℕ) : ℝ) := by
        calc
          _ = ∑ h ∈ divisorQuotients I d, F (d * h) :=
            sum_filter_dvd_reindex d I F
          _ = ∑ h ∈ divisorQuotients I d,
                ((χ (d : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (d : ℝ))) *
                  ((χ (h : ZMod k) : ℂ) *
                    Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                      Real.log ((d * h : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro h hh
            simpa only [F] using
              source_term_factorization k χ u d h hd (hquotient_pos h hh)
          _ = ((χ (d : ZMod k) : ℂ) *
                Complex.exp (Complex.I * u * Real.log (d : ℝ))) *
              ∑ h ∈ divisorQuotients I d,
                (χ (h : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                    Real.log ((d * h : ℕ) : ℝ) := by
            rw [Finset.mul_sum]
      calc
        _ = ((-1 : ℂ) ^ S.card) *
            (((χ (d : ZMod k) : ℂ) *
                Complex.exp (Complex.I * u * Real.log (d : ℝ))) *
              ∑ h ∈ divisorQuotients I d,
                (χ (h : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                    Real.log ((d * h : ℕ) : ℝ)) :=
              congrArg (fun z : ℂ => ((-1 : ℂ) ^ S.card) * z) hinner
        _ = ((-1 : ℂ) ^ S.card) *
            ((χ (d : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (d : ℝ))) *
              ∑ h ∈ divisorQuotients I d,
                (χ (h : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                    Real.log ((d * h : ℕ) : ℝ) := by ring
        _ = _ := by
          simp [d]
          ring
    _ = _ := by
      simp [P, Q]
      ring

/-- Identify the quotient set of a dyadic interval with the corresponding
rescaled dyadic interval. -/
theorem divisorQuotients_dyadic_interval (l r : ℝ) (d : ℕ)
    (hl : 0 < l) (hlr : l ≤ r) (hd : 0 < d) :
    divisorQuotients
        ((Finset.range (⌊r⌋₊ + 1)).filter
          (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r)) d =
      (Finset.range (⌊r / (d : ℝ)⌋₊ + 1)).filter
        (fun (h : ℕ) => l / (d : ℝ) ≤ (h : ℝ) ∧
          (h : ℝ) ≤ r / (d : ℝ)) := by
  classical
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hrNonneg : 0 ≤ r := le_trans hl.le hlr
  ext h
  simp only [divisorQuotients, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, hquot⟩
    rcases Finset.mem_filter.mp hm with ⟨hmI, hdiv⟩
    rcases Finset.mem_filter.mp hmI with ⟨_, ⟨hmlo, hmhi⟩⟩
    have hmul : m = d * h := by
      calc
        m = d * (m / d) := (Nat.mul_div_cancel' hdiv).symm
        _ = d * h := congrArg (fun q : ℕ => d * q) hquot
    have hmcast : (m : ℝ) = (d : ℝ) * (h : ℝ) := by
      exact_mod_cast hmul
    have hlo : l / (d : ℝ) ≤ (h : ℝ) :=
      (div_le_iff₀ hdR).2 (by nlinarith [hmlo, hmcast])
    have hhi : (h : ℝ) ≤ r / (d : ℝ) :=
      (le_div_iff₀ hdR).2 (by nlinarith [hmhi, hmcast])
    have hfloor : h ≤ ⌊r / (d : ℝ)⌋₊ :=
      (Nat.le_floor_iff (div_nonneg hrNonneg hdR.le)).2 hhi
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hfloor), ⟨hlo, hhi⟩⟩
  · intro hh
    rcases Finset.mem_filter.mp hh with ⟨_, ⟨hlo, hhi⟩⟩
    let m : ℕ := d * h
    have hdiv : d ∣ m := ⟨h, rfl⟩
    have hquot : m / d = h := by
      dsimp [m]
      exact Nat.mul_div_cancel_left h hd
    have hmcast : (m : ℝ) = (d : ℝ) * (h : ℝ) := by
      dsimp [m]
      norm_cast
    have hmlo : l ≤ (m : ℝ) := by
      calc
        l ≤ (h : ℝ) * (d : ℝ) := (div_le_iff₀ hdR).1 hlo
        _ = (d : ℝ) * (h : ℝ) := by ring
        _ = (m : ℝ) := hmcast.symm
    have hmhi : (m : ℝ) ≤ r := by
      calc
        (m : ℝ) = (d : ℝ) * (h : ℝ) := hmcast
        _ = (h : ℝ) * (d : ℝ) := by ring
        _ ≤ r := (le_div_iff₀ hdR).1 hhi
    have hmFloor : m ≤ ⌊r⌋₊ :=
      (Nat.le_floor_iff hrNonneg).2 hmhi
    have hmI : m ∈ (Finset.range (⌊r⌋₊ + 1)).filter
        (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r) := by
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hmFloor), ⟨hmlo, hmhi⟩⟩
    exact ⟨m, Finset.mem_filter.mpr ⟨hmI, hdiv⟩, hquot⟩

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
