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

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
