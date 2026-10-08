import Mathlib

/-! Finite-field identities for the A1 Gauss-character construction. -/

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_gauss_sol

variable {k : Type*} [Field k] [Fintype k]

def quadraticComplex : MulChar k ℂ := by
  classical
  exact (quadraticChar k).ringHomComp (Int.castRingHom ℂ)

theorem jacobiSum_duplication (χ : MulChar k ℂ) (hχ : χ ≠ 1)
    (hodd : ringChar k ≠ 2) :
    χ 4 * jacobiSum χ χ = jacobiSum (quadraticComplex (k := k)) χ := by
  classical
  have htwo : (2 : k) ≠ 0 := by
    intro h
    apply hodd
    apply neg_one_eq_one_iff.mp
    linear_combination -h
  let e : k ≃ k := (Equiv.mulLeft₀ (2 : k) htwo).trans (Equiv.subRight 1)
  have hchange : χ 4 * jacobiSum χ χ = ∑ t : k, χ (1 - t ^ 2) := by
    calc
      χ 4 * jacobiSum χ χ = ∑ x : k, χ (4 * x * (1 - x)) := by
        simp only [jacobiSum, Finset.mul_sum, map_mul, mul_assoc]
      _ = ∑ x : k, χ (1 - (e x) ^ 2) := by
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        simp only [e, Equiv.trans_apply, Equiv.mulLeft₀_apply, Equiv.subRight_apply]
        ring
      _ = ∑ t : k, χ (1 - t ^ 2) := e.sum_comp (fun t : k => χ (1 - t ^ 2))
  have hcount (s : k) :
      ((Finset.univ.filter (fun t : k => t ^ 2 = s)).card : ℂ) =
        quadraticComplex (k := k) s + 1 := by
    have h : ((Finset.univ.filter (fun t : k => t ^ 2 = s)).card : ℤ) =
        quadraticChar k s + 1 := by
      simpa only [Set.toFinset_ofPred] using quadraticChar_card_sqrts hodd s
    have hc := congrArg (Int.castRingHom ℂ) h
    simpa [quadraticComplex] using hc
  have hsum : ∑ s : k, χ (1 - s) = 0 := by
    calc
      (∑ s : k, χ (1 - s)) = ∑ s : k, χ s := (Equiv.subLeft 1).sum_comp χ
      _ = 0 := χ.sum_eq_zero_of_ne_one hχ
  rw [hchange]
  calc
    (∑ t : k, χ (1 - t ^ 2)) =
        ∑ s : k, ∑ t ∈ Finset.univ with t ^ 2 = s, χ (1 - s) :=
      (Finset.sum_fiberwise' Finset.univ (fun t : k => t ^ 2)
        (fun s : k => χ (1 - s))).symm
    _ = ∑ s : k, (quadraticComplex (k := k) s + 1) * χ (1 - s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_const, nsmul_eq_mul, hcount]
    _ = jacobiSum (quadraticComplex (k := k)) χ := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib, hsum, add_zero, jacobiSum]

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
