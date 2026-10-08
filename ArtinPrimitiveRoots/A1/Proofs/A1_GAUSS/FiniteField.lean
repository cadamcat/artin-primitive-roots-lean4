import Mathlib

/-! Finite-field identities for the A1 Gauss-character construction. -/

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_gauss_sol

variable {k : Type*} [Field k] [Fintype k]

def quadraticComplex : MulChar k ℂ := by
  classical
  exact (quadraticChar k).ringHomComp (Int.castRingHom ℂ)

def normalizedGauss (χ : MulChar k ℂ) (ψ : AddChar k ℂ) : ℂ :=
  ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * gaussSum χ ψ

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

theorem normalized_sextic_duplication (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ6 : χ ^ 6 = 1)
    (hquad : χ ^ 3 = quadraticComplex (k := k)) (hneg : χ (-1) = 1)
    (hodd : ringChar k ≠ 2) (hψ : ψ.IsPrimitive) :
    normalizedGauss χ ψ * normalizedGauss (χ ^ 2) ψ =
      (χ 4)⁻¹ * normalizedGauss (χ ^ 3) ψ * normalizedGauss (χ ^ 2) ψ ^ 3 := by
  let g1 := gaussSum χ ψ
  let g2 := gaussSum (χ ^ 2) ψ
  let g3 := gaussSum (χ ^ 3) ψ
  let g4 := gaussSum (χ ^ 4) ψ
  let n : ℂ := Fintype.card k
  let c : ℂ := ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)
  have hn0 : (Fintype.card k : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card k ≠ 0)
  have hg1 : g1 ≠ 0 := gaussSum_ne_zero_of_nontrivial hn0 hχ hψ
  have hχ4inv : χ ^ 4 = (χ ^ 2)⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_add]
    exact hχ6
  have hχ4 : χ ^ 4 ≠ 1 := by
    rw [hχ4inv, inv_ne_one]
    exact hχ2
  have hneg4 : (χ ^ 4) (-1) = 1 := by
    rw [MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), hneg, one_pow]
  have hprod : g2 * g4 = n := by
    have hshift := mul_gaussSum_inv_eq_gaussSum (χ ^ 4) ψ
    rw [hneg4, one_mul] at hshift
    have h := gaussSum_mul_gaussSum_eq_card hχ2 hψ
    rw [← hχ4inv, hshift] at h
    exact h
  have hself : g2 * jacobiSum χ χ = g1 * g1 := by
    simpa only [g1, g2, pow_two] using
      jacobiSum_mul_nontrivial (show χ * χ ≠ 1 by simpa only [pow_two] using hχ2) ψ
  have h31 : χ ^ 3 * χ = χ ^ 4 := by rw [← pow_succ]
  have hcross : g4 * jacobiSum (χ ^ 3) χ = g3 * g1 := by
    simpa only [g1, g3, g4, h31] using
      jacobiSum_mul_nontrivial (show χ ^ 3 * χ ≠ 1 by rw [h31]; exact hχ4) ψ
  have hdup := jacobiSum_duplication χ hχ hodd
  rw [← hquad] at hdup
  have hraw : χ 4 * g1 * g4 = g2 * g3 := by
    apply mul_right_cancel₀ hg1
    calc
      (χ 4 * g1 * g4) * g1 = χ 4 * (g1 * g1) * g4 := by ring
      _ = χ 4 * (g2 * jacobiSum χ χ) * g4 := by rw [hself]
      _ = g2 * (g4 * (χ 4 * jacobiSum χ χ)) := by ring
      _ = g2 * (g4 * jacobiSum (χ ^ 3) χ) := by rw [hdup]
      _ = g2 * (g3 * g1) := by rw [hcross]
      _ = (g2 * g3) * g1 := by ring
  have htwo : (2 : k) ≠ 0 := by
    intro h
    apply hodd
    apply neg_one_eq_one_iff.mp
    linear_combination -h
  have hfour : (4 : k) ≠ 0 := by
    convert mul_ne_zero htwo htwo using 1 <;> norm_num
  have hval4 : χ 4 ≠ 0 := χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hfour)
  have hrel : χ 4 * (g1 * n) = g2 ^ 2 * g3 := by
    calc
      χ 4 * (g1 * n) = χ 4 * (g1 * (g2 * g4)) := by rw [hprod]
      _ = (χ 4 * g1 * g4) * g2 := by ring
      _ = g2 ^ 2 * g3 := by rw [hraw]; ring
  have hrel' : g1 * n = (χ 4)⁻¹ * g2 ^ 2 * g3 := by
    apply mul_left_cancel₀ hval4
    calc
      χ 4 * (g1 * n) = g2 ^ 2 * g3 := hrel
      _ = χ 4 * ((χ 4)⁻¹ * g2 ^ 2 * g3) := by field_simp
  have hpos : 0 < (Fintype.card k : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card k)
  have hscale : ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
      (Fintype.card k : ℝ) = 1 := by
    calc
      ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * (Fintype.card k : ℝ) =
          (Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ) * 2) * (Fintype.card k : ℝ) := by
            congr 1
            simpa using (Real.rpow_mul_natCast (le_of_lt hpos) (-(1 / 2 : ℝ)) 2).symm
      _ = (Fintype.card k : ℝ) ^ (-1 : ℝ) * (Fintype.card k : ℝ) := by norm_num
      _ = 1 := by rw [Real.rpow_neg_one, inv_mul_cancel₀ hpos.ne']
  have hc : c ^ 2 * n = 1 := by
    dsimp [c, n]
    exact_mod_cast hscale
  change (c * g1) * (c * g2) = (χ 4)⁻¹ * (c * g3) * (c * g2) ^ 3
  calc
    (c * g1) * (c * g2) = (c ^ 2 * n) * (c ^ 2 * g1 * g2) := by rw [hc]; ring
    _ = c ^ 4 * g2 * (g1 * n) := by ring
    _ = (χ 4)⁻¹ * (c * g3) * (c * g2) ^ 3 := by rw [hrel']; ring

theorem normalized_cubic_gauss_cube (ρ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hρ : ρ ≠ 1) (hρ3 : ρ ^ 3 = 1) (hneg : ρ (-1) = 1)
    (hψ : ψ.IsPrimitive) :
    normalizedGauss ρ ψ ^ 3 =
      ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * jacobiSum ρ ρ := by
  let g := gaussSum ρ ψ
  let g2 := gaussSum (ρ ^ 2) ψ
  let n : ℂ := Fintype.card k
  let c : ℂ := ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)
  have hρinv : ρ ^ 2 = ρ⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ']
    exact hρ3
  have hρ2 : ρ ^ 2 ≠ 1 := by
    rw [hρinv, inv_ne_one]
    exact hρ
  have hneg2 : (ρ ^ 2) (-1) = 1 := by
    rw [MulChar.pow_apply' ρ (by decide : (2 : ℕ) ≠ 0), hneg, one_pow]
  have hprod : g * g2 = n := by
    have hshift := mul_gaussSum_inv_eq_gaussSum (ρ ^ 2) ψ
    rw [hneg2, one_mul] at hshift
    have h := gaussSum_mul_gaussSum_eq_card hρ hψ
    rw [← hρinv, hshift] at h
    exact h
  have hself : g2 * jacobiSum ρ ρ = g * g := by
    simpa only [g, g2, pow_two] using
      jacobiSum_mul_nontrivial (show ρ * ρ ≠ 1 by simpa only [pow_two] using hρ2) ψ
  have hcube : g ^ 3 = n * jacobiSum ρ ρ := by
    calc
      g ^ 3 = g * (g * g) := by ring
      _ = g * (g2 * jacobiSum ρ ρ) := by rw [hself]
      _ = (g * g2) * jacobiSum ρ ρ := by ring
      _ = n * jacobiSum ρ ρ := by rw [hprod]
  have hpos : 0 < (Fintype.card k : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card k)
  have hscale : ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
      (Fintype.card k : ℝ) = 1 := by
    calc
      ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * (Fintype.card k : ℝ) =
          (Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ) * 2) * (Fintype.card k : ℝ) := by
            congr 1
            simpa using (Real.rpow_mul_natCast (le_of_lt hpos) (-(1 / 2 : ℝ)) 2).symm
      _ = (Fintype.card k : ℝ) ^ (-1 : ℝ) * (Fintype.card k : ℝ) := by norm_num
      _ = 1 := by rw [Real.rpow_neg_one, inv_mul_cancel₀ hpos.ne']
  have hc : c ^ 2 * n = 1 := by
    dsimp [c, n]
    exact_mod_cast hscale
  change (c * g) ^ 3 = c * jacobiSum ρ ρ
  calc
    (c * g) ^ 3 = c ^ 3 * g ^ 3 := by ring
    _ = c * (c ^ 2 * n) * jacobiSum ρ ρ := by rw [hcube]; ring
    _ = c * jacobiSum ρ ρ := by rw [hc, mul_one]

theorem normalized_quadratic_gauss_sq (φ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hφ : φ ≠ 1) (hquad : φ.IsQuadratic) (hneg : φ (-1) = 1)
    (hψ : ψ.IsPrimitive) :
    normalizedGauss φ ψ ^ 2 = 1 := by
  let g := gaussSum φ ψ
  let n : ℂ := Fintype.card k
  let c : ℂ := ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)
  have hsq : g ^ 2 = n := by
    simpa only [hneg, one_mul] using gaussSum_sq hφ hquad hψ
  have hpos : 0 < (Fintype.card k : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card k)
  have hscale : ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
      (Fintype.card k : ℝ) = 1 := by
    calc
      ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * (Fintype.card k : ℝ) =
          (Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ) * 2) * (Fintype.card k : ℝ) := by
            congr 1
            simpa using (Real.rpow_mul_natCast (le_of_lt hpos) (-(1 / 2 : ℝ)) 2).symm
      _ = (Fintype.card k : ℝ) ^ (-1 : ℝ) * (Fintype.card k : ℝ) := by norm_num
      _ = 1 := by rw [Real.rpow_neg_one, inv_mul_cancel₀ hpos.ne']
  have hc : c ^ 2 * n = 1 := by
    dsimp [c, n]
    exact_mod_cast hscale
  change (c * g) ^ 2 = 1
  calc
    (c * g) ^ 2 = c ^ 2 * g ^ 2 := by ring
    _ = c ^ 2 * n := by rw [hsq]
    _ = 1 := hc

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
