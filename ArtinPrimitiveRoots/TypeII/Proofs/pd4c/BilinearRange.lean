import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RationalRange
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.FiniteGram

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Rationally approximable phases control the squared norm of a finite bilinear matrix. -/
theorem rational_bilinear_range_bound (c : ℤ) (d M N : ℕ)
    (hd : 2 ≤ d) (hcop : Int.gcd c (d : ℤ) = 1)
    (θ : ℝ) (happrox : |θ-(c : ℝ)/(d : ℝ)| ≤ 1/(d : ℝ)^2)
    (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range N, ‖∑ i ∈ Finset.range M,
      additiveCharacter (θ*(i : ℝ)*(n : ℝ))*f i‖^2) ≤
    (((M/(d/2)+1 : ℕ) : ℝ)*
      ((N : ℝ)+32*(d : ℝ)*(1+Real.log (4*(d : ℝ))))) *
      (∑ i ∈ Finset.range M, ‖f i‖^2) := by
  let k (n i : ℕ) : ℂ := additiveCharacter (θ*(i : ℝ)*(n : ℝ))
  let G (i j : ℕ) : ℂ := ∑ n ∈ Finset.range N, star (k n i)*k n j
  let R : ℝ := ((M/(d/2)+1 : ℕ) : ℝ)*
    ((N : ℝ)+32*(d : ℝ)*(1+Real.log (4*(d : ℝ))))
  have hstar (t : ℝ) : star (additiveCharacter t) = additiveCharacter (-t) := by
    have hmul : additiveCharacter (-t)*additiveCharacter t=1 := by
      rw [← pd4c_character_add]
      simp [additiveCharacter]
    calc
      _ = (additiveCharacter t)⁻¹ :=
        (Complex.inv_eq_conj (pd4c_character_norm t)).symm
      _ = _ := inv_eq_of_mul_eq_one_left hmul
  have hentry (i j : ℕ) : G i j = ∑ n ∈ Finset.range N,
      additiveCharacter ((((j : ℤ)-(i : ℤ) : ℤ) : ℝ)*θ*(n : ℝ)) := by
    dsimp only [G, k]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hstar, ← pd4c_character_add]
    congr 1
    push_cast
    ring
  have hrow (i : ℕ) (hi : i ∈ Finset.range M) :
      (∑ j ∈ Finset.range M, ‖G i j‖) ≤ R := by
    simp_rw [hentry]
    exact rational_geometric_range_bound c d M N hd hcop θ happrox (i : ℤ)
  have hsym (i j : ℕ) : ‖G i j‖=‖G j i‖ := by
    have heq : G i j=star (G j i) := by
      dsimp only [G]
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [star_mul, star_star] <;> ring
    rw [heq, norm_star]
  have hcol (j : ℕ) (hj : j ∈ Finset.range M) :
      (∑ i ∈ Finset.range M, ‖G i j‖) ≤ R := by
    calc
      _ = ∑ i ∈ Finset.range M, ‖G j i‖ :=
        Finset.sum_congr rfl fun i hi => hsym i j
      _ ≤ _ := hrow j hj
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (4*(d : ℝ)) := Real.log_nonneg (by linarith only [hdR])
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  exact finite_gram_norm_bound (Finset.range M) (Finset.range N) k f R hR hrow hcol

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
