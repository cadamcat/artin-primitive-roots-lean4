import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.BilinearRange
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.FiniteTensor

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The determinant character is a crossed tensor of two controlled bilinear matrices. -/
theorem rational_determinant_range_bound (c : ℤ) (d M N : ℕ)
    (hd : 2 ≤ d) (hcop : Int.gcd c (d : ℤ)=1)
    (θ : ℝ) (happrox : |θ-(c : ℝ)/(d : ℝ)| ≤ 1/(d : ℝ)^2)
    (f : ℕ → ℕ → ℂ) :
    (∑ x ∈ Finset.range M, ∑ y ∈ Finset.range N,
      ‖∑ u ∈ Finset.range M, ∑ v ∈ Finset.range N,
        additiveCharacter (θ*((x : ℝ)*(v : ℝ)-(y : ℝ)*(u : ℝ)))*f u v‖^2) ≤
    (((N/(d/2)+1 : ℕ) : ℝ)*((M : ℝ)+32*(d : ℝ)*(1+Real.log (4*(d : ℝ))))) *
    (((M/(d/2)+1 : ℕ) : ℝ)*((N : ℝ)+32*(d : ℝ)*(1+Real.log (4*(d : ℝ))))) *
    (∑ u ∈ Finset.range M, ∑ v ∈ Finset.range N, ‖f u v‖^2) := by
  let k (x v : ℕ) : ℂ := additiveCharacter (θ*(v : ℝ)*(x : ℝ))
  let l (y u : ℕ) : ℂ := additiveCharacter ((-θ)*(u : ℝ)*(y : ℝ))
  let a : ℝ := ((N/(d/2)+1 : ℕ) : ℝ)*
    ((M : ℝ)+32*(d : ℝ)*(1+Real.log (4*(d : ℝ))))
  let b : ℝ := ((M/(d/2)+1 : ℕ) : ℝ)*
    ((N : ℝ)+32*(d : ℝ)*(1+Real.log (4*(d : ℝ))))
  have hcopNeg : Int.gcd (-c) (d : ℤ)=1 := by simpa using hcop
  have happroxNeg : |(-θ)-((-c : ℤ) : ℝ)/(d : ℝ)| ≤ 1/(d : ℝ)^2 := by
    have heq : (-θ)-((-c : ℤ) : ℝ)/(d : ℝ) = -(θ-(c : ℝ)/(d : ℝ)) := by
      push_cast
      ring
    rw [heq, abs_neg]
    exact happrox
  have hk (g : ℕ → ℂ) : (∑ x ∈ Finset.range M, ‖∑ v ∈ Finset.range N, k x v*g v‖^2) ≤
      a*(∑ v ∈ Finset.range N, ‖g v‖^2) :=
    rational_bilinear_range_bound c d N M hd hcop θ happrox g
  have hl (g : ℕ → ℂ) : (∑ y ∈ Finset.range N, ‖∑ u ∈ Finset.range M, l y u*g u‖^2) ≤
      b*(∑ u ∈ Finset.range M, ‖g u‖^2) :=
    rational_bilinear_range_bound (-c) d M N hd hcopNeg (-θ) happroxNeg g
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (4*(d : ℝ)) := Real.log_nonneg (by linarith only [hdR])
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hentry (x y u v : ℕ) : k x v*l y u =
      additiveCharacter (θ*((x : ℝ)*(v : ℝ)-(y : ℝ)*(u : ℝ))) := by
    dsimp only [k, l]
    rw [← pd4c_character_add]
    congr 1
    ring
  have h := finite_tensor_norm_bound (Finset.range M) (Finset.range N) k l f a b ha hb hk hl
  simp_rw [hentry] at h
  exact h

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
