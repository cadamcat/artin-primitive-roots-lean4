import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- Exact weighted adjoint balance transfers a finite kernel norm bound, including zero masses. -/
theorem finite_weighted_adjoint_kernel_bound {α : Type*} [DecidableEq α]
    (T : Finset α) (μ : α → ℝ) (hμ : ∀ u ∈ T, 0 ≤ μ u)
    (a b : α → α → ℂ) (R : ℝ)
    (hbalance : ∀ u ∈ T, ∀ v ∈ T,
      (μ u : ℂ)*b u v = (μ v : ℂ)*star (a v u))
    (hforward : ∀ g : α → ℂ,
      (∑ u ∈ T, μ u*‖∑ v ∈ T, a u v*g v‖^2) ≤
        R^2*(∑ v ∈ T, μ v*‖g v‖^2))
    (f : α → ℂ) :
    (∑ u ∈ T, μ u*‖∑ v ∈ T, b u v*f v‖^2) ≤
      R^2*(∑ v ∈ T, μ v*‖f v‖^2) := by
  let E := fun g : α → ℂ => ∑ u ∈ T, μ u*‖g u‖^2
  let pair := fun g h : α → ℂ => ∑ u ∈ T, (μ u : ℂ)*star (g u)*h u
  let A := fun g : α → ℂ => fun u : α => ∑ v ∈ T, a u v*g v
  let B := fun g : α → ℂ => fun u : α => ∑ v ∈ T, b u v*g v
  have hE (g : α → ℂ) : 0 ≤ E g :=
    Finset.sum_nonneg (fun u hu => mul_nonneg (hμ u hu) (sq_nonneg _))
  have hstar (z : ℂ) : star z*z = ((‖z‖^2 : ℝ) : ℂ) := by
    simp only [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow]
  have hself (g : α → ℂ) : (pair g g).re = E g := by
    dsimp only [pair, E]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [mul_assoc, hstar, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hself_square (g : α → ℂ) : (E g)^2 ≤ ‖pair g g‖^2 := by
    have hle : E g ≤ ‖pair g g‖ := by
      rw [← hself g]
      exact Complex.re_le_norm _
    simpa only [pow_two] using mul_le_mul hle hle (hE g) (norm_nonneg _)
  have hcs (g h : α → ℂ) : ‖pair g h‖^2 ≤ E g*E h := by
    let V := fun u : α => Real.sqrt (μ u)*‖g u‖
    let W := fun u : α => Real.sqrt (μ u)*‖h u‖
    have hmul (u : α) (hu : u ∈ T) : V u*W u = μ u*‖g u‖*‖h u‖ := by
      calc
        _ = (Real.sqrt (μ u))^2*‖g u‖*‖h u‖ := by dsimp only [V, W]; ring
        _ = _ := by rw [Real.sq_sqrt (hμ u hu)]
    have hV (u : α) (hu : u ∈ T) : (V u)^2 = μ u*‖g u‖^2 := by
      calc
        _ = (Real.sqrt (μ u))^2*‖g u‖^2 := by dsimp only [V]; ring
        _ = _ := by rw [Real.sq_sqrt (hμ u hu)]
    have hW (u : α) (hu : u ∈ T) : (W u)^2 = μ u*‖h u‖^2 := by
      calc
        _ = (Real.sqrt (μ u))^2*‖h u‖^2 := by dsimp only [W]; ring
        _ = _ := by rw [Real.sq_sqrt (hμ u hu)]
    have hnorm : ‖pair g h‖ ≤ ∑ u ∈ T, μ u*‖g u‖*‖h u‖ := by
      calc
        _ ≤ ∑ u ∈ T, ‖(μ u : ℂ)*star (g u)*h u‖ := norm_sum_le T _
        _ = _ := Finset.sum_congr rfl (fun u hu => by
          rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hμ u hu)])
    have hnonneg : 0 ≤ ∑ u ∈ T, μ u*‖g u‖*‖h u‖ :=
      Finset.sum_nonneg (fun u hu => mul_nonneg (mul_nonneg (hμ u hu) (norm_nonneg _))
        (norm_nonneg _))
    have hsumVW : (∑ u ∈ T, V u*W u) = ∑ u ∈ T, μ u*‖g u‖*‖h u‖ :=
      Finset.sum_congr rfl (fun u hu => hmul u hu)
    have hsumV : (∑ u ∈ T, (V u)^2) = E g :=
      Finset.sum_congr rfl (fun u hu => hV u hu)
    have hsumW : (∑ u ∈ T, (W u)^2) = E h :=
      Finset.sum_congr rfl (fun u hu => hW u hu)
    calc
      _ ≤ (∑ u ∈ T, μ u*‖g u‖*‖h u‖)^2 := by
        simpa only [pow_two] using mul_le_mul hnorm hnorm (norm_nonneg _) hnonneg
      _ = (∑ u ∈ T, V u*W u)^2 := congrArg (fun x : ℝ => x^2) hsumVW.symm
      _ ≤ (∑ u ∈ T, (V u)^2)*(∑ u ∈ T, (W u)^2) :=
        Finset.sum_mul_sq_le_sq_mul_sq T V W
      _ = _ := by rw [hsumV, hsumW]
  have hadjoint (g h : α → ℂ) : pair g (B h) = pair (A g) h := by
    dsimp only [pair, A, B]
    simp_rw [star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    calc
      _ = ((μ u : ℂ)*b u v)*star (g u)*h v := by ring
      _ = ((μ v : ℂ)*star (a v u))*star (g u)*h v := by rw [hbalance u hu v hv]
      _ = _ := by ring
  have hforward' : E (A (B f)) ≤ R^2*E (B f) := hforward (B f)
  have hineq : (E (B f))^2 ≤ E (A (B f))*E f := by
    calc
      _ ≤ ‖pair (B f) (B f)‖^2 := hself_square (B f)
      _ = ‖pair (A (B f)) f‖^2 := congrArg (fun z : ℂ => ‖z‖^2) (hadjoint (B f) f)
      _ ≤ _ := hcs (A (B f)) f
  change E (B f) ≤ R^2*E f
  by_cases hzero : E (B f) = 0
  · rw [hzero]
    exact mul_nonneg (sq_nonneg _) (hE f)
  · have hpos : 0 < E (B f) := lt_of_le_of_ne (hE (B f)) (Ne.symm hzero)
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      _ ≤ E (A (B f))*E f := by simpa only [pow_two] using hineq
      _ ≤ (R^2*E (B f))*E f := mul_le_mul_of_nonneg_right hforward' (hE f)
      _ = _ := by ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
