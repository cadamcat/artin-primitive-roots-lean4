import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-HAD».Dyadic
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-HAD».Counts
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-HAD».Affine

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

def inverseSquareTerms (G : ℂ → ℂ) (z : ℂ) : ℝ :=
  if G z = 0 then (analyticOrderNatAt G z : ℝ) * ‖z‖⁻¹ ^ 2 else 0

def zeroLogTerms (G : ℂ → ℂ) (s z : ℂ) : ℂ :=
  if G z = 0 then (analyticOrderNatAt G z : ℂ) * ((s - z)⁻¹ + z⁻¹) else 0

/-- Jensen growth on dyadic disks gives the genus-one convergence exponent. -/
theorem inverse_square_summable (G : ℂ → ℂ) (hG : Differentiable ℂ G) (hG0 : G 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖G s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2))) :
    Summable (inverseSquareTerms G) := by
  obtain ⟨A, hA, hfinite, hcount⟩ := entire_dyadic_zero_count G hG hG0 hgrowth
  have hsum := inverse_square_of_dyadic_count hA hfinite hcount
  have heq : (fun z : ℂ => (zeroOrderWeights G z : ℝ) * ‖z‖⁻¹ ^ 2) =
      inverseSquareTerms G := by
    funext z
    by_cases hz : G z = 0 <;> simp [zeroOrderWeights, inverseSquareTerms, hz]
  rw [heq] at hsum
  exact hsum

/-- Affine factorization and divisor-fiber grouping give the order-one logarithmic derivative. -/
theorem hadamard_logDeriv_order_one (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hG0 : G 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖G s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2))) :
    ∃ B : ℂ, ∀ s : ℂ, G s ≠ 0 →
      Summable (zeroLogTerms G s) ∧
      deriv G s / G s = B + ∑' z : ℂ, zeroLogTerms G s z := by
  classical
  let I := Port.Complex.Hadamard.divisorZeroIndex₀ G (Set.univ : Set ℂ)
  let value : I → ℂ := Port.Complex.Hadamard.divisorZeroIndex₀_val
  let fiber (z : ℂ) : Set I := {p | value p = z}
  have hfinite (z : ℂ) : (fiber z).Finite :=
    Port.Complex.Hadamard.divisorZeroIndex₀_fiber_finite G z
  have hcard (z : ℂ) : Nat.card (fiber z) =
      if z = 0 then 0 else analyticOrderNatAt G z := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card (fiber z) (hfinite z)]
    change (Port.Complex.Hadamard.divisorZeroIndex₀_fiberFinset G z).card = _
    by_cases hz : z = 0
    · have he : Port.Complex.Hadamard.divisorZeroIndex₀_fiberFinset G z = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hv := (Port.Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset G z p).mp hp
        exact Port.Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p (hv.trans hz)
      rw [he]
      simp [hz]
    · simp only [if_neg hz]
      exact Port.Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt hG hz
  have hord (z : ℂ) (hz : G z ≠ 0) : analyticOrderNatAt G z = 0 := by
    by_contra hn
    exact hz (apply_eq_zero_of_analyticOrderNatAt_ne_zero hn)
  have hreal (z : ℂ) :
      (∑' p : fiber z, ‖value p‖⁻¹ ^ 2) = inverseSquareTerms G z := by
    calc
      _ = ∑' _p : fiber z, ‖z‖⁻¹ ^ 2 := by
        apply tsum_congr
        intro p
        rw [show value p = z from p.property]
      _ = (Nat.card (fiber z) : ℝ) * ‖z‖⁻¹ ^ 2 := by
        letI := (hfinite z).fintype
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ = inverseSquareTerms G z := by
        rw [hcard]
        by_cases hz : z = 0
        · simp [hz, inverseSquareTerms, hG0]
        · simp only [if_neg hz]
          by_cases hg : G z = 0
          · simp [inverseSquareTerms, hg]
          · simp [inverseSquareTerms, hg, hord z hg]
  have hsquare : Summable (fun p : I => ‖value p‖⁻¹ ^ 2) := by
    have hpart : ∀ p : I, ∃! z : ℂ, p ∈ fiber z := by
      intro p
      exact ⟨value p, rfl, fun z hz => hz.symm⟩
    apply (summable_partition (fun p => by positivity) (s := fiber) hpart).mpr
    refine ⟨?_, ?_⟩
    · intro z
      exact (hfinite z).summable (fun p : I => ‖value p‖⁻¹ ^ 2)
    · exact (inverse_square_summable G hG hG0 hgrowth).congr fun z => (hreal z).symm
  have hzero (p : I) : G (value p) = 0 := by
    apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
    intro hn
    have hd := Port.Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int hG (value p)
    exact Port.Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p
      (hd.trans (by rw [hn]; rfl))
  obtain ⟨A, B, hfac⟩ := hadamard_affine_divisor_product G hG hG0 hgrowth
  refine ⟨B, fun s hs => ?_⟩
  have haway (p : I) : s ≠ value p := by
    intro hp
    exact hs (hp ▸ hzero p)
  let term (p : I) : ℂ := 1 / (s - value p) + 1 / value p
  have hterms : Summable term :=
    Port.Complex.Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
      hsquare haway
  have hcomplex (z : ℂ) : (∑' p : fiber z, term p) = zeroLogTerms G s z := by
    calc
      _ = ∑' _p : fiber z, (1 / (s - z) + 1 / z) := by
        apply tsum_congr
        intro p
        dsimp [term]
        rw [show value p = z from p.property]
      _ = (Nat.card (fiber z) : ℂ) * (1 / (s - z) + 1 / z) := by
        letI := (hfinite z).fintype
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ = zeroLogTerms G s z := by
        rw [hcard]
        by_cases hz : z = 0
        · simp [hz, zeroLogTerms, hG0]
        · simp only [if_neg hz]
          by_cases hg : G z = 0
          · simp [zeroLogTerms, hg, one_div]
          · simp [zeroLogTerms, hg, hord z hg]
  have hgroup : HasSum (zeroLogTerms G s) (∑' p : I, term p) := by
    have ht := hterms.hasSum.tsum_fiberwise value
    have heq : (fun z : ℂ => ∑' p : value ⁻¹' {z}, term p) = zeroLogTerms G s := by
      funext z
      change (∑' p : fiber z, term p) = zeroLogTerms G s z
      exact hcomplex z
    rw [heq] at ht
    exact ht
  refine ⟨hgroup.summable, ?_⟩
  let E : ℂ → ℂ := fun w => Complex.exp (A + B * w)
  let P : ℂ → ℂ := Port.Complex.Hadamard.divisorCanonicalProduct 1 G Set.univ
  have hfun : G = E * P := funext hfac
  have hPne : P s ≠ 0 := by
    intro hp
    apply hs
    rw [hfac s]
    change E s * P s = 0
    rw [hp, mul_zero]
  have hEder : HasDerivAt E (E s * B) s := by
    simpa [E] using (((hasDerivAt_id s).const_mul B).const_add A).cexp
  have hPdiff : DifferentiableAt ℂ P s :=
    Port.Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ 1 G hsquare s
  have hElog : logDeriv E s = B := by
    rw [logDeriv_apply, hEder.deriv]
    exact mul_div_cancel_left₀ B (Complex.exp_ne_zero (A + B * s))
  have hPlog : logDeriv P s = ∑' p : I, term p :=
    Port.Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
      hsquare haway
  calc
    deriv G s / G s = logDeriv G s := rfl
    _ = logDeriv (E * P) s := congrArg (fun f : ℂ → ℂ => logDeriv f s) hfun
    _ = logDeriv E s + logDeriv P s :=
      logDeriv_mul s (Complex.exp_ne_zero (A + B * s)) hPne hEder.differentiableAt hPdiff
    _ = B + ∑' p : I, term p := by rw [hElog, hPlog]
    _ = B + ∑' z : ℂ, zeroLogTerms G s z := by rw [hgroup.tsum_eq]

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
