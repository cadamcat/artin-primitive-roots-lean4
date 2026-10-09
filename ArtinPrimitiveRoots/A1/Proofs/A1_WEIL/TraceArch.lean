import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import Mathlib.LinearAlgebra.QuadraticForm.Signature

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The real trace form has balanced signature because multiplication by i negates it.
Guide: PROOFS.md:480–485. Uses: primitive fourth root from D; QuadraticForm signature invariance and weighted-squares counts. -/
theorem quadratic_trace_arch_phase_one (D : FieldData F) (a : Fˣ)
    (T : QuadraticTraceDiagonal a) : traceArchPhase T = 1 := by
  let m : F →ₗ[ℚ] F := LinearMap.mul ℚ F (a : F)
  let B : LinearMap.BilinForm ℚ F := (Algebra.traceForm ℚ F).compLeft m
  let Q : QuadraticForm ℚ F := B.toQuadraticMap
  have hQval (x : F) : Q x = Algebra.trace ℚ F ((a : F) * x ^ 2) := by
    simp only [Q, LinearMap.BilinMap.toQuadraticMap_apply, B,
      LinearMap.BilinForm.compLeft_apply, m, Algebra.traceForm_apply]
    congr 1
    change (a : F) * x * x = (a : F) * x ^ 2
    ring
  let c : Fin (Module.finrank ℚ F) → ℚ := fun j => (T.coeff j : ℚ)
  have hdiag : Q.Equivalent (QuadraticMap.weightedSumSquares ℚ c) := by
    refine ⟨{ T.basis.equivFun with map_app' := ?_ }⟩
    intro x
    calc
      QuadraticMap.weightedSumSquares ℚ c (T.basis.equivFun x) =
          ∑ j, (T.coeff j : ℚ) * (T.basis.repr x j) ^ 2 := by
        rw [QuadraticMap.weightedSumSquares_apply, T.basis.equivFun_apply]
        simp [c, Units.smul_def, pow_two]
      _ = Q x := (T.diagonal x).symm.trans (hQval x).symm

  let i : F := D.ζ12 ^ 3
  have hζ6sq : (D.ζ12 ^ 6) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact D.hζ12.pow_eq_one
  have hζ6ne : D.ζ12 ^ 6 ≠ 1 :=
    D.hζ12.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hζ6 : D.ζ12 ^ 6 = -1 := by
    rcases sq_eq_one_iff.mp hζ6sq with h | h
    · exact (hζ6ne h).elim
    · exact h
  have hi2 : i ^ 2 = -1 := by
    dsimp [i]
    calc
      (D.ζ12 ^ 3) ^ 2 = D.ζ12 ^ (3 * 2) := by rw [pow_mul]
      _ = D.ζ12 ^ 6 := by norm_num
      _ = -1 := hζ6
  have hi0 : i ≠ 0 := by
    intro h
    rw [h] at hi2
    norm_num at hi2
  have hiSq : i * i = -1 := by simpa [pow_two] using hi2
  have hiInv : i * (-i) = 1 := by
    rw [mul_neg, hiSq]
    simp
  let f : F →ₗ[ℚ] F := LinearMap.mul ℚ F i
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact mul_left_cancel₀ hi0 (by simpa [f] using hxy)
    · intro y
      refine ⟨(-i) * y, ?_⟩
      change i * ((-i) * y) = y
      rw [← mul_assoc, hiInv, one_mul]
  let e : F ≃ₗ[ℚ] F := LinearEquiv.ofBijective f hf
  have heval (x : F) : e x = i * x := rfl
  have hanti (x : F) : Q (e x) = -Q x := by
    rw [heval, hQval, hQval]
    calc
      Algebra.trace ℚ F ((a : F) * (i * x) ^ 2) =
          Algebra.trace ℚ F (-((a : F) * x ^ 2)) := by
        congr 1
        rw [mul_pow, hi2]
        ring
      _ = -Algebra.trace ℚ F ((a : F) * x ^ 2) := by simp
  have hantiEquiv : Q.Equivalent (-Q) := by
    refine ⟨{ e with map_app' := ?_ }⟩
    intro x
    change -Q (e x) = Q x
    rw [hanti x]
    simp
  have hbalance : sigPos Q = sigNeg Q := by
    calc
      sigPos Q = sigPos (-Q) := hantiEquiv.sigPos_eq
      _ = sigNeg Q := rfl
  have hpos : sigPos Q = {j | 0 < c j}.ncard :=
    QuadraticForm.sigPos_of_equiv_weightedSumSquares hdiag
  have hneg : sigNeg Q = {j | c j < 0}.ncard :=
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares hdiag
  let pos : Finset (Fin (Module.finrank ℚ F)) :=
    Finset.univ.filter fun j => 0 < c j
  let neg : Finset (Fin (Module.finrank ℚ F)) :=
    Finset.univ.filter fun j => c j < 0
  have hposSet : ({j | 0 < c j} : Set (Fin (Module.finrank ℚ F))) = pos := by
    ext j
    simp [pos]
  have hnegSet : ({j | c j < 0} : Set (Fin (Module.finrank ℚ F))) = neg := by
    ext j
    simp [neg]
  have hposCard : sigPos Q = pos.card := by
    rw [hpos]
    rw [hposSet, Set.ncard_coe_finset]
  have hnegCard : sigNeg Q = neg.card := by
    rw [hneg]
    rw [hnegSet, Set.ncard_coe_finset]
  have hcounts : pos.card = neg.card := by
    calc
      pos.card = sigPos Q := hposCard.symm
      _ = sigNeg Q := hbalance
      _ = neg.card := hnegCard
  have hcne (j : Fin (Module.finrank ℚ F)) : c j ≠ 0 := by
    simp [c]
  have hdisj : Disjoint pos neg := by
    apply Finset.disjoint_left.mpr
    intro j hjp hjn
    simp [pos] at hjp
    simp [neg] at hjn
    linarith
  have hcover : pos ∪ neg = Finset.univ := by
    ext j
    simp only [pos, neg, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro _
      trivial
    · intro _
      rcases lt_or_gt_of_ne (Ne.symm (hcne j)) with hp | hn
      · exact Or.inl hp
      · exact Or.inr hn
  let z : ℂ := -(Real.pi * Complex.I / 4)
  let s : Fin (Module.finrank ℚ F) → ℂ :=
    fun j => if 0 < c j then 1 else -1
  have hphase (j : Fin (Module.finrank ℚ F)) :
      rationalArchPhase (T.coeff j) = Complex.exp (z * s j) := by
    unfold rationalArchPhase z s
    congr 1
    ring
  have hposSum : (∑ j ∈ pos, s j) = (pos.card : ℂ) := by
    calc
      (∑ j ∈ pos, s j) = ∑ j ∈ pos, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hp : 0 < c j := by simpa [pos] using hj
        simp [s, hp]
      _ = (pos.card : ℂ) := by simp
  have hnegSum : (∑ j ∈ neg, s j) = -(neg.card : ℂ) := by
    calc
      (∑ j ∈ neg, s j) = ∑ j ∈ neg, (-1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hn : c j < 0 := by simpa [neg] using hj
        have hnp : ¬0 < c j := not_lt_of_ge (le_of_lt hn)
        simp [s, hnp]
      _ = -(neg.card : ℂ) := by simp
  have hsum : (∑ j, s j) = (pos.card : ℂ) - (neg.card : ℂ) := by
    calc
      (∑ j, s j) = ∑ j ∈ pos ∪ neg, s j := by rw [hcover]
      _ = (∑ j ∈ pos, s j) + (∑ j ∈ neg, s j) := Finset.sum_union hdisj
      _ = (pos.card : ℂ) - (neg.card : ℂ) := by rw [hposSum, hnegSum]; ring
  calc
    traceArchPhase T = ∏ j, rationalArchPhase (T.coeff j) := rfl
    _ = Complex.exp (∑ j, z * s j) := by
      rw [Complex.exp_sum]
      apply Finset.prod_congr rfl
      intro j hj
      exact hphase j
    _ = Complex.exp (z * ((pos.card : ℂ) - (neg.card : ℂ))) := by
      congr 1
      rw [← Finset.mul_sum, hsum]
    _ = 1 := by rw [hcounts]; simp

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
