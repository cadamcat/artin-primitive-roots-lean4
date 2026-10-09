import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.WeightedDiagonal
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.ProductMass

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Prime-tuple masses transfer the counting kernel norm with the clean 1/Y factor. -/
theorem prime_tuple_weighted_kernel_bound {ι : Type*} [DecidableEq ι] {K : ℕ}
    (x : ℝ) (a : Fin K → ℝ) (q Y Ceta R : ℝ) (hY : 0 < Y) (hCeta : 0 ≤ Ceta)
    (hV : ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass x (a i))
    (hb : ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (1/2 : ℝ) ≤ memoryBPrime x q p)
    (I : Finset (ι × (Fin K → ℕ)))
    (hI : ∀ u ∈ I, IsMarkedPrimeTuple x K a u.2 ∧ Y ≤ (tupleProduct u.2 : ℝ))
    (k : (ι × (Fin K → ℕ)) → (ι × (Fin K → ℕ)) → ℂ)
    (d e : (ι × (Fin K → ℕ)) → ℂ)
    (hd : ∀ u ∈ I, ‖d u‖ ≤ Ceta) (he : ∀ u ∈ I, ‖e u‖ ≤ Ceta)
    (hk : ∀ g : (ι × (Fin K → ℕ)) → ℂ,
      (∑ u ∈ I, ‖∑ v ∈ I, k u v*g v‖^2) ≤ R^2*(∑ v ∈ I, ‖g v‖^2))
    (f : (ι × (Fin K → ℕ)) → ℂ) :
    let μ : (ι × (Fin K → ℕ)) → ℝ :=
      fun u => ∏ i : Fin K, memoryNu x K a q i (u.2 i)
    (∑ u ∈ I, μ u*‖d u*(∑ v ∈ I, k u v*(μ v : ℂ)*e v*f v)‖^2) ≤
      (((Ceta^2*(4/Real.log 2)^K/Y)*R)^2)*(∑ v ∈ I, μ v*‖f v‖^2) := by
  let μ : (ι × (Fin K → ℕ)) → ℝ :=
    fun u => ∏ i : Fin K, memoryNu x K a q i (u.2 i)
  let M : ℝ := (4/Real.log 2)^K/Y
  let C : ℝ := Ceta*Real.sqrt M
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hC : 0 ≤ C := mul_nonneg hCeta (Real.sqrt_nonneg M)
  have hmass (u : ι × (Fin K → ℕ)) (hu : u ∈ I) : 0 ≤ μ u ∧ μ u ≤ M :=
    clean_product_mass_le x a q Y hY hV hb u.2 (hI u hu).1 (hI u hu).2
  have hendpoint (E : (ι × (Fin K → ℕ)) → ℂ)
      (hE : ∀ u ∈ I, ‖E u‖ ≤ Ceta) (u : ι × (Fin K → ℕ)) (hu : u ∈ I) :
      Real.sqrt (μ u)*‖E u‖ ≤ C := by
    calc
      _ ≤ Real.sqrt (μ u)*Ceta :=
        mul_le_mul_of_nonneg_left (hE u hu) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt M*Ceta :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hmass u hu).2) hCeta
      _ = C := by dsimp only [C]; ring
  have hbound := finite_weighted_diagonal_transfer I μ k d e C C R hC hC
    (fun u hu => (hmass u hu).1) (hendpoint d hd) (hendpoint e he) hk f
  have hconst : C*C*R = (Ceta^2*(4/Real.log 2)^K/Y)*R := by
    calc
      _ = Ceta^2*(Real.sqrt M)^2*R := by dsimp only [C]; ring
      _ = Ceta^2*M*R := by rw [Real.sq_sqrt hM]
      _ = _ := by dsimp only [M]; ring
  rw [hconst] at hbound
  exact hbound

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
