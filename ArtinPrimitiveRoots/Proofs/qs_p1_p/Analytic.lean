import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1

/-!
# P1 analytic helpers

The initial helper proves absolute convergence of the transformed ideal series. The contour and
Mellin continuation arguments are added below as they are established.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

private theorem qs_p1_norm_multiset_map_prod_le_one {α : Type} (s : Multiset α)
    (f : α → ℂ) (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) <|
        ih (fun x hx => hf x (Multiset.mem_cons_of_mem hx))

private theorem qs_p1_idealValue_norm_le_one
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (hsq : χ ^ 2 = 1)
    (I : Ideal (𝓞 K)) : ‖χ.idealValue I‖ ≤ 1 := by
  classical
  have hχ : ∀ x : IdeleClassGroup (𝓞 K) K,
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
    intro x
    have hpow : (χ x : ℂˣ) ^ 2 = 1 := by
      have h := congrArg (fun ψ : ArtinPrimitiveRoots.A1.HeckeChar K => ψ x) hsq
      simpa using h
    have hval : (((χ x : ℂˣ) : ℂ) ^ 2) = 1 := congrArg Units.val hpow
    have hnorm : ‖((χ x : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, hval]
      norm_num
    nlinarith [norm_nonneg (((χ x : ℂˣ) : ℂ))]
  have hprime (v : ArtinPrimitiveRoots.A1.FinPlace K) :
      ‖χ.primeValue v‖ ≤ 1 := by
    unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
    split_ifs with hv
    · have hχ' := hχ (IdeleClassGroup.ofAdicCompletion
        (𝓞 K) K v (ArtinPrimitiveRoots.A1.toLoc v
          (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
            (ArtinPrimitiveRoots.A1.unif_ne_zero v))))
      exact le_of_eq (by simpa [ArtinPrimitiveRoots.A1.HeckeChar.loc] using hχ')
    · simp
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  apply qs_p1_norm_multiset_map_prod_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using hprime ⟨P, h.1, h.2⟩
  · simp [h]

/-- The transformed ideal series in the frozen P1 statement is absolutely summable. -/
theorem qs_p1_dual_summable [IsTotallyComplex K]
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor χ f) (hsq : χ ^ 2 = 1) (hne : χ ≠ 1)
    (hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1)
    (h : ℝ → ℂ) (hh : IsQSWeight h) (X : ℝ) (hX : 0 < X) :
    Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      ‖χ.idealValue a.1 * qsTransform K h
        (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ))‖) := by
  have hf0 : f ≠ ⊥ := hf.1
  have hNf0 : Ideal.absNorm f ≠ 0 := by
    intro hN
    exact hf0 (Ideal.absNorm_eq_zero_iff.mp hN)
  have hNf : 0 < (Ideal.absNorm f : ℝ) := Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hNf0)
  let c : ℝ := X / (Ideal.absNorm f : ℝ)
  have hc : 0 < c := div_pos hX hNf
  obtain ⟨_, ⟨C, hC, hbound⟩⟩ :=
    qs_transform_bounds_P0 (K := K) h hh 2 0 2 (by norm_num)
  let D : ℝ := C * c ^ (-2 : ℝ)
  have hD : 0 ≤ D := mul_nonneg hC.le (Real.rpow_nonneg (le_of_lt hc) _)
  let g : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun a =>
    D * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 a.1
  have hg : Summable g := by
    have hs : Summable (fun I : Ideal (𝓞 K) =>
        ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 I) :=
      ArtinPrimitiveRoots.Hecke.summable_idealNormRpow (K := K) (by norm_num)
    exact (hs.mul_left D).subtype (fun I : Ideal (𝓞 K) => I ≠ ⊥)
  apply Summable.of_norm_bounded hg
  intro a
  have hNa0 : Ideal.absNorm a.1 ≠ 0 := by
    intro hN
    exact a.2 (Ideal.absNorm_eq_zero_iff.mp hN)
  have hn : 0 < (Ideal.absNorm a.1 : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hNa0)
  have hx : 0 < X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ) :=
    div_pos (mul_pos hX hn) hNf
  have hxform : X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ) =
      c * (Ideal.absNorm a.1 : ℝ) := by
    dsimp [c]
    ring
  have hscale :
      (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ)) ^ (-2 : ℝ) =
        c ^ (-2 : ℝ) * (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ) := by
    rw [hxform, Real.mul_rpow (le_of_lt hc) (le_of_lt hn)]
  have hT : ‖qsTransform K h
      (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ))‖ ≤
        C * (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ)) ^ (-2 : ℝ) := by
    rcases le_total (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ)) 1 with hsmall | hlarge
    · simpa [iteratedDeriv_zero] using (hbound _ hx).1 hsmall
    · simpa [iteratedDeriv_zero] using (hbound _ hx).2 hlarge
  have hnormχ := qs_p1_idealValue_norm_le_one χ hsq a.1
  rw [norm_mul]
  have hT' := hT
  rw [hscale] at hT'
  have hmul := mul_le_mul hnormχ hT' (norm_nonneg _)
    (show 0 ≤ (1 : ℝ) by norm_num)
  have hterm : ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (K := K) 2 a.1 =
      (Ideal.absNorm a.1 : ℝ) ^ (-2 : ℝ) := by
    simp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm, hNa0,
      Real.rpow_neg (Nat.cast_nonneg _)]
  simpa [g, D, hterm, mul_assoc] using hmul

end ArtinPrimitiveRoots.A2

end
