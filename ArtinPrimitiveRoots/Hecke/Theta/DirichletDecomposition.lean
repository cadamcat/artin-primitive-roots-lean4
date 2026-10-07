import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Hecke.Theta.IdealNormSummability

/-!
# Reindex the ray-class Dirichlet series by ideals

The first input to the theta construction is the ideal-indexed version of `LSeriesRay`. The
summability hypothesis below is explicit: the continuation argument will discharge it from the
usual ideal-norm estimate on `Re s > 1`.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

open ClassFieldTheory
open Classical

local instance rayNormFiberFinite (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).to_subtype

local instance rayNormFiberFintype (n : ℕ) :
    Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := Fintype.ofFinite _

local instance rayGroupFintype (m : RayClassModulus K) :
    Fintype (RayClassGroup m) := Fintype.ofFinite _

/-- The ideal term grouped by absolute norm, with the norm-zero ideal contributing zero. -/
def rayIdealDirichletTerm {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (s : ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if Ideal.absNorm I = 0 then 0 else
    charValue η I / (Ideal.absNorm I : ℂ) ^ s

/-- The partial ideal term in a fixed ray class, with non-coprime ideals omitted. -/
def rayClassIdealDirichletTerm {m : RayClassModulus K}
    (C : RayClassGroup m) (s : ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if h : IsCoprimeTo m I then
    if rayClass m I h = C then rayIdealDirichletTerm (1 : RayClassGroup m →* ℂˣ) s I else 0
  else 0

/-- The partial zeta series of a single ray class. -/
def rayClassPartialZeta {m : RayClassModulus K}
    (C : RayClassGroup m) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 K), rayClassIdealDirichletTerm C s I

private theorem rayIdealDirichletTerm_eq_class_sum {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (s : ℂ) (I : Ideal (𝓞 K)) :
    rayIdealDirichletTerm η s I =
      ∑ C : RayClassGroup m, (η C : ℂ) * rayClassIdealDirichletTerm C s I := by
  classical
  by_cases h : IsCoprimeTo m I
  · have hN : Ideal.absNorm I ≠ 0 := by
      intro hzero
      exact h.1 (Ideal.absNorm_eq_zero_iff.mp hzero)
    simp [rayIdealDirichletTerm, rayClassIdealDirichletTerm, charValue, h, hN, div_eq_mul_inv]
  · simp [rayIdealDirichletTerm, rayClassIdealDirichletTerm, charValue, h]

private theorem coeff_eq_normFiber_sum {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (n : ℕ) :
    coeff η n = ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, charValue η I := by
  classical
  let hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
  let S := hfin.toFinset
  let e : {I : Ideal (𝓞 K) // I ∈ S} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    Equiv.subtypeEquivRight (fun I => by simp [S])
  calc
    coeff η n = ∑ I ∈ S, charValue η I := by rfl
    _ = ∑ I ∈ S.attach, charValue η I := (Finset.sum_attach S _).symm
    _ = ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, charValue η I := by
      simpa [e] using (Equiv.sum_comp e (fun I => charValue η I))

private theorem rayIdealDirichletTerm_normFiber_sum {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (s : ℂ) (n : ℕ) :
    ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, rayIdealDirichletTerm η s I
      = LSeries.term (coeff η) s n := by
  classical
  rw [tsum_fintype]
  by_cases hn : n = 0
  · subst n
    rw [LSeries.term_zero]
    apply Finset.sum_eq_zero
    intro I _
    simp [rayIdealDirichletTerm, I.property]
  · rw [LSeries.term_of_ne_zero hn]
    have hnorm (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) :
        Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 := by
      intro h
      exact hn (I.property.symm.trans h)
    have hterm (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) :
      rayIdealDirichletTerm η s I = charValue η I / (n : ℂ) ^ s := by
      unfold rayIdealDirichletTerm
      rw [ite_eq_right (hnorm I)]
      rw [I.property]
    simp_rw [hterm]
    rw [← Finset.sum_div]
    rw [coeff_eq_normFiber_sum]

/-- For any `s`, an absolutely summable ideal-indexed series with the ray coefficients is exactly
`LSeriesRay η s`. This isolates the arithmetic reindexing from the analytic summability estimate. -/
theorem LSeriesRay_eq_tsum_rayIdealDirichletTerm {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) (s : ℂ)
    (hsum : Summable (fun I : Ideal (𝓞 K) => rayIdealDirichletTerm η s I)) :
    LSeriesRay η s = ∑' I : Ideal (𝓞 K), rayIdealDirichletTerm η s I := by
  classical
  let fiber (n : ℕ) := {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  let F : (Σ n : ℕ, fiber n) → ℂ := fun p => rayIdealDirichletTerm η s p.2
  let e : (Σ n : ℕ, fiber n) ≃ Ideal (𝓞 K) := Equiv.sigmaFiberEquiv Ideal.absNorm
  have hSigma : Summable F := by
    apply (Equiv.summable_iff e).2 hsum
  have hdecomp := hSigma.tsum_sigma' (fun n => Summable.of_finite)
  calc
    LSeriesRay η s = ∑' n : ℕ, LSeries.term (coeff η) s n := rfl
    _ = ∑' n : ℕ, ∑' I : fiber n, F ⟨n, I⟩ := by
      apply tsum_congr
      intro n
      exact (rayIdealDirichletTerm_normFiber_sum η s n).symm
    _ = ∑' p : (Σ n : ℕ, fiber n), F p := hdecomp.symm
    _ = ∑' I : Ideal (𝓞 K), rayIdealDirichletTerm η s I := by
      exact Equiv.tsum_eq e (fun I => rayIdealDirichletTerm η s I)

/-- The ideal-indexed ray series is absolutely summable on its half-plane of convergence. -/
theorem summable_rayIdealDirichletTerm {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) => rayIdealDirichletTerm η s I) := by
  let σ := s.re
  have hσ : 1 < σ := hs
  have hmajor : Summable (fun I : Ideal (𝓞 K) => idealNormRpowTerm σ I) :=
    summable_idealNormRpow hσ
  apply hmajor.of_norm_bounded
  intro I
  by_cases hI : Ideal.absNorm I = 0
  · simp [rayIdealDirichletTerm, idealNormRpowTerm, hI]
  · have hN : 0 < (Ideal.absNorm I : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hI)
    have hpow : 0 < (Ideal.absNorm I : ℝ) ^ σ := Real.rpow_pos_of_pos hN σ
    rw [rayIdealDirichletTerm, idealNormRpowTerm,
      ite_eq_right (fun h => hI h), ite_eq_right (fun h => hI h)]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hI),
      Real.rpow_neg hN.le]
    calc
      ‖charValue η I‖ / (Ideal.absNorm I : ℝ) ^ σ =
          ‖charValue η I‖ * ((Ideal.absNorm I : ℝ) ^ σ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 1 * ((Ideal.absNorm I : ℝ) ^ σ)⁻¹ :=
          mul_le_mul_of_nonneg_right (norm_charValue_le_one η I) (inv_nonneg.mpr hpow.le)
      _ = ((Ideal.absNorm I : ℝ) ^ σ)⁻¹ := one_mul _

/-- The unconditionally named reindexing result, now with the absolute-convergence hypothesis
discharged for `Re s > 1`. -/
theorem LSeriesRay_eq_tsum_rayIdealDirichletTerm_of_re_gt {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesRay η s = ∑' I : Ideal (𝓞 K), rayIdealDirichletTerm η s I :=
  LSeriesRay_eq_tsum_rayIdealDirichletTerm η s (summable_rayIdealDirichletTerm η hs)

/-- The nonzero ideal series in one ray class is dominated by the series with trivial character. -/
private theorem summable_rayClassIdealDirichletTerm {m : RayClassModulus K}
    (C : RayClassGroup m) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) => rayClassIdealDirichletTerm C s I) := by
  have hbase := summable_rayIdealDirichletTerm
    (1 : RayClassGroup m →* ℂˣ) hs
  apply hbase.norm.of_norm_bounded
  intro I
  simp only [rayClassIdealDirichletTerm]
  split_ifs <;> simp

/-- Decomposition of the ray-class L-series into partial zeta series. -/
theorem LSeriesRay_eq_rayClassPartialZeta_sum {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesRay η s =
      ∑ C : RayClassGroup m, (η C : ℂ) * rayClassPartialZeta C s := by
  classical
  calc
    LSeriesRay η s = ∑' I : Ideal (𝓞 K), rayIdealDirichletTerm η s I :=
      LSeriesRay_eq_tsum_rayIdealDirichletTerm_of_re_gt η hs
    _ = ∑' I : Ideal (𝓞 K), ∑ C : RayClassGroup m,
          (η C : ℂ) * rayClassIdealDirichletTerm C s I := by
      apply tsum_congr
      intro I
      exact rayIdealDirichletTerm_eq_class_sum η s I
    _ = ∑ C : RayClassGroup m,
          ∑' I : Ideal (𝓞 K), (η C : ℂ) * rayClassIdealDirichletTerm C s I := by
      rw [Summable.tsum_finsetSum (fun C _ =>
        (summable_rayClassIdealDirichletTerm C hs).mul_left _)]
    _ = ∑ C : RayClassGroup m, (η C : ℂ) * rayClassPartialZeta C s := by
      apply Finset.sum_congr rfl
      intro C _
      rw [rayClassPartialZeta, ← tsum_mul_left]

/-- H1 reduces to entire continuations of the individual ray-class partial zeta functions. -/
theorem LSeriesRay_entire_of_rayClassPartialZeta_entire {m : RayClassModulus K}
    (η : RayClassGroup m →* ℂˣ)
    (hC : ∀ C : RayClassGroup m, ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
        ∀ s : ℂ, 1 < s.re → F s = rayClassPartialZeta C s) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay η s := by
  classical
  choose F hF hFeq using hC
  refine ⟨fun s => ∑ C : RayClassGroup m, (η C : ℂ) * F C s, ?_, fun s hs => ?_⟩
  · simpa only [Finset.sum_apply] using
      (Differentiable.fun_sum (u := Finset.univ)
        (fun C _ => (hF C).const_mul (η C : ℂ)))
  · rw [LSeriesRay_eq_rayClassPartialZeta_sum η hs]
    apply Finset.sum_congr rfl
    intro C _
    rw [hFeq C s hs]

end ArtinPrimitiveRoots.Hecke

end
