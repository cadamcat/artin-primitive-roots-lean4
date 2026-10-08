import ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs

/-!
# QS-ANALYTIC, RN-S: vertical-strip bounds for the completed ray-character function

`Hecke.hkCompleted ψ` is a constant times `(N m)^{s/2}` times the completed function `Λ(s/2)` of
H1's character-weighted theta pair.  For `ψ ≠ 1` both constant terms of that pair vanish
(orthogonality), so it is a strong FE pair and `Λ` is the Mellin transform of a function with
rapid decay at `0` and `∞`; this bounds `Λ` on every vertical strip.
-/

set_option autoImplicit false

open NumberField ClassFieldTheory MeasureTheory
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2

/-- RN-S1: the completed function of a strong FE pair is bounded on every vertical strip. -/
theorem qsa_strongFEPair_strip_bound (P : WeakFEPair ℂ) (hP : IsStrongFEPair P) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖P.Λ s‖ ≤ C := by
  have ha := (hP.hasMellin (a : ℂ)).1
  have hb := (hP.hasMellin (b : ℂ)).1
  let g : ℝ → ℝ := fun t =>
    ‖(t : ℂ) ^ ((a : ℂ) - 1) • P.f t‖ + ‖(t : ℂ) ^ ((b : ℂ) - 1) • P.f t‖
  have hg : IntegrableOn g (Set.Ioi 0) := ha.norm.add hb.norm
  refine ⟨∫ t in Set.Ioi 0, g t, fun s hsa hsb => ?_⟩
  rw [← (hP.hasMellin s).2]
  unfold mellin
  refine (norm_integral_le_integral_norm _).trans ?_
  refine MeasureTheory.setIntegral_mono_on (hP.hasMellin s).1.norm hg measurableSet_Ioi ?_
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  simp only [g, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re,
    Complex.ofReal_re, Complex.one_re]
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rcases le_total t 1 with h1 | h1
  · have : t ^ (s.re - 1) ≤ t ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 h1 (by linarith)
    linarith [Real.rpow_nonneg ht0.le (b - 1)]
  · have : t ^ (s.re - 1) ≤ t ^ (b - 1) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    linarith [Real.rpow_nonneg ht0.le (a - 1)]

/-- RN-S2: for a nontrivial ray character of a totally complex field, `hkCompleted ψ` is
bounded on every vertical strip. -/
theorem qsa_hkCompleted_strip_bound {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    {m : RayClassModulus K} (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Hecke.hkCompleted ψ s‖ ≤ C := by
  classical
  let _ : Fintype (RayClassGroup m) := Hecke.rayFEGroupFintype m
  set R := Hecke.hkRayRepresentatives m
  have hstrong : IsStrongFEPair (Hecke.rayCharacterFEPair R ψ) :=
    { hf₀ := Hecke.Theta.finiteFEPair_f₀_eq_zero_of_nontrivialCharacter ψ hψ
        (fun C => Hecke.rayFEPair m (R.ideal C) (R.coprime C)) (Hecke.rayPrimalConstant m : ℂ)
        (fun _ => rfl) (1 / 2) (by norm_num) (fun _ => rfl)
      hg₀ := Hecke.Theta.finiteFEPair_g₀_eq_zero_of_nontrivialCharacter ψ hψ
        (fun C => Hecke.rayFEPair m (R.ideal C) (R.coprime C)) (Hecke.rayDualConstant m : ℂ)
        (fun _ => by simp [Hecke.rayFEPair]) (1 / 2) (by norm_num) (fun _ => rfl) }
  obtain ⟨C₁, hC₁⟩ := qsa_strongFEPair_strip_bound _ hstrong (a / 2) (b / 2)
  set c : ℂ := (2 : ℂ) ^ InfinitePlace.nrComplexPlaces K /
    ((((DedekindResidue.heckeJacobian K : NNReal) : ℝ) : ℂ))
  have hN : (0 : ℕ) < Hecke.modulusNorm m := Dictionary.HKDICTRay.modulusNorm_pos m
  refine ⟨‖c‖ * ((Hecke.modulusNorm m : ℝ) ^ (b / 2)) * max C₁ 0, fun s hsa hsb => ?_⟩
  have hΛ : ‖(Hecke.rayCharacterFEPair R ψ).Λ (s / 2)‖ ≤ max C₁ 0 :=
    (hC₁ (s / 2) (by simp; linarith) (by simp; linarith)).trans (le_max_left _ _)
  have hpow : ‖((Hecke.modulusNorm m : ℕ) : ℂ) ^ (s / 2)‖ ≤
      (Hecke.modulusNorm m : ℝ) ^ (b / 2) := by
    rw [Complex.norm_natCast_cpow_of_pos hN]
    apply Real.rpow_le_rpow_of_exponent_le
    · exact Nat.one_le_cast.mpr hN
    · simp; linarith
  change ‖c * ((Hecke.modulusNorm m : ℕ) : ℂ) ^ (s / 2) *
    (Hecke.rayCharacterFEPair (Hecke.hkRayRepresentatives m) ψ).Λ (s / 2)‖ ≤ _
  rw [norm_mul, norm_mul]
  gcongr

end ArtinPrimitiveRoots.A2
