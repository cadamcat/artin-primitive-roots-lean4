import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Endpoints
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open scoped NumberField Topology
open NumberField IsDedekindDomain Complex Filter

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- The endpoint order at zero is the number of archimedean places minus one. -/
theorem sharp_order_zero (K : Type*) [Field K] [NumberField K] :
    meromorphicOrderAt (dedekindZetaSharp K) 0 =
      ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℤ) := by
  obtain ⟨hinv, heq, _, hxi₀⟩ := sharp_continuation K
  have hunit {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf₀ : f 0 ≠ 0) :
      meromorphicOrderAt f 0 = (0 : ℤ) := by
    refine (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).mpr ⟨f, hf, hf₀, ?_⟩
    filter_upwards with z
    simp
  let R : ℂ → ℂ := fun s => (Gammaℝ s)⁻¹
  let C : ℂ → ℂ := fun s => (Gammaℂ s)⁻¹
  have hR : AnalyticAt ℂ R 0 := differentiable_Gammaℝ_inv.analyticAt 0
  have hC : AnalyticAt ℂ C 0 := differentiable_Gammaℂ_inv.analyticAt 0
  have hR₀ : R 0 = 0 := by simp [R, Gammaℝ_def]
  have hderiv : HasDerivAt R (2 : ℂ)⁻¹ 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hslope : slope R 0 = fun s : ℂ => (s * Gammaℝ s)⁻¹ := by
      funext s
      rw [slope_def_field, hR₀, sub_zero, sub_zero]
      dsimp [R]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [hslope]
    exact Gammaℝ_residue_zero.inv₀ two_ne_zero
  have hRord : meromorphicOrderAt R 0 = (1 : ℤ) := by
    rw [hR.meromorphicOrderAt_eq,
      hR.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hR₀
        (by rw [hderiv.deriv]; exact inv_ne_zero two_ne_zero)]
    simp
  have hR₁ : AnalyticAt ℂ (fun s : ℂ => R (s + 1)) 0 :=
    (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (1 : ℂ))).analyticAt 0
  have hR₁₀ : R (0 + 1) ≠ 0 := by simp [R]
  have hCfun : C = fun s : ℂ => R s * R (s + 1) := by
    funext s
    dsimp [C, R]
    rw [← Gammaℝ_mul_Gammaℝ_add_one s, mul_inv]
  have hCord : meromorphicOrderAt C 0 = (1 : ℤ) := by
    rw [hCfun]
    change meromorphicOrderAt (R * (fun s : ℂ => R (s + 1))) 0 = (1 : ℤ)
    rw [meromorphicOrderAt_mul hR.meromorphicAt hR₁.meromorphicAt, hRord, hunit hR₁ hR₁₀]
    simp
  let P : ℂ → ℂ := fun s => (absoluteDiscriminant K : ℂ) ^ (-s / 2)
  have hD : (absoluteDiscriminant K : ℂ) ≠ 0 := by
    unfold absoluteDiscriminant
    exact_mod_cast abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hPdiff : Differentiable ℂ P :=
    (differentiable_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hD)
  have hP : AnalyticAt ℂ P 0 := hPdiff.analyticAt 0
  have hP₀ : P 0 ≠ 0 := by simp [P]
  have hPord := hunit hP hP₀
  have hinvfun : invPrefactor K = fun s : ℂ =>
      P s * R s ^ InfinitePlace.nrRealPlaces K * C s ^ InfinitePlace.nrComplexPlaces K := rfl
  have hinvord : meromorphicOrderAt (invPrefactor K) 0 =
      (((InfinitePlace.nrRealPlaces K : ℤ) + (InfinitePlace.nrComplexPlaces K : ℤ) : ℤ) :
        WithTop ℤ) := by
    rw [hinvfun]
    change meromorphicOrderAt
      ((P * R ^ InfinitePlace.nrRealPlaces K) * C ^ InfinitePlace.nrComplexPlaces K) 0 = _
    rw [meromorphicOrderAt_mul (hP.mul (hR.pow _)).meromorphicAt (hC.pow _).meromorphicAt,
      meromorphicOrderAt_mul hP.meromorphicAt (hR.pow _).meromorphicAt,
      meromorphicOrderAt_pow hR.meromorphicAt,
      meromorphicOrderAt_pow hC.meromorphicAt, hPord, hRord, hCord]
    simp
  have hxi : AnalyticAt ℂ (dedekindXi K) 0 :=
    (Classical.choose_spec (dedekind_completed K)).1.analyticAt 0
  have hxiord := hunit hxi hxi₀
  have hsub : AnalyticAt ℂ (fun s : ℂ => s - 1) 0 :=
    analyticAt_id.sub analyticAt_const
  have hden : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) 0 := analyticAt_id.mul hsub
  have hdenord : meromorphicOrderAt (fun s : ℂ => s * (s - 1)) 0 = (1 : ℤ) := by
    change meromorphicOrderAt (id * (fun s : ℂ => s - 1)) 0 = (1 : ℤ)
    rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hsub.meromorphicAt,
      meromorphicOrderAt_id, hunit hsub (by norm_num)]
    simp
  have hfun : dedekindZetaSharp K = fun s : ℂ =>
      dedekindXi K s * invPrefactor K s / (s * (s - 1)) := funext heq
  have hsigned : meromorphicOrderAt (dedekindZetaSharp K) 0 =
      (((InfinitePlace.nrRealPlaces K : ℤ) + (InfinitePlace.nrComplexPlaces K : ℤ) - 1 : ℤ) :
        WithTop ℤ) := by
    rw [hfun]
    change meromorphicOrderAt
      ((dedekindXi K * invPrefactor K) / (fun s : ℂ => s * (s - 1))) 0 = _
    rw [meromorphicOrderAt_div (hxi.mul (hinv.analyticAt 0)).meromorphicAt hden.meromorphicAt,
      meromorphicOrderAt_mul hxi.meromorphicAt (hinv.analyticAt 0).meromorphicAt,
      hxiord, hinvord, hdenord]
    simp
  have hdegree : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hsignature := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hplaces : 1 ≤ InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by omega
  have hcast : ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : ℤ) =
      (InfinitePlace.nrRealPlaces K : ℤ) + (InfinitePlace.nrComplexPlaces K : ℤ) - 1 := by
    rw [Nat.cast_sub hplaces, Nat.cast_add, Nat.cast_one]
  rw [hsigned, hcast]

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
