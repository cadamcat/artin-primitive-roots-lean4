import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.HaarDilation
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.SchwartzAffine

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1

/-- The Fourier transform of an affine change of variables in the S-adic space. -/
theorem bruhat_fourier_affine
    {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (A : AddCharData F)
    (sd : S.SelfDualMeasure A) (μ : ∀ v : FinPlace F, Theta.LocHaar v)
    (f : S.BruhatSchwartz) (b : S.FS) (k : S.FSˣ) (y : S.FS) :
    S.fourier A sd.measure
      (fun x : S.FS => (f : S.FS → ℂ) ((b + x) * (k⁻¹ : S.FSˣ).val)) y =
      ((S.absS (k : S.FS) : ℝ) : ℂ) * S.e A (b * y) *
        S.fourier A sd.measure (f : S.FS → ℂ) ((k : S.FS) * y) := by
  letI : MeasurableSpace S.FS := borel S.FS
  letI : BorelSpace S.FS := ⟨rfl⟩
  letI : Measure.IsAddHaarMeasure sd.measure := sd.isHaar
  let δ : S.FS ≃ₜ S.FS :=
    { toFun := fun x => x * (k⁻¹ : S.FSˣ).val
      invFun := fun x => x * k.val
      left_inv := by intro x; simp [mul_assoc]
      right_inv := by intro x; simp [mul_assoc]
      continuous_toFun := continuous_id.mul continuous_const
      continuous_invFun := continuous_id.mul continuous_const }
  let g : S.FS → ℂ := fun u => (f : S.FS → ℂ) u * S.e A (-(u * (k.val * y)))
  have hnonneg : 0 ≤ S.absS (k : S.FS) := by
    unfold SData.absS
    apply mul_nonneg
    · exact Finset.prod_nonneg fun v _ => by rw [Theta.absFin_eq_norm]; positivity
    · exact Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _
  have hdilate : (∫ x, g (δ x) ∂sd.measure) =
      S.absS (k : S.FS) • ∫ u, g u ∂sd.measure := by
    calc
      _ = ∫ u, g u ∂Measure.map δ sd.measure :=
        (integral_map_equiv δ.toMeasurableEquiv g).symm
      _ = ∫ u, g u ∂(ENNReal.ofReal (S.absS (k : S.FS)) • sd.measure) := by
        rw [show Measure.map δ sd.measure = _ from selfDual_map_unit_inverse S A sd μ k]
      _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal hnonneg]
  have hphase (x : S.FS) :
      S.e A (-(x * y)) = S.e A (b * y) *
        S.e A (-(((b + x) * (k⁻¹ : S.FSˣ).val) * (k.val * y))) := by
    have hprod : ((b + x) * (k⁻¹ : S.FSˣ).val) * (k.val * y) = (b + x) * y := by
      simp [mul_assoc]
    rw [hprod, ← ArtinPrimitiveRoots.Proofs.a1_dual_p.e_add]
    congr 1
    ring
  unfold SData.fourier
  calc
    _ = ∫ x, S.e A (b * y) * g (δ (b + x)) ∂sd.measure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (f : S.FS → ℂ) ((b + x) * (k⁻¹ : S.FSˣ).val) * S.e A (-(x * y)) =
          S.e A (b * y) *
            ((f : S.FS → ℂ) ((b + x) * (k⁻¹ : S.FSˣ).val) *
              S.e A (-(((b + x) * (k⁻¹ : S.FSˣ).val) * (k.val * y))))
        rw [hphase]
        ring
    _ = S.e A (b * y) * ∫ x, g (δ (b + x)) ∂sd.measure :=
      integral_const_mul _ _
    _ = S.e A (b * y) * ∫ x, g (δ x) ∂sd.measure := by
      rw [integral_add_left_eq_self (fun x => g (δ x)) b]
    _ = S.e A (b * y) * (S.absS (k : S.FS) • ∫ u, g u ∂sd.measure) := by
      rw [hdilate]
    _ = _ := by
      rw [Complex.real_smul]
      dsimp only [g]
      ring

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
