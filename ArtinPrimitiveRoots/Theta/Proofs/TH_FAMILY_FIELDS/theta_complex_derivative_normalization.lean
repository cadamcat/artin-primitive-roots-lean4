import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_normalizationScalar_ne_zero
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_complex_derivative_tensor

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Normalize the differentiated common-section coefficient to the exact T5 indicator and Bessel expression with cS = 4π.
Guide: sol-thin-thglobal/PROOFS.md:1180–1190.
Uses theta_complex_derivative_tensor, theta_normalizationScalar_ne_zero, jacquetC_derivative and CoverPackage.aS_components. -/
theorem theta_complex_derivative_normalization {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛) (y : S.FSˣ) :
    thetaFamilyW B L (P.tc.aS y) =
      (if (y : S.FS).1 ∈ thetaCommonU B then (1 : ℂ) else 0) *
      ∏ w : InfinitePlace F, (Complex.normSq ((y : S.FS).2 w) : ℂ) *
        omegaAng (L.m w) ((y : S.FS).2 w) *
        (besselK (1 / 3) ((4 * Real.pi) * ‖(y : S.FS).2 w‖) : ℂ) := by
  classical
  obtain ⟨r, hrq, hrF, hrC⟩ := P.aS_components y
  have hr : ∀ v, v ∉ S.Sf → P.compF v r = 1 := by
    intro v hv
    rw [hrF v]
    simp [hv]
  have hTensor := theta_complex_derivative_tensor B Q L hL r hr
  rw [hrq] at hTensor
  let c : InfinitePlace F → ℂ := fun _ =>
    (-(4 * Real.pi * Complex.I) * besselConst : ℂ)
  let a : InfinitePlace F → ℂ := fun w =>
    (Complex.normSq ((y : S.FS).2 w) : ℂ) * omegaAng (L.m w) ((y : S.FS).2 w) *
      (besselK (1 / 3) ((4 * Real.pi) * ‖(y : S.FS).2 w‖) : ℂ)
  have hJacC (w : InfinitePlace F) :
      jacquetC (rtr (P.compC w r) (derivVecC (L.m w) (sphC (1 / 6)))) = c w * a w := by
    rw [hrC w]
    change jacquetC (rtr (aC (S.compC w y))
      (derivVecC (L.m w) (sphC (1 / 6)))) = _
    have hcompC : ((S.compC w y : ℂˣ) : ℂ) = ((y : S.FS).2 w) := by
      rfl
    simpa [c, a, hcompC, mul_assoc] using
      (jacquetC_derivative (L.m w) (L.hm w) (S.compC w y))
  have hJac :
      (∏ w : InfinitePlace F,
        jacquetC (rtr (P.compC w r) (derivVecC (L.m w) (sphC (1 / 6))))) =
        (∏ w, c w) * ∏ w, a w := by
    simp_rw [hJacC]
    rw [Finset.prod_mul_distrib]
  let J : ∀ v : S.Sf, (N.G.T v.1).V := fun v =>
    jacquet (P.loc v.1) A (N.μ v.1)
      (rtr (P.compF v.1 r) ((B.Fam.sec (1 / 6)).f v.1))
  have hcompFin (v : S.Sf) :
      ((S.compU v y : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) =
        (y : S.FS).1 v := rfl
  have hJ (v : S.Sf) : J v =
      (B.Uv v).indicator (fun _ => N.x v) (S.compU v y : v.1.adicCompletion F) := by
    dsimp [J]
    rw [hrF v]
    simpa [v.2] using B.jacquet_indicator v (S.compU v y)
  have hLambda : N.Λ J =
      if (y : S.FS).1 ∈ thetaCommonU B then N.Λ N.x else 0 := by
    by_cases hU : (y : S.FS).1 ∈ thetaCommonU B
    · have hJx : J = N.x := by
        funext v
        rw [hJ v]
        have hvU : (y : S.FS).1 v ∈ B.Uv v := by
          simpa [thetaCommonU] using hU v
        have hvU' : (S.compU v y : v.1.adicCompletion F) ∈ B.Uv v := by
          rw [hcompFin]
          exact hvU
        simp [hvU']
      simp [hU, hJx]
    · have hex : ∃ v : S.Sf, (y : S.FS).1 v ∉ B.Uv v := by
        by_contra h
        apply hU
        intro v
        by_contra hv
        exact h ⟨v, hv⟩
      obtain ⟨v, hv⟩ := hex
      have hz : J v = 0 := by
        rw [hJ v]
        have hv' : (S.compU v y : v.1.adicCompletion F) ∉ B.Uv v := by
          rw [hcompFin]
          exact hv
        simp [hv']
      rw [N.Λ.map_coord_zero v hz]
      simp [hU]
  rw [hTensor, hLambda, hJac]
  by_cases hU : (y : S.FS).1 ∈ thetaCommonU B
  · simp only [if_pos hU, one_mul]
    have hscalar : thetaNormalizationScalar N = N.Λ N.x * ∏ w, c w := rfl
    have hscalarne := theta_normalizationScalar_ne_zero N
    calc
      (thetaNormalizationScalar N)⁻¹ * N.Λ N.x * ((∏ w, c w) * ∏ w, a w) =
          ((thetaNormalizationScalar N)⁻¹ * (N.Λ N.x * ∏ w, c w)) * ∏ w, a w := by
            ring
      _ = ((thetaNormalizationScalar N)⁻¹ * thetaNormalizationScalar N) * ∏ w, a w := by
            rw [← hscalar]
      _ = ∏ w, a w := by simp [hscalarne]
  · simp [hU]
end ArtinPrimitiveRoots.A1.Theta
