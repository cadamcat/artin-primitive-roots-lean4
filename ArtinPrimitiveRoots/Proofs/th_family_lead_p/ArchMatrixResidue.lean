import ArtinPrimitiveRoots.Proofs.th_family_lead_p.ComponentMatrixResidue
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_representatives

set_option autoImplicit false
open NumberField Matrix
open scoped Classical MatrixGroups Matrix.Norms.Elementwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Pure archimedean insertion moves through a rational element by conjugation. -/
theorem thetaArchRP_conj_rat (P : CoverPackage D S H A)
    (c : InfinitePlace F → PGL2 ℂ) (γ : GL (Fin 2) F) :
    P.q (thetaArchRP P c) * P.tc.rat γ = P.tc.rat γ *
      P.q (thetaArchRP P (fun w =>
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
          c w * QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ))) := by
  have h : thetaArchRP P c * P.ratRP γ = P.ratRP γ *
      thetaArchRP P (fun w =>
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
          c w * QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ)) := by
    apply P.comp_ext
    · intro v
      simp only [map_mul, thetaArchRP_compF, one_mul, mul_one]
    · intro w
      simp only [map_mul, thetaArchRP_compC, P.compC_ratRP]
      group
  simpa only [map_mul, P.q_ratRP] using congrArg P.q h

/-- One smooth matrix formula describes the residue on each fixed finite-level coset. -/
theorem theta_residue_arch_matrix_representation
    [IsTotallyComplex F] {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) (g : P.tc.G) :
    ∃ f : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) → ℂ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f thetaMatrixRegion ∧
      ∀ m : InfinitePlace F → GL (Fin 2) ℂ,
        ∀ k ∈ levelSet P I.T0 C.hsub C.m,
          R.theta (P.q (thetaArchRP P (fun w => QuotientGroup.mk (m w))) * g * k) =
            f (fun w => (m w : Matrix (Fin 2) (Fin 2) ℂ)) := by
  obtain ⟨j, γ, x, y, u, k, hy, hu, hk, hg⟩ :=
    continuedEis_component_representatives C g
  obtain ⟨ru, hqu, huF, huC⟩ := hu
  choose κ hκ hκC using huC
  let cU : InfinitePlace F → PGL2 ℂ := fun w => QuotientGroup.mk (κ w)
  have huarch : P.q (thetaArchRP P cU) = u := by
    have hr : thetaArchRP P cU = ru := by
      apply P.comp_ext
      · intro v
        simp [huF]
      · intro w
        simp [cU, hκC]
    rw [hr, hqu]
  have huj : u * j = j * u := by
    obtain ⟨rj, hqj, hjC⟩ := C.finite_components j j.property
    rw [← huarch, ← hqj]
    exact thetaArchRP_commutes_finite P cU rj hjC
  let m0 : InfinitePlace F → GL (Fin 2) ℂ := fun w =>
    upperM ℂ (x w) * diagM ℂ
      (Units.mk0 (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')) * κ w
  have hm0 : (fun w => (QuotientGroup.mk (m0 w) : PGL2 ℂ)) =
      (fun w => QuotientGroup.mk (upperM ℂ (x w))) *
        (fun w => QuotientGroup.mk (diagM ℂ (Units.mk0
          (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')))) * cU := by
    funext w
    simp only [m0, Pi.mul_apply, QuotientGroup.mk_mul]
    rfl
  have hm0arch : P.q (thetaArchRP P (fun w => QuotientGroup.mk (m0 w))) =
      nInf P x * aInf P y * u := by
    rw [hm0]
    simp only [map_mul, thetaArchRP_nInf, thetaArchRP_aInf P y hy, huarch]
  have hgshape : g = P.tc.rat γ *
      (P.q (thetaArchRP P (fun w => QuotientGroup.mk (m0 w))) * j) * k := by
    rw [hg, hm0arch]
    simp only [mul_assoc, huj]
  let δ : InfinitePlace F → GL (Fin 2) ℂ :=
    fun w => Matrix.GeneralLinearGroup.map w.embedding γ
  let h : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) →
      (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) := fun M w =>
    (δ w)⁻¹ * M w * δ w * m0 w
  let f : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) → ℂ := fun M =>
    C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (thetaMatrixCoords (h M)))
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := by
    apply contDiff_pi.mpr
    intro w
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro q
    simp only [h, Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have hregion : Set.MapsTo h thetaMatrixRegion thetaMatrixRegion := by
    intro M hM w
    change ((↑((δ w)⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) * M w *
      (δ w : Matrix (Fin 2) (Fin 2) ℂ) * (m0 w : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ((δ w)⁻¹).det_ne_zero (hM w))
      (δ w).det_ne_zero) (m0 w).det_ne_zero
  refine ⟨f, (theta_residue_component_matrix_formula R j).2.comp
    hsmooth.contDiffOn hregion, ?_⟩
  intro m k' hk'
  let c : InfinitePlace F → PGL2 ℂ := fun w => QuotientGroup.mk (m w)
  let cγ : InfinitePlace F → PGL2 ℂ := fun w =>
    (QuotientGroup.mk (δ w) : PGL2 ℂ)⁻¹ * c w * QuotientGroup.mk (δ w)
  let mt : InfinitePlace F → GL (Fin 2) ℂ := fun w =>
    (δ w)⁻¹ * m w * δ w * m0 w
  have hmt : (fun w => (QuotientGroup.mk (mt w) : PGL2 ℂ)) =
      cγ * (fun w => QuotientGroup.mk (m0 w)) := by
    funext w
    simp only [mt, cγ, c, Pi.mul_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hmtarch : P.q (thetaArchRP P (fun w => QuotientGroup.mk (mt w))) =
      P.q (thetaArchRP P cγ) *
        P.q (thetaArchRP P (fun w => QuotientGroup.mk (m0 w))) := by
    rw [hmt, map_mul, map_mul]
  have hconj : P.q (thetaArchRP P c) * P.tc.rat γ =
      P.tc.rat γ * P.q (thetaArchRP P cγ) := thetaArchRP_conj_rat P c γ
  have hshape : P.q (thetaArchRP P c) * g = P.tc.rat γ *
      (P.q (thetaArchRP P (fun w => QuotientGroup.mk (mt w))) * j) * k := by
    rw [hgshape, hmtarch]
    calc
      _ = (P.q (thetaArchRP P c) * P.tc.rat γ) *
          (P.q (thetaArchRP P (fun w => QuotientGroup.mk (m0 w))) * j) * k := by group
      _ = _ := by rw [hconj]; group
  rw [R.theta_level _ k' hk']
  change R.theta (P.q (thetaArchRP P c) * g) = f _
  rw [hshape, R.theta_level _ k hk, R.theta_aut]
  rw [(theta_residue_component_matrix_formula R j).1 mt]
  rfl

end ArtinPrimitiveRoots.Proofs.majorant_sol
