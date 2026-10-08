import ArtinPrimitiveRoots.Proofs.th_res_whit_b.SectionCore
import ArtinPrimitiveRoots.Proofs.th_res_whit_b.ComplexArch
import ArtinPrimitiveRoots.Proofs.th_res_whit_b.ComplexBesselPos
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_rtr
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_adapted_domain_exists
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.torusCoeff_analytic
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.regularized_residue_eval
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

def complexArchFactor (x : P.RP) (s : ℂ) : ℂ :=
  ∏ w, jacquetC (rtr (P.compC w x) (sphC s))

theorem complexArchFactor_analytic (x : P.RP) :
    AnalyticOnNhd ℂ (complexArchFactor x) {s | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  rw [Complex.analyticOnNhd_iff_differentiableOn hopen]
  classical
  unfold complexArchFactor
  apply DifferentiableOn.fun_finsetProd
  intro w hw
  exact (jacquetC_spherical_analytic (P.compC w x)).differentiableOn

private theorem familyFourierHyp (Fam : AnalyticFamily P G μ) :
    FourierFamilyHyp μ Fam.sec Fam.T0 :=
  ⟨Fam.T0_eq, Fam.fC_sph, Fam.f_analytic, Fam.M_analytic, Fam.J_analytic, Fam.level⟩

private def continuedFourierData {Fam : AnalyticFamily P G μ}
    (C : ContinuedEis Fam) : FourierResidueData Fam.sec where
  ε := C.ε
  ε_pos := C.ε_pos
  E := C.E
  E_series := C.E_series
  E_analytic := C.E_analytic
  theta := C.theta
  laurent := C.laurent
  laurent_torus := C.laurent_torus

theorem analyticFamily_translate_S (Base Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = Base.T0)
    (hOff : ∀ s v, v ∉ S.Sf → (Fam.sec s).f v = (Base.sec s).f v)
    (x : P.RP) :
    ∃ Fam' : AnalyticFamily P G μ, Fam'.T0 = Base.T0 ∧
      (∀ s v, v ∉ S.Sf → (Fam'.sec s).f v = (Base.sec s).f v) ∧
      ∀ s (v : S.Sf), (Fam'.sec s).f v.1 = rtr (P.compF v.1 x) ((Fam.sec s).f v.1) := by
  classical
  have hrec : ∀ t : Finset S.Sf, ∃ Fam' : AnalyticFamily P G μ,
      Fam'.T0 = Fam.T0 ∧
      (∀ s v, v ∉ S.Sf → (Fam'.sec s).f v = (Base.sec s).f v) ∧
      (∀ s (v : S.Sf), v ∈ t →
        (Fam'.sec s).f v.1 = rtr (P.compF v.1 x) ((Fam.sec s).f v.1)) ∧
      (∀ s (v : S.Sf), v ∉ t → (Fam'.sec s).f v.1 = (Fam.sec s).f v.1) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨Fam, rfl, hOff, ?_⟩
        constructor
        · intro s v hv
          simp at hv
        · intro s v hv
          rfl
    | @insert v t hvt ih =>
        obtain ⟨B, hBT, hBOff, hBCoord, hBRest⟩ := ih
        have hvT : v.1 ∈ B.T0 := by
          rw [hBT, hT, ← Base.T0_eq (1 / 6)]
          exact (Base.sec (1 / 6)).sub v.2
        obtain ⟨Fam', hFamT, hFamOff, hFamAt⟩ :=
          analyticFamily_rtr B v.1 hvT (P.compF v.1 x)
        have hT' : Fam'.T0 = Fam.T0 := hFamT.trans hBT
        have hOff' : ∀ s w, w ∉ S.Sf →
            (Fam'.sec s).f w = (Base.sec s).f w := by
          intro s w hw
          have hwv : w ≠ v.1 := by
            intro heq
            exact hw (heq ▸ v.2)
          calc
            (Fam'.sec s).f w = (B.sec s).f w := hFamOff s w hwv
            _ = (Base.sec s).f w := hBOff s w hw
        have hCoord' : ∀ s (w : S.Sf), w ∈ insert v t →
            (Fam'.sec s).f w.1 = rtr (P.compF w.1 x) ((Fam.sec s).f w.1) := by
          intro s w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with hEq | hw
          · rw [hEq]
            calc
              (Fam'.sec s).f v.1 = rtr (P.compF v.1 x) ((B.sec s).f v.1) := hFamAt s
              _ = rtr (P.compF v.1 x) ((Fam.sec s).f v.1) := by
                rw [hBRest s v hvt]
          · have hwv : w.1 ≠ v.1 := by
              intro heq
              have hEq : w = v := Subtype.ext heq
              exact hvt (hEq ▸ hw)
            calc
              (Fam'.sec s).f w.1 = (B.sec s).f w.1 := hFamOff s w.1 hwv
              _ = rtr (P.compF w.1 x) ((Fam.sec s).f w.1) := hBCoord s w hw
        have hRest' : ∀ s (w : S.Sf), w ∉ insert v t →
            (Fam'.sec s).f w.1 = (Fam.sec s).f w.1 := by
          intro s w hw
          simp only [Finset.mem_insert, not_or] at hw
          have hwv : w.1 ≠ v.1 := by
            intro heq
            have hEq : w = v := Subtype.ext heq
            exact hw.1 hEq
          calc
            (Fam'.sec s).f w.1 = (B.sec s).f w.1 := hFamOff s w.1 hwv
            _ = (Fam.sec s).f w.1 := hBRest s w hw.2
        exact ⟨Fam', hT', hOff', hCoord', hRest'⟩
  obtain ⟨Fam', hT', hOff', hCoord', hRest'⟩ := hrec Finset.univ
  refine ⟨Fam', hT'.trans hT, hOff', ?_⟩
  intro s v
  exact hCoord' s v (by simp)

private theorem contDomain_mono (η η' : ℝ) (hη : η ≤ η') :
    ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η ⊆
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η' := by
  intro z hz
  simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hz ⊢
  rcases hz with hz | hz
  · rcases hz with hstrip | hconv
    · exact Or.inl (Or.inl hstrip)
    · exact Or.inl (Or.inr hconv)
  · exact Or.inr ⟨Metric.ball_subset_ball hη hz.1, hz.2⟩

private theorem convBall_posRe {s : ℂ}
    (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) : (1 / 2 : ℝ) < s.re := by
  have hn : ‖s - (5 / 2 : ℂ)‖ < (1 / 2 : ℝ) := by
    simpa [Complex.dist_eq] using Metric.mem_ball.mp hs
  have habs : |s.re - 5 / 2| < (1 / 2 : ℝ) := by
    calc
      |s.re - 5 / 2| = |(s - (5 / 2 : ℂ)).re| := by simp
      _ ≤ ‖s - (5 / 2 : ℂ)‖ := Complex.abs_re_le_norm _
      _ < (1 / 2 : ℝ) := hn
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  linarith

private theorem residueBall_posRe {η : ℝ} (hη : η ≤ (1 / 6 : ℝ)) {z : ℂ}
    (hz : z ∈ Metric.ball (1 / 6 : ℂ) η) : 0 < z.re := by
  have hn : ‖z - (1 / 6 : ℂ)‖ < η := by
    simpa [Complex.dist_eq] using Metric.mem_ball.mp hz
  have habs : |z.re - 1 / 6| < η := by
    calc
      |z.re - 1 / 6| = |(z - (1 / 6 : ℂ)).re| := by simp
      _ ≤ ‖z - (1 / 6 : ℂ)‖ := Complex.abs_re_le_norm _
      _ < η := hn
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  have hnonneg : 0 ≤ (1 / 6 : ℝ) - η := by linarith [hη]
  exact lt_of_le_of_lt hnonneg (by linarith)

private theorem contDomain_posRe (η : ℝ) (hη : η ≤ (1 / 6 : ℝ)) :
    ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η ⊆ {s : ℂ | 0 < s.re} := by
  intro z hz
  simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hz
  rcases hz with hz | hz
  · rcases hz with hstrip | hconv
    · exact hstrip.1
    · have h := convBall_posRe hconv
      exact lt_trans (by norm_num) h
  · have hball : z ∈ Metric.ball (1 / 6 : ℂ) η := by simpa using hz.1
    exact residueBall_posRe hη hball

private theorem ratDiagOne : P.tc.rat (diagGL (1 : Fˣ)) = 1 := by
  have hdiag : diagGL (1 : Fˣ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL]
  rw [hdiag]
  exact P.tc.rat.map_one

private theorem whittakerE_arch_cross (Base Fam₁ Fam₂ : AnalyticFamily P G μ)
    (x x0 xStar : P.RP)
    (hOff₁ : ∀ s v, v ∉ S.Sf → (Fam₁.sec s).f v = (Base.sec s).f v)
    (hOff₂ : ∀ s v, v ∉ S.Sf → (Fam₂.sec s).f v = (Base.sec s).f v)
    (hXOff : ∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0)
    (hStarOff : ∀ v, v ∉ S.Sf → P.compF v xStar = P.compF v x0)
    (hCoord : ∀ s (v : S.Sf),
      rtr (P.compF v.1 xStar) ((Fam₂.sec s).f v.1) =
        rtr (P.compF v.1 x) ((Fam₁.sec s).f v.1))
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    whittakerE P G μ (Fam₁.sec s) (P.q x) * complexArchFactor xStar s =
      whittakerE P G μ (Fam₂.sec s) (P.q xStar) * complexArchFactor x s := by
  obtain ⟨Λ, hΛ⟩ := whittakerE_multilinear P G μ (Base.sec s) x0 hs
  have hC₁ : (Fam₁.sec s).fC = (Base.sec s).fC := by
    funext w
    rw [Fam₁.fC_sph, Base.fC_sph]
  have hC₂ : (Fam₂.sec s).fC = (Base.sec s).fC := by
    funext w
    rw [Fam₂.fC_sph, Base.fC_sph]
  have hW₁ := hΛ (Fam₁.sec s) x (fun v hv => hOff₁ s v hv) hC₁
    (fun v hv => hXOff v hv)
  have hW₂ := hΛ (Fam₂.sec s) xStar (fun v hv => hOff₂ s v hv) hC₂
    (fun v hv => hStarOff v hv)
  have hJac :
      (fun v : S.Sf => jacquet (P.loc v.1) A (μ v.1)
        (rtr (P.compF v.1 x) ((Fam₁.sec s).f v.1))) =
      (fun v : S.Sf => jacquet (P.loc v.1) A (μ v.1)
        (rtr (P.compF v.1 xStar) ((Fam₂.sec s).f v.1))) := by
    funext v
    exact congrArg (jacquet (P.loc v.1) A (μ v.1)) (hCoord s v).symm
  rw [hW₁, hW₂, hJac]
  simp_rw [Fam₁.fC_sph, Fam₂.fC_sph]
  dsimp [complexArchFactor]
  ring

theorem thetaWhit_arch_cross (Base Fam₁ Fam₂ : AnalyticFamily P G μ)
    (C₁ : ContinuedEis Fam₁) (C₂ : ContinuedEis Fam₂)
    (x x0 xStar : P.RP) (laws : ThetaResidueLaws P G μ)
    (hOff₁ : ∀ s v, v ∉ S.Sf → (Fam₁.sec s).f v = (Base.sec s).f v)
    (hOff₂ : ∀ s v, v ∉ S.Sf → (Fam₂.sec s).f v = (Base.sec s).f v)
    (hXOff : ∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0)
    (hStarOff : ∀ v, v ∉ S.Sf → P.compF v xStar = P.compF v x0)
    (hCoord : ∀ s (v : S.Sf),
      rtr (P.compF v.1 xStar) ((Fam₂.sec s).f v.1) =
        rtr (P.compF v.1 x) ((Fam₁.sec s).f v.1)) :
    thetaWhit C₁ (P.q x) * complexArchFactor xStar (1 / 6) =
      thetaWhit C₂ (P.q xStar) * complexArchFactor x (1 / 6) := by
  classical
  let FH₁ := familyFourierHyp Fam₁
  let FH₂ := familyFourierHyp Fam₂
  let R₁ := continuedFourierData C₁
  let R₂ := continuedFourierData C₂
  obtain ⟨𝔞₁, Pd₁, hD₁, hm₁⟩ := theta_adapted_domain_exists FH₁ (P.q x)
  obtain ⟨𝔞₂, Pd₂, hD₂, hm₂⟩ := theta_adapted_domain_exists FH₂ (P.q xStar)
  have hθ₁ : thetaWhit C₁ (P.q x) = torusCoeff P C₁.theta (P.q x) Pd₁ (1 : F) := by
    have h := (laws.fourierCoeff Fam₁ C₁ (P.q x) 𝔞₁ hD₁.1 hD₁.2.1 Pd₁
      hD₁.2.2.1 hD₁.2.2.2.1 (1 : Fˣ) hD₁.2.2.2.2).symm
    rw [ratDiagOne] at h
    simpa using h
  have hθ₂ : thetaWhit C₂ (P.q xStar) =
      torusCoeff P C₂.theta (P.q xStar) Pd₂ (1 : F) := by
    have h := (laws.fourierCoeff Fam₂ C₂ (P.q xStar) 𝔞₂ hD₂.1 hD₂.2.1 Pd₂
      hD₂.2.2.1 hD₂.2.2.2.1 (1 : Fˣ) hD₂.2.2.2.2).symm
    rw [ratDiagOne] at h
    simpa using h
  let coeff₁ : ℂ → ℂ := fun s => torusCoeff P (C₁.E s) (P.q x) Pd₁ (1 : F)
  let coeff₂ : ℂ → ℂ := fun s => torusCoeff P (C₂.E s) (P.q xStar) Pd₂ (1 : F)
  have hRawCross : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      coeff₁ s * complexArchFactor xStar s = coeff₂ s * complexArchFactor x s := by
    intro s hs
    have hsRe := convBall_posRe hs
    have hW := whittakerE_arch_cross Base Fam₁ Fam₂ x x0 xStar hOff₁ hOff₂
      hXOff hStarOff hCoord s hsRe
    have hFix₁ : ∀ u, ∀ ξ ∈ (𝔞₁ : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (Fam₁.sec u).f (Fam₁.sec u).fC
          (h * ((P.q x)⁻¹ * nFin P ξ * P.q x)) =
          scalarOf P G (Fam₁.sec u).f (Fam₁.sec u).fC h := by
      intro u ξ hξ h
      exact hD₁.2.1 u ξ hξ h
    have hFix₂ : ∀ u, ∀ ξ ∈ (𝔞₂ : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G (Fam₂.sec u).f (Fam₂.sec u).fC
          (h * ((P.q xStar)⁻¹ * nFin P ξ * P.q xStar)) =
          scalarOf P G (Fam₂.sec u).f (Fam₂.sec u).fC h := by
      intro u ξ hξ h
      exact hD₂.2.1 u ξ hξ h
    have hEis₁ := eisenstein_whittaker P G μ hsRe (Fam₁.sec s) (P.q x) 𝔞₁ hD₁.1
      (fun ξ hξ h => hFix₁ s ξ hξ h) Pd₁ hD₁.2.2.1
      (1 : Fˣ) hD₁.2.2.2.2
    have hEis₂ := eisenstein_whittaker P G μ hsRe (Fam₂.sec s) (P.q xStar) 𝔞₂ hD₂.1
      (fun ξ hξ h => hFix₂ s ξ hξ h) Pd₂ hD₂.2.2.1
      (1 : Fˣ) hD₂.2.2.2.2
    have hCoeff₁ : coeff₁ s = whittakerE P G μ (Fam₁.sec s) (P.q x) := by
      dsimp [coeff₁]
      have hEeq : C₁.E s = eisenstein P G (Fam₁.sec s) := by
        funext g
        exact C₁.E_series s hs g
      rw [hEeq]
      rw [ratDiagOne] at hEis₁
      simpa using hEis₁
    have hCoeff₂ : coeff₂ s = whittakerE P G μ (Fam₂.sec s) (P.q xStar) := by
      dsimp [coeff₂]
      have hEeq : C₂.E s = eisenstein P G (Fam₂.sec s) := by
        funext g
        exact C₂.E_series s hs g
      rw [hEeq]
      rw [ratDiagOne] at hEis₂
      simpa using hEis₂
    rw [← hCoeff₁, ← hCoeff₂] at hW
    exact hW
  obtain ⟨η₁, hη₁pos, hη₁C, hη₁le, hAnal₁⟩ :=
    torusCoeff_analytic FH₁ R₁ (P.q x) 𝔞₁ hD₁.1 hD₁.2.1 Pd₁
      hD₁.2.2.1 hD₁.2.2.2.1 hm₁ (1 : F)
  obtain ⟨η₂, hη₂pos, hη₂C, hη₂le, hAnal₂⟩ :=
    torusCoeff_analytic FH₂ R₂ (P.q xStar) 𝔞₂ hD₂.1 hD₂.2.1 Pd₂
      hD₂.2.2.1 hD₂.2.2.2.1 hm₂ (1 : F)
  let η : ℝ := min η₁ η₂
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min_iff.mpr ⟨hη₁pos, hη₂pos⟩
  have hηle₁ : η ≤ η₁ := by dsimp [η]; exact min_le_left _ _
  have hηle₂ : η ≤ η₂ := by dsimp [η]; exact min_le_right _ _
  have hηle : η ≤ (1 / 6 : ℝ) := le_trans hηle₁ hη₁le
  have hηC₁ : η ≤ C₁.ε := by
    dsimp [R₁] at hη₁C
    exact le_trans hηle₁ hη₁C
  have hηC₂ : η ≤ C₂.ε := by
    dsimp [R₂] at hη₂C
    exact le_trans hηle₂ hη₂C
  obtain ⟨Ψ₁, hΨ₁, hΨ₁val, hΨ₁eq⟩ := C₁.laurent_torus
    (P.q x) Pd₁ hD₁.2.2.2.1 hm₁ (1 : F)
  obtain ⟨Ψ₂, hΨ₂, hΨ₂val, hΨ₂eq⟩ := C₂.laurent_torus
    (P.q xStar) Pd₂ hD₂.2.2.2.1 hm₂ (1 : F)
  have hcont₁ : AnalyticOnNhd ℂ coeff₁
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
    change AnalyticOnNhd ℂ (fun s => torusCoeff P (C₁.E s) (P.q x) Pd₁ (1 : F)) _
    exact hAnal₁.mono (contDomain_mono η η₁ hηle₁)
  have hcont₂ : AnalyticOnNhd ℂ coeff₂
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
    change AnalyticOnNhd ℂ (fun s => torusCoeff P (C₂.E s) (P.q xStar) Pd₂ (1 : F)) _
    exact hAnal₂.mono (contDomain_mono η η₂ hηle₂)
  have hArch₁ : AnalyticOnNhd ℂ (complexArchFactor xStar)
      {s : ℂ | 0 < s.re} := complexArchFactor_analytic xStar
  have hArch₂ : AnalyticOnNhd ℂ (complexArchFactor x)
      {s : ℂ | 0 < s.re} := complexArchFactor_analytic x
  have hDomainPos : ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η ⊆
      {s : ℂ | 0 < s.re} := contDomain_posRe η hηle
  have hPosBall : Metric.ball (1 / 6 : ℂ) η ⊆ {s : ℂ | 0 < s.re} := by
    intro z hz
    exact residueBall_posRe hηle hz
  have hArch₁Ball : AnalyticOnNhd ℂ (complexArchFactor xStar)
      (Metric.ball (1 / 6 : ℂ) η) := hArch₁.mono hPosBall
  have hArch₂Ball : AnalyticOnNhd ℂ (complexArchFactor x)
      (Metric.ball (1 / 6 : ℂ) η) := hArch₂.mono hPosBall
  have hΨ₁Ball : AnalyticOnNhd ℂ Ψ₁ (Metric.ball (1 / 6 : ℂ) η) :=
    hΨ₁.mono (Metric.ball_subset_ball hηC₁)
  have hΨ₂Ball : AnalyticOnNhd ℂ Ψ₂ (Metric.ball (1 / 6 : ℂ) η) :=
    hΨ₂.mono (Metric.ball_subset_ball hηC₂)
  have hΨ₁small (z : ℂ) (hz : z ∈ Metric.ball (1 / 6 : ℂ) η)
      (hne : z ≠ (1 / 6 : ℂ)) : Ψ₁ z = (z - 1 / 6) * coeff₁ z := by
    apply hΨ₁eq z (Metric.ball_subset_ball hηC₁ hz) hne
  have hΨ₂small (z : ℂ) (hz : z ∈ Metric.ball (1 / 6 : ℂ) η)
      (hne : z ≠ (1 / 6 : ℂ)) : Ψ₂ z = (z - 1 / 6) * coeff₂ z := by
    apply hΨ₂eq z (Metric.ball_subset_ball hηC₂ hz) hne
  have hΨ₁at : Ψ₁ (1 / 6 : ℂ) = thetaWhit C₁ (P.q x) := by
    calc
      Ψ₁ (1 / 6 : ℂ) = torusCoeff P C₁.theta (P.q x) Pd₁ (1 : F) := hΨ₁val
      _ = thetaWhit C₁ (P.q x) := hθ₁.symm
  have hΨ₂at : Ψ₂ (1 / 6 : ℂ) = thetaWhit C₂ (P.q xStar) := by
    calc
      Ψ₂ (1 / 6 : ℂ) = torusCoeff P C₂.theta (P.q xStar) Pd₂ (1 : F) := hΨ₂val
      _ = thetaWhit C₂ (P.q xStar) := hθ₂.symm
  let f : ℂ → ℂ := fun s => coeff₁ s * complexArchFactor xStar s -
    coeff₂ s * complexArchFactor x s
  let Ψ : ℂ → ℂ := fun s => Ψ₁ s * complexArchFactor xStar s -
    Ψ₂ s * complexArchFactor x s
  let r : ℂ := thetaWhit C₁ (P.q x) * complexArchFactor xStar (1 / 6) -
    thetaWhit C₂ (P.q xStar) * complexArchFactor x (1 / 6)
  have hf : AnalyticOnNhd ℂ f (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
    change AnalyticOnNhd ℂ
      (fun s => coeff₁ s * complexArchFactor xStar s -
        coeff₂ s * complexArchFactor x s) _
    exact (hcont₁.mul (hArch₁.mono hDomainPos)).sub (hcont₂.mul (hArch₂.mono hDomainPos))
  have hB : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) {s | 0 < s.re} := by fun_prop
  have hr : ∃ Ψ' : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ' (Metric.ball (1 / 6 : ℂ) η) ∧ Ψ' (1 / 6) = r ∧
        ∀ s ∈ Metric.ball (1 / 6 : ℂ) η, s ≠ 1 / 6 → Ψ' s = (s - 1 / 6) * f s := by
    refine ⟨Ψ, ?_, ?_, ?_⟩
    · change AnalyticOnNhd ℂ
        (fun s => Ψ₁ s * complexArchFactor xStar s -
          Ψ₂ s * complexArchFactor x s) _
      exact (hΨ₁Ball.mul hArch₁Ball).sub (hΨ₂Ball.mul hArch₂Ball)
    · change Ψ₁ (1 / 6) * complexArchFactor xStar (1 / 6) -
        Ψ₂ (1 / 6) * complexArchFactor x (1 / 6) = _
      rw [hΨ₁at, hΨ₂at]
    · intro s hs hne
      dsimp [Ψ, f]
      rw [hΨ₁small s hs hne, hΨ₂small s hs hne]
      ring
  have hgeneric0 : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      (s - 1 / 6) * f s = (0 : ℂ) := by
    intro s hs
    have h := hRawCross s hs
    dsimp [f]
    rw [h]
    ring
  have hres := regularized_residue_eval η hηpos hηle f (fun _ => (0 : ℂ)) r hf hB hr
    hgeneric0
  have hzero : r = 0 := by simpa using hres
  apply sub_eq_zero.mp
  simpa [r] using hzero

private theorem jacquetC_spherical_identity_ne_zero :
    jacquetC (sphC (1 / 6)) ≠ 0 := by
  have hGamma : 0 < Real.Gamma (4 / 3 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hConst : 0 < besselConst := by
    unfold besselConst
    exact mul_pos (div_pos (by positivity) hGamma)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hBessel : 0 < besselK (1 / 3 : ℝ) (4 * Real.pi) :=
    besselK_oneThird_pos (by positivity)
  have hR : 0 < besselConst * ‖(1 : ℂ)‖ * besselK (1 / 3 : ℝ) (4 * Real.pi) := by
    simpa using mul_pos hConst hBessel
  have hValue :
      ((besselConst * ‖(1 : ℂ)‖ * besselK (1 / 3 : ℝ) (4 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hR
  have hdiag : diagM ℂ (1 : ℂˣ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagM]
  have hA : aC (1 : ℂˣ) = 1 := by
    change QuotientGroup.mk (diagM ℂ (1 : ℂˣ)) = 1
    rw [hdiag]
    simp
  have hFormula := jacquetC_spherical (1 : ℂˣ)
  have hTranslated : jacquetC (rtr (aC (1 : ℂˣ)) (sphC (1 / 6))) ≠ 0 := by
    rw [hFormula]
    simpa using hValue
  have hrtr : rtr (aC (1 : ℂˣ)) (sphC (1 / 6)) = sphC (1 / 6) := by
    rw [hA]
    funext z
    simp [rtr]
  rw [hrtr] at hTranslated
  exact hTranslated

theorem complexArchFactor_ref_ne_zero (xStar : P.RP)
    (hStarC : ∀ w, P.compC w xStar = 1) : complexArchFactor xStar (1 / 6) ≠ 0 := by
  classical
  unfold complexArchFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro w hw
  rw [hStarC w]
  have htr : rtr (1 : PGL2 ℂ) (sphC (1 / 6)) = sphC (1 / 6) := by
    funext y
    simp [rtr]
  rw [htr]
  exact jacquetC_spherical_identity_ne_zero

end ArtinPrimitiveRoots.A1.Theta
