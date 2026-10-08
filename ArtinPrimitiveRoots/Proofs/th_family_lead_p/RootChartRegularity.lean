import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_translation_regular_fields

set_option autoImplicit false
open NumberField
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Pulling a jointly smooth root orbit back along two extra root translations preserves
joint smoothness. The parameters describe `nInf x * nInf y * g * nInf z`; the two left
translations combine into one root coordinate. -/
theorem jointRootSmooth_rootChart_contDiff {P : CoverPackage D S H A}
    {Ψ : P.tc.G → ℂ} (hΨ : JointRootSmooth P Ψ) (g : P.tc.G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) ×
          (InfinitePlace F → ℂ) =>
        Ψ (nInf P p.1.1 * nInf P p.1.2 * g * nInf P p.2)) := by
  have hroot := hΨ g
  have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) ×
          (InfinitePlace F → ℂ) => (p.1.1 + p.1.2, p.2)) := by
    fun_prop
  have hcomp := hroot.comp hmap
  convert hcomp using 1
  funext p
  have hadd (x y : InfinitePlace F → ℂ) :
      nInf P (x + y) = nInf P x * nInf P y := by
    change P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y)) =
      P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)) *
        P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y))
    have hη : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x) +
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) := by
      ext <;> simp
    rw [hη, ofAdd_add, map_mul]
  simp only [Function.comp_apply]
  rw [← hadd p.1.1 p.1.2]

/-- Every fixed iterated derivative of the pulled-back joint-root function is bounded on a
compact set of root-chart parameters. -/
theorem jointRootSmooth_rootChart_iteratedFDeriv_isBounded {P : CoverPackage D S H A}
    {Ψ : P.tc.G → ℂ} (hΨ : JointRootSmooth P Ψ) (g : P.tc.G) (n : ℕ)
    (K : Set (((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) ×
      (InfinitePlace F → ℂ))) (hK : IsCompact K) :
    Bornology.IsBounded
      (iteratedFDeriv ℝ n
        (fun p : ((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) ×
          (InfinitePlace F → ℂ) =>
          Ψ (nInf P p.1.1 * nInf P p.1.2 * g * nInf P p.2)) '' K) := by
  have hcont := (jointRootSmooth_rootChart_contDiff hΨ g).continuous_iteratedFDeriv
    (m := n) (by simp)
  exact (hK.image hcont).isBounded

/-- A numeric bound for a fixed iterated derivative on a compact root-chart parameter set. -/
theorem jointRootSmooth_rootChart_iteratedFDeriv_bound {P : CoverPackage D S H A}
    {Ψ : P.tc.G → ℂ} (hΨ : JointRootSmooth P Ψ) (g : P.tc.G) (n : ℕ)
    (K : Set (((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) ×
      (InfinitePlace F → ℂ))) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n
        (fun p : ((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) ×
          (InfinitePlace F → ℂ) =>
          Ψ (nInf P p.1.1 * nInf P p.1.2 * g * nInf P p.2)) p‖ ≤ C := by
  have hbounded := jointRootSmooth_rootChart_iteratedFDeriv_isBounded hΨ g n K hK
  obtain ⟨C, hC⟩ := hbounded.subset_closedBall (0 : _)
  refine ⟨C, fun p hp => ?_⟩
  have hmem := hC (Set.mem_image_of_mem _ hp)
  simpa [Metric.mem_closedBall, dist_eq_norm] using hmem

/-- Apply the root-chart compact derivative estimate to the normalized theta family. -/
theorem thetaFamilyTheta_rootChart_iteratedFDeriv_bound {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (L : SChar S)
    (hL : L ∈ 𝓛) (g : P.tc.G) (n : ℕ)
    (K : Set (((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) ×
      (InfinitePlace F → ℂ))) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n
        (fun p : ((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) ×
          (InfinitePlace F → ℂ) =>
          thetaFamilyTheta B L (nInf P p.1.1 * nInf P p.1.2 * g * nInf P p.2)) p‖ ≤ C := by
  exact jointRootSmooth_rootChart_iteratedFDeriv_bound
    (theta_translation_regular_fields hRP B L hL).2.2 g n K hK

end ArtinPrimitiveRoots.A1.Theta
