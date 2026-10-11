import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_uniform_adapted_lattice
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_translation_regular_fields
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.RootChartRegularity
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.FourierOrbit
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CompactFourierDomain
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.SpecResidueBounds
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.ResidueReconstruction
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.MajorantPlan

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Bound all actual normalized coefficients on a compact set by one summable real majorant; pointwise Summable is insufficient.
Uses theta_uniform_adapted_lattice, uniform mixed derivative bounds on compact coordinate closures and full dual-lattice Fourier decay. -/
theorem theta_compact_fourier_majorant {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (L : SChar S) (hL : L ∈ 𝓛) (K : Set P.tc.G)
    (hK : @IsCompact P.tc.G P.tc.topology K) :
    ∃ M : Fˣ → ℝ, (∀ ν, 0 ≤ M ν) ∧ Summable M ∧
      ∀ ν g, g ∈ K → ‖thetaFamilyW B L (P.tc.rat (diagGL ν) * g)‖ ≤ M ν := by
  obtain ⟨𝔞, Pd, h𝔞, hPd, hb, hm, _, hfix, hper⟩ :=
    theta_uniform_adapted_lattice hRP B Q K hK
  obtain ⟨n, b, hperiods, κ, hκ⟩ := theta_dual_integer_coordinates D 𝔞 h𝔞
  have hzero : nInf P (0 : InfinitePlace F → ℂ) = 1 := by
    change P.tc.nS (Multiplicative.ofAdd (0 : S.FS)) = 1
    rw [ofAdd_zero, map_one]
  have hsm : ∀ g ∈ K, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => thetaFamilyTheta B L (nInf P x * g)) := by
    intro g hg
    have hroot := (theta_translation_regular_fields hRP B L hL).2.2 g
    have hparam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : InfinitePlace F → ℂ => (x, (0 : InfinitePlace F → ℂ))) :=
      contDiff_id.prodMk contDiff_const
    simpa [Function.comp_def, hzero] using hroot.comp hparam
  obtain ⟨C, hC, hbound⟩ := theta_periodic_fourier_product_bound
    (thetaFamilyTheta B L) K 𝔞 h𝔞 Pd hPd hb hm n b hperiods κ hκ
    (hper L hL) hsm (theta_compact_root_derivative_bounds hRP B L hL K hK Pd hb)
  let M : Fˣ → ℝ := fun ν =>
    if hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1
    then C * thetaLatticeWeight n (κ ⟨ν, hν⟩) else 0
  have hweight : ∀ k : Fin n → ℤ, 0 ≤ thetaLatticeWeight n k := by
    intro k
    exact Finset.prod_nonneg fun i hi => inv_nonneg.mpr (sq_nonneg _)
  have hMnonneg : ∀ ν, 0 ≤ M ν := by
    intro ν
    dsimp [M]
    split_ifs
    · exact mul_nonneg hC (hweight _)
    · exact le_rfl
  have hsDual : Summable (fun ν : thetaDualUnits 𝔞 => M ν.1) := by
    have hs := ((theta_lattice_weight_summable n).comp_injective κ.injective).mul_left C
    convert hs using 1
    funext ν
    dsimp only [M, Function.comp_apply]
    rw [dif_pos ν.2]
    rfl
  have hinj : Function.Injective (fun ν : thetaDualUnits 𝔞 => ν.1) :=
    Subtype.val_injective
  have hsM : Summable M := by
    apply (hinj.summable_iff (f := M) ?_).mp hsDual
    intro ν hν
    have hnot : ¬ ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1 := by
      intro hdual
      exact hν ⟨⟨ν, hdual⟩, rfl⟩
    dsimp only [M]
    rw [dif_neg hnot]
  refine ⟨M, hMnonneg, hsM, ?_⟩
  intro ν g hg
  by_cases hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1
  · have hcoeff := thetaFamilyW_eq_torusCoeff B Q L g 𝔞 h𝔞 Pd hPd hb hm
      (hfix g hg) ν hν
    dsimp only [M]
    rw [dif_pos hν, ← hcoeff]
    exact hbound ⟨ν, hν⟩ g hg
  · rw [thetaFamilyW_zero_of_not_dual B Q L hL g 𝔞 (hfix g hg) ν hν]
    simpa only [norm_zero] using hMnonneg ν
end ArtinPrimitiveRoots.A1.Theta
