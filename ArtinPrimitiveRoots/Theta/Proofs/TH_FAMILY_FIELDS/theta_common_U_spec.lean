import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Export exactly the seven common-neighborhood fields consumed by ThetaFamily.U_spec.
Guide: sol-thin-thglobal/PROOFS.md:1173–1180.
Uses ThetaCommonSections, finite products of open and compact sets. -/
theorem theta_common_U_spec {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) :
    IsOpen (thetaCommonU B) ∧ IsCompact (thetaCommonU B) ∧ (1 ∈ thetaCommonU B) ∧
    (∀ y ∈ thetaCommonU B, ∀ v : S.Sf, y v ∈ v.1.adicCompletionIntegers F) ∧
    (∀ y ∈ thetaCommonU B, ∀ v : S.Sf, Valued.v (y v) = 1) ∧
    (∀ y ∈ thetaCommonU B, ∃ c : ∀ v : S.Sf, v.1.adicCompletion F, y = c ^ 6) ∧
    (∀ L ∈ 𝓛, ∀ y : S.FSˣ, y.1.1 ∈ thetaCommonU B →
      (∀ w, y.1.2 w = 1) → L.L y = 1) := by
  classical
  have hUeq : thetaCommonU B = Set.pi Set.univ B.Uv := by
    ext y
    simp [thetaCommonU]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hUeq]
    exact isOpen_set_pi Set.finite_univ (fun v _ => B.open_Uv v)
  · rw [hUeq]
    exact isCompact_univ_pi B.compact_Uv
  · intro v
    exact B.one_Uv v
  · intro y hy v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      B.unit_Uv v (y v) (hy v)]
  · intro y hy v
    exact B.unit_Uv v (y v) (hy v)
  · intro y hy
    choose c hc using fun v => B.sixth_Uv v (y v) (hy v)
    refine ⟨fun v => (c v : v.1.adicCompletion F), ?_⟩
    funext v
    simpa using hc v
  · intro L hL y hy hcomplex
    exact B.character_kernel L hL y (fun v => hy v) hcomplex
end ArtinPrimitiveRoots.A1.Theta
