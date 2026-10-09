import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs

/-!
# A1-FOURIER part `a1_fourier_unfold` (IMPL)

Unfolding an integral over `F_S` along a measurable fundamental domain of the diagonal
S-integer lattice.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Unfolding along a fundamental domain `K` of `R ↪ F_S`: for integrable `g`,
`∫ g = ∑_{m ∈ R} ∫_K g(x + m)`, and the series of `∫_K ‖g(x+m)‖` converges.

Proof hint: let `S.R` (additive group, countable since `F` is countable) act on `F_S` by
`m +ᵥ x = S.diag m + x`; the action is measure preserving for the Haar measure `μ`; `hK` and
`hKm` give `IsAddFundamentalDomain S.R K μ` (compare `htoFD` in the proof of the private
`covol_candidate_fundamental_domain_mass_eq`, `A1/SLattice.lean` ~2726–2795); then
`IsAddFundamentalDomain.integral_eq_tsum'` and `lintegral_eq_tsum'` (applied to `‖g‖ₑ`).
Used by: `a1_fourier_poisson_abstract`. -/
theorem a1_fourier_unfold (S : SData F CE condη) {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (μ : Measure S.FS) [μ.IsAddHaarMeasure]
    (K : Set S.FS) (hKm : MeasurableSet K)
    (hK : ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2)
    (g : S.FS → ℂ) (hg : Integrable g μ) :
    Summable (fun m : S.R => ∫ x in K, ‖g (x + S.diag (m : F))‖ ∂μ) ∧
      ∫ x, g x ∂μ = ∑' m : S.R, ∫ x in K, g (x + S.diag (m : F)) ∂μ := by
  classical
  haveI : Countable F := by
    haveI : Countable ℚ := inferInstance
    exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  haveI : Countable S.R := inferInstance
  letI : AddAction S.R S.FS :=
    { vadd := fun r x => S.diag (r : F) + x
      add_vadd := by
        intro r s x
        change S.diag ((r + s : S.R) : F) + x =
          S.diag (r : F) + (S.diag (s : F) + x)
        simp only [Subalgebra.coe_add, map_add]
        abel
      zero_vadd := by
        intro x
        change S.diag ((0 : S.R) : F) + x = x
        simp }
  have hcont : ∀ r : S.R, Continuous (fun x : S.FS => S.diag (r : F) + x) := fun r =>
    continuous_const_add _
  have hmeas : ∀ r : S.R, Measurable (fun x : S.FS => S.diag (r : F) + x) := fun r =>
    (hcont r).measurable
  letI : MeasurableConstVAdd S.R S.FS := ⟨hmeas⟩
  have hInv : VAddInvariantMeasure S.R S.FS μ := by
    constructor
    intro r T hT
    change μ ((fun x : S.FS => S.diag (r : F) + x) ⁻¹' T) = μ T
    exact (measurePreserving_add_left μ (S.diag (r : F))).measure_preimage
      hT.nullMeasurableSet
  letI := hInv
  have hexact : ∀ x : S.FS, ∃! r : S.R, r +ᵥ x ∈ K := by
    intro x
    obtain ⟨p, hp, huniq⟩ := hK x
    rcases p with ⟨r, k⟩
    rcases hp with ⟨hk, hrep⟩
    refine ⟨-r, ?_, ?_⟩
    · change S.diag ((-r : S.R) : F) + x ∈ K
      rw [hrep]
      have heq : S.diag ((-r : S.R) : F) + (S.diag (r : F) + k) = k := by
        have h1 : ((-r : S.R) : F) = -((r : S.R) : F) := by simp
        rw [h1, map_neg]
        abel
      rw [heq]
      exact hk
    · intro q hq
      have hrep' : x = S.diag ((-q : S.R) : F) + (q +ᵥ x) := by
        change x = S.diag ((-q : S.R) : F) + (S.diag (q : F) + x)
        have h1 : ((-q : S.R) : F) = -((q : S.R) : F) := by simp
        rw [h1, map_neg]
        abel
      have hpair : ((-q : S.R), q +ᵥ x).2 ∈ K ∧
          x = S.diag (((-q : S.R), q +ᵥ x).1 : F) + ((-q : S.R), q +ᵥ x).2 :=
        ⟨hq, hrep'⟩
      have hchosen : (r, k).2 ∈ K ∧ x = S.diag ((r, k).1 : F) + (r, k).2 :=
        ⟨hk, hrep⟩
      have heq := huniq (-q, q +ᵥ x) hpair
      have hfirst : -q = r := congrArg Prod.fst heq
      have : q = -r := by simpa using congrArg (fun a : S.R => -a) hfirst
      exact this
  have hFD : IsAddFundamentalDomain S.R K μ :=
    IsAddFundamentalDomain.mk' hKm.nullMeasurableSet hexact
  have hunfold : ∫ x, g x ∂μ = ∑' m : S.R, ∫ x in K, g (m +ᵥ x) ∂μ :=
    hFD.integral_eq_tsum'' g hg
  have hcomm : ∀ m : S.R, (∫ x in K, g (m +ᵥ x) ∂μ) =
      (∫ x in K, g (x + S.diag (m : F)) ∂μ) := by
    intro m
    apply setIntegral_congr_fun hKm
    intro x _
    show g (m +ᵥ x) = g (x + S.diag (m : F))
    have hv : (m +ᵥ x) = x + S.diag (m : F) := by
      show S.diag (m : F) + x = x + S.diag (m : F)
      rw [add_comm]
    rw [hv]
  have heq2 : ∫ x, g x ∂μ = ∑' m : S.R, ∫ x in K, g (x + S.diag (m : F)) ∂μ := by
    rw [hunfold]
    apply tsum_congr
    intro m
    exact hcomm m
  have hlin : ∫⁻ x, ‖g x‖ₑ ∂μ = ∑' m : S.R, ∫⁻ x in K, ‖g (m +ᵥ x)‖ₑ ∂μ :=
    hFD.lintegral_eq_tsum'' _
  have hfin : ∫⁻ x, ‖g x‖ₑ ∂μ < (∞ : ℝ≥0∞) := hg.hasFiniteIntegral
  have hne : (∑' m : S.R, ∫⁻ x in K, ‖g (m +ᵥ x)‖ₑ ∂μ) ≠ (∞ : ℝ≥0∞) := by
    rw [← hlin]
    exact ne_top_of_lt hfin
  have hsumReal : Summable (fun m : S.R => (∫⁻ x in K, ‖g (m +ᵥ x)‖ₑ ∂μ).toReal) :=
    ENNReal.summable_toReal hne
  have hterm : ∀ m : S.R, (∫ x in K, ‖g (m +ᵥ x)‖ ∂μ) =
      (∫⁻ x in K, ‖g (m +ᵥ x)‖ₑ ∂μ).toReal := by
    intro m
    have h1 : Integrable (fun x : S.FS => g (S.diag (m : F) + x)) μ :=
      hg.comp_add_left (S.diag (m : F))
    have hInt : IntegrableOn (fun x => g (m +ᵥ x)) K μ := h1.integrableOn
    have hAEM : AEStronglyMeasurable (fun x => g (m +ᵥ x)) (μ.restrict K) :=
      hInt.aestronglyMeasurable
    have hEq := integral_norm_eq_lintegral_enorm (μ := μ.restrict K)
      (f := fun x => g (m +ᵥ x)) hAEM
    exact hEq
  have hsumVadd : Summable (fun m : S.R => ∫ x in K, ‖g (m +ᵥ x)‖ ∂μ) := by
    have : (fun m : S.R => ∫ x in K, ‖g (m +ᵥ x)‖ ∂μ) =
        (fun m : S.R => (∫⁻ x in K, ‖g (m +ᵥ x)‖ₑ ∂μ).toReal) := by
      funext m
      exact hterm m
    rw [this]
    exact hsumReal
  have hsum : Summable (fun m : S.R => ∫ x in K, ‖g (x + S.diag (m : F))‖ ∂μ) := by
    have hEq : (fun m : S.R => ∫ x in K, ‖g (x + S.diag (m : F))‖ ∂μ) =
        (fun m : S.R => ∫ x in K, ‖g (m +ᵥ x)‖ ∂μ) := by
      funext m
      apply setIntegral_congr_fun hKm
      intro x _
      show ‖g (x + S.diag (m : F))‖ = ‖g (m +ᵥ x)‖
      have hv : x + S.diag (m : F) = (m +ᵥ x) := by
        show x + S.diag (m : F) = S.diag (m : F) + x
        rw [add_comm]
      rw [hv]
    rw [hEq]
    exact hsumVadd
  exact ⟨hsum, heq2⟩

end ArtinPrimitiveRoots.A1
