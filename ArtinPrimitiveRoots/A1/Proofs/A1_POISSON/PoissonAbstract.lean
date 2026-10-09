import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Unfold
import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Orthogonality
import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Uniqueness
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A1-POISSON part `a1_fourier_poisson_abstract` (IMPL)

Abstract Poisson summation on `F_S / R` from unfolding, orthogonality and uniqueness.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private instance poissonAdicLocallyCompact (v : FinPlace F) :
    LocallyCompactSpace (v.adicCompletion F) := by
  have hC := ArtinPrimitiveRoots.Proofs.A1_LATTICE.adicCompletionIntegers_compact v
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup hC
    (hO.mem_nhds (v.adicCompletionIntegers F).zero_mem)

private theorem poisson_periodic_bound (S : SData F CE condη) (D : FieldData F)
    (Q : S.FS → ℂ) (hQ : Continuous Q)
    (hper : ∀ (m : S.R) (x : S.FS), Q (x + S.diag (m : F)) = Q x) :
    ∃ B : ℝ, ∀ x, ‖Q x‖ ≤ B := by
  obtain ⟨C, hC, hcover⟩ :=
    ArtinPrimitiveRoots.Proofs.A1_LATTICE.diagR_has_compact_cover S D
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hQ.continuousOn
  refine ⟨B, fun x => ?_⟩
  obtain ⟨m, k, hk, rfl⟩ := hcover x
  simpa only [add_comm (S.diag (m : F)) k, hper] using hB k hk

private theorem poisson_periodization_continuous (S : SData F CE condη)
    (f : S.FS → ℂ) (hf : Continuous f)
    (hmaj : ∀ C : Set S.FS, IsCompact C → ∃ b : S.R → ℝ, Summable b ∧
      ∀ m : S.R, ∀ x ∈ C, ‖f (x + S.diag (m : F))‖ ≤ b m) :
    Continuous (fun x => ∑' m : S.R, f (x + S.diag (m : F))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨b, hb, hbound⟩ := hmaj C hC
  exact (continuousOn_tsum
    (fun m => (hf.comp (continuous_id.add continuous_const)).continuousOn)
    hb hbound).continuousAt hx

/-- Abstract Poisson summation for `R ⊂ F_S`: for continuous integrable `f` with a summable
majorant of its `R`-translates, uniform on compacts, and absolutely summable Fourier transform on
`R`, `∑_m f(m) = ∑_ν f̂(ν)` with `f̂(y) = ∫ f(x) e(-x y) dμ` (this is `S.fourier A μ f`).

Proof plan: `P x = ∑' m, f (x + m)` is continuous (local M-test from `hmaj` on compact
neighbourhoods; `F_S` is locally compact) and `R`-periodic (reindex by `Equiv.addLeft`);
`G x = ∑' ν, f̂ ν * e(x ν)` is continuous (M-test with `hdual`, `‖e‖ = 1`) and periodic
(`hself`). Both are bounded (periodic + compact cover `A1_LATTICE.diagR_has_compact_cover`), so
integrable on `K`. Coefficients: `∫_K P e(-xν) = ∑_m ∫_K f(x+m) e(-(x+m)ν) = f̂ ν` by
`integral_tsum` (summability from `a1_fourier_unfold` for `f`), `hself` and `a1_fourier_unfold`
for `f·e(-·ν)`; `∫_K G e(-xν) = f̂ ν` by `integral_tsum` and `a1_fourier_orthogonality`
(for `ν' - ν`). Hence `a1_fourier_uniqueness` gives `P = G`; evaluate at `0`.
Uses: `a1_fourier_e_basic`, `a1_fourier_unfold`, `a1_fourier_orthogonality`,
`a1_fourier_uniqueness`. Used by: the glue of `SData.poisson` (`A1/SLattice.lean`). -/
theorem a1_fourier_poisson_abstract (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (μ : Measure S.FS) [μ.IsAddHaarMeasure]
    (K : Set S.FS) (hKm : MeasurableSet K)
    (hK : ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2)
    (hKμ : μ K = 1)
    (hself : ∀ r s : S.R, S.e A (S.diag (r : F) * S.diag (s : F)) = 1)
    (hann : ∀ y : S.FS, (∀ r : S.R, S.e A (S.diag (r : F) * y) = 1) →
      ∃ r : S.R, y = S.diag (r : F))
    (f : S.FS → ℂ) (hf : Continuous f) (hfi : Integrable f μ)
    (hmaj : ∀ C : Set S.FS, IsCompact C → ∃ b : S.R → ℝ, Summable b ∧
      ∀ m : S.R, ∀ x ∈ C, ‖f (x + S.diag (m : F))‖ ≤ b m)
    (hdual : Summable (fun ν : S.R => ‖∫ x, f x * S.e A (-(x * S.diag (ν : F))) ∂μ‖)) :
    ∑' m : S.R, f (S.diag (m : F)) =
      ∑' ν : S.R, ∫ x, f x * S.e A (-(x * S.diag (ν : F))) ∂μ := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  let : IsFiniteMeasure (μ.restrict K) :=
    isFiniteMeasure_restrict.mpr (by rw [hKμ]; exact ENNReal.one_ne_top)
  obtain ⟨hec, hen, hea, _⟩ := a1_fourier_e_basic S A
  have he0 : S.e A 0 = 1 := by simpa using hself 0 0
  let E : S.R → S.FS → ℂ := fun ν x => S.e A (x * S.diag (ν : F))
  have hEc (ν : S.R) : Continuous (E ν) :=
    hec.comp (continuous_id.mul continuous_const)
  have hEn (ν : S.R) (x : S.FS) : ‖E ν x‖ = 1 := hen _
  have hEper (ν m : S.R) (x : S.FS) : E ν (x + S.diag (m : F)) = E ν x := by
    simp only [E, add_mul, hea, hself, mul_one]
  have hEmul (ρ σ : S.R) (x : S.FS) : E ρ x * E σ x = E (ρ + σ) x := by
    simp only [E, Subalgebra.coe_add, map_add, mul_add, hea]
  let c : S.R → ℂ := fun ν => ∫ x, f x * E (-ν) x ∂μ
  have hc : Summable (fun ν => ‖c ν‖) := by
    simpa [c, E, map_neg, mul_neg] using hdual
  let P : S.FS → ℂ := fun x => ∑' m : S.R, f (x + S.diag (m : F))
  let G : S.FS → ℂ := fun x => ∑' ν : S.R, c ν * E ν x
  have hPc : Continuous P := poisson_periodization_continuous S f hf hmaj
  have hPper (m : S.R) (x : S.FS) : P (x + S.diag (m : F)) = P x := by
    calc
      P (x + S.diag (m : F)) = ∑' n : S.R, f (x + S.diag ((m + n : S.R) : F)) := by
        apply tsum_congr
        intro n
        simp only [Subalgebra.coe_add, map_add, add_assoc]
      _ = P x := (Equiv.addLeft m).tsum_eq (fun n : S.R => f (x + S.diag (n : F)))
  have hGc : Continuous G := continuous_tsum
    (fun ν => continuous_const.mul (hEc ν)) hc
    (fun ν x => by simp only [norm_mul, hEn, mul_one]; exact le_rfl)
  have hGper (m : S.R) (x : S.FS) : G (x + S.diag (m : F)) = G x := by
    apply tsum_congr
    intro ν
    rw [hEper]
  obtain ⟨BP, hBP⟩ := poisson_periodic_bound S D P hPc hPper
  obtain ⟨BG, hBG⟩ := poisson_periodic_bound S D G hGc hGper
  have hPi : Integrable P (μ.restrict K) :=
    (integrable_const BP).mono' hPc.aestronglyMeasurable (Filter.Eventually.of_forall hBP)
  have hGi : Integrable G (μ.restrict K) :=
    (integrable_const BG).mono' hGc.aestronglyMeasurable (Filter.Eventually.of_forall hBG)
  have hPcoef (ν : S.R) : ∫ x in K, P x * E (-ν) x ∂μ = c ν := by
    let g : S.FS → ℂ := fun x => f x * E (-ν) x
    have hgi : Integrable g μ := hfi.mul_bdd (hEc (-ν)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (hEn (-ν) x).le)
    have hu := a1_fourier_unfold S μ K hKm hK g hgi
    have ht := hasSum_integral_of_summable_integral_norm
      (fun m : S.R => (hgi.comp_add_right (S.diag (m : F))).restrict) hu.1
    calc
      ∫ x in K, P x * E (-ν) x ∂μ = ∫ x in K, ∑' m : S.R, g (x + S.diag (m : F)) ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        simp only [P, g, hEper, tsum_mul_right]
      _ = ∑' m : S.R, ∫ x in K, g (x + S.diag (m : F)) ∂μ := ht.tsum_eq.symm
      _ = c ν := hu.2.symm
  have hGcoef (ν : S.R) : ∫ x in K, G x * E (-ν) x ∂μ = c ν := by
    have hterm (ρ : S.R) : Integrable (fun x => c ρ * E (ρ - ν) x) (μ.restrict K) :=
      (integrable_const (c ρ)).mul_bdd (hEc (ρ - ν)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (hEn (ρ - ν) x).le)
    have hnorm : Summable (fun ρ : S.R => ∫ x in K, ‖c ρ * E (ρ - ν) x‖ ∂μ) := by
      simpa [norm_mul, hEn, Measure.real, hKμ] using hc
    have ht := hasSum_integral_of_summable_integral_norm hterm hnorm
    have horth (ρ : S.R) : (∫ x in K, c ρ * E (ρ - ν) x ∂μ) =
        if ρ = ν then c ν else 0 := by
      rw [integral_const_mul]
      change c ρ * (∫ x in K, S.e A (x * S.diag ((ρ - ν : S.R) : F)) ∂μ) = _
      rw [a1_fourier_orthogonality S A μ K hKm hK hKμ hself]
      by_cases h : ρ = ν
      · subst ρ
        simp
      · have h0 : (ρ : F) - (ν : F) ≠ 0 := by
          intro h0
          apply h
          apply Subtype.ext
          exact sub_eq_zero.mp h0
        simp [h, h0]
    calc
      ∫ x in K, G x * E (-ν) x ∂μ = ∫ x in K, ∑' ρ : S.R, c ρ * E (ρ - ν) x ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        dsimp [G]
        rw [← tsum_mul_right]
        apply tsum_congr
        intro ρ
        rw [mul_assoc, hEmul, sub_eq_add_neg]
      _ = ∑' ρ : S.R, ∫ x in K, c ρ * E (ρ - ν) x ∂μ := ht.tsum_eq.symm
      _ = c ν := by simp only [horth]; simp
  have hQcoef (ν : S.R) :
      ∫ x in K, (P x - G x) * S.e A (-(x * S.diag (ν : F))) ∂μ = 0 := by
    have hEi : AEStronglyMeasurable (E (-ν)) (μ.restrict K) := (hEc (-ν)).aestronglyMeasurable
    have hEb : ∀ᵐ x ∂μ.restrict K, ‖E (-ν) x‖ ≤ 1 :=
      Filter.Eventually.of_forall fun x => (hEn (-ν) x).le
    have hneg (x : S.FS) : S.e A (-(x * S.diag (ν : F))) = E (-ν) x := by
      simp [E, map_neg, mul_neg]
    simp_rw [hneg, sub_mul]
    rw [integral_sub (hPi.mul_bdd hEi hEb) (hGi.mul_bdd hEi hEb), hPcoef, hGcoef, sub_self]
  have hQ := a1_fourier_uniqueness S D A μ K hKm hK hKμ hself hann
    (fun x => P x - G x) (hPc.sub hGc)
    (fun m x => by rw [hPper, hGper]) hQcoef 0
  have hPG : P 0 = G 0 := sub_eq_zero.mp hQ
  simpa [P, G, c, E, he0, map_neg, mul_neg] using hPG

end ArtinPrimitiveRoots.A1
