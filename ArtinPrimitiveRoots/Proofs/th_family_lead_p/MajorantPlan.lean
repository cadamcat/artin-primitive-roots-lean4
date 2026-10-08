import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CompactFourierDomain
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.RootChartRegularity
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.SpecResidueBounds
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.ResidueReconstruction
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.SmoothMatrixCoordinates
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.MatrixIwasawa
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.ComponentMatrixResidue
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.ArchMatrixResidue
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CompactPGLMatrixLifts
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CompactFiniteLevelMatrixCharts
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.MatrixChartDerivatives
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.MatrixChartBounds
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.PeriodicFourier
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CharacterIntegralDerivative
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.DirectionalFourier

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Nonzero frequencies in the full dual of the period ideal. -/
def thetaDualUnits (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
  {ν : Fˣ // ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1}

/-- The real phase in `psiInf = exp (2π i phase)`. -/
def thetaFourierPhase (ν : F) (x : InfinitePlace F → ℂ) : ℝ :=
  -2 * ∑ w, (w.embedding ν * x w).re

/-- A summable product weight on integer lattice coordinates. -/
def thetaLatticeWeight (n : ℕ) (k : Fin n → ℤ) : ℝ :=
  ∏ i, ((1 + |(k i : ℝ)|) ^ 2)⁻¹

private theorem thetaFourierPhase_exp (ν : F) (x : InfinitePlace F → ℂ) :
    psiInf ν x = Complex.exp ((thetaFourierPhase ν x : ℂ) *
      (2 * Real.pi * Complex.I)) := by
  simp only [psiInf, psiC]
  rw [← Complex.exp_sum]
  congr 1
  unfold thetaFourierPhase
  push_cast
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

private theorem thetaFourierPhase_integer (ν : F) (x : InfinitePlace F → ℂ)
    (h : psiInf ν x = 1) : ∃ k : ℤ, (k : ℝ) = thetaFourierPhase ν x := by
  rw [thetaFourierPhase_exp] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have hcast : (thetaFourierPhase ν x : ℂ) = (k : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero hk
  exact ⟨k, by exact_mod_cast hcast.symm⟩

private def thetaFourierPhaseLM (ν : F) : (InfinitePlace F → ℂ) →ₗ[ℝ] ℝ where
  toFun := thetaFourierPhase ν
  map_add' x y := by
    simp only [thetaFourierPhase, Pi.add_apply, mul_add, Complex.add_re,
      Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [thetaFourierPhase, Pi.smul_apply, mul_smul_comm,
      Complex.smul_re, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

private theorem thetaFourierPhase_single (ν : F) (w : InfinitePlace F) (z : ℂ) :
    thetaFourierPhase ν (Pi.single w z) = -2 * (w.embedding ν * z).re := by
  unfold thetaFourierPhase
  congr 1
  rw [Finset.sum_eq_single w]
  · simp
  · intro v hv hvw
    simp [Pi.single, hvw]
  · simp

private theorem thetaFourierPhaseLM_injective :
    Function.Injective (thetaFourierPhaseLM (F := F)) := by
  intro ν μ h
  let w : InfinitePlace F := Classical.choice inferInstance
  have hvalue (x : InfinitePlace F → ℂ) :
      thetaFourierPhase ν x = thetaFourierPhase μ x :=
    congrArg (fun f : (InfinitePlace F → ℂ) →ₗ[ℝ] ℝ => f x) h
  have hRe : (w.embedding ν).re = (w.embedding μ).re := by
    have h1 := hvalue (Pi.single w 1)
    rw [thetaFourierPhase_single, thetaFourierPhase_single] at h1
    simp only [mul_one] at h1
    linarith
  have hIm : (w.embedding ν).im = (w.embedding μ).im := by
    have hI := hvalue (Pi.single w Complex.I)
    rw [thetaFourierPhase_single, thetaFourierPhase_single] at hI
    simp only [Complex.mul_I_re] at hI
    linarith
  exact w.embedding.injective (Complex.ext hRe hIm)

/-- Choose real period coordinates and inject every nonzero dual frequency into the full
integer lattice. The phase identity is the multiplier used in integration by parts. -/
theorem theta_dual_integer_coordinates (D : FieldData F)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ (InfinitePlace F → ℂ)),
      (∀ i, ∃ ξ ∈ (𝔞 : Submodule (𝓞 F) F), infEmbA ξ = b i) ∧
      ∃ κ : thetaDualUnits 𝔞 ↪ (Fin n → ℤ),
        ∀ ν i, (κ ν i : ℝ) = thetaFourierPhase (ν.1 : F) (b i) := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  let I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 𝔞 h𝔞
  let ι := Module.Free.ChooseBasisIndex ℤ I
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ I
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let b : Module.Basis (Fin n) ℝ (InfinitePlace F → ℂ) :=
    ((mixedEmbedding.fractionalIdealLatticeBasis F I).map
      (ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv (F := F))).reindex e
  have hb : ∀ i, ∃ ξ ∈ (𝔞 : Submodule (𝓞 F) F), infEmbA ξ = b i := by
    intro i
    refine ⟨basisOfFractionalIdeal F I (e.symm i), ?_, ?_⟩
    · rw [basisOfFractionalIdeal_apply]
      exact (fractionalIdealBasis F I.1 (e.symm i)).2
    · ext w
      simp [b, Module.Basis.reindex_apply, Module.Basis.map_apply,
        mixedEmbedding.fractionalIdealLatticeBasis_apply,
        ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv, infEmbA,
        mixedEmbedding]
  have hint (ν : thetaDualUnits 𝔞) (i : Fin n) :
      ∃ k : ℤ, (k : ℝ) = thetaFourierPhase (ν.1 : F) (b i) := by
    obtain ⟨ξ, hξ, hξb⟩ := hb i
    apply thetaFourierPhase_integer
    rw [← hξb]
    exact ν.2 ξ hξ
  let κ : thetaDualUnits 𝔞 → (Fin n → ℤ) := fun ν i => Classical.choose (hint ν i)
  have hκ : ∀ ν i, (κ ν i : ℝ) = thetaFourierPhase (ν.1 : F) (b i) :=
    fun ν i => Classical.choose_spec (hint ν i)
  have hinj : Function.Injective κ := by
    intro ν μ h
    have hphase : thetaFourierPhaseLM (ν.1 : F) = thetaFourierPhaseLM (μ.1 : F) := by
      apply b.ext
      intro i
      change thetaFourierPhase (ν.1 : F) (b i) = thetaFourierPhase (μ.1 : F) (b i)
      rw [← hκ ν i, ← hκ μ i, h]
    apply Subtype.ext
    apply Units.ext
    exact thetaFourierPhaseLM_injective hphase
  exact ⟨n, b, hb, ⟨κ, hinj⟩, hκ⟩

open scoped MatrixGroups Matrix.Norms.Elementwise in
open ArtinPrimitiveRoots.Proofs.majorant_sol in
/-- Compact adelic charts give one bound for every fixed left-root derivative. This is
the chart-transfer obligation; fixed-point root smoothness alone does not supply it. -/
theorem theta_compact_root_derivative_bounds {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (L : SChar S) (hL : L ∈ 𝓛) (K : Set P.tc.G)
    (hK : @IsCompact P.tc.G P.tc.topology K)
    (Pd : Set (InfinitePlace F → ℂ)) (hb : Bornology.IsBounded Pd) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ x ∈ closure Pd,
      ‖iteratedFDeriv ℝ n
        (fun x => thetaFamilyTheta B L (nInf P x * g)) x‖ ≤ C := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  obtain ⟨I, C, R, hθ⟩ := continuedEis_spec_residue_reconstruction B.Fam B.C
  obtain ⟨J, CM, hCM, hreg, hcover⟩ :=
    theta_compact_finite_level_matrix_charts P hRP I.T0 C.hsub C.m C.hm K hK
  have hPdCompact : IsCompact (closure Pd) := hb.isCompact_closure
  have hcharts (j : P.tc.G) :
      ∃ f : (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) → ℂ,
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f thetaMatrixRegion ∧
        ∀ M : InfinitePlace F → GL (Fin 2) ℂ,
          ∀ k ∈ levelSet P I.T0 C.hsub C.m,
            thetaFamilyTheta B L
              (P.q (thetaArchRP P (fun w => QuotientGroup.mk (M w))) * j * k) =
                f (fun w => (M w : Matrix (Fin 2) (Fin 2) ℂ)) := by
    obtain ⟨fR, hfR, hrepR⟩ := theta_residue_matrix_chart_derivatives R L.m j
    refine ⟨fun M => (thetaNormalizationScalar N)⁻¹ * fR M,
      contDiffOn_const.mul hfR, ?_⟩
    intro M k hk
    rw [thetaFamilyTheta_eq_spec_residue_deriv B L R hθ, hrepR M k hk]
  choose f hf hrep using hcharts
  intro n
  have hbounds (j : P.tc.G) := theta_matrix_chart_left_root_derivative_bounds
    (f j) (hf j) n (closure Pd) hPdCompact CM hCM hreg
  choose Cb hCb0 hCb using hbounds
  refine ⟨∑ j ∈ J, Cb j, Finset.sum_nonneg (fun j hj => hCb0 j), ?_⟩
  intro g hg x hx
  obtain ⟨j, hj, M, hM, k, hk, hgshape⟩ := hcover g hg
  have hleft (y : InfinitePlace F → ℂ) :
      thetaFamilyTheta B L (nInf P y * g) =
        f j (fun w => (upperM ℂ (y w) : Matrix (Fin 2) (Fin 2) ℂ) * M w) := by
    let Mt : InfinitePlace F → GL (Fin 2) ℂ := fun w => upperM ℂ (y w) * M w
    have hMt : (fun w => (QuotientGroup.mk (Mt w) : PGL2 ℂ)) =
        (fun w => QuotientGroup.mk (upperM ℂ (y w))) *
          (fun w => QuotientGroup.mk (M w)) := by
      funext w
      simp only [Mt, Pi.mul_apply, QuotientGroup.mk_mul]
    have hshape :
        P.q (thetaArchRP P (fun w => QuotientGroup.mk (Mt w))) * j * k =
          nInf P y * g := by
      rw [hMt]
      simp only [map_mul, thetaArchRP_nInf]
      rw [hgshape]
      simp only [mul_assoc]
    rw [← hshape, hrep j Mt k hk]
    rfl
  have hfun : (fun y => thetaFamilyTheta B L (nInf P y * g)) =
      (fun y => f j (fun w => (upperM ℂ (y w) : Matrix (Fin 2) (Fin 2) ℂ) * M w)) :=
    funext hleft
  rw [hfun]
  exact (hCb j (fun w => (M w : Matrix (Fin 2) (Fin 2) ℂ)) hM x hx).trans
    (Finset.single_le_sum (fun i hi => hCb0 i) hj)

/-- Repeated integration by parts in every lattice direction yields product decay,
including frequencies with zero coordinates. -/
theorem theta_periodic_fourier_product_bound {P : CoverPackage D S H A}
    (Ψ : P.tc.G → ℂ) (K : Set P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hb : Bornology.IsBounded Pd) (hm : MeasurableSet Pd)
    (n : ℕ) (b : Module.Basis (Fin n) ℝ (InfinitePlace F → ℂ))
    (hperiods : ∀ i, ∃ ξ ∈ (𝔞 : Submodule (𝓞 F) F), infEmbA ξ = b i)
    (κ : thetaDualUnits 𝔞 ↪ (Fin n → ℤ))
    (hκ : ∀ ν i, (κ ν i : ℝ) = thetaFourierPhase (ν.1 : F) (b i))
    (hper : ∀ g ∈ K, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x,
      Ψ (nInf P (x + infEmbA ξ) * g) = Ψ (nInf P x * g))
    (hsm : ∀ g ∈ K, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Ψ (nInf P x * g)))
    (hbound : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ x ∈ closure Pd,
      ‖iteratedFDeriv ℝ m (fun x => Ψ (nInf P x * g)) x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : thetaDualUnits 𝔞, ∀ g ∈ K,
      ‖torusCoeff P Ψ g Pd (ν.1 : F)‖ ≤ C * thetaLatticeWeight n (κ ν) := by
  sorry

/-- Summability over the full integer lattice, before restriction to the field frequencies. -/
theorem theta_lattice_weight_summable (n : ℕ) : Summable (thetaLatticeWeight n) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
