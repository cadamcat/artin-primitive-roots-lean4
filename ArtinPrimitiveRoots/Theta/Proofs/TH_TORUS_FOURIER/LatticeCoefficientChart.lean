import ArtinPrimitiveRoots.Theta.Eis
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Algebra.Module.ZLattice.Basic
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.NormalizedBasisIntegral

set_option autoImplicit false

open NumberField IsDedekindDomain Module MeasureTheory AddCircle
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem torus_coeff_lattice_chart {n : ℕ}
    (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (b : Basis (Fin (n + 1)) ℝ (InfinitePlace F → ℂ))
    (F₀ : C(UnitAddTorus (Fin (n + 1)), ℂ))
    (hF₀ : ∀ x : Fin (n + 1) → ℝ,
      F₀ (fun j => (x j : UnitAddCircle)) = Ψ (nInf P (b.equivFun.symm x) * g))
    (ν : F) (k : Fin (n + 1) → ℤ)
    (hChar : ∀ x : Fin (n + 1) → ℝ,
      psiInf (-ν) (b.equivFun.symm x) =
        UnitAddTorus.mFourier (-k) (fun j => (x j : UnitAddCircle)))
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup Pd volume)
    (hb : Bornology.IsBounded Pd) :
    torusCoeff P Ψ g Pd ν = UnitAddTorus.mFourierCoeff F₀ k := by
  classical
  let L : Submodule ℤ (InfinitePlace F → ℂ) := Submodule.span ℤ (Set.range b)
  let : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  let q : (InfinitePlace F → ℂ) → UnitAddTorus (Fin (n + 1)) :=
    fun x i => (b.equivFun x i : UnitAddCircle)
  let U : (InfinitePlace F → ℂ) → ℂ :=
    fun x => UnitAddTorus.mFourier (-k) (q x) * F₀ (q x)
  have hEval (x : InfinitePlace F → ℂ) :
      Ψ (nInf P x * g) * psiInf (-ν) x = U x := by
    have h₁ := hF₀ (b.equivFun x)
    have h₂ := hChar (b.equivFun x)
    simp only [LinearEquiv.symm_apply_apply] at h₁ h₂
    change F₀ (q x) = Ψ (nInf P x * g) at h₁
    change psiInf (-ν) x = UnitAddTorus.mFourier (-k) (q x) at h₂
    change Ψ (nInf P x * g) * psiInf (-ν) x =
      UnitAddTorus.mFourier (-k) (q x) * F₀ (q x)
    rw [← h₁, h₂]
    exact mul_comm _ _
  have hper : ∀ (y : L.toAddSubgroup) (x : InfinitePlace F → ℂ),
      U (y +ᵥ x) = U x := by
    intro y x
    have hq : q ((y : InfinitePlace F → ℂ) + x) = q x := by
      funext i
      obtain ⟨r, hr⟩ := (b.mem_span_iff_repr_mem (R := ℤ)
        (y : InfinitePlace F → ℂ)).mp y.property i
      have hz : (b.equivFun (y : InfinitePlace F → ℂ) i : UnitAddCircle) = 0 := by
        apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
        refine ⟨r, ?_⟩
        simpa only [Algebra.algebraMap_eq_smul_one, zsmul_eq_mul, mul_one,
          Basis.equivFun_apply] using hr
      change (b.equivFun ((y : InfinitePlace F → ℂ) + x) i : UnitAddCircle) =
        (b.equivFun x i : UnitAddCircle)
      rw [map_add]
      simp only [Pi.add_apply, AddCircle.coe_add, hz, zero_add]
    change U ((y : InfinitePlace F → ℂ) + x) = U x
    simp only [U, hq]
  have hFD := ZSpan.isAddFundamentalDomain' b
    (volume : Measure (InfinitePlace F → ℂ))
  have hVol : volume Pd = volume (ZSpan.fundamentalDomain b) := hPd.measure_eq hFD
  have hInt : (∫ x in Pd, U x) = ∫ x in ZSpan.fundamentalDomain b, U x :=
    hPd.setIntegral_eq hFD hper
  let Bco : Set (Fin (n + 1) → ℝ) :=
    Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)
  let Boc : Set (Fin (n + 1) → ℝ) :=
    Set.pi Set.univ (fun _ => Set.Ioc (0 : ℝ) 1)
  have hCubes : Bco =ᵐ[volume] Boc := by
    rw [volume_pi]
    exact Measure.pi_Ico_ae_eq_pi_Icc.trans Measure.pi_Ioc_ae_eq_pi_Icc.symm
  have hPull (x : Fin (n + 1) → ℝ) :
      U (b.equivFun.symm x) =
        UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) *
          F₀ (fun i => (x i : UnitAddCircle)) := by
    change UnitAddTorus.mFourier (-k)
        (fun i => (b.equivFun (b.equivFun.symm x) i : UnitAddCircle)) *
      F₀ (fun i => (b.equivFun (b.equivFun.symm x) i : UnitAddCircle)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hNorm := normalized_basis_integral
    (volume : Measure (InfinitePlace F → ℂ)) b U
  simp only [hPull] at hNorm
  unfold torusCoeff
  simp_rw [hEval]
  rw [hVol, hInt]
  calc
    ((volume (ZSpan.fundamentalDomain b)).toReal)⁻¹ *
        (∫ x in ZSpan.fundamentalDomain b, U x) =
        ∫ x in Bco, UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) *
          F₀ (fun i => (x i : UnitAddCircle)) := by
      simpa only [Complex.real_smul] using hNorm
    _ = ∫ x in Boc, UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) *
          F₀ (fun i => (x i : UnitAddCircle)) := setIntegral_congr_set hCubes
    _ = UnitAddTorus.mFourierCoeff F₀ k := by
      simpa [Boc, Set.pi, smul_eq_mul] using
        (UnitAddTorus.mFourierCoeff_eq_integral F₀ k (0 : Fin (n + 1) → ℝ)).symm

end ArtinPrimitiveRoots.Proofs.thsol_torusf
