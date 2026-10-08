import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_complex_derivative_tensor

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
open Module
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem multilinear_finBasis_expand {ι : Type} [Fintype ι] [DecidableEq ι]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    [∀ i, Fintype (Fin (Module.finrank ℂ (V i)))]
    (Λ : MultilinearMap ℂ V ℂ) (x : ∀ i, V i) :
    Λ x = ∑ j : ∀ i, Fin (Module.finrank ℂ (V i)),
      (∏ i, (Module.finBasis ℂ (V i)).repr (x i) (j i)) *
        Λ (fun i => Module.finBasis ℂ (V i) (j i)) := by
  let b : ∀ i, Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i) :=
    fun i => Module.finBasis ℂ (V i)
  have hx : x = fun i => ∑ j, (b i).repr (x i) j • b i j := by
    funext i
    exact ((b i).sum_repr (x i)).symm
  rw [hx, MultilinearMap.map_sum]
  simp_rw [MultilinearMap.map_smul_univ]
  simp [smul_eq_mul, b]

/-- Export the finite tensor expansion at the Weyl translate with δ = 1/3, including the one empty tensor when S.Sf is empty.
Guide: sol-thin-thglobal/PROOFS.md:1191–1199.
Uses theta_complex_derivative_tensor, rotatedCoord_sheetHyp, sheetHypC_bessel, derivVecC_rotate and the finite-place bases. -/
theorem theta_T6_sheet_bound {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛) :
    ∃ (J : ℕ) (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
      (fc : Fin J → InfinitePlace F → ℂ → ℂ),
      (∀ ℓ v, SheetHypFin v.1 (1 / 3) (ff ℓ v)) ∧
      (∀ ℓ w, SheetHypC (1 / 3) (fc ℓ w)) ∧
      ∀ y : S.FSˣ, thetaFamilyW B L (P.tc.aS y * P.tc.wS) =
        ∑ ℓ : Fin J, (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
          ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w) := by
  classical
  let b : ∀ v : S.Sf, Basis (Fin (Module.finrank ℂ ((N.G.T v.1).V))) ℂ ((N.G.T v.1).V) :=
    fun v => Module.finBasis ℂ ((N.G.T v.1).V)
  let ι : Type := ∀ v : S.Sf, Fin (Module.finrank ℂ ((N.G.T v.1).V))
  let J : ℕ := Fintype.card ι
  let e : ι ≃ Fin J := Fintype.equivFin ι
  let w₀ : InfinitePlace F := Classical.choice inferInstance
  let coeff (j : ι) : ℂ := (thetaNormalizationScalar N)⁻¹ *
    N.Λ (fun v => b v (j v))
  let ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ := fun ℓ v z =>
    rotatedCoord (P.loc v.1) (N.G.T v.1) A (N.μ v.1) (1 / 6) (B.φ v)
      ((b v).coord ((e.symm ℓ) v)) z
  let fc : Fin J → InfinitePlace F → ℂ → ℂ := fun ℓ w z =>
    if hw : w = w₀ then
      (-(4 * Real.pi * Complex.I) * besselConst * coeff (e.symm ℓ)) *
        (Complex.normSq z : ℂ) * omegaAng (-L.m w) z *
        (besselK (1 / 3) (4 * Real.pi * ‖z‖) : ℂ)
    else
      (-(4 * Real.pi * Complex.I) * besselConst) *
        (Complex.normSq z : ℂ) * omegaAng (-L.m w) z *
        (besselK (1 / 3) (4 * Real.pi * ‖z‖) : ℂ)
  refine ⟨J, ff, fc, ?_, ?_, ?_⟩
  · intro ℓ v
    exact rotatedCoord_sheetHyp (P.loc v.1) (N.G.T v.1) A (N.μ v.1)
      (B.φ v) (B.locally_constant v) (B.compact_support v)
      ((b v).coord ((e.symm ℓ) v))
  · intro ℓ w
    by_cases hw : w = w₀
    · simpa [fc, hw, mul_assoc] using sheetHypC_bessel (-L.m w)
        (by rcases L.hm w with h | h <;> simp [h])
        (-(4 * Real.pi * Complex.I) * besselConst * coeff (e.symm ℓ))
    · simpa [fc, hw, mul_assoc] using sheetHypC_bessel (-L.m w)
        (by rcases L.hm w with h | h <;> simp [h])
        (-(4 * Real.pi * Complex.I) * besselConst)
  · intro y
    obtain ⟨ra, hqa, hfa, hca⟩ := P.aS_components y
    obtain ⟨rw, hqw, hfw, hcw⟩ := P.wS_components
    let r : P.RP := ra * rw
    have hq : P.q r = P.tc.aS y * P.tc.wS := by
      change P.q (ra * rw) = P.tc.aS y * P.tc.wS
      rw [map_mul, hqa, hqw]
    have hr : ∀ v, v ∉ S.Sf → P.compF v r = 1 := by
      intro v hv
      change P.compF v (ra * rw) = 1
      rw [map_mul, hfa v, hfw v]
      simp [hv]
    have hTensor := theta_complex_derivative_tensor B Q L hL r hr
    rw [hq] at hTensor
    have hfinite (v : S.Sf) :
        P.compF v.1 r = (P.loc v.1).a (S.compU v y) * (P.loc v.1).w := by
      change P.compF v.1 (ra * rw) = _
      rw [map_mul, hfa v.1, hfw v.1]
      simp [v.2]
    have hcomplex (w : InfinitePlace F) :
        P.compC w r = aC (S.compC w y) * wC := by
      change P.compC w (ra * rw) = _
      rw [map_mul, hca w, hcw w]
      rfl
    have hval (w : InfinitePlace F) :
        ((S.compC w y : ℂˣ) : ℂ) = (y : S.FS).2 w := rfl
    have hΛ := multilinear_finBasis_expand N.Λ
      (fun v => jacquet (P.loc v.1) A (N.μ v.1)
        (rtr (P.compF v.1 r) ((B.Fam.sec (1 / 6)).f v.1)))
    have harch (w : InfinitePlace F) :
        jacquetC (rtr (P.compC w r) (derivVecC (L.m w) (sphC (1 / 6)))) =
          (-(4 * Real.pi * Complex.I) * besselConst) *
          (Complex.normSq (S.compC w y : ℂ) : ℂ) *
              omegaAng (-L.m w) (S.compC w y : ℂ) *
                (besselK (1 / 3) (4 * Real.pi * ‖(S.compC w y : ℂ)‖) : ℂ) := by
      rw [hcomplex w]
      have hrt : rtr (aC (S.compC w y) * wC) (derivVecC (L.m w) (sphC (1 / 6))) =
          rtr (aC (S.compC w y))
            (rtr wC (derivVecC (L.m w) (sphC (1 / 6)))) := by
        funext g
        simp [rtr, mul_assoc]
      rw [hrt, derivVecC_rotate]
      exact jacquetC_derivative (-L.m w)
        (by rcases L.hm w with h | h <;> simp [h]) (S.compC w y)
    have hfiniteEval (v : S.Sf) (j : ι) :
        (b v).repr
          (jacquet (P.loc v.1) A (N.μ v.1)
            (rtr (P.compF v.1 r) ((B.Fam.sec (1 / 6)).f v.1))) (j v) =
          ff (e j) v ((y : S.FS).1 v) := by
      rw [hfinite v]
      rw [B.finite_section (1 / 6) v]
      have hvalv : ((S.compU v y : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) =
          ((y : S.FS).1 v) := rfl
      have hraw : ((y : S.FS).1 v) ≠ 0 := by
        intro hz
        exact (S.compU v y).ne_zero (hvalv.trans hz)
      have hmk : Units.mk0 ((y : S.FS).1 v) hraw = S.compU v y := by
        apply Units.ext
        exact hvalv.symm
      simp [ff, rotatedCoord, hraw, hmk, rtr, Equiv.symm_apply_apply]
    have hfc (j : ι) :
        (∏ w : InfinitePlace F, fc (e j) w ((y : S.FS).2 w)) =
          coeff j * ∏ w : InfinitePlace F,
            (-(4 * Real.pi * Complex.I) * besselConst) *
              (Complex.normSq ((y : S.FS).2 w) : ℂ) *
                omegaAng (-L.m w) ((y : S.FS).2 w) *
                  (besselK (1 / 3) (4 * Real.pi * ‖(y : S.FS).2 w‖) : ℂ) := by
      have hpoint (w : InfinitePlace F) :
          fc (e j) w ((y : S.FS).2 w) =
            (if w = w₀ then coeff j else 1) *
              ((-(4 * Real.pi * Complex.I) * besselConst) *
                (Complex.normSq ((y : S.FS).2 w) : ℂ) *
                  omegaAng (-L.m w) ((y : S.FS).2 w) *
                    (besselK (1 / 3) (4 * Real.pi * ‖(y : S.FS).2 w‖) : ℂ)) := by
        by_cases hw : w = w₀ <;>
          simp [fc, hw, coeff, mul_assoc, Equiv.symm_apply_apply] <;> ring
      calc
        _ = (∏ w : InfinitePlace F, (if w = w₀ then coeff j else 1)) *
              ∏ w : InfinitePlace F,
                ((-(4 * Real.pi * Complex.I) * besselConst) *
                  (Complex.normSq ((y : S.FS).2 w) : ℂ) *
                    omegaAng (-L.m w) ((y : S.FS).2 w) *
                      (besselK (1 / 3) (4 * Real.pi * ‖(y : S.FS).2 w‖) : ℂ)) := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro w hw
            exact hpoint w
        _ = coeff j * ∏ w : InfinitePlace F,
              ((-(4 * Real.pi * Complex.I) * besselConst) *
                (Complex.normSq ((y : S.FS).2 w) : ℂ) *
                  omegaAng (-L.m w) ((y : S.FS).2 w) *
                    (besselK (1 / 3) (4 * Real.pi * ‖(y : S.FS).2 w‖) : ℂ)) := by
            rw [Finset.prod_ite_eq_of_mem' (s := Finset.univ) (a := w₀)
              (b := fun _ : InfinitePlace F => coeff j) (Finset.mem_univ _)]
    have hterm (j : ι) :
        (thetaNormalizationScalar N)⁻¹ *
            ((∏ v : S.Sf,
                (b v).repr
                  (jacquet (P.loc v.1) A (N.μ v.1)
                    (rtr (P.compF v.1 r) ((B.Fam.sec (1 / 6)).f v.1))) (j v)) *
              N.Λ (fun v => b v (j v))) *
            ∏ w, jacquetC (rtr (P.compC w r) (derivVecC (L.m w) (sphC (1 / 6)))) =
          (∏ v : S.Sf, ff (e j) v ((y : S.FS).1 v)) *
            (∏ w : InfinitePlace F, fc (e j) w ((y : S.FS).2 w)) := by
      rw [Finset.prod_congr rfl (fun v hv => hfiniteEval v j)]
      simp_rw [harch, hval]
      rw [hfc]
      dsimp [coeff]
      ring
    rw [hTensor, hΛ, Finset.mul_sum, Finset.sum_mul]
    calc
      _ = ∑ j : ι,
            (∏ v : S.Sf, ff (e j) v ((y : S.FS).1 v)) *
              (∏ w : InfinitePlace F, fc (e j) w ((y : S.FS).2 w)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j
      _ = ∑ ℓ : Fin J,
            (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
              ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w) := by
            exact Equiv.sum_comp e (fun ℓ : Fin J =>
              (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
                ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w))
end ArtinPrimitiveRoots.A1.Theta
