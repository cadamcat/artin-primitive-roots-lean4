import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.intertwined_scalar_q
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.lam_torus_nonzero_iff_mem_alag
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.tame_lagrangian_vector_selector
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

omit [NumberField F] in
private theorem nonzero_diagonal_map {K : Type} [Field K]
    (φ : F →+* K) (δ : Fˣ) :
    Matrix.GeneralLinearGroup.map φ (diagGL δ) =
      diagM K (Units.map φ.toMonoidHom δ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map_apply, diagGL, diagM]

private theorem nonzero_complex_diagonal (y : ℂˣ) :
    intertwineC (sphC (1 / 6)) (QuotientGroup.mk (diagM ℂ y)) ≠ 0 := by
  rw [intertwineC_spherical (1 / 6) (by norm_num)]
  refine mul_ne_zero (div_ne_zero ?_ (by norm_num)) ?_
  · exact_mod_cast Real.pi_ne_zero
  · rw [sphC_mk]
    have hformula : sphericalC (-(1 / 6 : ℂ)) (diagM ℂ y) =
        (‖(y : ℂ)‖ : ℂ) ^ (1 + 2 * (-(1 / 6 : ℂ))) := by
      simp [sphericalC, diagM, Matrix.det_fin_two]
    rw [hformula]
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact_mod_cast (norm_ne_zero_iff.mpr y.ne_zero)

set_option backward.isDefEq.respectTransparency false in
/-- The normalized intertwined scalar on rational diagonals is supported
exactly on the global Lagrangian subgroup. -/
theorem rat_intertwined_scalar_nonzero_iff_mem_delta {P : CoverPackage D S H A}
    (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v) (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf)
    (h1 : ∀ v ∈ S.Sf,
      G.lam v (intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) 1) = 1)
    (hzero : ∀ v ∈ S.Sf, ∀ y : (v.adicCompletion F)ˣ, y ∉ G.Alag v →
      G.lam v ((G.T v).σa y
        (intertwine (P.loc v) (μ v) ((Fam.sec (1 / 6)).f v) 1)) = 0)
    (δ : Fˣ) :
    fourierRawM μ Fam.sec (1 / 6) (P.tc.rat (diagGL δ)) ≠ 0 ↔ δ ∈ G.Δ := by
  classical
  let Fs := Fam.sec (1 / 6)
  let r := P.ratRP (diagGL δ)
  let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
    if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
    else sphWeyl P G v (fun h => hv (Fs.sub h)) (1 / 6)
  have hs : 0 < (1 / 6 : ℂ).re := by norm_num
  have hFsT : Fs.T0 = S.Sf := (Fam.T0_eq (1 / 6)).trans hT
  obtain ⟨hfinite, hprod⟩ := intertwined_scalar_q P G μ hs Fs r
  have hformula : fourierRawM μ Fam.sec (1 / 6) (P.tc.rat (diagGL δ)) =
      (∏ᶠ v, G.lam v (fM v (P.compF v r))) *
        ∏ w, intertwineC (Fs.fC w) (P.compC w r) := by
    change scalarOf P G fM (fun w => intertwineC (Fs.fC w))
      (P.tc.rat (diagGL δ)) = _
    rw [← P.q_ratRP]
    exact hprod
  have hcomp (v : FinPlace F) : P.compF v r = (P.loc v).a (toLoc v δ) := by
    dsimp only [r]
    rw [P.compF_ratRP, nonzero_diagonal_map, ← (P.loc v).sec_a]
    rfl
  have hlocal (v : FinPlace F) :
      G.lam v (fM v (P.compF v r)) ≠ 0 ↔ toLoc v δ ∈ G.Alag v := by
    rw [hcomp]
    dsimp only [fM]
    by_cases hv : v ∈ Fs.T0
    · simp only [dite_eq_left hv]
      have hvS : v ∈ S.Sf := hFsT ▸ hv
      exact lam_torus_nonzero_iff_mem_alag G v (-(1 / 6 : ℂ))
        (intertwine (P.loc v) (μ v) (Fs.f v))
        (intertwine_isSection (P.loc v) (G.T v) (μ v) (1 / 6) hs
          (Fs.f v) (Fs.f_sec v)).2
        (h1 v hvS) (hzero v hvS) (toLoc v δ)
    · simp only [dite_eq_right hv]
      have hvS : v ∉ S.Sf := fun h => hv (Fs.sub h)
      have hsec : IsSection (P.loc v) (G.T v).weyl (-(1 / 6 : ℂ))
          (sphWeyl P G v hvS (1 / 6)) :=
        (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl (G.B v hvS).weyl
          (fun h => hvS (S.over6 v h)) (-(1 / 6 : ℂ))).choose_spec.1
      have hval : sphWeyl P G v hvS (1 / 6) 1 = (G.B v hvS).e 0 := by
        have h :=
          (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl (G.B v hvS).weyl
            (fun h => hvS (S.over6 v h)) (-(1 / 6 : ℂ))).choose_spec.2.1
        change sphWeyl P G v hvS (1 / 6) 1 = (G.B v hvS).e (-0) at h
        simpa only [neg_zero] using h
      apply lam_torus_nonzero_iff_mem_alag G v (-(1 / 6 : ℂ))
        (sphWeyl P G v hvS (1 / 6)) hsec
      · rw [hval]
        simp [G.lam_tame]
      · intro y hy
        rw [hval]
        exact tame_lagrangian_vector_selector G v hvS y hy
  have harch (w : InfinitePlace F) :
      intertwineC (Fs.fC w) (P.compC w r) ≠ 0 := by
    dsimp only [Fs, r]
    rw [Fam.fC_sph, P.compC_ratRP, nonzero_diagonal_map]
    exact nonzero_complex_diagonal _
  have hdelta : δ ∈ G.Δ ↔ ∀ v, toLoc v δ ∈ G.Alag v := by
    simp [GlobalDatum.Δ]
  rw [hformula, hdelta]
  constructor
  · intro hn v
    apply (hlocal v).mp
    intro hz
    exact (mul_ne_zero_iff.mp hn).1 (finprod_eq_zero _ v hz hfinite)
  · intro hd
    exact mul_ne_zero (finprod_ne_zero fun v => (hlocal v).mpr (hd v))
      (Finset.prod_ne_zero_iff.mpr fun w _ => harch w)

end ArtinPrimitiveRoots.A1.Theta
