import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.constantCell_finite_analytic
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_fourier_expansion

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-! ### The complex intertwined spherical factor -/

/-- The explicit value of the spherical section on a right root translate. -/
private theorem thetaN_sphC_mul_nC (s : ℂ) (M : GL (Fin 2) ℂ) (z : ℂ) :
    sphC s (QuotientGroup.mk M * nC z) =
      ((‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
        (‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
          ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) : ℝ) :
        ℂ) ^ (1 + 2 * s) := by
  have hmk : (QuotientGroup.mk M : PGL2 ℂ) * nC z = QuotientGroup.mk (M * upperM ℂ z) := rfl
  rw [hmk, sphC_mk]
  unfold sphericalC
  have hU : ((upperM ℂ z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, z; 0, 1] := rfl
  have hdet : ((M * upperM ℂ z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
      (M : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [Units.val_mul, Matrix.det_mul, hU]
    simp [Matrix.det_fin_two]
  have h10 : ((M * upperM ℂ z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    rw [Units.val_mul, hU]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((M * upperM ℂ z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    rw [Units.val_mul, hU]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hdet, h10, h11]

private theorem thetaN_GL_det_ne_zero (M : GL (Fin 2) ℂ) :
    (M : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
  have h := congrArg Matrix.det M.mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

private theorem thetaN_denom_pos (M : GL (Fin 2) ℂ) (z : ℂ) :
    0 < ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
  by_cases hc : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · have hd : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
      intro hd
      apply thetaN_GL_det_ne_zero M
      rw [Matrix.det_fin_two, hc, hd]
      ring
    rw [hc, zero_mul, zero_add]
    have : 0 < ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ := norm_pos_iff.mpr hd
    positivity
  · have : 0 < ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ := norm_pos_iff.mpr hc
    positivity

/-- The real ratio in the spherical section along a right root line. -/
private def thetaN_ratio (M : GL (Fin 2) ℂ) (z : ℂ) : ℝ :=
  ‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
    (‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)

private theorem thetaN_ratio_pos (M : GL (Fin 2) ℂ) (z : ℂ) : 0 < thetaN_ratio M z := by
  unfold thetaN_ratio
  have := thetaN_denom_pos M z
  have : 0 < ‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ := norm_pos_iff.mpr (thetaN_GL_det_ne_zero M)
  positivity

private theorem thetaN_ratio_contDiff (M : GL (Fin 2) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (thetaN_ratio M) := by
  unfold thetaN_ratio
  apply ContDiff.div contDiff_const
  · apply ContDiff.add contDiff_const
    apply ContDiff.norm_sq ℝ
    fun_prop
  · intro z
    exact (thetaN_denom_pos M z).ne'

/-- The intertwined complex spherical factor `M_ℂ(1/6) f°`. -/
private def thetaN_fC : PGL2 ℂ → ℂ := intertwineC (sphC (1 / 6))

private theorem thetaN_fC_eq : thetaN_fC = fun g => (Real.pi / (2 * (1 / 6 : ℂ))) * sphC (-(1 / 6)) g :=
  intertwineC_spherical (1 / 6) (by norm_num)

private theorem thetaN_fC_mul_nC (M : GL (Fin 2) ℂ) (z : ℂ) :
    thetaN_fC (QuotientGroup.mk M * nC z) =
      (Real.pi / (2 * (1 / 6 : ℂ))) * (((thetaN_ratio M z ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
  rw [thetaN_fC_eq]
  simp only
  rw [thetaN_sphC_mul_nC]
  congr 1
  rw [Complex.ofReal_cpow (thetaN_ratio_pos M z).le]
  congr 1
  push_cast
  ring

private theorem thetaN_fC_ne_zero (g : PGL2 ℂ) : thetaN_fC g ≠ 0 := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective g
  have h := thetaN_fC_mul_nC M 0
  have h0 : (QuotientGroup.mk M : PGL2 ℂ) * nC 0 = QuotientGroup.mk M := by
    have : nC 0 = 1 := by
      change (QuotientGroup.mk (upperM ℂ 0) : PGL2 ℂ) = QuotientGroup.mk 1
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [this, mul_one]
  rw [h0] at h
  rw [h]
  apply mul_ne_zero
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero hpi (by norm_num)
  · exact_mod_cast (Real.rpow_pos_of_pos (thetaN_ratio_pos M 0) _).ne'

private theorem thetaN_fC_smooth (g : PGL2 ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => thetaN_fC (g * nC z)) := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective g
  have heq : (fun z : ℂ => thetaN_fC (QuotientGroup.mk M * nC z)) =
      fun z => (Real.pi / (2 * (1 / 6 : ℂ))) * (((thetaN_ratio M z ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
    funext z
    exact thetaN_fC_mul_nC M z
  rw [heq]
  apply contDiff_const.mul
  have hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => thetaN_ratio M z ^ (2 / 3 : ℝ)) :=
    (thetaN_ratio_contDiff M).rpow_const_of_ne (fun z => (thetaN_ratio_pos M z).ne')
  exact Complex.ofRealCLM.contDiff.comp hr

private theorem thetaN_ratio_upper (x : ℂ) (M : GL (Fin 2) ℂ) (z : ℂ) :
    thetaN_ratio (upperM ℂ x * M) z = thetaN_ratio M z := by
  have hU : ((upperM ℂ x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, x; 0, 1] := rfl
  have hdet : ((upperM ℂ x * M : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
      (M : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [Units.val_mul, Matrix.det_mul, hU]
    simp [Matrix.det_fin_two]
  have h10 : ((upperM ℂ x * M : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    rw [Units.val_mul, hU]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((upperM ℂ x * M : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    rw [Units.val_mul, hU]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold thetaN_ratio
  rw [hdet, h10, h11]

private theorem thetaN_fC_jointSmooth (g : PGL2 ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℂ => thetaN_fC (nC p.1 * g * nC p.2)) := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective g
  have heq : (fun p : ℂ × ℂ => thetaN_fC (nC p.1 * QuotientGroup.mk M * nC p.2)) =
      fun p => (Real.pi / (2 * (1 / 6 : ℂ))) * (((thetaN_ratio M p.2 ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by
    funext p
    have hmk : nC p.1 * (QuotientGroup.mk M : PGL2 ℂ) =
        QuotientGroup.mk (upperM ℂ p.1 * M) := rfl
    rw [hmk, thetaN_fC_mul_nC, thetaN_ratio_upper]
  rw [heq]
  apply contDiff_const.mul
  have hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => thetaN_ratio M z ^ (2 / 3 : ℝ)) :=
    (thetaN_ratio_contDiff M).rpow_const_of_ne (fun z => (thetaN_ratio_pos M z).ne')
  exact Complex.ofRealCLM.contDiff.comp (hr.comp contDiff_snd)

private theorem thetaN_fC_isSection :
    IsSectionC (-(1 / 6)) thetaN_fC ∧ Continuous thetaN_fC := by
  obtain ⟨hsec, hcont⟩ := sphC_isSection (-(1 / 6))
  rw [thetaN_fC_eq]
  refine ⟨?_, continuous_const.mul hcont⟩
  intro x y g
  simp only
  rw [hsec x y g]
  ring

/-! ### The Weyl-twisted global datum carrying the intertwined sections -/

/-- The same global datum with every torus representation replaced by its Weyl conjugate. -/
private def thetaNWeylDatum {P : CoverPackage D S H A} (G : GlobalDatum P) : GlobalDatum P where
  T v := (G.T v).weyl
  B v hv := (G.B v hv).weyl
  Alag := G.Alag
  alag_cubes := G.alag_cubes
  alag_lagrangian := G.alag_lagrangian
  lam := G.lam
  ω v y := G.ω v y⁻¹
  lam_equiv := fun v y hy x => G.lam_equiv v y⁻¹ (inv_mem hy) x
  lam_ne := G.lam_ne
  alag_tame := G.alag_tame
  ω_tame := fun v hv y hy => G.ω_tame v hv y⁻¹ (inv_mem hy)
  lam_tame := by
    intro v hv k
    change G.lam v ((G.B v hv).e (-k)) = _
    rw [G.lam_tame v hv (-k)]
    simp only [neg_eq_zero]
  ω_rational := by
    intro δ hδ
    have h := G.ω_rational δ⁻¹ (fun v => by rw [map_inv]; exact inv_mem (hδ v))
    simpa only [map_inv] using h

private theorem thetaN_sphWeyl_spec {P : CoverPackage D S H A} (G : GlobalDatum P)
    (v : FinPlace F) (hv : v ∉ S.Sf) (s : ℂ) :
    IsSection (P.loc v) (G.T v).weyl (-s) (sphWeyl P G v hv s) ∧
      sphWeyl P G v hv s 1 = (G.B v hv).weyl.e 0 ∧
      ∀ g, ∀ k ∈ (P.tame v hv).Kmax, sphWeyl P G v hv s (g * k) = sphWeyl P G v hv s g := by
  have h := (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
    (fun h => hv (S.over6 v h)) (-s)).choose_spec
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The `M(1/6)`-data of the common family as a global section of the Weyl-twisted datum. -/
private def thetaNSection {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) :
    GlobalSection P (thetaNWeylDatum N.G) (-(1 / 6)) where
  T0 := B.Fam.T0
  sub := by
    have h := (B.Fam.sec (1 / 6)).sub
    rwa [B.Fam.T0_eq] at h
  f := fun v => show (P.loc v).L → (N.G.T v).V from famM B.Fam v
  f_sec := by
    intro v
    change IsSection (P.loc v) (N.G.T v).weyl (-(1 / 6)) (famM B.Fam v)
    unfold famM
    split_ifs with hv
    · exact (intertwine_isSection (P.loc v) (N.G.T v) (N.μ v) (1 / 6) (by norm_num) _
        ((B.Fam.sec (1 / 6)).f_sec v)).2
    · exact (thetaN_sphWeyl_spec N.G v _ (1 / 6)).1
  f_sph := by
    intro v hv
    change famM B.Fam v 1 = _ ∧ ∀ g, ∀ k ∈ _, famM B.Fam v (g * k) = famM B.Fam v g
    unfold famM
    rw [dite_cond_eq_false (eq_false hv)]
    exact (thetaN_sphWeyl_spec N.G v _ (1 / 6)).2
  fC := fun _ => thetaN_fC
  fC_sec := fun _ => thetaN_fC_isSection
  fC_smooth := fun _ g => thetaN_fC_smooth g
  fC_jointSmooth := fun _ g => thetaN_fC_jointSmooth g

/-- The intertwined scalar section of the constant term. -/
private def thetaNPhi {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (g : P.tc.G) : ℂ :=
  scalarOf P N.G (famM B.Fam) (fun _ => intertwineC (sphC (1 / 6))) g

private theorem thetaNPhi_eq {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) :
    thetaNPhi B = scalarOf P (thetaNWeylDatum N.G) (thetaNSection B).f (thetaNSection B).fC :=
  rfl

private theorem thetaFamilyBaseN_eq {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (g : P.tc.G) :
    thetaFamilyBaseN B g = (κF F)⁻¹ * resCprod B.Fam.T0 *
      ∑' δ : Fˣ ⧸ N.G.Δ, thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * g) := rfl

/-! ### Invariances of the intertwined scalar section -/

private theorem thetaNPhi_q {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (x : P.RP) :
    thetaNPhi B (P.q x) =
      (∏ᶠ v, N.G.lam v (famM B.Fam v (P.compF v x))) * ∏ w, thetaN_fC (P.compC w x) :=
  (scalarOf_q P (thetaNWeylDatum N.G) (thetaNSection B) x).2

private theorem thetaN_famM_Kmax {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (v : FinPlace F) (hv : v ∉ S.Sf)
    (g k : (P.loc v).L) (hk : k ∈ (P.tame v hv).Kmax) :
    famM B.Fam v (g * k) = famM B.Fam v g := by
  have hvT : v ∉ (thetaNSection B).T0 := by
    change v ∉ B.Fam.T0
    rw [B.level]
    exact hv
  exact ((thetaNSection B).f_sph v hvT).2 g k hk

private theorem thetaNPhi_inv {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) :
    (∀ b ∈ Bstar (thetaNWeylDatum N.G), ∀ g, thetaNPhi B (P.tc.rat b * g) = thetaNPhi B g) ∧
    (∀ ζ g, thetaNPhi B (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaNPhi B g) := by
  obtain ⟨h1, -, -, h4⟩ := scalarOf_invariance P (thetaNWeylDatum N.G) (thetaNSection B)
  exact ⟨h1, h4⟩

private theorem thetaN_upperGL_mem {P : CoverPackage D S H A} (G : GlobalDatum P) (x : F) :
    upperGL x ∈ Bstar G := by
  refine ⟨?_, 1, one_mem _, ?_⟩
  · simp [upperGL]
  · simp [upperGL]

private theorem thetaN_diagGL_mem {P : CoverPackage D S H A} (G : GlobalDatum P) (d : Fˣ)
    (hd : d ∈ G.Δ) : diagGL d ∈ Bstar G := by
  refine ⟨?_, d, hd, ?_⟩
  · simp [diagGL]
  · simp [diagGL]

private theorem thetaN_diagGL_mul (a b : Fˣ) : diagGL (a * b) = diagGL a * diagGL b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two]

private theorem thetaNPhi_diag_out {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (a : Fˣ) (g : P.tc.G) :
    thetaNPhi B (P.tc.rat (diagGL (Quotient.out (QuotientGroup.mk a : Fˣ ⧸ N.G.Δ))) * g) =
      thetaNPhi B (P.tc.rat (diagGL a) * g) := by
  set o := Quotient.out (QuotientGroup.mk a : Fˣ ⧸ N.G.Δ)
  have ho : (QuotientGroup.mk o : Fˣ ⧸ N.G.Δ) = QuotientGroup.mk a := QuotientGroup.out_eq' _
  have hd : a⁻¹ * o ∈ N.G.Δ := QuotientGroup.eq.mp ho.symm
  have hsplit : o = (a⁻¹ * o) * a := by rw [mul_comm, mul_inv_cancel_left]
  rw [hsplit, thetaN_diagGL_mul, map_mul, mul_assoc]
  exact (thetaNPhi_inv B).1 _ (thetaN_diagGL_mem (thetaNWeylDatum N.G) _ hd) _

/-- Rational upper triangular left invariance of the undifferentiated constant term. -/
private theorem thetaFamilyBaseN_borel {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (b : GL (Fin 2) F)
    (hb : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (g : P.tc.G) :
    thetaFamilyBaseN B (P.tc.rat b * g) = thetaFamilyBaseN B g := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have h := congrArg Matrix.det b.mul_inv
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdet' : (b : Matrix (Fin 2) (Fin 2) F).det =
      (b : Matrix (Fin 2) (Fin 2) F) 0 0 * (b : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.det_fin_two, hb]; ring
  have h00 : (b : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h; apply hdet; rw [hdet', h, zero_mul]
  have h11 : (b : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h; apply hdet; rw [hdet', h, mul_zero]
  let t : Fˣ := Units.mk0 _ (div_ne_zero h00 h11)
  let c : Fˣ := Units.mk0 _ h11
  have hterm (a : Fˣ) :
      thetaNPhi B (P.tc.rat (diagGL a) * (P.tc.rat b * g)) =
        thetaNPhi B (P.tc.rat (diagGL (a * t)) * g) := by
    have hmat : diagGL a * b = scalarGL c *
        (upperGL ((a : F) * (b : Matrix (Fin 2) (Fin 2) F) 0 1 / (b : Matrix (Fin 2) (Fin 2) F) 1 1) *
          diagGL (a * t)) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp only [Units.val_mul, diagGL, upperGL, scalarGL, t, c]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hb] <;> field_simp
    rw [← mul_assoc, ← map_mul, hmat, map_mul, P.tc.rat_scalar, one_mul, map_mul, mul_assoc]
    exact (thetaNPhi_inv B).1 _ (thetaN_upperGL_mem (thetaNWeylDatum N.G) _) _
  have h1 : ∀ δ : Fˣ ⧸ N.G.Δ,
      thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * (P.tc.rat b * g)) =
        thetaNPhi B (P.tc.rat (diagGL (Quotient.out (δ * (QuotientGroup.mk t : Fˣ ⧸ N.G.Δ)))) * g) := by
    intro δ
    rw [hterm]
    have hq : (QuotientGroup.mk (Quotient.out δ * t) : Fˣ ⧸ N.G.Δ) =
        δ * QuotientGroup.mk t := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [← hq, thetaNPhi_diag_out]
  have h2 := (Equiv.mulRight (QuotientGroup.mk t : Fˣ ⧸ N.G.Δ)).tsum_eq
    (fun δ => thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * g))
  simp only [Equiv.coe_mulRight] at h2
  rw [thetaFamilyBaseN_eq, thetaFamilyBaseN_eq, tsum_congr h1, h2]

private theorem thetaNPhi_Kext {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (X k : P.tc.G)
    (hk : k ∈ P.tc.Kext) : thetaNPhi B (X * k) = thetaNPhi B X := by
  obtain ⟨xk, hq, hext, hS, hC⟩ := P.Kext_components k hk
  obtain ⟨x0, rfl⟩ := P.q_surj X
  rw [← hq, ← map_mul, thetaNPhi_q, thetaNPhi_q]
  congr 1
  · apply finprod_congr
    intro v
    rw [map_mul]
    by_cases hv : v ∈ S.Sf
    · rw [hS v hv, mul_one]
    · rw [thetaN_famM_Kmax B v hv _ _ (hext v hv)]
  · apply Finset.prod_congr rfl
    intro w _
    rw [map_mul, hC w, mul_one]

private theorem thetaFamilyBaseN_Kext {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (g k : P.tc.G)
    (hk : k ∈ P.tc.Kext) : thetaFamilyBaseN B (g * k) = thetaFamilyBaseN B g := by
  have h : ∀ δ : Fˣ ⧸ N.G.Δ,
      thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * (g * k)) =
        thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * g) := by
    intro δ
    rw [← mul_assoc]
    exact thetaNPhi_Kext B _ k hk
  rw [thetaFamilyBaseN_eq, thetaFamilyBaseN_eq, tsum_congr h]

private theorem thetaFamilyBaseN_genuine {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (ζ : rootsOfUnity 3 ℂ) (g : P.tc.G) :
    thetaFamilyBaseN B (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaFamilyBaseN B g := by
  have h : ∀ δ : Fˣ ⧸ N.G.Δ,
      thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * (P.tc.z ζ * g)) =
        ((ζ : ℂˣ) : ℂ) * thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * g) := by
    intro δ
    rw [← mul_assoc, ← P.tc.z_central ζ, mul_assoc]
    exact (thetaNPhi_inv B).2 ζ _
  rw [thetaFamilyBaseN_eq, thetaFamilyBaseN_eq, tsum_congr h, tsum_mul_left]
  ring

private theorem thetaN_upperM_zero : (QuotientGroup.mk (upperM ℂ 0) : PGL2 ℂ) = 1 := by
  change (QuotientGroup.mk (upperM ℂ 0) : PGL2 ℂ) = QuotientGroup.mk 1
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem thetaN_fC_diag_left (y : ℂˣ) (hy : ‖(y : ℂ)‖ = 1) (Z : PGL2 ℂ) :
    thetaN_fC (QuotientGroup.mk (diagM ℂ y) * Z) = thetaN_fC Z := by
  have h := thetaN_fC_isSection.1 0 y Z
  rw [thetaN_upperM_zero, one_mul] at h
  rw [h, Complex.normSq_eq_norm_sq, hy]
  simp

private theorem thetaN_map_diag_comm (e : F →+* ℂ) (δ : Fˣ) (y : ℂˣ) :
    Matrix.GeneralLinearGroup.map e (diagGL δ) * diagM ℂ y =
      diagM ℂ y * Matrix.GeneralLinearGroup.map e (diagGL δ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diagGL, diagM, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem thetaN_compC_atComplex (w w' : InfinitePlace F) (zc : ℂˣ)
    (hzc : ‖(zc : ℂ)‖ = 1) : ‖((S.compC w' (S.atComplex w zc) : ℂˣ) : ℂ)‖ = 1 := by
  change ‖(Function.update (fun _ => (1 : ℂ)) w (zc : ℂ)) w'‖ = 1
  by_cases h : w' = w
  · subst h
    simpa using hzc
  · rw [Function.update_of_ne h]
    simp

private theorem thetaN_compU_atComplex (w : InfinitePlace F) (zc : ℂˣ) (v : S.Sf) :
    S.compU v (S.atComplex w zc) = 1 := by
  apply Units.ext
  rfl

private theorem thetaNPhi_radial {P : CoverPackage D S H A} {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (w : InfinitePlace F) (zc : ℂˣ)
    (hzc : ‖(zc : ℂ)‖ = 1) (δ : Fˣ) (g : P.tc.G) :
    thetaNPhi B (P.tc.rat (diagGL δ) * (P.tc.aS (S.atComplex w zc) * g)) =
      thetaNPhi B (P.tc.rat (diagGL δ) * g) := by
  obtain ⟨xa, hxa, hxaF, hxaC⟩ := P.aS_components (S.atComplex w zc)
  obtain ⟨xg, rfl⟩ := P.q_surj g
  have e1 : P.tc.rat (diagGL δ) * (P.tc.aS (S.atComplex w zc) * P.q xg) =
      P.q (P.ratRP (diagGL δ) * xa * xg) := by
    rw [map_mul, map_mul, P.q_ratRP, hxa, mul_assoc]
  have e2 : P.tc.rat (diagGL δ) * P.q xg = P.q (P.ratRP (diagGL δ) * xg) := by
    rw [map_mul, P.q_ratRP]
  rw [e1, e2, thetaNPhi_q, thetaNPhi_q]
  congr 1
  · apply finprod_congr
    intro v
    have hv1 : P.compF v xa = 1 := by
      rw [hxaF v]
      split_ifs with hv
      · rw [thetaN_compU_atComplex, (P.loc v).a_one]
      · rfl
    simp only [map_mul, hv1, mul_one]
  · apply Finset.prod_congr rfl
    intro w' _
    simp only [map_mul, hxaC w', P.compC_ratRP]
    rw [← QuotientGroup.mk_mul, thetaN_map_diag_comm, QuotientGroup.mk_mul, mul_assoc,
      thetaN_fC_diag_left _ (thetaN_compC_atComplex w w' zc hzc)]

private theorem thetaFamilyBaseN_radial {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (w : InfinitePlace F) (zc : ℂˣ) (hzc : ‖(zc : ℂ)‖ = 1) (g : P.tc.G) :
    thetaFamilyBaseN B (P.tc.aS (S.atComplex w zc) * g) = thetaFamilyBaseN B g := by
  have h : ∀ δ : Fˣ ⧸ N.G.Δ,
      thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * (P.tc.aS (S.atComplex w zc) * g)) =
        thetaNPhi B (P.tc.rat (diagGL (Quotient.out δ)) * g) :=
    fun δ => thetaNPhi_radial B w zc hzc _ g
  rw [thetaFamilyBaseN_eq, thetaFamilyBaseN_eq, tsum_congr h]

/-! ### Left translations and scalars through the derivative fold -/

private theorem thetaN_deriv_left {P : CoverPackage D S H A} (m : InfinitePlace F → ℤ)
    (Ψ : P.tc.G → ℂ) (a g : P.tc.G) :
    thetaFamilyDeriv P m Ψ (a * g) = thetaFamilyDeriv P m (fun x => Ψ (a * x)) g :=
  thetaFamilyDeriv_congr_rootOrbit m Ψ (fun x => Ψ (a * x)) (a * g) g Set.univ isOpen_univ
    trivial (fun x _ => by simp only [mul_assoc])

private theorem thetaN_rootStep_const_mul {P : CoverPackage D S H A}
    (w : InfinitePlace F) (m : ℤ) (Ψ : P.tc.G → ℂ) (c : ℂ) (g : P.tc.G) :
    thetaRootStep w m (fun h => c * Ψ h) g = c * thetaRootStep w m Ψ g := by
  by_cases hc : c = 0
  · subst c
    simp [thetaRootStep]
  · let Φ : ℂ → ℂ := fun z => Ψ (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))
    let cUnit : ℂˣ := Units.mk0 c hc
    let cEquiv : ℂ ≃L[ℝ] ℂ := (cUnit.mulLeftLinearEquiv ℝ ℂ).toContinuousLinearEquiv
    have hcEquiv (z : ℂ) : cEquiv z = c * z := by
      simp [cEquiv, cUnit, Units.mulLeftLinearEquiv_apply]
    have hcurve :
        (fun z : ℂ => (fun h => c * Ψ h) (g * P.tc.nS
          (Multiplicative.ofAdd
            ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) =
        (fun z => cEquiv (Φ z)) := by
      funext z
      exact (hcEquiv (Φ z)).symm
    have hval (v : ℂ) : fderiv ℝ (fun z : ℂ => cEquiv (Φ z)) 0 v = c * fderiv ℝ Φ 0 v := by
      have h := cEquiv.comp_fderiv (f := Φ) (x := 0)
      have h' := congrArg (fun T : ℂ →L[ℝ] ℂ => T v) h
      change fderiv ℝ (cEquiv ∘ Φ) 0 v = _
      rw [h']
      exact hcEquiv _
    change fderiv ℝ (fun z : ℂ => (fun h => c * Ψ h)
        (g * P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
      (m : ℂ) * Complex.I * fderiv ℝ (fun z : ℂ => (fun h => c * Ψ h)
        (g * P.tc.nS (Multiplicative.ofAdd
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I = _
    rw [hcurve, hval, hval]
    dsimp [thetaRootStep, Φ]
    ring

private theorem thetaN_deriv_const_mul {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (c : ℂ) (g : P.tc.G) :
    thetaFamilyDeriv P m (fun h => c * Ψ h) g = c * thetaFamilyDeriv P m Ψ g := by
  classical
  have hFold (ws : List (InfinitePlace F)) :
      ∀ g, ws.foldr (fun w acc => thetaRootStep w (m w) acc) (fun h => c * Ψ h) g =
        c * ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ g := by
    induction ws with
    | nil => intro g; rfl
    | cons w ws ih =>
        intro g
        have hacc : ws.foldr (fun w acc => thetaRootStep w (m w) acc) (fun h => c * Ψ h) =
            fun h => c * ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ h := by
          funext h
          exact ih h
        change thetaRootStep w (m w)
            (ws.foldr (fun w acc => thetaRootStep w (m w) acc) (fun h => c * Ψ h)) g =
          c * thetaRootStep w (m w)
            (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) g
        rw [hacc]
        exact thetaN_rootStep_const_mul w (m w)
          (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) c g
  change (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaRootStep w (m w) acc) (fun h => c * Ψ h)) g =
    c * (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaRootStep w (m w) acc) Ψ) g
  exact hFold (Finset.univ : Finset (InfinitePlace F)).toList g

/-! ### The derivative fold in root-chart coordinates -/

/-- One right root step in the archimedean root chart. -/
private def thetaN_chartStep (w : InfinitePlace F) (m : ℤ)
    (f : (InfinitePlace F → ℂ) → ℂ) : (InfinitePlace F → ℂ) → ℂ := fun x =>
  fderiv ℝ (fun z : ℂ => f (x + Pi.single w z)) 0 1 -
    (m : ℂ) * Complex.I * fderiv ℝ (fun z : ℂ => f (x + Pi.single w z)) 0 Complex.I

/-- The one-variable complex derivative vector `(∂₁ - m i ∂₂) φ`. -/
private def thetaN_D (m : ℤ) (φ : ℂ → ℂ) : ℂ → ℂ := fun z =>
  fderiv ℝ φ z 1 - (m : ℂ) * Complex.I * fderiv ℝ φ z Complex.I

private def thetaN_groupStep {P : CoverPackage D S H A} (w : InfinitePlace F) (m : ℤ)
    (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ := fun g =>
  fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
      (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 1 -
    (m : ℂ) * Complex.I *
      fderiv ℝ (fun z : ℂ => Ψ (g * P.tc.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) 0 Complex.I

private theorem thetaN_nInf_add {P : CoverPackage D S H A} (x y : InfinitePlace F → ℂ) :
    nInf P (x + y) = nInf P x * nInf P y := by
  have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y) =
      ((0, x) : S.FS) + ((0, y) : S.FS) := by
    ext v <;> simp
  change P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y)) =
    P.tc.nS (Multiplicative.ofAdd ((0, x) : S.FS)) *
      P.tc.nS (Multiplicative.ofAdd ((0, y) : S.FS))
  rw [hp, ofAdd_add, map_mul]

private theorem thetaN_fold_chart {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (ws : List (InfinitePlace F))
    (Ψ : P.tc.G → ℂ) (g : P.tc.G) (x : InfinitePlace F → ℂ) :
    ws.foldr (fun w acc => thetaN_groupStep w (m w) acc) Ψ (g * nInf P x) =
      ws.foldr (fun w acc => thetaN_chartStep w (m w) acc)
        (fun y => Ψ (g * nInf P y)) x := by
  revert x
  induction ws with
  | nil => intro x; rfl
  | cons w ws ih =>
      intro x
      have hcurve :
          (fun z : ℂ => ws.foldr (fun w acc => thetaN_groupStep w (m w) acc) Ψ
            (g * nInf P x * P.tc.nS (Multiplicative.ofAdd
              ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)))) =
          (fun z => ws.foldr (fun w acc => thetaN_chartStep w (m w) acc)
            (fun y => Ψ (g * nInf P y)) (x + Pi.single w z)) := by
        funext z
        have hsingle : P.tc.nS (Multiplicative.ofAdd
            ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z)) =
            nInf P (Pi.single w z) := rfl
        rw [mul_assoc, hsingle, ← thetaN_nInf_add]
        exact ih (x + Pi.single w z)
      change thetaN_groupStep w (m w)
          (ws.foldr (fun w acc => thetaN_groupStep w (m w) acc) Ψ) (g * nInf P x) =
        thetaN_chartStep w (m w)
          (ws.foldr (fun w acc => thetaN_chartStep w (m w) acc)
            (fun y => Ψ (g * nInf P y))) x
      simp only [thetaN_groupStep, thetaN_chartStep]
      rw [hcurve]

private theorem thetaN_deriv_chart {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ) (g : P.tc.G) :
    thetaFamilyDeriv P m Ψ g =
      ((Finset.univ : Finset (InfinitePlace F)).toList).foldr
        (fun w acc => thetaN_chartStep w (m w) acc) (fun x => Ψ (g * nInf P x)) 0 := by
  have h := thetaN_fold_chart m (Finset.univ : Finset (InfinitePlace F)).toList Ψ g 0
  change ((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaN_groupStep w (m w) acc) Ψ g =
    ((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaN_chartStep w (m w) acc) (fun x => Ψ (g * nInf P x)) 0
  have hzero : P.tc.nS (Multiplicative.ofAdd
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), (0 : InfinitePlace F → ℂ))) = 1 := by
    change P.tc.nS (1 : Multiplicative S.FS) = 1
    exact map_one P.tc.nS
  simpa [nInf, hzero] using h

/-- Finite sums of products of one-variable functions of the root coordinates. -/
private def thetaN_sumProd {ι : Type} (T : Finset ι) (a : ι → ℂ)
    (φ : ι → InfinitePlace F → ℂ → ℂ) (x : InfinitePlace F → ℂ) : ℂ :=
  ∑ i ∈ T, a i * ∏ u, φ i u (x u)

private theorem thetaN_chartStep_sumProd {ι : Type} (T : Finset ι) (a : ι → ℂ)
    (φ : ι → InfinitePlace F → ℂ → ℂ) (w : InfinitePlace F) (m : ℤ)
    (hφ : ∀ i, Differentiable ℝ (φ i w)) :
    thetaN_chartStep w m (thetaN_sumProd T a φ) =
      thetaN_sumProd T a (fun i u => if u = w then thetaN_D m (φ i w) else φ i u) := by
  classical
  funext x
  let C : ι → ℂ := fun i => a i * ∏ u ∈ Finset.univ.erase w, φ i u (x u)
  have hrest (i : ι) (z : ℂ) :
      ∏ u ∈ Finset.univ.erase w, φ i u ((x + Pi.single w z : InfinitePlace F → ℂ) u) =
        ∏ u ∈ Finset.univ.erase w, φ i u (x u) := by
    apply Finset.prod_congr rfl
    intro u hu
    have huw : u ≠ w := Finset.ne_of_mem_erase hu
    simp [Pi.single_eq_of_ne huw]
  have hcurve : (fun z : ℂ => thetaN_sumProd T a φ (x + Pi.single w z)) =
      fun z => ∑ i ∈ T, C i * φ i w (x w + z) := by
    funext z
    unfold thetaN_sumProd
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), hrest]
    simp only [C, Pi.add_apply, Pi.single_eq_same]
    ring
  have hderiv : HasFDerivAt (fun z : ℂ => ∑ i ∈ T, C i * φ i w (x w + z))
      (∑ i ∈ T, C i • (fderiv ℝ (φ i w) (x w))) 0 := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hin : HasFDerivAt (fun z : ℂ => x w + z) (ContinuousLinearMap.id ℝ ℂ) 0 :=
      (hasFDerivAt_id (0 : ℂ)).const_add (x w)
    have hφi : HasFDerivAt (φ i w) (fderiv ℝ (φ i w) (x w)) (x w + 0) := by
      rw [add_zero]
      exact (hφ i (x w)).hasFDerivAt
    have hcomp := hφi.comp (0 : ℂ) hin
    simpa using hcomp.const_mul (C i)
  have hval (v : ℂ) : fderiv ℝ (fun z : ℂ => thetaN_sumProd T a φ (x + Pi.single w z)) 0 v =
      ∑ i ∈ T, C i * fderiv ℝ (φ i w) (x w) v := by
    rw [hcurve, hderiv.fderiv]
    simp
  unfold thetaN_chartStep
  rw [hval, hval]
  unfold thetaN_sumProd
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have hrest' : ∏ u ∈ Finset.univ.erase w,
      (if u = w then thetaN_D m (φ i w) else φ i u) (x u) =
        ∏ u ∈ Finset.univ.erase w, φ i u (x u) := by
    apply Finset.prod_congr rfl
    intro u hu
    simp [Finset.ne_of_mem_erase hu]
  rw [hrest']
  simp only [if_pos, C, thetaN_D]
  ring

private theorem thetaN_fold_sumProd {ι : Type} (T : Finset ι) (a : ι → ℂ)
    (m : InfinitePlace F → ℤ) (φ : ι → InfinitePlace F → ℂ → ℂ)
    (hφ : ∀ i u, Differentiable ℝ (φ i u)) (ws : List (InfinitePlace F)) (hws : ws.Nodup) :
    ws.foldr (fun w acc => thetaN_chartStep w (m w) acc) (thetaN_sumProd T a φ) =
      thetaN_sumProd T a (fun i u => if u ∈ ws then thetaN_D (m u) (φ i u) else φ i u) := by
  classical
  induction ws with
  | nil =>
      simp
  | cons w ws ih =>
      rw [List.nodup_cons] at hws
      obtain ⟨hw, hws⟩ := hws
      change thetaN_chartStep w (m w)
          (ws.foldr (fun w acc => thetaN_chartStep w (m w) acc) (thetaN_sumProd T a φ)) = _
      rw [ih hws]
      have hdiff : ∀ i, Differentiable ℝ
          ((fun i u => if u ∈ ws then thetaN_D (m u) (φ i u) else φ i u) i w) := by
        intro i
        simp only [if_neg hw]
        exact hφ i w
      rw [thetaN_chartStep_sumProd T a _ w (m w) hdiff]
      congr 1
      funext i u
      by_cases huw : u = w
      · subst huw
        simp [hw]
      · simp [huw]

/-! ### Local constancy of the finite factors in the torus parameter -/

private theorem thetaN_muThree_one : muThree D (1 : rootsOfUnity 6 F) = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [muThree]

private theorem thetaN_hilb_sixth (v : FinPlace F) (u0 u1 : (v.adicCompletion F)ˣ)
    (h6 : ∃ c : (v.adicCompletion F)ˣ, u1 = c ^ 6) : H.hilb v u0 u1 = 1 := by
  have h1 := H.sixth_power v u1 u0 h6
  have h2 := H.skew v u0 u1
  rw [h1, mul_one] at h2
  exact h2

/-- Near `u0`, right translation by the torus element `a(u)` before a fixed `Y` does not change
an intertwined finite section, uniformly in the left argument. -/
private theorem thetaN_famM_torus_nhds {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (v : S.Sf) (u0 : (v.1.adicCompletion F)ˣ) (Y : (P.loc v.1).L) :
    ∀ᶠ u in 𝓝 u0, ∀ X : (P.loc v.1).L,
      famM B.Fam v.1 (X * (P.loc v.1).a u * Y) = famM B.Fam v.1 (X * (P.loc v.1).a u0 * Y) := by
  let L := P.loc v.1
  obtain ⟨m, hm, hlev⟩ := ((thetaNSection B).f_sec v.1).2.2
  let W : Set L.L := {k | Y⁻¹ * k * Y ∈ L.Kc m}
  have hcont : Continuous (fun k : L.L => Y⁻¹ * k * Y) := by fun_prop
  have hWopen : IsOpen W := by
    change IsOpen ((fun k : L.L => Y⁻¹ * k * Y) ⁻¹' (L.Kc m : Set L.L))
    exact (L.Kc_open m hm).preimage hcont
  have hWone : (1 : L.L) ∈ W := by simp [W]
  obtain ⟨m', hm', hsub⟩ := L.Kc_nhds W (hWopen.mem_nhds hWone)
  let K := v.1.adicCompletion F
  let V : Set K := B.Uv v ∩ (fun x : K => x - 1) ⁻¹' ball v.1 (m' : ℤ)
  have hballopen : IsOpen (ball v.1 (m' : ℤ)) := by
    change IsOpen {x : K | Valued.v x ≤ WithZero.exp (-(m' : ℤ))}
    exact v.1.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hsubcont : Continuous (fun x : K => x - 1) := continuous_sub_right 1
  have hVopen : IsOpen V := (B.open_Uv v).inter (hballopen.preimage hsubcont)
  have hVone : (1 : K) ∈ V := by
    refine ⟨B.one_Uv v, ?_⟩
    change Valued.v ((1 : K) - 1) ≤ WithZero.exp (-(m' : ℤ))
    rw [sub_self, map_zero]
    exact zero_le
  let φ : Kˣ → K := fun u => ((u0⁻¹ * u : Kˣ) : K)
  have hφcont : Continuous φ := Units.continuous_val.comp (continuous_const.mul continuous_id)
  have hφu0 : φ u0 = 1 := by simp [φ]
  have hnhds : φ ⁻¹' V ∈ 𝓝 u0 := by
    apply hφcont.continuousAt.preimage_mem_nhds
    rw [hφu0]
    exact hVopen.mem_nhds hVone
  filter_upwards [hnhds] with u hu X
  obtain ⟨huU, huB⟩ := hu
  set u1 : Kˣ := u0⁻¹ * u with hu1
  have hu : u = u0 * u1 := by rw [hu1, mul_inv_cancel_left]
  have h6 : ∃ c : Kˣ, u1 = c ^ 6 := by
    obtain ⟨c, hc⟩ := B.sixth_Uv v (u1 : K) huU
    exact ⟨c, Units.ext hc⟩
  have hmul : L.a u = L.a u0 * L.a u1 := by
    have h := L.a_mul u0 u1
    rw [thetaN_hilb_sixth v.1 u0 u1 h6, thetaN_muThree_one, map_one, one_mul, ← hu] at h
    exact h.symm
  have hK : L.a u1 ∈ L.Kc m' := L.a_Kc m' hm' u1 huB
  have harg : X * L.a u * Y = (X * L.a u0 * Y) * (Y⁻¹ * L.a u1 * Y) := by
    rw [hmul]; group
  change famM B.Fam v.1 (X * L.a u * Y) = famM B.Fam v.1 (X * L.a u0 * Y)
  rw [harg]
  exact hlev _ _ (hsub hK)

/-- Export the constant-term invariances, torus continuity and T7 radiality for the same normalized constant term.
Guide: sol-thin-thglobal/PROOFS.md:1200–1210.
Uses thetaFamilyBaseN, theta_constantTerm, intertwineC_spherical and left-translation commutation with thetaFamilyDeriv. -/
theorem thetaN_fields {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (L : SChar S) (hL : L ∈ 𝓛) :
    (∀ (b : GL (Fin 2) F), (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      ∀ g, thetaFamilyThetaN B L (P.tc.rat b * g) = thetaFamilyThetaN B L g) ∧
    (∀ g, ∀ k ∈ P.tc.Kext, thetaFamilyThetaN B L (g * k) = thetaFamilyThetaN B L g) ∧
    (∀ ζ g, thetaFamilyThetaN B L (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaFamilyThetaN B L g) ∧
    (∀ g h, Continuous fun y : S.FSˣ => thetaFamilyThetaN B L (g * P.tc.aS y * h)) ∧
    (∀ (w : InfinitePlace F) (zc : ℂˣ), ‖(zc : ℂ)‖ = 1 →
      ∀ g, thetaFamilyThetaN B L (P.tc.aS (S.atComplex w zc) * g) = thetaFamilyThetaN B L g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb g
    change (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaFamilyBaseN B) (P.tc.rat b * g) =
      (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m (thetaFamilyBaseN B) g
    have hfun : (fun x => thetaFamilyBaseN B (P.tc.rat b * x)) = thetaFamilyBaseN B :=
      funext fun x => thetaFamilyBaseN_borel B b hb x
    rw [thetaN_deriv_left, hfun]
  · intro g k hk
    change (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaFamilyBaseN B) (g * k) =
      (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m (thetaFamilyBaseN B) g
    have h := thetaFamilyDeriv_congr_rootOrbit L.m (thetaFamilyBaseN B) (thetaFamilyBaseN B)
      (g * k) g Set.univ isOpen_univ trivial (fun x _ => by
        have hcomm : k * nInf P x = nInf P x * k :=
          P.tc.Kext_comm_S k hk _ (P.tc.nS_mem _)
        rw [mul_assoc, hcomm, ← mul_assoc, thetaFamilyBaseN_Kext B _ k hk])
    rw [h]
  · intro ζ g
    change (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaFamilyBaseN B) (P.tc.z ζ * g) =
      ((ζ : ℂˣ) : ℂ) *
        ((thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m (thetaFamilyBaseN B) g)
    have hfun : (fun x => thetaFamilyBaseN B (P.tc.z ζ * x)) =
        fun x => ((ζ : ℂˣ) : ℂ) * thetaFamilyBaseN B x :=
      funext fun x => thetaFamilyBaseN_genuine B ζ x
    rw [thetaN_deriv_left, hfun, thetaN_deriv_const_mul]
    ring
  · sorry
  · intro w zc hzc g
    change (thetaNormalizationScalar N)⁻¹ *
        thetaFamilyDeriv P L.m (thetaFamilyBaseN B) (P.tc.aS (S.atComplex w zc) * g) =
      (thetaNormalizationScalar N)⁻¹ * thetaFamilyDeriv P L.m (thetaFamilyBaseN B) g
    have hfun : (fun x => thetaFamilyBaseN B (P.tc.aS (S.atComplex w zc) * x)) =
        thetaFamilyBaseN B :=
      funext fun x => thetaFamilyBaseN_radial B w zc hzc x
    rw [thetaN_deriv_left, hfun]
end ArtinPrimitiveRoots.A1.Theta
