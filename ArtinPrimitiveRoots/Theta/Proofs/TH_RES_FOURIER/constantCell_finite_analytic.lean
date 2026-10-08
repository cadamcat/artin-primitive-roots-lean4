import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs
import ArtinPrimitiveRoots.Proofs.th_res_fourier_a.KummerSupport

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem sphericalC_eval_analytic (g : GL (Fin 2) ℂ) :
    AnalyticOnNhd ℂ (fun s => sphericalC s g) Set.univ := by
  classical
  let d : ℝ := ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
    ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2
  have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
    have hmat : (g : Matrix (Fin 2) (Fin 2) ℂ) *
        ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
    have hmul := Matrix.det_mul (g : Matrix (Fin 2) (Fin 2) ℂ)
      ((g⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    rw [hmat] at hmul
    intro hzero
    rw [hzero, zero_mul] at hmul
    norm_num at hmul
  have hrow : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 ∨
      (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hdet
    rw [Matrix.det_fin_two]
    simp [h.1, h.2]
  have hd : 0 < d := by
    dsimp [d]
    rcases hrow with h | h
    · have hn : 0 < ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ := norm_pos_iff.mpr h
      positivity
    · have hn : 0 < ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ := norm_pos_iff.mpr h
      positivity
  let c : ℂ := ((‖Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ)‖ / d : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    have hn : 0 < ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_pos_iff.mpr hdet
    have hratio : 0 < ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ)‖ / d := div_pos hn hd
    dsimp [c]
    exact_mod_cast hratio.ne'
  have hpow : AnalyticOnNhd ℂ (fun s : ℂ => c ^ (1 + 2 * s)) Set.univ := by
    have hEq : (fun s : ℂ => c ^ (1 + 2 * s)) =
        (fun s => Complex.exp (Complex.log c * (1 + 2 * s))) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero hc]
    rw [hEq]
    intro s hs
    have harg : AnalyticAt ℂ (fun z : ℂ => Complex.log c * (1 + 2 * z)) s := by
      fun_prop
    exact analyticAt_cexp.comp harg
  have hEq : (fun s : ℂ => sphericalC s g) = fun s => c ^ (1 + 2 * s) := by
    funext s
    simp [sphericalC, c, d]
  rw [hEq]
  exact hpow

private theorem sphC_eval_analytic (g : PGL2 ℂ) :
    AnalyticOnNhd ℂ (fun s => sphC s g) Set.univ := by
  simpa [sphC] using sphericalC_eval_analytic (Quotient.out g)

private theorem glMap_diagGL {K : Type} [Field K] (φ : F →+* K) (ν : Fˣ) :
    Matrix.GeneralLinearGroup.map φ (diagGL ν) =
      diagM K (Units.map φ.toMonoidHom ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL, diagM]

private theorem section_eval_zero_of_tame_residue {v : FinPlace F}
    {L : FinLocalCover D H v} (τ : TameSplitting L) {T : TorusRep D H v}
    (B : TameTorusBasis T) (lam : T.V →ₗ[ℂ] ℂ)
    (hLam : ∀ k : ZMod 3, lam (B.e k) = if k = 0 then 1 else 0)
    (f : L.L → T.V) (s : ℂ) (hf : IsSection L T s f)
    (h1 : f 1 = B.e 0)
    (hK : ∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g)
    (δ : Fˣ) (e : ℤ) (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u)
    (hy : toLoc v δ = unifLoc v ^ e * u) (he : (e : ZMod 3) ≠ 0)
    (k : L.L) (hk : k ∈ τ.Kmax) :
    lam (f (L.a (toLoc v δ) * k)) = 0 := by
  have hright : f (L.a (toLoc v δ) * k) = f (L.a (toLoc v δ)) :=
    hK (L.a (toLoc v δ)) k hk
  have hsection := hf.1 0 (toLoc v δ) 1
  have hformula : f (L.a (toLoc v δ)) =
      ((absFin v (toLoc v δ) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        T.σa (toLoc v δ) (B.e 0) := by
    simpa [h1] using hsection
  rw [hright, hformula, hy, B.act e u hu 0]
  have he' : (0 : ZMod 3) + (e : ZMod 3) ≠ 0 := by simpa using he
  have hcoeff : lam (B.e (0 + (e : ZMod 3))) = 0 := by
    rw [hLam, if_neg he']
  rw [lam.map_smul, lam.map_smul, hcoeff]
  simp

private theorem sphWeyl_data {P : CoverPackage D S H A} {G : GlobalDatum P}
    (v : FinPlace F) (hv : v ∉ S.Sf) (s : ℂ) :
    IsSection (P.loc v) (G.T v).weyl (-s) (sphWeyl P G v hv s) ∧
      sphWeyl P G v hv s 1 = (G.B v hv).weyl.e 0 ∧
      ∀ g k, k ∈ (P.tame v hv).Kmax →
        sphWeyl P G v hv s (g * k) = sphWeyl P G v hv s g := by
  have hv6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  let τ := P.tame v hv
  let B := G.B v hv
  refine ⟨?_, ?_, ?_⟩
  · change IsSection (P.loc v) (G.T v).weyl (-s)
      (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose
    exact (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose_spec.1
  · change (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose 1 = _
    exact (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose_spec.2.1
  · intro g k hk
    change (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose (g * k) = _
    exact (spherical_section (P.loc v) τ (G.T v).weyl B.weyl hv6 (-s)).choose_spec.2.2.1 g k hk

private theorem scalarOf_zero_of_lift {P : CoverPackage D S H A} {G : GlobalDatum P}
    (fv : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V)
    (fc : InfinitePlace F → PGL2 ℂ → ℂ) (h : P.tc.G)
    (hχ : ∀ v ζ y, fv v ((P.loc v).z ζ * y) = ((ζ : ℂˣ) : ℂ) • fv v y)
    (x : P.RP) (hx : P.q x = h) (v : FinPlace F)
    (hz : G.lam v (fv v (P.compF v x)) = 0)
    (hsupp : (Function.mulSupport fun v' =>
      G.lam v' (fv v' (P.compF v' (Function.surjInv P.q_surj h)))).Finite) :
    scalarOf P G fv fc h = 0 := by
  let x₀ := Function.surjInv P.q_surj h
  have hx₀ : P.q x₀ = h := Function.surjInv_eq P.q_surj h
  obtain ⟨ζ, hζfin, hζprod, hcomp, hcompC⟩ :=
    (P.q_eq x₀ x).mp (hx₀.trans hx.symm)
  have hz₀ : G.lam v (fv v (P.compF v x₀)) = 0 := by
    rw [hcomp v, hχ v (ζ v) (P.compF v x)]
    simp only [map_smul, smul_eq_mul]
    rw [hz, mul_zero]
  have hprod : (∏ᶠ v' : FinPlace F,
      G.lam v' (fv v' (P.compF v' x₀))) = 0 :=
    finprod_eq_zero _ v hz₀ hsupp
  simp only [scalarOf]
  change (∏ᶠ v' : FinPlace F,
      G.lam v' (fv v' (P.compF v' (Function.surjInv P.q_surj h)))) * _ = 0
  rw [show Function.surjInv P.q_surj h = x₀ from rfl, hprod]
  simp

private theorem sphWeyl_eval_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    (v : FinPlace F) (hv : v ∉ S.Sf) (h6 : (6 : 𝓞 F) ∉ v.asIdeal)
    (x : (P.loc v).L) :
    AnalyticOnNhd ℂ (fun s => G.lam v (sphWeyl P G v hv s x)) {s | 0 < s.re} := by
  classical
  let L := P.loc v
  let B := G.B v hv
  obtain ⟨b, y, ζ, k, hk, hb⟩ :=
    iwasawa_tame L (P.tame v hv) x
  let c : ℂ := (absFin v (y : v.adicCompletion F) : ℂ)
  have hc : c ≠ 0 := by
    have hpos : 0 < absFin v (y : v.adicCompletion F) :=
      absFin_pos (Units.ne_zero y)
    dsimp [c]
    exact_mod_cast hpos.ne'
  let F0 (s : ℂ) : ℂ := ((ζ : ℂˣ) : ℂ) * c ^ ((1 : ℂ) / 2 + (-s)) *
      G.lam v ((G.T v).σa y⁻¹ (B.e 0))
  have hpow : AnalyticOnNhd ℂ (fun s : ℂ => c ^ ((1 : ℂ) / 2 + (-s)))
      {s | 0 < s.re} := by
    have hEq : (fun s : ℂ => c ^ ((1 : ℂ) / 2 + (-s))) =
        (fun s => Complex.exp (Complex.log c * ((1 : ℂ) / 2 + (-s)))) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero hc]
    rw [hEq]
    intro s hs
    have harg : AnalyticAt ℂ (fun z : ℂ => Complex.log c * ((1 : ℂ) / 2 + (-z))) s := by
      fun_prop
    exact analyticAt_cexp.comp harg
  have hF0 : AnalyticOnNhd ℂ F0 {s | 0 < s.re} := by
    dsimp [F0]
    exact (analyticOnNhd_const.mul hpow).mul analyticOnNhd_const
  have hEval (s : ℂ) : 0 < s.re →
      G.lam v (sphWeyl P G v hv s x) = F0 s := by
    intro hs
    let f := (spherical_section L (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
      h6 (-s)).choose
    have hf := (spherical_section L (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
      h6 (-s)).choose_spec
    have hf0 : f 1 = B.weyl.e 0 := hf.2.1
    have hkfix : ∀ z, ∀ k' ∈ (P.tame v hv).Kmax, f (z * k') = f z := hf.2.2.1
    have hcentral : L.n (Multiplicative.ofAdd b) * L.z ζ =
        L.z ζ * L.n (Multiplicative.ofAdd b) := (L.z_central ζ _).symm
    have hdec : L.n (Multiplicative.ofAdd b) * L.z ζ * L.a y * k =
        L.z ζ * (L.n (Multiplicative.ofAdd b) * L.a y * k) := by
      calc
        _ = (L.z ζ * L.n (Multiplicative.ofAdd b)) * L.a y * k := by rw [hcentral]
        _ = L.z ζ * (L.n (Multiplicative.ofAdd b) * L.a y * k) := by group
    have hzformula : f (L.z ζ * (L.n (Multiplicative.ofAdd b) * L.a y * k)) =
        ((ζ : ℂˣ) : ℂ) • f (L.n (Multiplicative.ofAdd b) * L.a y * k) := by
      change (spherical_section L (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
        h6 (-s)).choose (L.z ζ * (L.n (Multiplicative.ofAdd b) * L.a y * k)) = _
      exact hf.1.2.1 ζ (L.n (Multiplicative.ofAdd b) * L.a y * k)
    have hnaformula : f (L.n (Multiplicative.ofAdd b) * L.a y * k) =
        ((absFin v (y : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + (-s))) •
          (G.T v).weyl.σa y (f k) := by
      change (spherical_section L (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
        h6 (-s)).choose (L.n (Multiplicative.ofAdd b) * L.a y * k) =
          ((absFin v (y : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + (-s))) •
            (G.T v).weyl.σa y
              ((spherical_section L (P.tame v hv) (G.T v).weyl
                (G.B v hv).weyl h6 (-s)).choose k)
      exact hf.1.1 b y k
    have hk0 : f k = B.weyl.e 0 := by
      calc
        f k = f (1 * k) := by simp
        _ = f 1 := hkfix 1 k hk
        _ = B.weyl.e 0 := hf0
    have hformula : f x = ((ζ : ℂˣ) : ℂ) •
        (((absFin v (y : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + (-s))) •
          (G.T v).weyl.σa y (B.weyl.e 0)) := by
      rw [hb, hdec]
      rw [hzformula, hnaformula, hk0]
    have hBw0 : B.weyl.e 0 = B.e 0 := rfl
    have hformula' : f x = ((ζ : ℂˣ) : ℂ) •
        (((absFin v (y : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + (-s))) •
          (G.T v).σa y⁻¹ (B.e 0)) := by
      calc
        f x = ((ζ : ℂˣ) : ℂ) •
            (((absFin v (y : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 - s)) •
              (G.T v).weyl.σa y (B.weyl.e 0)) := hformula
        _ = _ := by rfl
    have hmap : G.lam v (f x) = F0 s := by
      dsimp [F0, c]
      rw [hformula']
      simp only [map_smul, smul_eq_mul]
      ring
    simpa [sphWeyl, f] using hmap
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact hF0.congr hopen (by
    intro s hs
    exact (hEval s hs).symm)

private theorem scalarCell_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0) (h : P.tc.G) :
    AnalyticOnNhd ℂ (fun s => scalarOf P G (sec s).f (sec s).fC h)
      {s | 0 < s.re} := by
  classical
  let x : P.RP := Function.surjInv P.q_surj h
  have hq : P.q x = h := Function.surjInv_eq P.q_surj h
  have hsub : S.Sf ⊆ T0 := by
    intro v hv
    have hv' : v ∈ (sec 0).T0 := (sec 0).sub hv
    rwa [hFam.T0_eq 0] at hv'
  let bad : Set (FinPlace F) :=
    {v | ∃ hv : v ∉ S.Sf, P.compF v x ∉ (P.tame v hv).Kmax}
  have hbad : bad.Finite := P.comp_restricted x
  let V : Finset (FinPlace F) := T0 ∪ hbad.toFinset
  let f (s : ℂ) (v : FinPlace F) : ℂ :=
    G.lam v ((sec s).f v (P.compF v x))
  have hgood (v : FinPlace F) (hv : v ∉ V) (s : ℂ) : f s v = 1 := by
    have hvT : v ∉ T0 := by
      intro hmem
      exact hv (Finset.mem_union_left _ hmem)
    have hvS : v ∉ S.Sf := fun hmem => hvT (hsub hmem)
    have hvBad : v ∉ hbad.toFinset := by
      intro hmem
      exact hv (Finset.mem_union_right _ hmem)
    have hvK : P.compF v x ∈ (P.tame v hvS).Kmax := by
      by_contra hnot
      apply hvBad
      exact hbad.mem_toFinset.mpr ⟨hvS, hnot⟩
    have hvSec : v ∉ (sec s).T0 := by
      rw [hFam.T0_eq s]
      exact hvT
    have hfsph := (sec s).f_sph v hvSec
    have hvalue : (sec s).f v (P.compF v x) = (G.B v hvS).e 0 := by
      calc
        _ = (sec s).f v 1 := by
          simpa using hfsph.2 1 (P.compF v x) hvK
        _ = (G.B v hvS).e 0 := hfsph.1
    simp [f, hvalue, G.lam_tame v hvS]
  have hsupport (s : ℂ) : Function.mulSupport (f s) ⊆ V := by
    intro v hv
    by_contra hnot
    exact hv (hgood v hnot s)
  have hfinprod (s : ℂ) : (∏ᶠ v : FinPlace F, f s v) = ∏ v ∈ V, f s v := by
    exact finprod_eq_prod_of_mulSupport_subset (f s) (hsupport s)
  have hloc (v : FinPlace F) (hv : v ∈ V) :
      AnalyticOnNhd ℂ (fun s => f s v) {s | 0 < s.re} := by
    let lam : (G.T v).V →L[ℂ] ℂ :=
      ⟨G.lam v, LinearMap.continuous_of_finiteDimensional (G.lam v)⟩
    exact lam.comp_analyticOnNhd (hFam.f_analytic v (P.compF v x))
  have harch (w : InfinitePlace F) : AnalyticOnNhd ℂ
      (fun s => (sec s).fC w (P.compC w x)) {s | 0 < s.re} := by
    have heq : (fun s => (sec s).fC w (P.compC w x)) =
        (fun s => sphC s (P.compC w x)) := by
      funext s
      rw [hFam.fC_sph]
    rw [heq]
    exact (sphC_eval_analytic (P.compC w x)).mono (by intro s hs; trivial)
  have harchProd : AnalyticOnNhd ℂ (fun s => ∏ w, (sec s).fC w (P.compC w x))
      {s | 0 < s.re} := by
    change AnalyticOnNhd ℂ (fun s => ∏ w ∈ Finset.univ,
      (sec s).fC w (P.compC w x)) {s | 0 < s.re}
    exact Finset.analyticOnNhd_fun_prod Finset.univ (by
      intro w hw
      exact harch w)
  have hlocalProd : AnalyticOnNhd ℂ (fun s => ∏ v ∈ V, f s v)
      {s | 0 < s.re} :=
    Finset.analyticOnNhd_fun_prod V hloc
  have han : AnalyticOnNhd ℂ
      (fun s => (∏ v ∈ V, f s v) * ∏ w, (sec s).fC w (P.compC w x))
      {s | 0 < s.re} := hlocalProd.mul harchProd
  have hscalar (s : ℂ) : scalarOf P G (sec s).f (sec s).fC h =
      (∏ v ∈ V, f s v) * ∏ w, (sec s).fC w (P.compC w x) := by
    rw [← hq, (scalarOf_q P G (sec s) x).2, hfinprod]
  exact han.congr (isOpen_lt continuous_const Complex.continuous_re) (by
    intro s hs
    exact (hscalar s).symm)

private theorem rawM_cell_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0) (h : P.tc.G) :
    AnalyticOnNhd ℂ (fun s => fourierRawM μ sec s h) {s | 0 < s.re} := by
  classical
  let x : P.RP := Function.surjInv P.q_surj h
  have hq : P.q x = h := Function.surjInv_eq P.q_surj h
  have hsub : S.Sf ⊆ T0 := by
    intro v hv
    have hv' : v ∈ (sec 0).T0 := (sec 0).sub hv
    rwa [hFam.T0_eq 0] at hv'
  let bad : Set (FinPlace F) :=
    {v | ∃ hv : v ∉ S.Sf, P.compF v x ∉ (P.tame v hv).Kmax}
  have hbad : bad.Finite := P.comp_restricted x
  let V : Finset (FinPlace F) := T0 ∪ hbad.toFinset
  let fv (s : ℂ) (v : FinPlace F) : (P.loc v).L → (G.T v).V :=
    if hv : v ∈ T0 then intertwine (P.loc v) (μ v) ((sec s).f v)
    else sphWeyl P G v (fun hs => hv (hsub hs)) s
  let eval (s : ℂ) (v : FinPlace F) : ℂ := G.lam v (fv s v (P.compF v x))
  have hgood (s : ℂ) (v : FinPlace F) (hv : v ∉ V) : eval s v = 1 := by
    have hvT : v ∉ T0 := by
      intro hm
      exact hv (Finset.mem_union_left _ hm)
    have hvS : v ∉ S.Sf := fun hm => hvT (hsub hm)
    have hvBad : v ∉ hbad.toFinset := by
      intro hm
      exact hv (Finset.mem_union_right _ hm)
    have hk : P.compF v x ∈ (P.tame v hvS).Kmax := by
      by_contra hnot
      apply hvBad
      exact hbad.mem_toFinset.mpr ⟨hvS, hnot⟩
    have hsph := (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
      (G.B v hvS).weyl (fun h6 => hvS (S.over6 v h6)) (-s)).choose_spec
    have hvalue : sphWeyl P G v hvS s (P.compF v x) = (G.B v hvS).weyl.e 0 := by
      change (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
        (G.B v hvS).weyl (fun h6 => hvS (S.over6 v h6)) (-s)).choose
          (P.compF v x) = _
      calc
        _ = (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
            (G.B v hvS).weyl (fun h6 => hvS (S.over6 v h6)) (-s)).choose
              (1 * P.compF v x) := by simp
        _ = (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
            (G.B v hvS).weyl (fun h6 => hvS (S.over6 v h6)) (-s)).choose 1 :=
              hsph.2.2.1 1 (P.compF v x) hk
        _ = (G.B v hvS).weyl.e 0 := hsph.2.1
    have hlam0 : G.lam v ((G.B v hvS).weyl.e 0) = 1 := by
      simpa [TameTorusBasis.weyl] using G.lam_tame v hvS (0 : ZMod 3)
    simp [eval, fv, hvT, hvalue, hlam0]
  have hsupport (s : ℂ) : Function.mulSupport (eval s) ⊆ V := by
    intro v hv
    by_contra hnot
    exact hv (hgood s v hnot)
  have hlocal (v : FinPlace F) (hv : v ∈ V) :
      AnalyticOnNhd ℂ (fun s => eval s v) {s | 0 < s.re} := by
    by_cases hvT : v ∈ T0
    · let lam : (G.T v).V →L[ℂ] ℂ :=
        ⟨G.lam v, LinearMap.continuous_of_finiteDimensional (G.lam v)⟩
      have heq : (fun s => eval s v) =
          (fun s => lam (intertwine (P.loc v) (μ v) ((sec s).f v) (P.compF v x))) := by
        funext s
        simp [eval, fv, hvT, lam]
      rw [heq]
      exact lam.comp_analyticOnNhd (hFam.M_analytic v hvT (P.compF v x))
    · have hvS : v ∉ S.Sf := fun hs => hvT (hsub hs)
      have heq : (fun s => eval s v) =
          (fun s => G.lam v (sphWeyl P G v hvS s (P.compF v x))) := by
        funext s
        simp [eval, fv, hvT]
      rw [heq]
      exact sphWeyl_eval_analytic v hvS (fun h6 => hvS (S.over6 v h6)) (P.compF v x)
  have hlocalProd : AnalyticOnNhd ℂ (fun s => ∏ v ∈ V, eval s v)
      {s | 0 < s.re} := Finset.analyticOnNhd_fun_prod V hlocal
  let Dpos : Set ℂ := {s | 0 < s.re}
  have hcoef : AnalyticOnNhd ℂ (fun s : ℂ => (Real.pi : ℂ) / (2 * s)) Dpos := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro hzero
      subst s
      simp [Dpos] at hs
    have h2s : (2 : ℂ) * s ≠ 0 := mul_ne_zero (by norm_num) hs0
    fun_prop
  have hnegSph (w : InfinitePlace F) :
      AnalyticOnNhd ℂ (fun s => sphC (-s) (P.compC w x)) Dpos := by
    have hminus : AnalyticOnNhd ℂ (fun s : ℂ => -s) Dpos := by fun_prop
    have hcomp := (sphC_eval_analytic (P.compC w x)).comp hminus
      (by intro s hs; trivial)
    simpa [Function.comp_def] using hcomp
  have harch (w : InfinitePlace F) : AnalyticOnNhd ℂ
      (fun s => intertwineC ((sec s).fC w) (P.compC w x)) Dpos := by
    have hprod := (hcoef.mul (hnegSph w))
    exact hprod.congr (isOpen_lt continuous_const Complex.continuous_re) (by
      intro s hs
      change 0 < s.re at hs
      calc
        (Real.pi / (2 * s)) * sphC (-s) (P.compC w x) =
            intertwineC (sphC s) (P.compC w x) :=
          (congrFun (intertwineC_spherical s hs) (P.compC w x)).symm
        _ = intertwineC ((sec s).fC w) (P.compC w x) := by
          rw [← hFam.fC_sph s w])
  have harchProd : AnalyticOnNhd ℂ
      (fun s => ∏ w, intertwineC ((sec s).fC w) (P.compC w x)) Dpos := by
    change AnalyticOnNhd ℂ (fun s => ∏ w ∈ Finset.univ,
      intertwineC ((sec s).fC w) (P.compC w x)) Dpos
    exact Finset.analyticOnNhd_fun_prod Finset.univ (by
      intro w hw
      exact harch w)
  have han : AnalyticOnNhd ℂ
      (fun s => (∏ v ∈ V, eval s v) * ∏ w, intertwineC ((sec s).fC w) (P.compC w x)) Dpos :=
    hlocalProd.mul harchProd
  have hscalar (s : ℂ) : fourierRawM μ sec s h =
      (∏ v ∈ V, eval s v) * ∏ w, intertwineC ((sec s).fC w) (P.compC w x) := by
    simp only [fourierRawM, scalarOf, hFam.T0_eq s]
    dsimp only [eval, fv, x]
    rw [finprod_eq_prod_of_mulSupport_subset _
      (s := V) (by simpa only [eval, fv, x] using hsupport s)]
  exact han.congr (isOpen_lt continuous_const Complex.continuous_re) (by
    intro s hs
    exact (hscalar s).symm)

private theorem rawM_scalar_support {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (s : ℂ) (h : P.tc.G) :
    (Function.mulSupport fun v => G.lam v
      ((if hv : v ∈ (sec s).T0 then intertwine (P.loc v) (μ v) ((sec s).f v)
        else sphWeyl P G v (fun hs => hv ((sec s).sub hs)) s)
        (P.compF v (Function.surjInv P.q_surj h)))).Finite := by
  classical
  have hsub : S.Sf ⊆ T0 := by
    intro v hv
    have hv' : v ∈ (sec 0).T0 := (sec 0).sub hv
    rwa [hFam.T0_eq 0] at hv'
  let x : P.RP := Function.surjInv P.q_surj h
  let bad : Set (FinPlace F) :=
    {v | ∃ hv : v ∉ S.Sf, P.compF v x ∉ (P.tame v hv).Kmax}
  have hbad : bad.Finite := P.comp_restricted x
  let V : Finset (FinPlace F) := T0 ∪ hbad.toFinset
  have hgood (v : FinPlace F) (hv : v ∉ V) :
      G.lam v ((if hT : v ∈ (sec s).T0 then intertwine (P.loc v) (μ v) ((sec s).f v)
        else sphWeyl P G v (fun hs => hT ((sec s).sub hs)) s) (P.compF v x)) = 1 := by
    have hvT : v ∉ T0 := by
      intro hm
      exact hv (Finset.mem_union_left _ hm)
    have hvTs : v ∉ (sec s).T0 := by rw [hFam.T0_eq s]; exact hvT
    have hvS : v ∉ S.Sf := fun hs => hvT (hsub hs)
    have hvBad : v ∉ hbad.toFinset := by
      intro hm
      exact hv (Finset.mem_union_right _ hm)
    have hk : P.compF v x ∈ (P.tame v hvS).Kmax := by
      by_contra hnot
      apply hvBad
      exact hbad.mem_toFinset.mpr ⟨hvS, hnot⟩
    have hsph := (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
      (G.B v hvS).weyl (fun h6 => hvS (S.over6 v h6)) (-s)).choose_spec
    have hvalue : sphWeyl P G v hvS s (P.compF v x) = (G.B v hvS).weyl.e 0 := by
      change (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
        (G.B v hvS).weyl (fun h6 => hvS (S.over6 v h6)) (-s)).choose
          (P.compF v x) = _
      calc
        _ = (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
            (G.B v hvS).weyl (fun h6 => hvS (S.over6 v h6)) (-s)).choose
              (1 * P.compF v x) := by simp
        _ = (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
            (G.B v hvS).weyl (fun h6 => hvS (S.over6 v h6)) (-s)).choose 1 :=
              hsph.2.2.1 1 (P.compF v x) hk
        _ = (G.B v hvS).weyl.e 0 := hsph.2.1
    have hlam0 : G.lam v ((G.B v hvS).weyl.e 0) = 1 := by
      simpa [TameTorusBasis.weyl] using G.lam_tame v hvS (0 : ZMod 3)
    simpa [hvTs, hvalue, hlam0]
  have hsubset : Function.mulSupport (fun v => G.lam v
      ((if hv : v ∈ (sec s).T0 then intertwine (P.loc v) (μ v) ((sec s).f v)
        else sphWeyl P G v (fun hs => hv ((sec s).sub hs)) s) (P.compF v x))) ⊆ V := by
    intro v hv
    by_contra hnot
    exact hv (hgood v hnot)
  exact V.finite_toSet.subset hsubset

/-- Both scalar cell sums have one finite delta support for the whole positive half-plane;
every surviving scalar factor is analytic there. This supplies uniform support near 1/6.
Guide: sol-thin-thglobal/PROOFS.md:835–843. Uses intertwine_isSection, sphWeyl,
intertwineC_spherical, and the compact/Alag finite-coset argument. Feeds theta_constantTerm. -/
theorem constantCell_finite_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0) (g : P.tc.G) :
    ∃ T : Finset (Fˣ ⧸ G.Δ),
      (∀ s : ℂ, 0 < s.re → ∀ δ : Fˣ ⧸ G.Δ, δ ∉ T →
        scalarOf P G (sec s).f (sec s).fC
          (P.tc.rat (diagGL (Quotient.out δ)) * g) = 0 ∧
        fourierRawM μ sec s (P.tc.rat (diagGL (Quotient.out δ)) * g) = 0) ∧
      (∀ δ ∈ T, AnalyticOnNhd ℂ (fun s =>
        scalarOf P G (sec s).f (sec s).fC
          (P.tc.rat (diagGL (Quotient.out δ)) * g)) {s | 0 < s.re}) ∧
      (∀ δ ∈ T, AnalyticOnNhd ℂ (fun s =>
        fourierRawM μ sec s (P.tc.rat (diagGL (Quotient.out δ)) * g)) {s | 0 < s.re}) := by
  classical
  obtain ⟨xg, hxg⟩ := P.q_surj g
  have hsub : S.Sf ⊆ T0 := by
    intro v hv
    have hv' : v ∈ (sec 0).T0 := (sec 0).sub hv
    rwa [hFam.T0_eq 0] at hv'
  let bad : Set (FinPlace F) :=
    {v | ∃ hv : v ∉ S.Sf, P.compF v xg ∉ (P.tame v hv).Kmax}
  have hbad : bad.Finite := P.comp_restricted xg
  let V : Finset (FinPlace F) := T0 ∪ hbad.toFinset
  let cube : Subgroup Fˣ := (powMonoidHom (α := Fˣ) 3).range
  have hcubeΔ : cube ≤ G.Δ := by
    rintro a ⟨u, rfl⟩
    change (powMonoidHom (α := Fˣ) 3) u ∈
      (⨅ v : FinPlace F, (G.Alag v).comap (toLoc v))
    simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    simpa [powMonoidHom_apply] using G.alag_cubes v (toLoc v u)
  let H : Subgroup (Fˣ ⧸ cube) :=
    IsDedekindDomain.selmerGroup (R := 𝓞 F) (K := F)
      (S := (V : Set (FinPlace F))) (n := 3)
  haveI : Finite H := by
    change Finite (IsDedekindDomain.selmerGroup (R := 𝓞 F) (K := F)
      (S := (V : Set (FinPlace F))) (n := 3))
    exact finite_numberField_cubeSelmer' V
  letI : Fintype H := Fintype.ofFinite H
  have hcubeΔ' : cube ≤ Subgroup.comap (MonoidHom.id Fˣ) G.Δ := by
    simpa using hcubeΔ
  let qmap : Fˣ ⧸ cube →* Fˣ ⧸ G.Δ :=
    QuotientGroup.map cube G.Δ (MonoidHom.id Fˣ) hcubeΔ'
  let key : H → Fˣ ⧸ G.Δ := fun a => qmap a
  have hrange : (Set.range key).Finite := Set.finite_range key
  let T : Finset (Fˣ ⧸ G.Δ) := hrange.toFinset
  have hcover (δ : Fˣ ⧸ G.Δ) (hδ : δ ∉ T) :
      ∃ v, v ∉ V ∧ v.valuationOfNeZeroMod 3
        (QuotientGroup.mk (Quotient.out δ) : Fˣ ⧸ cube) ≠ 1 := by
    let δ0 : Fˣ := Quotient.out δ
    let q0 : Fˣ ⧸ cube := QuotientGroup.mk δ0
    have hnotH : q0 ∉ H := by
      intro hq0
      apply hδ
      apply hrange.mem_toFinset.mpr
      refine ⟨⟨q0, hq0⟩, ?_⟩
      change qmap (QuotientGroup.mk' cube δ0) = δ
      calc
        _ = QuotientGroup.mk' G.Δ ((MonoidHom.id Fˣ) δ0) :=
          QuotientGroup.map_mk' cube G.Δ (MonoidHom.id Fˣ) hcubeΔ' δ0
        _ = δ := by simpa [δ0]
    have hnot : ¬ (∀ v, v ∉ (V : Set (FinPlace F)) →
        v.valuationOfNeZeroMod 3 q0 = 1) := by
      change ¬ (∀ v, v ∉ (V : Set (FinPlace F)) →
        v.valuationOfNeZeroMod 3 q0 = 1) at hnotH
      exact hnotH
    by_contra h
    push_neg at h
    exact hnot h
  have hzeros (s : ℂ) (hs : 0 < s.re) (δ : Fˣ ⧸ G.Δ) (hδ : δ ∉ T) :
      scalarOf P G (sec s).f (sec s).fC (P.tc.rat (diagGL (Quotient.out δ)) * g) = 0 ∧
      fourierRawM μ sec s (P.tc.rat (diagGL (Quotient.out δ)) * g) = 0 := by
    obtain ⟨v, hvV, hval⟩ := hcover δ hδ
    let δ0 : Fˣ := Quotient.out δ
    have hord : (ordv v (toLoc v δ0) : ZMod 3) ≠ 0 := by
      intro hzero
      apply hval
      exact (valuationMod_eq_one_iff_ordvMod_eq_zero δ0 v).2 hzero
    let e : ℤ := ordv v (toLoc v δ0)
    let u : (v.adicCompletion F)ˣ := unitPart v (toLoc v δ0)
    have he : (e : ZMod 3) ≠ 0 := by simpa [e] using hord
    have hu : IsLocUnit v u := by simpa [u] using unitPart_isLocUnit_rf v (toLoc v δ0)
    have hy : toLoc v δ0 = unifLoc v ^ e * u := by
      simpa [e, u] using (unitPart_factor_rf v (toLoc v δ0)).symm
    have hvT : v ∉ T0 := by
      intro hm
      exact hvV (Finset.mem_union_left _ hm)
    have hvS : v ∉ S.Sf := fun hsV => hvT (hsub hsV)
    have hvBad : v ∉ hbad.toFinset := by
      intro hm
      exact hvV (Finset.mem_union_right _ hm)
    have hk : P.compF v xg ∈ (P.tame v hvS).Kmax := by
      by_contra hnot
      apply hvBad
      exact hbad.mem_toFinset.mpr ⟨hvS, hnot⟩
    let xδ : P.RP := P.ratRP (diagGL δ0) * xg
    let hδg : P.tc.G := P.tc.rat (diagGL δ0) * g
    have hxδ : P.q xδ = hδg := by
      simp [xδ, hδg, P.q.map_mul, P.q_ratRP, hxg]
    have hcompδ : P.compF v xδ =
        (P.loc v).a (toLoc v δ0) * P.compF v xg := by
      calc
        P.compF v xδ = P.compF v (P.ratRP (diagGL δ0)) * P.compF v xg := by
          simp [xδ, (P.compF v).map_mul]
        _ = (P.loc v).a (toLoc v δ0) * P.compF v xg := by
          rw [P.compF_ratRP v (diagGL δ0), glMap_diagGL,
            ← (P.loc v).sec_a]
          rfl
    have hT0s : v ∉ (sec s).T0 := by rw [hFam.T0_eq s]; exact hvT
    have hsphS := (sec s).f_sph v hT0s
    have hzeroS : G.lam v ((sec s).f v (P.compF v xδ)) = 0 := by
      rw [hcompδ]
      exact section_eval_zero_of_tame_residue (P.tame v hvS)
        (G.B v hvS) (G.lam v) (G.lam_tame v hvS) ((sec s).f v) s
        ((sec s).f_sec v) hsphS.1 hsphS.2 δ0 e u hu hy he (P.compF v xg) hk
    have hsuppS : (Function.mulSupport fun v' =>
        G.lam v' ((sec s).f v' (P.compF v'
          (Function.surjInv P.q_surj hδg)))).Finite :=
      (scalarOf_q P G (sec s) (Function.surjInv P.q_surj hδg)).1
    have hchiS : ∀ v' ζ y, (sec s).f v' ((P.loc v').z ζ * y) =
        ((ζ : ℂˣ) : ℂ) • (sec s).f v' y := by
      intro v' ζ y
      exact ((sec s).f_sec v').2.1 ζ y
    have hscalarZero := scalarOf_zero_of_lift
      (fv := (sec s).f) (fc := (sec s).fC) hδg hchiS xδ hxδ v hzeroS hsuppS
    let fm : ∀ v' : FinPlace F, (P.loc v').L → (G.T v').weyl.V := fun v' =>
      if hv' : v' ∈ (sec s).T0 then intertwine (P.loc v') (μ v') ((sec s).f v')
      else sphWeyl P G v' (fun hnot => hv' ((sec s).sub hnot)) s
    have hchiM : ∀ v' ζ y, fm v' ((P.loc v').z ζ * y) =
        ((ζ : ℂˣ) : ℂ) • fm v' y := by
      intro v' ζ y
      by_cases hv' : v' ∈ (sec s).T0
      · have hsecM := (intertwine_isSection (P.loc v') (G.T v') (μ v') s hs
          ((sec s).f v') ((sec s).f_sec v')).2
        simpa [fm, hv'] using hsecM.2.1 ζ y
      · have hvT' : v' ∉ T0 := by rw [← hFam.T0_eq s]; exact hv'
        have hvS' : v' ∉ S.Sf := fun hvS' => hvT' (hsub hvS')
        have hsecW := sphWeyl_data (P := P) (G := G) v' hvS' s
        simpa [fm, hv'] using hsecW.1.2.1 ζ y
    have hLamW : ∀ k : ZMod 3,
        G.lam v ((G.B v hvS).weyl.e k) = if k = 0 then 1 else 0 := by
      intro k
      simpa [TameTorusBasis.weyl] using G.lam_tame v hvS (-k)
    have hsecW := sphWeyl_data (P := P) (G := G) v hvS s
    have hzeroW : G.lam v (sphWeyl P G v hvS s
        (P.compF v xδ)) = 0 := by
      rw [hcompδ]
      exact section_eval_zero_of_tame_residue (P.tame v hvS)
        ((G.B v hvS).weyl) (G.lam v) hLamW (sphWeyl P G v hvS s) (-s)
        hsecW.1 hsecW.2.1 hsecW.2.2 δ0 e u hu hy he (P.compF v xg) hk
    have hzeroM : G.lam v (fm v (P.compF v xδ)) = 0 := by
      have hvTs : v ∉ (sec s).T0 := by rw [hFam.T0_eq s]; exact hvT
      simpa [fm, hvTs] using hzeroW
    have hsuppM := rawM_scalar_support hFam s hδg
    have hrawZero := scalarOf_zero_of_lift
      (fv := fm) (fc := fun w => intertwineC ((sec s).fC w)) hδg hchiM
      xδ hxδ v hzeroM hsuppM
    constructor
    · exact hscalarZero
    · change scalarOf P G fm (fun w => intertwineC ((sec s).fC w)) hδg = 0
      exact hrawZero
  refine ⟨T, ?_, ?_, ?_⟩
  · intro s hs δ hδ
    exact hzeros s hs δ hδ
  · intro δ hδ
    exact scalarCell_analytic hFam (P.tc.rat (diagGL (Quotient.out δ)) * g)
  · intro δ hδ
    exact rawM_cell_analytic hFam (P.tc.rat (diagGL (Quotient.out δ)) * g)

end ArtinPrimitiveRoots.A1.Theta
