import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.LocalWhit
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.Cosets
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.ComplexMajorant
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.CubeClasses
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.LocalValuation
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.FiniteMajorant
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-EIS -/

section Eis

open MeasureTheory

variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- **def:global-datum** (10:46–58; KP §II.1 pp. 107–109 made explicit). At every finite place a
torus representation `T v` with the evaluation functional `lam v` of its induced model, equivariant
under the Lagrangian subgroup `Alag v` with character `ω v`; tame normalization outside `S`; and the
global-datum condition: `Π_{v∈S} ω_v(δ) = 1` for rational `δ` in every `Alag v`. C6 of
`sol-gate-theta` adds cube containment and the maximal-isotropic condition on each `Alag v`. -/
structure GlobalDatum (P : CoverPackage D S H A) where
  T : ∀ v : FinPlace F, TorusRep D H v
  B : ∀ v : FinPlace F, v ∉ S.Sf → TameTorusBasis (T v)
  Alag : ∀ v : FinPlace F, Subgroup (v.adicCompletion F)ˣ
  alag_cubes : ∀ v (t : (v.adicCompletion F)ˣ), t ^ 3 ∈ Alag v
  alag_lagrangian : ∀ v (x : (v.adicCompletion F)ˣ),
    x ∈ Alag v ↔ ∀ y ∈ Alag v, torusPairing D H v x y = 1
  lam : ∀ v : FinPlace F, (T v).V →ₗ[ℂ] ℂ
  ω : ∀ v : FinPlace F, (v.adicCompletion F)ˣ → ℂ
  lam_equiv : ∀ v, ∀ y ∈ Alag v, ∀ x, lam v ((T v).σa y x) = ω v y * lam v x
  lam_ne : ∀ v, lam v ≠ 0
  alag_tame : ∀ v, v ∉ S.Sf → ∀ y : (v.adicCompletion F)ˣ,
    y ∈ Alag v ↔ ∃ (k : ℤ) (u : (v.adicCompletion F)ˣ), IsLocUnit v u ∧ y = unifLoc v ^ (3 * k) * u
  ω_tame : ∀ v, v ∉ S.Sf → ∀ y ∈ Alag v, ω v y = 1
  lam_tame : ∀ v (hv : v ∉ S.Sf) (k : ZMod 3), lam v ((B v hv).e k) = if k = 0 then 1 else 0
  ω_rational : ∀ δ : Fˣ, (∀ v, toLoc v δ ∈ Alag v) → ∏ v ∈ S.Sf, ω v (toLoc v δ) = 1

/-- The rational subgroup `Δ = {δ ∈ F^× : δ ∈ Alag v for all v}`. -/
def GlobalDatum.Δ {P : CoverPackage D S H A} (G : GlobalDatum P) : Subgroup Fˣ :=
  ⨅ v : FinPlace F, (G.Alag v).comap (toLoc v)

/-- **eis:global-datum** (existence). The strengthened datum is required by C6 of
`sol-gate-theta`. -/
theorem exists_globalDatum (P : CoverPackage D S H A) (hSt : ∀ v, SteinbergAt H v) :
    Nonempty (GlobalDatum P) := by
  sorry

/-- **def:global-section**: a factorizable section of `I(σ_𝔸, s)`, spherical outside `T0 ⊇ S_f`.
Corrected per rev-theta to include archimedean smoothness along the root subgroups; C11 of
`sol-gate-theta` adds joint smoothness in both root variables. -/
structure GlobalSection (P : CoverPackage D S H A) (G : GlobalDatum P) (s : ℂ) where
  T0 : Finset (FinPlace F)
  sub : S.Sf ⊆ T0
  f : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V
  f_sec : ∀ v, IsSection (P.loc v) (G.T v) s (f v)
  f_sph : ∀ v (hv : v ∉ T0), f v 1 = (G.B v (fun h => hv (sub h))).e 0 ∧
    ∀ g, ∀ k ∈ (P.tame v (fun h => hv (sub h))).Kmax, f v (g * k) = f v g
  fC : InfinitePlace F → PGL2 ℂ → ℂ
  fC_sec : ∀ w, IsSectionC s (fC w) ∧ Continuous (fC w)
  fC_smooth : ∀ w (g : PGL2 ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => fC w (g * nC z))
  fC_jointSmooth : ∀ w (g : PGL2 ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℂ => fC w (nC p.1 * g * nC p.2))

/-- **def:scalar-section**: `Φ(q x) = Π_v lam_v(f_v(x_v)) · Π_w f_w(x_w)` (independent of the lift `x`). -/
def scalarOf (P : CoverPackage D S H A) (G : GlobalDatum P)
    (fv : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V) (fc : InfinitePlace F → PGL2 ℂ → ℂ)
    (g : P.tc.G) : ℂ :=
  (∏ᶠ v, G.lam v (fv v (P.compF v (Function.surjInv P.q_surj g)))) *
    ∏ w, fc w (P.compC w (Function.surjInv P.q_surj g))

/-- **eis:scalar-well-defined**: the formula at any lift, with finite support. -/
theorem scalarOf_q (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (Fs : GlobalSection P G s) (x : P.RP) :
    (Function.mulSupport fun v => G.lam v (Fs.f v (P.compF v x))).Finite ∧
    scalarOf P G Fs.f Fs.fC (P.q x) =
      (∏ᶠ v, G.lam v (Fs.f v (P.compF v x))) * ∏ w, Fs.fC w (P.compC w x) := by
  sorry

/-- `B_*(F) = {b upper triangular : b₁₁/b₂₂ ∈ Δ}`. -/
def Bstar {P : CoverPackage D S H A} (G : GlobalDatum P) : Subgroup (GL (Fin 2) F) where
  carrier := {b | (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
    ∃ δ ∈ G.Δ, (b : Matrix (Fin 2) (Fin 2) F) 0 0 = (δ : F) * (b : Matrix (Fin 2) (Fin 2) F) 1 1}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

/-- **eis:left-inv**: `Φ` is left `B_*(F)`-invariant, left `N(F_S)`- and `N(K_v)`-invariant, and
genuine. -/
theorem scalarOf_invariance (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (Fs : GlobalSection P G s) :
    (∀ b ∈ Bstar G, ∀ g, scalarOf P G Fs.f Fs.fC (P.tc.rat b * g) = scalarOf P G Fs.f Fs.fC g) ∧
    (∀ x g, scalarOf P G Fs.f Fs.fC (P.tc.nS x * g) = scalarOf P G Fs.f Fs.fC g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, scalarOf P G Fs.f Fs.fC (P.tc.n v x * g) = scalarOf P G Fs.f Fs.fC g) ∧
    (∀ ζ g, scalarOf P G Fs.f Fs.fC (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * scalarOf P G Fs.f Fs.fC g) := by
  sorry

/-- **def:eisenstein**: `E(g, Φ) = Σ_{γ ∈ B_*(F)\GL₂(F)} Φ(γ g)`. -/
def eisenstein (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (g : P.tc.G) : ℂ :=
  ∑' γ : Quotient (QuotientGroup.rightRel (Bstar G)),
    scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out γ) * g)

open scoped nonZeroDivisors in
/-- Only finitely many rational torus classes have a nonzero finite-place scalar
product at a fixed restricted-product lift. -/
theorem finite_torus_scalar_support (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP) :
    Set.Finite {δ : Fˣ ⧸ G.Δ |
      (∏ᶠ v, G.lam v (Fs.f v
        ((P.loc v).a (toLoc v (Quotient.out δ)) * P.compF v r))) ≠ 0} := by
  classical
  let W : Finset (FinPlace F) := Fs.T0 ∪ (P.comp_restricted r).toFinset
  let cubes : Subgroup Fˣ := (powMonoidHom 3 : Fˣ →* Fˣ).range
  have hcubes : cubes ≤ (G.Δ).comap (MonoidHom.id Fˣ) := by
    rintro a ⟨b, rfl⟩
    change b ^ 3 ∈ G.Δ
    simp only [GlobalDatum.Δ, Subgroup.mem_iInf, Subgroup.mem_comap, map_pow]
    exact fun v => G.alag_cubes v (toLoc v b)
  let π : (Fˣ ⧸ cubes) →* (Fˣ ⧸ G.Δ) :=
    QuotientGroup.map cubes G.Δ (MonoidHom.id Fˣ) hcubes
  have hcomp (a : Fˣ) (v : FinPlace F) :
      P.compF v (P.ratRP (diagGL a) * r) =
        (P.loc v).a (toLoc v a) * P.compF v r := by
    have hdiag : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (diagGL a) = diagM (v.adicCompletion F) (toLoc v a) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, toLoc]
    rw [map_mul, P.compF_ratRP, hdiag, ← (P.loc v).sec_a]
  apply ((finite_cubic_valuation_classes F W).image π).subset
  intro δ hδ
  let a : Fˣ := Quotient.out δ
  change (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r))) ≠ 0 at hδ
  have hsupp : (Function.mulSupport fun v =>
      G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r))).Finite := by
    simpa only [hcomp] using (scalarOf_q P G Fs (P.ratRP (diagGL a) * r)).1
  have ha : ∀ v, v ∉ W → (3 : ℤ) ∣ FractionalIdeal.count F v
      (toPrincipalIdeal (𝓞 F) F a : FractionalIdeal (𝓞 F)⁰ F) := by
    intro v hv
    simp only [W, Finset.mem_union, not_or] at hv
    have hT0 : v ∉ Fs.T0 := hv.1
    have hSf : v ∉ S.Sf := fun h => hT0 (Fs.sub h)
    have hk : P.compF v r ∈ (P.tame v hSf).Kmax := by
      by_contra hk
      exact hv.2
        ((P.comp_restricted r).mem_toFinset.mpr ⟨hSf, hk⟩)
    by_contra hcount
    have hsec : Fs.f v ((P.loc v).a (toLoc v a)) =
        ((absFin v (toLoc v a) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          (G.T v).σa (toLoc v a) (Fs.f v 1) := by
      simpa only [ofAdd_zero, map_one, one_mul, mul_one]
        using (Fs.f_sec v).1 0 (toLoc v a) 1
    have hz : G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r)) = 0 := by
      rw [(Fs.f_sph v hT0).2 _ _ hk, hsec, (Fs.f_sph v hT0).1, map_smul]
      rw [tame_coefficient_eq_zero_of_count_not_dvd (G.T v) (G.B v hSf)
        (G.lam v) (G.lam_tame v hSf) a hcount, smul_zero]
    exact hδ (finprod_eq_zero _ v hz hsupp)
  refine ⟨(QuotientGroup.mk' cubes) a, ⟨a, ha, rfl⟩, ?_⟩
  change (QuotientGroup.mk' G.Δ) a = δ
  exact Quotient.out_eq δ

open scoped nonZeroDivisors in
/-- One finite torus support set works for every lift whose projected components
are tame compact outside a fixed finite set of places. -/
theorem finite_torus_scalar_support_uniform (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (W : Finset (FinPlace F)) (hW : Fs.T0 ⊆ W) :
    ∃ U : Set (Fˣ ⧸ G.Δ), U.Finite ∧ ∀ r : P.RP,
      (∀ v (hv : v ∉ W),
        (P.loc v).pr (P.compF v r) ∈
          (P.loc v).pr ''
            ((P.tame v (fun h => hv (hW (Fs.sub h)))).Kmax : Set (P.loc v).L)) →
      {δ : Fˣ ⧸ G.Δ |
        (∏ᶠ v, G.lam v (Fs.f v
          ((P.loc v).a (toLoc v (Quotient.out δ)) * P.compF v r))) ≠ 0} ⊆ U := by
  classical
  let cubes : Subgroup Fˣ := (powMonoidHom 3 : Fˣ →* Fˣ).range
  have hcubes : cubes ≤ (G.Δ).comap (MonoidHom.id Fˣ) := by
    rintro a ⟨b, rfl⟩
    change b ^ 3 ∈ G.Δ
    simp only [GlobalDatum.Δ, Subgroup.mem_iInf, Subgroup.mem_comap, map_pow]
    exact fun v => G.alag_cubes v (toLoc v b)
  let π : (Fˣ ⧸ cubes) →* (Fˣ ⧸ G.Δ) :=
    QuotientGroup.map cubes G.Δ (MonoidHom.id Fˣ) hcubes
  let U : Set (Fˣ ⧸ G.Δ) := π ''
    ((QuotientGroup.mk' cubes) '' {a : Fˣ | ∀ v, v ∉ W →
      (3 : ℤ) ∣ FractionalIdeal.count F v
        (toPrincipalIdeal (𝓞 F) F a : FractionalIdeal (𝓞 F)⁰ F)})
  refine ⟨U, (finite_cubic_valuation_classes F W).image π, ?_⟩
  intro r hr δ hδ
  let a : Fˣ := Quotient.out δ
  change (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r))) ≠ 0 at hδ
  have hcomp (v : FinPlace F) :
      P.compF v (P.ratRP (diagGL a) * r) =
        (P.loc v).a (toLoc v a) * P.compF v r := by
    have hdiag : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (diagGL a) = diagM (v.adicCompletion F) (toLoc v a) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, toLoc]
    rw [map_mul, P.compF_ratRP, hdiag, ← (P.loc v).sec_a]
  have hsupp : (Function.mulSupport fun v =>
      G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r))).Finite := by
    simpa only [hcomp] using (scalarOf_q P G Fs (P.ratRP (diagGL a) * r)).1
  have ha : ∀ v, v ∉ W → (3 : ℤ) ∣ FractionalIdeal.count F v
      (toPrincipalIdeal (𝓞 F) F a : FractionalIdeal (𝓞 F)⁰ F) := by
    intro v hv
    have hT0 : v ∉ Fs.T0 := fun h => hv (hW h)
    have hSf : v ∉ S.Sf := fun h => hT0 (Fs.sub h)
    obtain ⟨k, hk, hkpr⟩ := hr v hv
    have hker : k⁻¹ * P.compF v r ∈ (P.loc v).pr.ker := by
      change (P.loc v).pr (k⁻¹ * P.compF v r) = 1
      rw [map_mul, map_inv, hkpr, inv_mul_cancel]
    rw [(P.loc v).pr_ker] at hker
    obtain ⟨ζ, hζ⟩ := hker
    have hrcomp : P.compF v r = (P.loc v).z ζ * k := by
      calc
        P.compF v r = k * (k⁻¹ * P.compF v r) := by group
        _ = k * (P.loc v).z ζ := by rw [← hζ]
        _ = (P.loc v).z ζ * k := ((P.loc v).z_central ζ k).symm
    by_contra hcount
    have hsec : Fs.f v ((P.loc v).a (toLoc v a)) =
        ((absFin v (toLoc v a) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          (G.T v).σa (toLoc v a) (Fs.f v 1) := by
      simpa only [ofAdd_zero, map_one, one_mul, mul_one]
        using (Fs.f_sec v).1 0 (toLoc v a) 1
    have hz : G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r)) = 0 := by
      rw [hrcomp, ← mul_assoc,
        ← (P.loc v).z_central ζ ((P.loc v).a (toLoc v a)), mul_assoc,
        (Fs.f_sec v).2.1, map_smul, (Fs.f_sph v hT0).2 _ _ hk,
        hsec, (Fs.f_sph v hT0).1, map_smul,
        tame_coefficient_eq_zero_of_count_not_dvd (G.T v) (G.B v hSf)
          (G.lam v) (G.lam_tame v hSf) a hcount, smul_zero, smul_zero]
    exact hδ (finprod_eq_zero _ v hz hsupp)
  refine ⟨(QuotientGroup.mk' cubes) a, ⟨a, ha, rfl⟩, ?_⟩
  change (QuotientGroup.mk' G.Δ) a = δ
  exact Quotient.out_eq δ

/-- Rational Bstar representatives refine any surjective family of Borel cusp representatives. -/
theorem rational_cusp_factorization (P : CoverPackage D S H A)
    (G : GlobalDatum P)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    {ι : Type} (σ : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (hσ : Function.Surjective
      (fun p : (Σ i, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) =>
        Quotient.mk
          (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F))
          ((σ p.1)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))))
    (g : GL (Fin 2) F) :
    ∃ (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i))
      (δ : Fˣ) (b : GL (Fin 2) F), b ∈ Bstar G ∧
      g = b * diagGL δ * Matrix.SpecialLinearGroup.toGL
        ((σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
          ((q.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) := by
  classical
  have hdiag (δ : Fˣ) : Matrix.GeneralLinearGroup.det (diagGL δ) = δ := by
    apply Units.ext
    change (diagGL δ : Matrix (Fin 2) (Fin 2) F).det = (δ : F)
    simp [diagGL, Matrix.det_fin_two]
  let d : Fˣ := Matrix.GeneralLinearGroup.det g
  have hk : (diagGL d)⁻¹ * g ∈ Matrix.GeneralLinearGroup.det.ker := by
    change Matrix.GeneralLinearGroup.det ((diagGL d)⁻¹ * g) = 1
    rw [map_mul, map_inv, hdiag]
    exact inv_mul_cancel d
  rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hk
  obtain ⟨γ, hγ⟩ := hk
  obtain ⟨⟨i, q⟩, hq⟩ := hσ (Quotient.mk _ γ)
  let c : Matrix.SpecialLinearGroup (Fin 2) F :=
    (σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
      ((q.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
  change Quotient.mk (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F)) c =
    Quotient.mk (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F)) γ at hq
  let u : Matrix.SpecialLinearGroup (Fin 2) F := γ * c⁻¹
  have hu : u 1 0 = 0 :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  let a : GL (Fin 2) F := diagGL d * Matrix.SpecialLinearGroup.toGL u
  have hga : g = a * Matrix.SpecialLinearGroup.toGL c := by
    calc
      g = diagGL d * Matrix.SpecialLinearGroup.toGL γ := by rw [hγ]; group
      _ = (diagGL d * Matrix.SpecialLinearGroup.toGL (γ * c⁻¹)) *
          Matrix.SpecialLinearGroup.toGL c := by rw [map_mul, map_inv]; group
      _ = _ := rfl
  let M : Matrix (Fin 2) (Fin 2) F := a
  have h10 : M 1 0 = 0 := by
    change ((diagGL d : Matrix (Fin 2) (Fin 2) F) *
      (u : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0
    simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two, hu]
  have hdet : M 0 0 * M 1 1 ≠ 0 := by
    have hd := Matrix.GeneralLinearGroup.det_ne_zero a
    change M.det ≠ 0 at hd
    simpa only [Matrix.det_fin_two, h10, mul_zero, sub_zero] using hd
  have h00 : M 0 0 ≠ 0 := (mul_ne_zero_iff.mp hdet).1
  have h11 : M 1 1 ≠ 0 := (mul_ne_zero_iff.mp hdet).2
  let δ : Fˣ := Units.mk0 (M 0 0 / M 1 1) (div_ne_zero h00 h11)
  let b : GL (Fin 2) F :=
    scalarGL (Units.mk0 (M 1 1) h11) * upperGL (M 0 1 / M 1 1)
  have hb : b ∈ Bstar G := by
    refine ⟨?_, 1, G.Δ.one_mem, ?_⟩
    · simp [b, scalarGL, upperGL, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [b, scalarGL, upperGL, Matrix.mul_apply, Fin.sum_univ_two]
  have ha : a = b * diagGL δ := by
    apply Units.ext
    change M = (b : Matrix (Fin 2) (Fin 2) F) * (diagGL δ : Matrix (Fin 2) (Fin 2) F)
    ext j k
    fin_cases j <;> fin_cases k
    all_goals simp [b, δ, scalarGL, upperGL, diagGL, Matrix.mul_apply,
      Fin.sum_univ_two, h10]
    all_goals field_simp
  refine ⟨i, q, δ, b, hb, ?_⟩
  exact hga.trans (congrArg (fun t => t * Matrix.SpecialLinearGroup.toGL c) ha)

/-- The finite torus support remains uniform over integral translates of a finite rational family. -/
theorem finite_integral_translate_torus_support
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) {ι : Type} [Fintype ι]
    (c : ι → GL (Fin 2) F) (r : P.RP) :
    ∃ U : Set (Fˣ ⧸ G.Δ), U.Finite ∧
      ∀ (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
        {δ : Fˣ ⧸ G.Δ |
          (∏ᶠ v, G.lam v (Fs.f v
            ((P.loc v).a (toLoc v (Quotient.out δ)) *
              P.compF v (P.ratRP
                (c i * Matrix.SpecialLinearGroup.toGL
                  (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * r)))) ≠ 0} ⊆ U := by
  classical
  let W : Finset (FinPlace F) := Fs.T0 ∪ (P.comp_restricted r).toFinset ∪
    Finset.univ.biUnion (fun i : ι => (P.comp_restricted (P.ratRP (c i))).toFinset)
  have hW : Fs.T0 ⊆ W := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  have hIntegral (v : FinPlace F) (hSf : v ∉ S.Sf)
      (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      (P.loc v).pr (P.compF v (P.ratRP (Matrix.SpecialLinearGroup.toGL
        (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)))) ∈
        (P.loc v).pr '' ((P.tame v hSf).Kmax : Set (P.loc v).L) := by
    rw [P.compF_ratRP, (P.loc v).sec_pr, (P.tame v hSf).image]
    let k : GL (Fin 2) (v.adicCompletion F) :=
      Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ))
    refine ⟨k, ?_, ?_, rfl⟩
    · intro j l
      change ((algebraMap (𝓞 F) F (γ j l) : F) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F
      exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v (γ j l)
    · have hdet : Matrix.GeneralLinearGroup.det k = 1 := by
        simp [k, Matrix.GeneralLinearGroup.map_det]
      have hdetinv : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = 1 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, hdet]
        rfl
      rw [hdetinv]
      exact (v.adicCompletionIntegers F).one_mem
  have hproj (v : FinPlace F) (a b : GL (Fin 2) F) :
      (P.loc v).pr (P.compF v (P.ratRP (a * b))) =
        (P.loc v).pr (P.compF v (P.ratRP a)) *
          (P.loc v).pr (P.compF v (P.ratRP b)) := by
    simp only [P.compF_ratRP, (P.loc v).sec_pr, map_mul, QuotientGroup.mk_mul]
  obtain ⟨U, hU, hcover⟩ := finite_torus_scalar_support_uniform P G Fs W hW
  refine ⟨U, hU, ?_⟩
  intro i γ
  apply hcover
  intro v hv
  have hSf : v ∉ S.Sf := fun h => hv (hW (Fs.sub h))
  have hVr : v ∉ (P.comp_restricted r).toFinset := by
    intro h
    exact hv (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
  have hVc : v ∉ (P.comp_restricted (P.ratRP (c i))).toFinset := by
    intro h
    exact hv (Finset.mem_union.mpr (Or.inr
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)))
  have hkr : P.compF v r ∈ (P.tame v hSf).Kmax := by
    by_contra h
    exact hVr ((P.comp_restricted r).mem_toFinset.mpr ⟨hSf, h⟩)
  have hkc : P.compF v (P.ratRP (c i)) ∈ (P.tame v hSf).Kmax := by
    by_contra h
    exact hVc ((P.comp_restricted (P.ratRP (c i))).mem_toFinset.mpr ⟨hSf, h⟩)
  obtain ⟨k, hk, hkpr⟩ := hIntegral v hSf γ
  refine ⟨P.compF v (P.ratRP (c i)) * k * P.compF v r,
    (P.tame v hSf).Kmax.mul_mem ((P.tame v hSf).Kmax.mul_mem hkc hk) hkr, ?_⟩
  simp only [map_mul, hkpr, hproj]

/-- Finite-place scalar products are uniformly bounded on integral translates of a finite rational family. -/
theorem finite_scalar_integral_translate_bound
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) {ι : Type} [Fintype ι]
    (c : ι → GL (Fin 2) F) (r : P.RP) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
        ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v
          (P.ratRP (c i * Matrix.SpecialLinearGroup.toGL
            (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * r)))‖ ≤ C := by
  classical
  let j : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) →* GL (Fin 2) F :=
    Matrix.SpecialLinearGroup.toGL.comp (ArtinPrimitiveRoots.A1.Spec.toSLF F)
  let jv (v : FinPlace F) :
      Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) →* GL (Fin 2) (v.adicCompletion F) :=
    (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))).comp j
  let Kint (v : FinPlace F) : Set (GL (Fin 2) (v.adicCompletion F)) :=
    {k | (∀ a b, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) a b ∈
      v.adicCompletionIntegers F) ∧ ∀ a b,
        ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F}
  let R (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) : P.RP :=
    P.ratRP (c i * j γ) * r
  let bcoeff (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) (v : FinPlace F) : ℂ :=
    G.lam v (Fs.f v (P.compF v (R i γ)))
  have hentries (v : FinPlace F) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (a b : Fin 2) : (jv v γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) a b ∈
        v.adicCompletionIntegers F := by
    change ((algebraMap (𝓞 F) F (γ a b) : F) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F
    exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v (γ a b)
  have hKint (v : FinPlace F) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      jv v γ ∈ Kint v := by
    refine ⟨hentries v γ, ?_⟩
    intro a b
    rw [← map_inv]
    exact hentries v γ⁻¹ a b
  have hlocal (i : ι) (v : FinPlace F) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F), ‖bcoeff i γ v‖ ≤ C := by
    let φ : GL (Fin 2) (v.adicCompletion F) → PGL2 (v.adicCompletion F) :=
      fun k => QuotientGroup.mk
        (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (c i) * k) *
          (P.loc v).pr (P.compF v r)
    have hφ : Continuous φ := by
      dsimp only [φ]
      have hleft : Continuous (fun k : GL (Fin 2) (v.adicCompletion F) =>
          Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (c i) * k) :=
        continuous_const.mul continuous_id
      have hquot : Continuous (fun k : GL (Fin 2) (v.adicCompletion F) =>
          (QuotientGroup.mk
            (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (c i) * k) :
              PGL2 (v.adicCompletion F))) := QuotientGroup.continuous_mk.comp hleft
      exact hquot.mul continuous_const
    let K : Set (P.loc v).L := (P.loc v).pr ⁻¹' (φ '' Kint v)
    have hK : IsCompact K := local_cover_compact_preimage (P.loc v) _
      ((local_integral_units_compact v).image hφ)
    obtain ⟨B, hB, hbound⟩ := section_norm_bound_on_compact
      (P.loc v) (G.T v) (Fs.f v) (Fs.f_sec v) K hK
    let lam : (G.T v).V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (G.lam v)
    refine ⟨‖lam‖ * B, mul_nonneg (norm_nonneg _) hB, ?_⟩
    intro γ
    have hmem : P.compF v (R i γ) ∈ K := by
      refine ⟨jv v γ, hKint v γ, ?_⟩
      simp only [φ, R, jv, MonoidHom.comp_apply, map_mul, P.compF_ratRP,
        (P.loc v).sec_pr, QuotientGroup.mk_mul]
    exact (lam.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hbound _ hmem) (norm_nonneg lam))
  choose Cv hCv hCvbound using hlocal
  let W : Finset (FinPlace F) := Fs.T0 ∪ (P.comp_restricted r).toFinset ∪
    Finset.univ.biUnion (fun i : ι => (P.comp_restricted (P.ratRP (c i))).toFinset)
  have hW : Fs.T0 ⊆ W := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  let pj (v : FinPlace F) (a : GL (Fin 2) F) : PGL2 (v.adicCompletion F) :=
    (P.loc v).pr (P.compF v (P.ratRP a))
  have hpj (v : FinPlace F) (a b : GL (Fin 2) F) :
      pj v (a * b) = pj v a * pj v b := by
    simp only [pj, P.compF_ratRP, (P.loc v).sec_pr, map_mul, QuotientGroup.mk_mul]
  have hIntegral (v : FinPlace F) (hSf : v ∉ S.Sf)
      (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      pj v (j γ) ∈ (P.loc v).pr '' ((P.tame v hSf).Kmax : Set (P.loc v).L) := by
    dsimp only [pj]
    rw [P.compF_ratRP, (P.loc v).sec_pr, (P.tame v hSf).image]
    refine ⟨jv v γ, hentries v γ, ?_, rfl⟩
    have hdet : Matrix.GeneralLinearGroup.det (jv v γ) = 1 := by
      simp [jv, j, Matrix.GeneralLinearGroup.map_det]
    have hdetinv : (jv v γ)⁻¹.val.det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, hdet]
      rfl
    rw [hdetinv]
    exact (v.adicCompletionIntegers F).one_mem
  have hprojTame (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (v : FinPlace F) (hv : v ∉ W) :
      (P.loc v).pr (P.compF v (R i γ)) ∈ (P.loc v).pr ''
        ((P.tame v (fun h => hv (hW (Fs.sub h)))).Kmax : Set (P.loc v).L) := by
    have hSf : v ∉ S.Sf := fun h => hv (hW (Fs.sub h))
    have hVr : v ∉ (P.comp_restricted r).toFinset := by
      intro h
      exact hv (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
    have hVc : v ∉ (P.comp_restricted (P.ratRP (c i))).toFinset := by
      intro h
      exact hv (Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)))
    have hkr : P.compF v r ∈ (P.tame v hSf).Kmax := by
      by_contra h
      exact hVr ((P.comp_restricted r).mem_toFinset.mpr ⟨hSf, h⟩)
    have hkc : P.compF v (P.ratRP (c i)) ∈ (P.tame v hSf).Kmax := by
      by_contra h
      exact hVc ((P.comp_restricted (P.ratRP (c i))).mem_toFinset.mpr ⟨hSf, h⟩)
    obtain ⟨k, hk, hkpr⟩ := hIntegral v hSf γ
    refine ⟨P.compF v (P.ratRP (c i)) * k * P.compF v r,
      (P.tame v hSf).Kmax.mul_mem ((P.tame v hSf).Kmax.mul_mem hkc hk) hkr, ?_⟩
    simp only [R, map_mul]
    change (pj v (c i) * (P.loc v).pr k) * (P.loc v).pr (P.compF v r) =
      pj v (c i * j γ) * (P.loc v).pr (P.compF v r)
    rw [hkpr, hpj]
  have hunitnorm (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (v : FinPlace F) (hv : v ∉ W) : ‖bcoeff i γ v‖ = 1 := by
    have hT0 : v ∉ Fs.T0 := fun h => hv (hW h)
    have hSf : v ∉ S.Sf := fun h => hT0 (Fs.sub h)
    obtain ⟨k, hk, hkpr⟩ := hprojTame i γ v hv
    have hker : P.compF v (R i γ) * k⁻¹ ∈ (P.loc v).pr.ker := by
      change (P.loc v).pr (P.compF v (R i γ) * k⁻¹) = 1
      rw [map_mul, map_inv, ← hkpr, mul_inv_cancel]
    rw [(P.loc v).pr_ker] at hker
    obtain ⟨ζ, hζ⟩ := hker
    have hcomp : P.compF v (R i γ) = (P.loc v).z ζ * k := by
      rw [hζ]
      simp only [inv_mul_cancel_right]
    have hfk : Fs.f v k = Fs.f v 1 := by
      simpa only [one_mul] using (Fs.f_sph v hT0).2 1 k hk
    have hcoeff : bcoeff i γ v = ((ζ : ℂˣ) : ℂ) := by
      dsimp only [bcoeff]
      rw [hcomp, (Fs.f_sec v).2.1, map_smul, hfk, (Fs.f_sph v hT0).1,
        G.lam_tame v hSf 0]
      simp
    have hζpow : (((ζ : ℂˣ) : ℂ)) ^ 3 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun u : ℂˣ => (u : ℂ)) ((mem_rootsOfUnity 3 (ζ : ℂˣ)).mp ζ.property)
    rw [hcoeff]
    exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hζpow⟩).norm_eq_one
  let Ci (i : ι) : ℝ := ∏ v ∈ W, Cv i v
  have hCi (i : ι) : 0 ≤ Ci i := Finset.prod_nonneg fun v _ => hCv i v
  refine ⟨∑ i, Ci i, Finset.sum_nonneg (fun i _ => hCi i), ?_⟩
  intro i γ
  change ‖∏ᶠ v, bcoeff i γ v‖ ≤ ∑ a, Ci a
  have hsupp : (Function.mulSupport (bcoeff i γ)).Finite :=
    (scalarOf_q P G Fs (R i γ)).1
  have heqnorm : ‖∏ᶠ v, bcoeff i γ v‖ = ∏ v ∈ W, ‖bcoeff i γ v‖ := by
    change (normHom.toMonoidHom : ℂ →* ℝ) (∏ᶠ v, bcoeff i γ v) = _
    rw [(normHom.toMonoidHom : ℂ →* ℝ).map_finprod hsupp]
    change (∏ᶠ v, ‖bcoeff i γ v‖) = _
    exact finprod_eq_prod_of_mulSupport_subset _
      (Function.mulSupport_subset_iff'.mpr fun v hv => hunitnorm i γ v hv)
  rw [heqnorm]
  exact (Finset.prod_le_prod₀ (fun v _ => norm_nonneg (bcoeff i γ v))
    (fun v _ => hCvbound i v γ)).trans
      (Finset.single_le_sum (fun a _ => hCi a) (Finset.mem_univ i))

/-- Uniform scalar height bounds over integral translates of a finite cusp and torus family. -/
theorem scalar_cusp_height_majorant
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) {ι : Type} [Fintype ι]
    (c : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (δ : ι → Fˣ) (r : P.RP) :
    ∃ z : ArtinPrimitiveRoots.A1.Spec.X F, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
        ‖scalarOf P G Fs.f Fs.fC
          (P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL
            (c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * P.q r)‖ ≤
          C * ArtinPrimitiveRoots.A1.Spec.normHeight F
            ((c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • z) ^ (1 + 2 * s.re) := by
  classical
  choose Cw hCw hbound using fun w =>
    sectionC_norm_majorant s (Fs.fC w) (Fs.fC_sec w).1 (Fs.fC_sec w).2
  obtain ⟨z, hz⟩ := complex_spherical_height_product (fun w => P.compC w r)
  obtain ⟨Cf, hCf, hfbound⟩ := finite_scalar_integral_translate_bound P G Fs
    (fun i => diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (c i)) r
  let t (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :=
    c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ
  let R (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) : P.RP :=
    P.ratRP (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * r
  let y (i : ι) (w : InfinitePlace F) : ℂˣ := Units.map w.embedding.toMonoidHom (δ i)
  let U (w : InfinitePlace F) (a : Matrix.SpecialLinearGroup (Fin 2) F) : PGL2 ℂ :=
    QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
      (ArtinPrimitiveRoots.A1.Spec.toInf F a w)) * P.compC w r
  let A (i : ι) (w : InfinitePlace F) : ℝ :=
    ‖(Complex.normSq (y i w : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)‖ * Cw w
  let Ai (i : ι) : ℝ := ∏ w, A i w
  have hA (i : ι) (w : InfinitePlace F) : 0 ≤ A i w :=
    mul_nonneg (norm_nonneg _) (hCw w)
  have hAi (i : ι) : 0 ≤ Ai i := Finset.prod_nonneg fun w _ => hA i w
  have hdiag (i : ι) (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (diagGL (δ i)) = diagM ℂ (y i w) := by
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, y]
  have hsl (w : InfinitePlace F) (a : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix.GeneralLinearGroup.map w.embedding (Matrix.SpecialLinearGroup.toGL a) =
        Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toInf F a w) := by
    apply Units.ext
    rfl
  have hcomp (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) (w : InfinitePlace F) :
      P.compC w (R i γ) = QuotientGroup.mk (diagM ℂ (y i w)) * U w (t i γ) := by
    dsimp only [R]
    rw [map_mul, P.compC_ratRP, map_mul, hdiag, hsl, QuotientGroup.mk_mul]
    exact mul_assoc _ _ _
  have hzero : upperM ℂ 0 = 1 := by
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;> simp [upperM]
  have hsec (w : InfinitePlace F) (a : ℂˣ) (k : PGL2 ℂ) :
      Fs.fC w (QuotientGroup.mk (diagM ℂ a) * k) =
        (Complex.normSq (a : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s) * Fs.fC w k := by
    simpa only [hzero, QuotientGroup.mk_one, one_mul] using (Fs.fC_sec w).1 0 a k
  have hlocal (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) (w : InfinitePlace F) :
      ‖Fs.fC w (P.compC w (R i γ))‖ ≤ A i w * ‖sphC (s.re : ℂ) (U w (t i γ))‖ := by
    rw [hcomp, hsec, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbound w (U w (t i γ))) (norm_nonneg _)).trans_eq
      (by dsimp [A]; ring)
  have hheight (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      (∏ w, ‖sphC (s.re : ℂ) (U w (t i γ))‖) =
        ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^ (1 + 2 * s.re) :=
    hz s.re (t i γ)
  have hheight_nonneg (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      0 ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^ (1 + 2 * s.re) := by
    rw [← hheight]
    exact Finset.prod_nonneg fun w _ => norm_nonneg _
  have hinf (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      (∏ w, ‖Fs.fC w (P.compC w (R i γ))‖) ≤
        Ai i * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^ (1 + 2 * s.re) := by
    calc
      _ ≤ ∏ w, A i w * ‖sphC (s.re : ℂ) (U w (t i γ))‖ :=
        Finset.prod_le_prod₀ (fun w _ => norm_nonneg _) (fun w _ => hlocal i γ w)
      _ = _ := by rw [Finset.prod_mul_distrib, hheight]
  refine ⟨z, Cf * ∑ i, Ai i, mul_nonneg hCf (Finset.sum_nonneg fun i _ => hAi i), ?_⟩
  intro i γ
  have hq : P.q (R i γ) =
      P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * P.q r := by
    simp only [R, map_mul, P.q_ratRP]
  change ‖scalarOf P G Fs.f Fs.fC
    (P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * P.q r)‖ ≤ _
  rw [← hq, (scalarOf_q P G Fs (R i γ)).2, norm_mul, norm_prod]
  have hf : ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v (R i γ)))‖ ≤ Cf := by
    simpa only [R, t, map_mul, mul_assoc] using hfbound i γ
  calc
    _ ≤ Cf * (Ai i * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^
        (1 + 2 * s.re)) :=
      mul_le_mul hf (hinf i γ) (Finset.prod_nonneg fun w _ => norm_nonneg _) hCf
    _ = (Cf * Ai i) * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^
        (1 + 2 * s.re) := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun a _ => hAi a) (Finset.mem_univ i)) hCf)
      (hheight_nonneg i γ)

/-- Every nonzero scalar summand has a cusp representative in one finite torus family. -/
theorem finite_supported_cusp_representatives
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    {ι : Type} [Fintype ι] (σ : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (hσ : Function.Surjective
      (fun p : (Σ i, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) =>
        Quotient.mk
          (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F))
          ((σ p.1)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))))
    (r : P.RP) :
    ∃ U : Set (Fˣ ⧸ G.Δ), U.Finite ∧
      ∀ β : Quotient (QuotientGroup.rightRel (Bstar G)),
        scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * P.q r) ≠ 0 →
        ∃ (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i))
          (δ : Fˣ ⧸ G.Δ), δ ∈ U ∧
            β = Quotient.mk (QuotientGroup.rightRel (Bstar G))
              (diagGL (Quotient.out δ) * Matrix.SpecialLinearGroup.toGL
                ((σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
                  ((q.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))) := by
  classical
  obtain ⟨U, hU, hsupport⟩ := finite_integral_translate_torus_support P G Fs
    (fun i => Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹)) r
  have hdiag_mul (a d : Fˣ) : diagGL (a * d) = diagGL a * diagGL d := by
    apply Units.ext
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hdiag_mem (a : Fˣ) (ha : a ∈ G.Δ) : diagGL a ∈ Bstar G := by
    change (diagGL a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ d ∈ G.Δ, (diagGL a : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (d : F) * (diagGL a : Matrix (Fin 2) (Fin 2) F) 1 1
    exact ⟨by simp [diagGL], a, ha, by simp [diagGL]⟩
  have hcomp (a : Fˣ) (x : P.RP) (v : FinPlace F) :
      P.compF v (P.ratRP (diagGL a) * x) =
        (P.loc v).a (toLoc v a) * P.compF v x := by
    have hdiag : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (diagGL a) = diagM (v.adicCompletion F) (toLoc v a) := by
      apply Units.ext
      ext j l
      fin_cases j <;> fin_cases l <;>
        simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, toLoc]
    rw [map_mul, P.compF_ratRP, hdiag, ← (P.loc v).sec_a]
  refine ⟨U, hU, ?_⟩
  intro β hβ
  obtain ⟨i, q, a, b, hb, hfactor⟩ :=
    rational_cusp_factorization P G Γ σ hσ (Quotient.out β)
  let γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) := (q.out : Γ)
  let k : GL (Fin 2) F := Matrix.SpecialLinearGroup.toGL
    ((σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ)
  let δ : Fˣ ⧸ G.Δ := QuotientGroup.mk a
  let d : Fˣ := Quotient.out δ
  let e : Fˣ := a * d⁻¹
  have he : e ∈ G.Δ := by
    have heq : (QuotientGroup.mk a : Fˣ ⧸ G.Δ) = QuotientGroup.mk d :=
      (QuotientGroup.out_eq' δ).symm
    simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem.mp heq)
  let b' : GL (Fin 2) F := b * diagGL e
  have hb' : b' ∈ Bstar G := (Bstar G).mul_mem hb (hdiag_mem e he)
  have had : a = e * d := by dsimp only [e]; group
  have hfactor' : Quotient.out β = b' * (diagGL d * k) := by
    change Quotient.out β = b * diagGL a * k at hfactor
    rw [hfactor, had, hdiag_mul]
    dsimp only [b']
    group
  have hscalar :
      scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * P.q r) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL d * k) * P.q r) := by
    rw [hfactor', map_mul, mul_assoc]
    exact (scalarOf_invariance P G Fs).1 b' hb' _
  let x : P.RP := P.ratRP k * r
  let y : P.RP := P.ratRP (diagGL d) * x
  have hq : P.q y = P.tc.rat (diagGL d * k) * P.q r := by
    simp only [y, x, map_mul, P.q_ratRP, mul_assoc]
  have hnonzero : scalarOf P G Fs.f Fs.fC (P.q y) ≠ 0 := by
    rw [hq]
    exact fun h => hβ (hscalar.trans h)
  rw [(scalarOf_q P G Fs y).2] at hnonzero
  have hfinite :
      (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v d) * P.compF v x))) ≠ 0 := by
    simpa only [y, hcomp] using (mul_ne_zero_iff.mp hnonzero).1
  have hk : k = Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹) *
      Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ) := by
    dsimp only [k]
    rw [map_mul]
  have hδ : δ ∈ U := by
    apply hsupport i γ
    change (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v d) *
      P.compF v (P.ratRP (Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹) *
        Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * r)))) ≠ 0
    simpa only [x, hk] using hfinite
  refine ⟨i, q, δ, hδ, ?_⟩
  change β = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (diagGL d * k)
  calc
    β = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (Quotient.out β) :=
      (Quotient.out_eq β).symm
    _ = _ := by
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      rw [hfactor']
      simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using (Bstar G).inv_mem hb'

/-- Finite cusp majorants after bounding the complex components by real spherical sections. -/
theorem eisenstein_finite_majorants (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (C : InfinitePlace F → ℝ) (hC : ∀ w, 0 ≤ C w)
    (hbound : ∀ w k, ‖Fs.fC w k‖ ≤ C w * ‖sphC (s.re : ℂ) k‖) :
    ∃ (n : ℕ) (m : Fin n → Quotient (QuotientGroup.rightRel (Bstar G)) → ℝ),
      (∀ i, Summable (m i)) ∧ ∀ γ,
        ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out γ) * g)‖ ≤ ∑ i, m i γ := by
  sorry

/-- **eis:converge** (via P-REDUCTION and P-SPEC `eisSeries_majorant`): absolute convergence for
`Re s > 1/2`. C6 of `sol-gate-theta` strengthens the input datum to exclude divergent cube repeats. -/
theorem eisenstein_summable (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G) :
    Summable fun γ : Quotient (QuotientGroup.rightRel (Bstar G)) =>
      ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out γ) * g)‖ := by
  classical
  choose C hC hbound using fun w =>
    sectionC_norm_majorant s (Fs.fC w) (Fs.fC_sec w).1 (Fs.fC_sec w).2
  obtain ⟨n, m, hm, hmajorant⟩ := eisenstein_finite_majorants P G hs Fs g C hC hbound
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmajorant
  exact summable_sum fun i _ => hm i

/-- **eis:automorphic**: in the convergence region `E` is automorphic, genuine, and right-invariant
under every element fixing all local sections. -/
theorem eisenstein_automorphic (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) :
    (∀ γ g, eisenstein P G Fs (P.tc.rat γ * g) = eisenstein P G Fs g) ∧
    (∀ ζ g, eisenstein P G Fs (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * eisenstein P G Fs g) ∧
    (∀ k : P.tc.G, (∀ h, scalarOf P G Fs.f Fs.fC (h * k) = scalarOf P G Fs.f Fs.fC h) →
      ∀ g, eisenstein P G Fs (g * k) = eisenstein P G Fs g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ g
    exact leftCosetSum_rightTranslate (Bstar G) P.tc.rat
      (scalarOf P G Fs.f Fs.fC) (scalarOf_invariance P G Fs).1 γ g
  · intro ζ g
    unfold eisenstein
    calc
      _ = ∑' q : Quotient (QuotientGroup.rightRel (Bstar G)),
          ((ζ : ℂˣ) : ℂ) * scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out q) * g) := by
        apply tsum_congr
        intro q
        rw [← mul_assoc, ← P.tc.z_central ζ, mul_assoc]
        exact (scalarOf_invariance P G Fs).2.2.2 ζ _
      _ = _ := tsum_mul_left
  · intro k hk g
    unfold eisenstein
    apply tsum_congr
    intro q
    simpa only [← mul_assoc] using hk (P.tc.rat (Quotient.out q) * g)

/-- The infinite embedding `F → ℂ^{places}`. -/
def infEmbA : F →+* (InfinitePlace F → ℂ) := RingHom.pi fun w => w.embedding

/-- `n(x)` at the archimedean places. -/
def nInf (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) : P.tc.G :=
  P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x))

/-- Joint smoothness on the left and right archimedean root orbits. C11 of `sol-gate-theta`
uses this condition for mixed derivatives and differentiation under torus integrals. -/
def JointRootSmooth (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) : Prop :=
  ∀ g : P.tc.G, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) =>
      Ψ (nInf P p.1 * g * nInf P p.2))

/-- `n(ξ)` at the finite places, for rational `ξ`: `rat(n(ξ)) · n_∞(-ξ)`. -/
def nFin (P : CoverPackage D S H A) (ξ : F) : P.tc.G :=
  P.tc.rat (upperGL ξ) * nInf P (-(infEmbA ξ))

/-- `ψ_∞(ν x) = Π_w ψ_w(ν_w x_w)`. -/
def psiInf (ν : F) (x : InfinitePlace F → ℂ) : ℂ := ∏ w, psiC (w.embedding ν * x w)

/-- **def:torus-coefficient**: the `ν`-th Fourier coefficient along `N(F_∞)` over a fundamental
domain `Pd` of a period lattice. -/
def torusCoeff (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (Pd : Set (InfinitePlace F → ℂ)) (ν : F) : ℂ :=
  ((volume Pd).toReal)⁻¹ * ∫ x in Pd, Ψ (nInf P x * g) * psiInf (-ν) x

/-- `κ_F = vol(F\𝔸)` for `Π_v μ_v × Lebesgue`: the covolume `2^{-r}|d_F|^{1/2}` of `O_F ⊂ ℂ^r`. -/
def κF (F : Type) [Field F] [NumberField F] : ℝ :=
  (2 : ℝ) ^ (-(numComplex F : ℤ)) * Real.sqrt |(NumberField.discr F : ℝ)|

/-- `Π_{v ∉ T0} c_v(s)` (P-RES identifies it with `ζ_F^{T0}(6s)/ζ_F^{T0}(6s+1)`). -/
def cprod (T0 : Finset (FinPlace F)) (s : ℂ) : ℂ := ∏' v : {v : FinPlace F // v ∉ T0}, cv v.1 s

/-- The spherical vector of `I(T.weyl, -s)` at `v ∉ T0` (from `spherical_section`). -/
def sphWeyl (P : CoverPackage D S H A) (G : GlobalDatum P) (v : FinPlace F) (hv : v ∉ S.Sf)
    (s : ℂ) : (P.loc v).L → (G.T v).V :=
  (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
    (fun h => hv (S.over6 v h)) (-s)).choose

/-- **def:intertwined-scalar**: `Φ^M = κ_F⁻¹ · Π_{v∉T0} c_v(s) · scalar section of
`(M_v f_v)_{v∈T0} ⊗ (f°'_v)_{v∉T0} ⊗ (M_w f_w)_w`. -/
def scalarM (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G) : ℂ :=
  (κF F)⁻¹ * cprod Fs.T0 s *
    scalarOf P G (fun v => if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
        else sphWeyl P G v (fun h => hv (Fs.sub h)) s)
      (fun w => intertwineC (Fs.fC w)) g

/-- **def:whittaker-E**: the unfolded Whittaker coefficient
`W_E(g) = κ_F⁻¹ Σ_{δ ∈ F^×/Δ} Π_v lam_v(σ_v(a(δ)) 𝒥_v(π(g_v) f_v)) · Π_w 𝒥_w(π(g_w) f_w)`. -/
def whittakerE (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G) : ℂ :=
  (κF F)⁻¹ * ∑' δ : Fˣ ⧸ G.Δ,
    (∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
      (jacquet (P.loc v) A (μ v) (rtr (P.compF v (Function.surjInv P.q_surj g)) (Fs.f v))))) *
    ∏ w, jacquetC (rtr (P.compC w (Function.surjInv P.q_surj g)) (Fs.fC w))

/-- **eis:constant-term** (KP Prop. II.1.2 replaced): for `Re s > 1/2`, over a period lattice
`𝔞 ⊆ F` (a nonzero fractional ideal) whose finite translations fix all sections at `g`. -/
theorem eisenstein_constantTerm (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume) :
    torusCoeff P (eisenstein P G Fs) g Pd 0 =
      ∑' δ : Fˣ ⧸ G.Δ, (scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL (Quotient.out δ)) * g) +
        scalarM P G μ Fs (P.tc.rat (diagGL (Quotient.out δ)) * g)) := by
  sorry

/-- **eis:whittaker** (unfolding): the `ν`-th torus coefficient is `W_E(a(ν) g)`, for `ν` in the dual
lattice. -/
theorem eisenstein_whittaker (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) :
    torusCoeff P (eisenstein P G Fs) g Pd (ν : F) =
      whittakerE P G μ Fs (P.tc.rat (diagGL ν) * g) := by
  sorry

/-- **eis:whittaker-equiv**: `W_E` is genuine, `(N(F_S), e)`- and `(N(K_v), ψ_v)`-equivariant,
right-invariant like the sections, and vanishes at `a(ν)g` for `ν` outside the dual lattice. -/
theorem whittakerE_equiv (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) :
    (∀ ζ g, whittakerE P G μ Fs (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * whittakerE P G μ Fs g) ∧
    (∀ x g, whittakerE P G μ Fs (P.tc.nS (Multiplicative.ofAdd x) * g) =
      S.e A x * whittakerE P G μ Fs g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, whittakerE P G μ Fs (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * whittakerE P G μ Fs g) ∧
    (∀ k : P.tc.G, (∀ h, scalarOf P G Fs.f Fs.fC (h * k) = scalarOf P G Fs.f Fs.fC h) →
      ∀ g, whittakerE P G μ Fs (g * k) = whittakerE P G μ Fs g) := by
  sorry

/-- **eis:multilinear** (linearity at the places of `S_f`): with the exterior and complex data fixed,
`W_E(g)` is a multilinear form in the local Jacquet vectors at `S_f`. The convergence half-plane
is required per `sol-thin-thglobal` for the defining `tsum`. -/
theorem whittakerE_multilinear (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s) (x0 : P.RP)
    (hs : (1 / 2 : ℝ) < s.re) :
    ∃ Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ,
      ∀ (Fs' : GlobalSection P G s) (x : P.RP), (∀ v, v ∉ S.Sf → Fs'.f v = Fs.f v) →
        Fs'.fC = Fs.fC → (∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0) →
        whittakerE P G μ Fs' (P.q x) =
          Λ (fun v => jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x) (Fs'.f v.1))) *
            ∏ w, jacquetC (rtr (P.compC w x) (Fs'.fC w)) := by
  sorry

end Eis

end ArtinPrimitiveRoots.A1.Theta
