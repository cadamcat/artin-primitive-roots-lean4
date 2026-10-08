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
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) := ⊤
  letI : Γ.FiniteIndex := by dsimp only [Γ]; infer_instance
  obtain ⟨ι, hι, σ, hσ⟩ := ArtinPrimitiveRoots.A1.Spec.exists_cusp_reps F Γ
  letI : Fintype ι := hι
  obtain ⟨r, rfl⟩ := P.q_surj g
  obtain ⟨U, hU, hcover⟩ := finite_supported_cusp_representatives P G Fs Γ σ hσ.2 r
  letI : Fintype U := hU.fintype
  let J := U × ι
  obtain ⟨z, C0, hC0, hscalar⟩ := scalar_cusp_height_majorant P G Fs
    (fun j : J => (σ j.2)⁻¹) (fun j : J => Quotient.out j.1.1) r
  choose m hm hmbound using fun i =>
    ArtinPrimitiveRoots.A1.Spec.eisSeries_majorant F Γ (σ i)
      ({z} : Set (ArtinPrimitiveRoots.A1.Spec.X F)) isCompact_singleton s.re s.re hs
  have hm_bound (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) :
      ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ i) (s.re : ℂ) z q‖ ≤ m i q := by
    exact hmbound i z (Set.mem_singleton z) (s.re : ℂ) (by simp) (by simp) q
  have hm_nonneg (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) :
      0 ≤ m i q := (norm_nonneg _).trans (hm_bound i q)
  let Ξ := Σ j : J, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ j.2)
  let M : Ξ → ℝ := fun p => C0 * m p.1.2 p.2
  have hM_nonneg (p : Ξ) : 0 ≤ M p := mul_nonneg hC0 (hm_nonneg p.1.2 p.2)
  have hM : Summable M := by
    apply (summable_sigma_of_nonneg hM_nonneg).2
    constructor
    · intro j
      exact (hm j.2).mul_left C0
    · exact (hasSum_fintype _).summable
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let f : Q → ℝ := fun β =>
    ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * P.q r)‖
  let V : Set Q := Function.support f
  let a (p : Ξ) : GL (Fin 2) F :=
    diagGL (Quotient.out p.1.1.1) * Matrix.SpecialLinearGroup.toGL
      ((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
        ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
  let ret : Ξ → Q := fun p => Quotient.mk (QuotientGroup.rightRel (Bstar G)) (a p)
  have hparam : ∀ β : V, ∃ p : Ξ, ret p = β.1 := by
    intro β
    have hn : scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β.1) * P.q r) ≠ 0 :=
      norm_ne_zero_iff.mp β.property
    obtain ⟨i, q, δ, hδ, heq⟩ := hcover β.1 hn
    exact ⟨⟨(⟨δ, hδ⟩, i), q⟩, heq.symm⟩
  choose φ hφ using hparam
  have hφinj : Function.Injective φ := by
    intro β η heq
    apply Subtype.ext
    calc
      β.1 = ret (φ β) := (hφ β).symm
      _ = ret (φ η) := congrArg ret heq
      _ = η.1 := hφ η
  have hrep (b d : GL (Fin 2) F) (hbd : QuotientGroup.rightRel (Bstar G) b d) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat b * P.q r) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat d * P.q r) := by
    have hd : d * b⁻¹ ∈ Bstar G := QuotientGroup.rightRel_apply.mp hbd
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (d * b⁻¹) hd (P.tc.rat b * P.q r)).symm
  have hterm (p : Ξ) :
      ArtinPrimitiveRoots.A1.Spec.normHeight F
        (((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
          ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) • z) ^
          (1 + 2 * s.re) =
        ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ p.1.2) (s.re : ℂ) z p.2‖ := by
    let γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) := (p.2.out : Γ)
    let y := ((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • z
    have hpos : 0 < ArtinPrimitiveRoots.A1.Spec.normHeight F y := by
      apply Finset.prod_pos
      intro w _
      rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (y w)
    have hact : (σ p.1.2)⁻¹ • (γ • z) = y := by
      change (σ p.1.2)⁻¹ • ((ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • z) = y
      exact (mul_smul _ _ _).symm
    change ArtinPrimitiveRoots.A1.Spec.normHeight F y ^ (1 + 2 * s.re) = _
    unfold ArtinPrimitiveRoots.A1.Spec.eisTerm
    change _ = ‖(ArtinPrimitiveRoots.A1.Spec.normHeight F
      ((σ p.1.2)⁻¹ • (γ • z)) : ℂ) ^ (1 + 2 * (s.re : ℂ))‖
    rw [hact, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hbound_support (β : V) : f β.1 ≤ M (φ β) := by
    have hcoset : QuotientGroup.rightRel (Bstar G) (Quotient.out β.1) (a (φ β)) := by
      apply Quotient.exact
      exact (Quotient.out_eq β.1).trans (hφ β).symm
    calc
      f β.1 = ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (a (φ β)) * P.q r)‖ :=
        congrArg norm (hrep _ _ hcoset)
      _ ≤ C0 * ArtinPrimitiveRoots.A1.Spec.normHeight F
          (((σ (φ β).1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            (((φ β).2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) • z) ^
            (1 + 2 * s.re) :=
        hscalar (φ β).1 (((φ β).2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      _ = C0 * ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ (φ β).1.2)
          (s.re : ℂ) z (φ β).2‖ := congrArg (C0 * ·) (hterm (φ β))
      _ ≤ M (φ β) := mul_le_mul_of_nonneg_left (hm_bound _ _) hC0
  have hsupp : Summable (fun β : V => f β.1) :=
    Summable.of_nonneg_of_le (fun β => norm_nonneg _) hbound_support (hM.comp_injective hφinj)
  have hf : Summable f :=
    ((hasSum_subtype_iff_of_support_subset (s := V) (Set.Subset.refl _)).1 hsupp.hasSum).summable
  refine ⟨1, fun _ => f, fun _ => hf, ?_⟩
  intro β
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  exact le_rfl

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

/-- Rational Bruhat factorization with a Bstar left factor in both cells. -/
theorem rational_bruhat_factorization
    (P : CoverPackage D S H A) (G : GlobalDatum P) (g : GL (Fin 2) F) :
    (∃ (δ : Fˣ) (b : GL (Fin 2) F), b ∈ Bstar G ∧ g = b * diagGL δ) ∨
    (∃ (δ : Fˣ) (x : F) (b : GL (Fin 2) F),
      b ∈ Bstar G ∧ g = b * diagGL δ * weylGL * upperGL x) := by
  classical
  have hB (r : Fˣ) (x : F) : scalarGL r * upperGL x ∈ Bstar G := by
    change ((scalarGL r * upperGL x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ δ ∈ G.Δ, ((scalarGL r * upperGL x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (δ : F) * ((scalarGL r * upperGL x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1
    refine ⟨?_, 1, G.Δ.one_mem, ?_⟩ <;>
      simp [scalarGL, upperGL, Matrix.mul_apply, Fin.sum_univ_two]
  let a : F := g 0 0
  let b : F := g 0 1
  let c : F := g 1 0
  let d : F := g 1 1
  have hdet : a * d - b * c ≠ 0 := by
    simpa [a, b, c, d, Matrix.det_fin_two] using g.det_ne_zero
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by
      intro hd
      exact hdet (by simp [hc, hd])
    have ha : a ≠ 0 := by
      intro ha
      exact hdet (by simp [ha, hc])
    have hc0 : g 1 0 = 0 := hc
    have hd0 : g 1 1 ≠ 0 := hd
    let r : Fˣ := Units.mk0 d hd
    let δ : Fˣ := Units.mk0 (a / d) (div_ne_zero ha hd)
    let x : F := b / d
    refine Or.inl ⟨δ, scalarGL r * upperGL x, hB r x, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scalarGL, upperGL, diagGL, r, δ, x, a, b, d, hc0,
        Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hd0]
  · let x : F := a / c
    let t : F := d / c
    let yy : F := b / c - (a / c) * (d / c)
    have hy : yy ≠ 0 := by
      intro hy
      dsimp [yy] at hy
      field_simp [hc] at hy
      have hz : a * d - b * c = 0 := by linear_combination -hy
      exact hdet hz
    have hc0 : g 1 0 ≠ 0 := hc
    let r : Fˣ := Units.mk0 c hc
    let δ : Fˣ := Units.mk0 yy hy
    refine Or.inr ⟨δ, t, scalarGL r * upperGL x, hB r x, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scalarGL, upperGL, diagGL, weylGL, r, δ, x, t, yy, a, b, c, d,
        Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hc0] <;> ring

/-- The rational Bruhat cells give exact representatives of the Bstar left quotient. -/
theorem rational_bruhat_coset_equiv
    (P : CoverPackage D S H A) (G : GlobalDatum P) :
    ∃ e : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) ≃
        Quotient (QuotientGroup.rightRel (Bstar G)),
      (∀ δ, e (Sum.inl δ) =
        Quotient.mk (QuotientGroup.rightRel (Bstar G)) (diagGL (Quotient.out δ))) ∧
      ∀ (δ : Fˣ ⧸ G.Δ) (x : F), e (Sum.inr (δ, x)) =
        Quotient.mk (QuotientGroup.rightRel (Bstar G))
          (diagGL (Quotient.out δ) * weylGL * upperGL x) := by
  classical
  let R : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) → GL (Fin 2) F :=
    Sum.elim (fun δ => diagGL (Quotient.out δ))
      (fun p => diagGL (Quotient.out p.1) * weylGL * upperGL p.2)
  let q : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) →
      Quotient (QuotientGroup.rightRel (Bstar G)) :=
    fun u => Quotient.mk (QuotientGroup.rightRel (Bstar G)) (R u)
  have hclass (a d : Fˣ ⧸ G.Δ) (b : GL (Fin 2) F)
      (hb : b ∈ Bstar G)
      (h00 : b 0 0 * ((Quotient.out a : Fˣ) : F) = ((Quotient.out d : Fˣ) : F))
      (h11 : b 1 1 = 1) : a = d := by
    rcases hb with ⟨_, t, ht, hdiag⟩
    have hd : ((Quotient.out d : Fˣ) : F) = (t : F) * ((Quotient.out a : Fˣ) : F) := by
      rw [hdiag, h11, mul_one] at h00
      exact h00.symm
    have hu : Quotient.out d * (Quotient.out a)⁻¹ = t := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      rw [hd, mul_assoc, mul_inv_cancel₀ (Quotient.out a).ne_zero, mul_one]
    have heq : (QuotientGroup.mk (Quotient.out d) : Fˣ ⧸ G.Δ) =
        QuotientGroup.mk (Quotient.out a) :=
      QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv, hu] using ht)
    simpa only [QuotientGroup.out_eq'] using heq.symm
  have hinj : Function.Injective q := by
    intro u v huv
    let b : GL (Fin 2) F := R v * (R u)⁻¹
    have hb : b ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact huv)
    have hb10 : b 1 0 = 0 := hb.1
    have hf : b * R u = R v := by dsimp only [b]; group
    cases u with
    | inl a =>
      cases v with
      | inl d =>
        have h00 := congrArg (fun m : GL (Fin 2) F => m 0 0) hf
        have h11 := congrArg (fun m : GL (Fin 2) F => m 1 1) hf
        simp [R, diagGL, Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
        exact congrArg Sum.inl (hclass a d b hb h00 h11)
      | inr p =>
        have h10 := congrArg (fun m : GL (Fin 2) F => m 1 0) hf
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two, hb10] at h10
    | inr p =>
      cases v with
      | inl d =>
        have h10 := congrArg (fun m : GL (Fin 2) F => m 1 0) hf
        have h11 := congrArg (fun m : GL (Fin 2) F => m 1 1) hf
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two] at h10
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two, hb10, h10] at h11
      | inr r =>
        have h00 := congrArg (fun m : GL (Fin 2) F => m 0 0) hf
        have h01 := congrArg (fun m : GL (Fin 2) F => m 0 1) hf
        have h10 := congrArg (fun m : GL (Fin 2) F => m 1 0) hf
        have h11 := congrArg (fun m : GL (Fin 2) F => m 1 1) hf
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two] at h00 h10
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two, h00] at h01
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two, hb10, h10] at h11
        exact congrArg Sum.inr (Prod.ext (hclass p.1 r.1 b hb h01 h10) h11)
  have hdiag_mul (a d : Fˣ) : diagGL (a * d) = diagGL a * diagGL d := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hnormal (a : Fˣ) :
      ∃ b : GL (Fin 2) F, b ∈ Bstar G ∧
        diagGL a = b * diagGL (Quotient.out (QuotientGroup.mk a : Fˣ ⧸ G.Δ)) := by
    let d : Fˣ := Quotient.out (QuotientGroup.mk a : Fˣ ⧸ G.Δ)
    let t : Fˣ := a * d⁻¹
    have ht : t ∈ G.Δ := by
      have heq : (QuotientGroup.mk a : Fˣ ⧸ G.Δ) = QuotientGroup.mk d :=
        (QuotientGroup.out_eq' _).symm
      simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem.mp heq)
    refine ⟨diagGL t, ?_, ?_⟩
    · change (diagGL t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        ∃ z ∈ G.Δ, (diagGL t : Matrix (Fin 2) (Fin 2) F) 0 0 =
          (z : F) * (diagGL t : Matrix (Fin 2) (Fin 2) F) 1 1
      exact ⟨by simp [diagGL], t, ht, by simp [diagGL]⟩
    · change diagGL a = diagGL t * diagGL d
      rw [← hdiag_mul]
      congr 1
      dsimp only [t]
      group
  have hsurj : Function.Surjective q := by
    intro β
    obtain hsmall | hbig := rational_bruhat_factorization P G (Quotient.out β)
    · obtain ⟨a, b, hb, hf⟩ := hsmall
      obtain ⟨c, hc, hn⟩ := hnormal a
      let δ : Fˣ ⧸ G.Δ := QuotientGroup.mk a
      refine ⟨Sum.inl δ, ?_⟩
      change Quotient.mk (QuotientGroup.rightRel (Bstar G))
        (diagGL (Quotient.out δ)) = β
      calc
        _ = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (Quotient.out β) := by
          apply Quotient.sound
          apply QuotientGroup.rightRel_apply.mpr
          rw [hf, hn]
          change b * (c * diagGL (Quotient.out δ)) * (diagGL (Quotient.out δ))⁻¹ ∈ Bstar G
          simpa only [mul_assoc, mul_inv_cancel, mul_one] using (Bstar G).mul_mem hb hc
        _ = β := Quotient.out_eq β
    · obtain ⟨a, x, b, hb, hf⟩ := hbig
      obtain ⟨c, hc, hn⟩ := hnormal a
      let δ : Fˣ ⧸ G.Δ := QuotientGroup.mk a
      refine ⟨Sum.inr (δ, x), ?_⟩
      change Quotient.mk (QuotientGroup.rightRel (Bstar G))
        (diagGL (Quotient.out δ) * weylGL * upperGL x) = β
      calc
        _ = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (Quotient.out β) := by
          apply Quotient.sound
          apply QuotientGroup.rightRel_apply.mpr
          rw [hf, hn]
          have heq : b * (c * diagGL (Quotient.out δ)) * weylGL * upperGL x *
              (diagGL (Quotient.out δ) * weylGL * upperGL x)⁻¹ = b * c := by group
          rw [heq]
          exact (Bstar G).mul_mem hb hc
        _ = β := Quotient.out_eq β
  refine ⟨Equiv.ofBijective q ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro δ
    rfl
  · intro δ x
    rfl

/-- Compare any ideal-lattice domain with a bounded measurable domain, including periodic integrals. -/
theorem ideal_periodic_domain_comparison (D : FieldData F)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume) :
    ∃ Pb : Set (InfinitePlace F → ℂ), MeasurableSet Pb ∧ IsCompact (closure Pb) ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pb volume ∧
      volume Pd = volume Pb ∧ 0 < (volume Pb).toReal ∧
      ∀ f : (InfinitePlace F → ℂ) → ℂ,
        (∀ t ∈ ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom),
          ∀ x, f (t + x) = f x) → (∫ x in Pd, f x) = ∫ x in Pb, f x := by
  classical
  let : IsTotallyComplex F := D.isTotallyComplex
  let I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 𝔞 h𝔞
  let b₀ := mixedEmbedding.fractionalIdealLatticeBasis F I
  let e := ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv (F := F)
  let b := b₀.map e
  let j : mixedEmbedding.mixedSpace F →ₗ[ℤ] (InfinitePlace F → ℂ) :=
    e.toLinearMap.restrictScalars ℤ
  have hj (y : F) : j (mixedEmbedding F y) = infEmbA y := by
    ext w
    simp [j, e, ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv, infEmbA,
      mixedEmbedding]
  have hlat : (Submodule.span ℤ (Set.range b)).toAddSubgroup =
      (𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom := by
    have hrange : Set.range b = j '' Set.range b₀ := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b₀ i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    have hspanMap : Submodule.span ℤ (Set.range b) =
        (Submodule.span ℤ (Set.range b₀)).map j := by
      rw [hrange, ← Submodule.map_span]
    have hspan₀ : Submodule.span ℤ (Set.range b₀) = mixedEmbedding.idealLattice F I :=
      mixedEmbedding.span_idealLatticeBasis F I
    have hspan (x : InfinitePlace F → ℂ) :
        x ∈ Submodule.span ℤ (Set.range b) ↔
          ∃ y : F, y ∈ (I : Submodule (𝓞 F) F) ∧ infEmbA y = x := by
      rw [hspanMap, Submodule.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hspan₀] at hz
        obtain ⟨y, hy, rfl⟩ := (mixedEmbedding.mem_idealLattice F I).mp hz
        exact ⟨y, hy, hj y⟩
      · rintro ⟨y, hy, rfl⟩
        apply Submodule.mem_map.mpr
        refine ⟨mixedEmbedding F y, ?_, hj y⟩
        rw [hspan₀]
        exact (mixedEmbedding.mem_idealLattice F I).mpr ⟨y, hy, rfl⟩
    apply AddSubgroup.ext
    intro x
    change x ∈ Submodule.span ℤ (Set.range b) ↔
      x ∈ (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
    rw [hspan]
    rfl
  let Pb := ZSpan.fundamentalDomain b
  have hcompact : IsCompact (closure Pb) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  have hfinite : volume Pb ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hcompact.measure_lt_top).ne
  have hpositive : 0 < (volume Pb).toReal :=
    ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero b) hfinite
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hPb : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup Pb volume :=
    ZSpan.isAddFundamentalDomain' b volume
  have hPd' : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup Pd volume := by
    rw [hlat]
    exact hPd
  refine ⟨Pb, ZSpan.fundamentalDomain_measurableSet b, hcompact, ?_,
    hPd'.measure_eq hPb, hpositive, ?_⟩
  · rwa [hlat] at hPb
  · intro f hf
    apply hPd'.setIntegral_eq hPb
    intro t x
    change f ((t : InfinitePlace F → ℂ) + x) = f x
    exact hf t (by rw [← hlat]; exact t.property) x

/-- The complex-place covolume of a nonzero fractional ideal in the global Haar normalization. -/
theorem ideal_domain_covolume (D : FieldData F)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume) :
    (volume Pd).toReal = κF F * (FractionalIdeal.absNorm 𝔞 : ℝ) := by
  classical
  let : IsTotallyComplex F := D.isTotallyComplex
  let : IsEmpty {w : InfinitePlace F // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w.1)) w.2⟩
  let : IsProbabilityMeasure
      (volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)) :=
    ⟨by simp [volume_pi]⟩
  let ec : {w : InfinitePlace F // w.IsComplex} ≃ InfinitePlace F :=
    { toFun := Subtype.val
      invFun := fun w => ⟨w, IsTotallyComplex.isComplex w⟩
      left_inv := fun w => by rfl
      right_inv := fun w => by rfl }
  let e := ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv (F := F)
  let E := e.toContinuousLinearEquiv
  have he : MeasurePreserving E volume volume := by
    exact (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℂ) ec).comp
      measurePreserving_snd
  have hes : MeasurePreserving E.symm volume volume :=
    MeasurePreserving.symm E.toHomeomorph.toMeasurableEquiv he
  let I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 𝔞 h𝔞
  let L := mixedEmbedding.idealLattice F I
  let Lc := ZLattice.comap ℝ L E.symm.toLinearMap
  have hemb (y : F) : E (mixedEmbedding F y) = infEmbA y := by
    ext w
    rfl
  have hlat : Lc.toAddSubgroup =
      (𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom := by
    apply AddSubgroup.ext
    intro x
    change E.symm x ∈ mixedEmbedding.idealLattice F I ↔
      x ∈ (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
    rw [mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨y, hy, ?_⟩
      have h := congrArg E heq
      change infEmbA y = x
      simpa only [hemb, E.apply_symm_apply] using h
    · rintro ⟨y, hy, heq⟩
      refine ⟨y, hy, ?_⟩
      apply E.injective
      change infEmbA y = x at heq
      simpa only [hemb, E.apply_symm_apply] using heq
  have hfd : IsAddFundamentalDomain Lc Pd volume := by
    change IsAddFundamentalDomain Lc.toAddSubgroup Pd volume
    rw [hlat]
    exact hPd
  have hn : NumberField.InfinitePlace.nrComplexPlaces F = numComplex F := Fintype.card_congr ec
  calc
    (volume Pd).toReal = ZLattice.covolume Lc volume := by
      simpa only [measureReal_def] using
        (ZLattice.covolume_eq_measure_fundamentalDomain Lc volume hfd).symm
    _ = ZLattice.covolume L volume := ZLattice.covolume_comap L volume volume hes
    _ = (FractionalIdeal.absNorm 𝔞 : ℝ) * (2⁻¹ : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        Real.sqrt |(NumberField.discr F : ℝ)| := by
      exact mixedEmbedding.covolume_idealLattice F I
    _ = κF F * (FractionalIdeal.absNorm 𝔞 : ℝ) := by
      simp only [κF, hn, zpow_neg, zpow_natCast, inv_pow]
      ring

/-- Finite translation fixation and rational automorphy imply ideal periodicity at infinity. -/
theorem eisenstein_ideal_periodic
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h) :
    ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x : InfinitePlace F → ℂ,
      eisenstein P G Fs (nInf P (infEmbA ξ + x) * g) =
        eisenstein P G Fs (nInf P x * g) := by
  classical
  have hupper (a b : ℂ) : upperM ℂ a * upperM ℂ b = upperM ℂ b * upperM ℂ a := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hcomm (ξ : F) (x : InfinitePlace F → ℂ) :
      P.tc.rat (upperGL ξ) * nInf P x = nInf P x * P.tc.rat (upperGL ξ) := by
    obtain ⟨r, hq, hf, hc⟩ := P.nS_components
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
    have hf1 (v : FinPlace F) : P.compF v r = 1 := by
      simpa using hf v
    have hRP : P.ratRP (upperGL ξ) * r = r * P.ratRP (upperGL ξ) := by
      apply P.comp_ext
      · intro v
        simp only [map_mul, hf1, mul_one, one_mul]
      · intro w
        have hu : Matrix.GeneralLinearGroup.map w.embedding (upperGL ξ) =
            upperM ℂ (w.embedding ξ) := by
          apply Units.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.GeneralLinearGroup.map, upperGL, upperM]
        rw [map_mul, map_mul, P.compC_ratRP, hc, hu]
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg (fun a : GL (Fin 2) ℂ => (QuotientGroup.mk a : PGL2 ℂ))
          (hupper (w.embedding ξ) (x w))
    have h := congrArg P.q hRP
    simpa only [map_mul, P.q_ratRP, hq, nInf] using h
  have hni (x y : InfinitePlace F → ℂ) : nInf P (x + y) = nInf P x * nInf P y := by
    dsimp only [nInf]
    have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x) +
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) := by simp
    rw [hp, ofAdd_add, map_mul]
  have hrat (ξ : F) : P.tc.rat (upperGL ξ) * P.tc.rat (upperGL (-ξ)) = 1 := by
    have hu : upperGL ξ * upperGL (-ξ) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two]
    rw [← map_mul, hu, map_one]
  intro ξ hξ x
  have hk : ∀ h, scalarOf P G Fs.f Fs.fC
      (h * (g⁻¹ * nFin P (-ξ) * g)) = scalarOf P G Fs.f Fs.fC h :=
    hfix (-ξ) ((𝔞 : Submodule (𝓞 F) F).neg_mem hξ)
  have hfactor : P.tc.rat (upperGL ξ) *
      (nInf P x * g * (g⁻¹ * nFin P (-ξ) * g)) =
        nInf P (infEmbA ξ + x) * g := by
    simp only [nFin, map_neg, neg_neg]
    calc
      P.tc.rat (upperGL ξ) * (nInf P x * g *
          (g⁻¹ * (P.tc.rat (upperGL (-ξ)) * nInf P (infEmbA ξ)) * g)) =
          P.tc.rat (upperGL ξ) * nInf P x * P.tc.rat (upperGL (-ξ)) *
            nInf P (infEmbA ξ) * g := by group
      _ = nInf P x * (P.tc.rat (upperGL ξ) * P.tc.rat (upperGL (-ξ))) *
          nInf P (infEmbA ξ) * g := by
        rw [hcomm]
        group
      _ = nInf P x * nInf P (infEmbA ξ) * g := by rw [hrat, mul_one]
      _ = nInf P (infEmbA ξ + x) * g := by rw [← hni, add_comm]
  calc
    eisenstein P G Fs (nInf P (infEmbA ξ + x) * g) =
        eisenstein P G Fs (P.tc.rat (upperGL ξ) *
          (nInf P x * g * (g⁻¹ * nFin P (-ξ) * g))) := by rw [hfactor]
    _ = eisenstein P G Fs (nInf P x * g * (g⁻¹ * nFin P (-ξ) * g)) :=
      (eisenstein_automorphic P G hs Fs).1 _ _
    _ = eisenstein P G Fs (nInf P x * g) :=
      (eisenstein_automorphic P G hs Fs).2.2 _ hk _

/-- Scalar cusp bounds are uniform under archimedean unipotent translation. -/
theorem scalar_cusp_height_majorant_unipotent
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) {ι : Type} [Fintype ι]
    (c : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (δ : ι → Fˣ) (r : P.RP) :
    ∃ Z : (InfinitePlace F → ℂ) → ArtinPrimitiveRoots.A1.Spec.X F,
      Continuous Z ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ (x : InfinitePlace F → ℂ) (i : ι)
          (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
          ‖scalarOf P G Fs.f Fs.fC
            (P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL
              (c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) *
                nInf P x * P.q r)‖ ≤
            C * ArtinPrimitiveRoots.A1.Spec.normHeight F
              ((c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • Z x) ^
                (1 + 2 * s.re) := by
  classical
  choose Cw hCw hbound using fun w =>
    sectionC_norm_majorant s (Fs.fC w) (Fs.fC_sec w).1 (Fs.fC_sec w).2
  obtain ⟨Z, hZ, hz⟩ := complex_spherical_height_product_unipotent (fun w => P.compC w r)
  obtain ⟨Cf, hCf, hfbound⟩ := finite_scalar_integral_translate_bound P G Fs
    (fun i => diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (c i)) r
  choose rn hqn hfn hcn using fun x : InfinitePlace F → ℂ =>
    P.nS_components ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hfn1 (x : InfinitePlace F → ℂ) (v : FinPlace F) : P.compF v (rn x) = 1 := by
    simpa using hfn x v
  let t (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :=
    c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ
  let R (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) : P.RP :=
    P.ratRP (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * rn x * r
  let y (i : ι) (w : InfinitePlace F) : ℂˣ := Units.map w.embedding.toMonoidHom (δ i)
  let U (w : InfinitePlace F) (a : Matrix.SpecialLinearGroup (Fin 2) F)
      (x : InfinitePlace F → ℂ) : PGL2 ℂ :=
    QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
      (ArtinPrimitiveRoots.A1.Spec.toInf F a w)) * nC (x w) * P.compC w r
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
  have hcomp (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      P.compC w (R i γ x) = QuotientGroup.mk (diagM ℂ (y i w)) * U w (t i γ) x := by
    simp only [R, U, map_mul, P.compC_ratRP, hdiag, hsl,
      QuotientGroup.mk_mul, hcn, nC, mul_assoc]
  have hcompF (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) (v : FinPlace F) :
      P.compF v (R i γ x) = P.compF v
        (P.ratRP (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * r) := by
    simp only [R, map_mul, hfn1, mul_one]
  have hzero : upperM ℂ 0 = 1 := by
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;> simp [upperM]
  have hsec (w : InfinitePlace F) (a : ℂˣ) (k : PGL2 ℂ) :
      Fs.fC w (QuotientGroup.mk (diagM ℂ a) * k) =
        (Complex.normSq (a : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s) * Fs.fC w k := by
    simpa only [hzero, QuotientGroup.mk_one, one_mul] using (Fs.fC_sec w).1 0 a k
  have hlocal (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      ‖Fs.fC w (P.compC w (R i γ x))‖ ≤
        A i w * ‖sphC (s.re : ℂ) (U w (t i γ) x)‖ := by
    rw [hcomp, hsec, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbound w (U w (t i γ) x))
      (norm_nonneg _)).trans_eq (by dsimp [A]; ring)
  have hheight (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) :
      (∏ w, ‖sphC (s.re : ℂ) (U w (t i γ) x)‖) =
        ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^ (1 + 2 * s.re) :=
    hz s.re (t i γ) x
  have hheight_nonneg (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) :
      0 ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^ (1 + 2 * s.re) := by
    rw [← hheight]
    exact Finset.prod_nonneg fun w _ => norm_nonneg _
  have hinf (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) :
      (∏ w, ‖Fs.fC w (P.compC w (R i γ x))‖) ≤
        Ai i * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^ (1 + 2 * s.re) := by
    calc
      _ ≤ ∏ w, A i w * ‖sphC (s.re : ℂ) (U w (t i γ) x)‖ :=
        Finset.prod_le_prod₀ (fun w _ => norm_nonneg _) (fun w _ => hlocal i γ x w)
      _ = _ := by rw [Finset.prod_mul_distrib, hheight]
  refine ⟨Z, hZ, Cf * ∑ i, Ai i, mul_nonneg hCf (Finset.sum_nonneg fun i _ => hAi i), ?_⟩
  intro x i γ
  have hq : P.q (R i γ x) =
      P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) *
        nInf P x * P.q r := by
    simp only [R, map_mul, P.q_ratRP, hqn, nInf]
  change ‖scalarOf P G Fs.f Fs.fC
    (P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) *
      nInf P x * P.q r)‖ ≤ _
  rw [← hq, (scalarOf_q P G Fs (R i γ x)).2, norm_mul, norm_prod]
  have hf : ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v (R i γ x)))‖ ≤ Cf := by
    simp only [hcompF]
    simpa only [t, map_mul, mul_assoc] using hfbound i γ
  calc
    _ ≤ Cf * (Ai i * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^
        (1 + 2 * s.re)) :=
      mul_le_mul hf (hinf i γ x) (Finset.prod_nonneg fun w _ => norm_nonneg _) hCf
    _ = (Cf * Ai i) * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^
        (1 + 2 * s.re) := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun a _ => hAi a) (Finset.mem_univ i)) hCf)
      (hheight_nonneg i γ x)

/-- One finite torus family supports cusp representatives for all archimedean translations. -/
theorem finite_supported_cusp_representatives_unipotent
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
      ∀ (x : InfinitePlace F → ℂ) (β : Quotient (QuotientGroup.rightRel (Bstar G))),
        scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P x * P.q r) ≠ 0 →
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
  intro ξ β hβ
  obtain ⟨rn, hqn, hfn, _⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), ξ)
  have hfn1 (v : FinPlace F) : P.compF v rn = 1 := by
    simpa using hfn v
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
      scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P ξ * P.q r) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL d * k) * nInf P ξ * P.q r) := by
    rw [hfactor', map_mul]
    simpa only [mul_assoc] using (scalarOf_invariance P G Fs).1 b' hb'
      (P.tc.rat (diagGL d * k) * nInf P ξ * P.q r)
  let x : P.RP := P.ratRP k * rn * r
  let y : P.RP := P.ratRP (diagGL d) * x
  have hq : P.q y = P.tc.rat (diagGL d * k) * nInf P ξ * P.q r := by
    simp only [y, x, map_mul, P.q_ratRP, hqn, nInf, mul_assoc]
  have hnonzero : scalarOf P G Fs.f Fs.fC (P.q y) ≠ 0 := by
    rw [hq]
    exact fun h => hβ (hscalar.trans h)
  rw [(scalarOf_q P G Fs y).2] at hnonzero
  have hfinite :
      (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v d) * P.compF v x))) ≠ 0 := by
    simpa only [y, hcomp] using (mul_ne_zero_iff.mp hnonzero).1
  have hxfin (v : FinPlace F) :
      P.compF v x = P.compF v (P.ratRP k * r) := by
    simp only [x, map_mul, hfn1, mul_one]
  have hk : k = Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹) *
      Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ) := by
    dsimp only [k]
    rw [map_mul]
  have hδ : δ ∈ U := by
    apply hsupport i γ
    change (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v d) *
      P.compF v (P.ratRP (Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹) *
        Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * r)))) ≠ 0
    simpa only [hxfin, hk] using hfinite
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

/-- Eisenstein summands admit a summable majorant uniform on compact archimedean sets. -/
theorem eisenstein_majorant_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K) :
    ∃ M : Quotient (QuotientGroup.rightRel (Bstar G)) → ℝ,
      Summable M ∧ (∀ β, 0 ≤ M β) ∧ ∀ x ∈ K, ∀ β,
        ‖scalarOf P G Fs.f Fs.fC
          (P.tc.rat (Quotient.out β) * nInf P x * g)‖ ≤ M β := by
  classical
  by_cases hKe : K = ∅
  · subst K
    refine ⟨fun _ => 0, summable_zero, fun _ => le_rfl, ?_⟩
    simp
  obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hKe
  let : IsTotallyComplex F := D.isTotallyComplex
  let Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) := ⊤
  let : Γ.FiniteIndex := by dsimp only [Γ]; infer_instance
  obtain ⟨ι, hι, σ, hσ⟩ := ArtinPrimitiveRoots.A1.Spec.exists_cusp_reps F Γ
  let : Fintype ι := hι
  obtain ⟨r, rfl⟩ := P.q_surj g
  obtain ⟨U, hU, hcover⟩ :=
    finite_supported_cusp_representatives_unipotent P G Fs Γ σ hσ.2 r
  let : Fintype U := hU.fintype
  let J := U × ι
  obtain ⟨Z, hZ, C0, hC0, hscalar⟩ := scalar_cusp_height_majorant_unipotent P G Fs
    (fun j : J => (σ j.2)⁻¹) (fun j : J => Quotient.out j.1.1) r
  choose m hm hmbound using fun i =>
    ArtinPrimitiveRoots.A1.Spec.eisSeries_majorant F Γ (σ i)
      (Z '' K) (hK.image hZ) s.re s.re hs
  have hm_bound (x : InfinitePlace F → ℂ) (hx : x ∈ K) (i : ι)
      (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) :
      ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ i) (s.re : ℂ) (Z x) q‖ ≤ m i q := by
    exact hmbound i (Z x) (Set.mem_image_of_mem Z hx) (s.re : ℂ) (by simp) (by simp) q
  have hm_nonneg (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) :
      0 ≤ m i q := (norm_nonneg _).trans (hm_bound x0 hx0 i q)
  let Ξ := Σ j : J, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ j.2)
  let weight : Ξ → ℝ := fun p => C0 * m p.1.2 p.2
  have hweight_nonneg (p : Ξ) : 0 ≤ weight p := mul_nonneg hC0 (hm_nonneg p.1.2 p.2)
  have hweight : Summable weight := by
    apply (summable_sigma_of_nonneg hweight_nonneg).2
    constructor
    · intro j
      exact (hm j.2).mul_left C0
    · exact (hasSum_fintype _).summable
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let V : Set Q := {β | ∃ x ∈ K,
    scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P x * P.q r) ≠ 0}
  let a (p : Ξ) : GL (Fin 2) F :=
    diagGL (Quotient.out p.1.1.1) * Matrix.SpecialLinearGroup.toGL
      ((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
        ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
  let ret : Ξ → Q := fun p => Quotient.mk (QuotientGroup.rightRel (Bstar G)) (a p)
  have hparam : ∀ β : V, ∃ p : Ξ, ret p = β.1 := by
    intro β
    obtain ⟨x, _, hn⟩ := β.property
    obtain ⟨i, q, δ, hδ, heq⟩ := hcover x β.1 hn
    exact ⟨⟨(⟨δ, hδ⟩, i), q⟩, heq.symm⟩
  choose φ hφ using hparam
  have hφinj : Function.Injective φ := by
    intro β η heq
    apply Subtype.ext
    calc
      β.1 = ret (φ β) := (hφ β).symm
      _ = ret (φ η) := congrArg ret heq
      _ = η.1 := hφ η
  let majorant : Q → ℝ := fun β => if h : β ∈ V then weight (φ ⟨β, h⟩) else 0
  have hmajorant_sub : (fun β : V => majorant β.1) = fun β : V => weight (φ β) := by
    funext β
    simp only [majorant, dite_eq_left β.property]
  have hsupp : Summable (fun β : V => majorant β.1) := by
    rw [hmajorant_sub]
    exact hweight.comp_injective hφinj
  have hsupport : Function.support majorant ⊆ V := by
    intro β hβ
    by_contra h
    exact hβ (by simp only [majorant, dite_eq_right h])
  have hmajorant : Summable majorant :=
    ((hasSum_subtype_iff_of_support_subset (s := V) hsupport).1 hsupp.hasSum).summable
  have hmajorant_nonneg (β : Q) : 0 ≤ majorant β := by
    dsimp only [majorant]
    split_ifs with h
    · exact hweight_nonneg _
    · exact le_rfl
  have hrep (b d : GL (Fin 2) F) (hbd : QuotientGroup.rightRel (Bstar G) b d)
      (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat b * nInf P x * P.q r) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat d * nInf P x * P.q r) := by
    have hd : d * b⁻¹ ∈ Bstar G := QuotientGroup.rightRel_apply.mp hbd
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (d * b⁻¹) hd
        (P.tc.rat b * nInf P x * P.q r)).symm
  have hterm (p : Ξ) (x : InfinitePlace F → ℂ) :
      ArtinPrimitiveRoots.A1.Spec.normHeight F
        (((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
          ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) • Z x) ^
          (1 + 2 * s.re) =
        ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ p.1.2) (s.re : ℂ) (Z x) p.2‖ := by
    let γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) := (p.2.out : Γ)
    let y := ((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • Z x
    have hpos : 0 < ArtinPrimitiveRoots.A1.Spec.normHeight F y := by
      apply Finset.prod_pos
      intro w _
      rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (y w)
    have hact : (σ p.1.2)⁻¹ • (γ • Z x) = y := by
      change (σ p.1.2)⁻¹ • ((ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • Z x) = y
      exact (mul_smul _ _ _).symm
    change ArtinPrimitiveRoots.A1.Spec.normHeight F y ^ (1 + 2 * s.re) = _
    unfold ArtinPrimitiveRoots.A1.Spec.eisTerm
    change _ = ‖(ArtinPrimitiveRoots.A1.Spec.normHeight F
      ((σ p.1.2)⁻¹ • (γ • Z x)) : ℂ) ^ (1 + 2 * (s.re : ℂ))‖
    rw [hact, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hbound_support (x : InfinitePlace F → ℂ) (hx : x ∈ K) (β : V) :
      ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out β.1) * nInf P x * P.q r)‖ ≤ weight (φ β) := by
    have hcoset : QuotientGroup.rightRel (Bstar G) (Quotient.out β.1) (a (φ β)) := by
      apply Quotient.exact
      exact (Quotient.out_eq β.1).trans (hφ β).symm
    calc
      _ = ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (a (φ β)) * nInf P x * P.q r)‖ :=
        congrArg norm (hrep _ _ hcoset x)
      _ ≤ C0 * ArtinPrimitiveRoots.A1.Spec.normHeight F
          (((σ (φ β).1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            (((φ β).2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) • Z x) ^
            (1 + 2 * s.re) :=
        hscalar x (φ β).1 (((φ β).2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      _ = C0 * ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ (φ β).1.2)
          (s.re : ℂ) (Z x) (φ β).2‖ := congrArg (C0 * ·) (hterm (φ β) x)
      _ ≤ weight (φ β) := mul_le_mul_of_nonneg_left (hm_bound x hx _ _) hC0
  refine ⟨majorant, hmajorant, hmajorant_nonneg, ?_⟩
  intro x hx β
  by_cases hβ : β ∈ V
  · simpa only [majorant, dite_eq_left hβ] using hbound_support x hx ⟨β, hβ⟩
  · have hzero : scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out β) * nInf P x * P.q r) = 0 := by
      by_contra hn
      exact hβ ⟨x, hx, hn⟩
    simp only [hzero, norm_zero, majorant, dite_eq_right hβ, le_refl]

/-- Each rational scalar summand is continuous along the archimedean unipotent orbit. -/
theorem scalarOf_unipotent_continuous
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G)
    (γ : GL (Fin 2) F) :
    Continuous (fun x : InfinitePlace F → ℂ =>
      scalarOf P G Fs.f Fs.fC (P.tc.rat γ * nInf P x * g)) := by
  classical
  have hcancel (t : ℂ) : upperM ℂ t * upperM ℂ (-t) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two]
  have hinv (t : ℂ) : (upperM ℂ t)⁻¹ = upperM ℂ (-t) := by
    calc
      (upperM ℂ t)⁻¹ = (upperM ℂ t)⁻¹ * (upperM ℂ t * upperM ℂ (-t)) := by
        rw [hcancel, mul_one]
      _ = upperM ℂ (-t) := by group
  have hval : Continuous (fun t : ℂ => (upperM ℂ t : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change Continuous (fun t : ℂ => (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ))
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first | exact continuous_const | exact continuous_id
  have hu : Continuous (upperM ℂ) := Units.continuous_iff.mpr ⟨hval, by
    simpa only [hinv, Function.comp_def] using
      hval.comp (continuous_neg : Continuous (fun t : ℂ => -t))⟩
  have hn : Continuous (nC : ℂ → PGL2 ℂ) := QuotientGroup.continuous_mk.comp hu
  obtain ⟨r, rfl⟩ := P.q_surj g
  choose rn hqn hfn hcn using fun x : InfinitePlace F → ℂ =>
    P.nS_components ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hfn1 (x : InfinitePlace F → ℂ) (v : FinPlace F) : P.compF v (rn x) = 1 := by
    simpa using hfn x v
  let R (x : InfinitePlace F → ℂ) : P.RP := P.ratRP γ * rn x * r
  let cf : ℂ := ∏ᶠ v, G.lam v (Fs.f v (P.compF v (P.ratRP γ * r)))
  have hq (x : InfinitePlace F → ℂ) :
      P.q (R x) = P.tc.rat γ * nInf P x * P.q r := by
    simp only [R, map_mul, P.q_ratRP, hqn, nInf]
  have hcompF (x : InfinitePlace F → ℂ) (v : FinPlace F) :
      P.compF v (R x) = P.compF v (P.ratRP γ * r) := by
    simp only [R, map_mul, hfn1, mul_one]
  have hcompC (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      P.compC w (R x) = P.compC w (P.ratRP γ) * nC (x w) * P.compC w r := by
    simp only [R, map_mul, hcn, nC]
  have hformula (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat γ * nInf P x * P.q r) =
        cf * ∏ w, Fs.fC w (P.compC w (P.ratRP γ) * nC (x w) * P.compC w r) := by
    rw [← hq, (scalarOf_q P G Fs (R x)).2]
    simp only [cf, hcompF, hcompC]
  have hprod : Continuous (fun x : InfinitePlace F → ℂ =>
      ∏ w, Fs.fC w (P.compC w (P.ratRP γ) * nC (x w) * P.compC w r)) := by
    apply continuous_finsetProd
    intro w _
    exact (Fs.fC_sec w).2.comp
      ((continuous_const.mul (hn.comp (continuous_apply w))).mul continuous_const)
  have hc : Continuous (fun x : InfinitePlace F → ℂ =>
      cf * ∏ w, Fs.fC w (P.compC w (P.ratRP γ) * nC (x w) * P.compC w r)) :=
    continuous_const.mul hprod
  exact hc.congr fun x => (hformula x).symm

/-- Compact majorants justify absolute termwise integration of the Eisenstein series. -/
theorem eisenstein_integral_tsum_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K) :
    (∀ β : Quotient (QuotientGroup.rightRel (Bstar G)),
      IntegrableOn (fun x => scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out β) * nInf P x * g)) B) ∧
    Summable (fun β : Quotient (QuotientGroup.rightRel (Bstar G)) =>
      ∫ x in B, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out β) * nInf P x * g)‖) ∧
    (∫ x in B, eisenstein P G Fs (nInf P x * g)) =
      ∑' β : Quotient (QuotientGroup.rightRel (Bstar G)),
        ∫ x in B, scalarOf P G Fs.f Fs.fC
          (P.tc.rat (Quotient.out β) * nInf P x * g) := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F)
    infer_instance
  let : Countable (GL (Fin 2) F) :=
    (Units.val_injective : Function.Injective
      (fun a : GL (Fin 2) F => (a : Matrix (Fin 2) (Fin 2) F))).countable
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let f (β : Q) (x : InfinitePlace F → ℂ) : ℂ :=
    scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P x * g)
  have hint (β : Q) : IntegrableOn (f β) B := by
    exact (ContinuousOn.integrableOn_compact hK
      (scalarOf_unipotent_continuous P G Fs g (Quotient.out β)).continuousOn).mono_set hBK
  have hBlt : volume B < ⊤ := lt_of_le_of_lt (measure_mono hBK)
    (lt_top_iff_ne_top.mpr hK.measure_ne_top)
  let : IsFiniteMeasure (volume.restrict B) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hBlt⟩
  obtain ⟨M, hM, _, hbound⟩ := eisenstein_majorant_on_compact P G hs Fs g K hK
  have hnonneg (β : Q) : 0 ≤ ∫ x in B, ‖f β x‖ :=
    integral_nonneg fun x => norm_nonneg _
  have hboundint (β : Q) : (∫ x in B, ‖f β x‖) ≤ volume.real B * M β := by
    calc
      _ ≤ ∫ x in B, M β := integral_mono_ae (hint β).norm (integrable_const _) (by
        filter_upwards [ae_restrict_mem hB] with x hx
        exact hbound x (hBK hx) β)
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have hsum : Summable (fun β : Q => ∫ x in B, ‖f β x‖) :=
    Summable.of_nonneg_of_le hnonneg hboundint (hM.mul_left (volume.real B))
  refine ⟨hint, hsum, ?_⟩
  simpa only [eisenstein, f, mul_assoc] using
    (integral_tsum_of_summable_integral_norm hint hsum).symm

/-- Integrating the Bruhat cells splits the absolutely convergent Eisenstein series. -/
theorem eisenstein_bruhat_integral_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K) :
    (∫ x in B, eisenstein P G Fs (nInf P x * g)) =
      (∑' δ : Fˣ ⧸ G.Δ, ∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ)) * nInf P x * g)) +
      ∑' p : (Fˣ ⧸ G.Δ) × F, ∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) *
          nInf P x * g) := by
  classical
  obtain ⟨_, habs, heq⟩ := eisenstein_integral_tsum_on_compact P G hs Fs g K hK B hB hBK
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let I (β : Q) : ℂ := ∫ x in B, scalarOf P G Fs.f Fs.fC
    (P.tc.rat (Quotient.out β) * nInf P x * g)
  have hsum : Summable I := habs.of_norm_bounded fun β => norm_integral_le_integral_norm _
  obtain ⟨e, hsmall, hbig⟩ := rational_bruhat_coset_equiv P G
  let R : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) → GL (Fin 2) F :=
    Sum.elim (fun δ => diagGL (Quotient.out δ))
      (fun p => diagGL (Quotient.out p.1) * weylGL * upperGL p.2)
  have he (u) : e u = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (R u) := by
    cases u with
    | inl δ => exact hsmall δ
    | inr p => exact hbig p.1 p.2
  have hrep (u) : I (e u) = ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (R u) * nInf P x * g) := by
    have hb : R u * (Quotient.out (e u))⁻¹ ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ((Quotient.out_eq (e u)).trans (he u)))
    apply integral_congr_ae
    filter_upwards [] with x
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (R u * (Quotient.out (e u))⁻¹) hb
        (P.tc.rat (Quotient.out (e u)) * (nInf P x * g))).symm
  have hsum' : Summable (fun u => I (e u)) := hsum.comp_injective e.injective
  calc
    _ = ∑' β : Q, I β := heq
    _ = ∑' u, I (e u) := (e.tsum_eq I).symm
    _ = (∑' δ, I (e (Sum.inl δ))) + ∑' p, I (e (Sum.inr p)) :=
      (hsum'.comp_injective Sum.inl_injective).tsum_sum
        (hsum'.comp_injective Sum.inr_injective)
    _ = _ := by
      congr 1
      · apply tsum_congr
        intro δ
        exact hrep (Sum.inl δ)
      · apply tsum_congr
        intro p
        exact hrep (Sum.inr p)

/-- A small-cell summand is unchanged by the archimedean unipotent variable. -/
theorem scalarOf_diag_unipotent
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (δ : Fˣ)
    (g : P.tc.G) (x : InfinitePlace F → ℂ) :
    scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL δ) * nInf P x * g) =
      scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL δ) * g) := by
  classical
  let y : InfinitePlace F → ℂ := infEmbA (δ : F) * x
  obtain ⟨r, hq, hf, hc⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  obtain ⟨t, hqt, hft, hct⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y)
  have hf1 (v : FinPlace F) : P.compF v r = 1 := by simpa using hf v
  have hft1 (v : FinPlace F) : P.compF v t = 1 := by simpa using hft v
  have hmat (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (diagGL δ) * upperM ℂ (x w) =
        upperM ℂ (y w) * Matrix.GeneralLinearGroup.map w.embedding (diagGL δ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.map, diagGL, upperM, y, infEmbA,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hRP : P.ratRP (diagGL δ) * r = t * P.ratRP (diagGL δ) := by
    apply P.comp_ext
    · intro v
      simp only [map_mul, hf1, hft1, mul_one, one_mul]
    · intro w
      rw [map_mul, map_mul, P.compC_ratRP, hc, hct]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg (fun a : GL (Fin 2) ℂ => (QuotientGroup.mk a : PGL2 ℂ)) (hmat w)
  have hcomm : P.tc.rat (diagGL δ) * nInf P x = nInf P y * P.tc.rat (diagGL δ) := by
    simpa only [map_mul, P.q_ratRP, hq, hqt, nInf] using congrArg P.q hRP
  rw [hcomm, mul_assoc]
  exact (scalarOf_invariance P G Fs).2.1
    (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y)) _

/-- The zero torus coefficient can be computed on a bounded measurable ideal domain. -/
theorem eisenstein_zeroCoeff_bounded_domain
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume) :
    ∃ Pb : Set (InfinitePlace F → ℂ), MeasurableSet Pb ∧ IsCompact (closure Pb) ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pb volume ∧
      volume Pd = volume Pb ∧ 0 < (volume Pb).toReal ∧
      torusCoeff P (eisenstein P G Fs) g Pd 0 =
        torusCoeff P (eisenstein P G Fs) g Pb 0 := by
  classical
  obtain ⟨Pb, hmb, hcb, hdb, hvol, hpos, hint⟩ :=
    ideal_periodic_domain_comparison D 𝔞 h𝔞 Pd hPd
  have hperiodic : ∀ t ∈
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom),
      ∀ x : InfinitePlace F → ℂ,
      eisenstein P G Fs (nInf P (t + x) * g) = eisenstein P G Fs (nInf P x * g) := by
    intro t ht x
    rcases ht with ⟨ξ, hξ, rfl⟩
    exact eisenstein_ideal_periodic P G hs Fs g 𝔞 hfix ξ hξ x
  have hi := hint (fun x => eisenstein P G Fs (nInf P x * g)) hperiodic
  have hpsi0 (x : InfinitePlace F → ℂ) : psiInf (0 : F) x = 1 := by
    simp [psiInf, psiC]
  refine ⟨Pb, hmb, hcb, hdb, hvol, hpos, ?_⟩
  simp only [torusCoeff, neg_zero, hpsi0, mul_one, hvol, hi]

/-- The normalized zero coefficient has summable small- and big-cell contributions. -/
theorem eisenstein_zeroCoeff_bruhat_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K)
    (hvol : 0 < (volume B).toReal) :
    Summable (fun δ : Fˣ ⧸ G.Δ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out δ)) * g)) ∧
    Summable (fun p : (Fˣ ⧸ G.Δ) × F => ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) *
        nInf P x * g)) ∧
    torusCoeff P (eisenstein P G Fs) g B 0 =
      (∑' δ : Fˣ ⧸ G.Δ, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ)) * g)) +
      ((volume B).toReal : ℂ)⁻¹ *
        ∑' p : (Fˣ ⧸ G.Δ) × F, ∫ x in B, scalarOf P G Fs.f Fs.fC
          (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) *
            nInf P x * g) := by
  classical
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  obtain ⟨e, hsmall, hbig⟩ := rational_bruhat_coset_equiv P G
  let R : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) → GL (Fin 2) F :=
    Sum.elim (fun δ => diagGL (Quotient.out δ))
      (fun p => diagGL (Quotient.out p.1) * weylGL * upperGL p.2)
  have he (u) : e u = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (R u) := by
    cases u with
    | inl δ => exact hsmall δ
    | inr p => exact hbig p.1 p.2
  have hrep (u) (h : P.tc.G) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out (e u)) * h) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat (R u) * h) := by
    have hb : R u * (Quotient.out (e u))⁻¹ ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ((Quotient.out_eq (e u)).trans (he u)))
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (R u * (Quotient.out (e u))⁻¹) hb
        (P.tc.rat (Quotient.out (e u)) * h)).symm
  have hsum : Summable (fun β : Q => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (Quotient.out β) * g)) :=
    (eisenstein_summable P G hs Fs g).of_norm_bounded fun _ => le_rfl
  have hsmallSum : Summable (fun δ : Fˣ ⧸ G.Δ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out δ)) * g)) :=
    (hsum.comp_injective (e.injective.comp Sum.inl_injective)).congr
      (fun δ => hrep (Sum.inl δ) g)
  obtain ⟨_, habs, _⟩ := eisenstein_integral_tsum_on_compact P G hs Fs g K hK B hB hBK
  let I (β : Q) : ℂ := ∫ x in B, scalarOf P G Fs.f Fs.fC
    (P.tc.rat (Quotient.out β) * nInf P x * g)
  have hsumI : Summable I := habs.of_norm_bounded fun _ => norm_integral_le_integral_norm _
  have hrepI (p : (Fˣ ⧸ G.Δ) × F) : I (e (Sum.inr p)) =
      ∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) * nInf P x * g) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simpa only [R, Sum.elim_inr, mul_assoc] using hrep (Sum.inr p) (nInf P x * g)
  have hbigSum : Summable (fun p : (Fˣ ⧸ G.Δ) × F => ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) * nInf P x * g)) :=
    (hsumI.comp_injective (e.injective.comp Sum.inr_injective)).congr hrepI
  have hsmallIntegral (δ : Fˣ ⧸ G.Δ) :
      (∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ)) * nInf P x * g)) =
      ((volume B).toReal : ℂ) * scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ)) * g) := by
    simp_rw [scalarOf_diag_unipotent P G Fs]
    rw [setIntegral_const, Complex.real_smul]
    rfl
  have hvolC : ((volume B).toReal : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hvol
  have hpsi0 (x : InfinitePlace F → ℂ) : psiInf (0 : F) x = 1 := by
    simp [psiInf, psiC]
  refine ⟨hsmallSum, hbigSum, ?_⟩
  simp only [torusCoeff, Complex.ofReal_inv, neg_zero, hpsi0, mul_one]
  rw [eisenstein_bruhat_integral_on_compact P G hs Fs g K hK B hB hBK]
  simp_rw [hsmallIntegral]
  rw [tsum_mul_left, mul_add, ← mul_assoc, inv_mul_cancel₀ hvolC, one_mul]

/-- A fixed finite rational period becomes an archimedean translation in a scalar summand. -/
theorem scalarOf_rational_period_translate
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G)
    (γ : GL (Fin 2) F) (α : F) (x : InfinitePlace F → ℂ)
    (hfix : ∀ h, scalarOf P G Fs.f Fs.fC
      (h * (g⁻¹ * nFin P α * g)) = scalarOf P G Fs.f Fs.fC h) :
    scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL α) * nInf P x * g) =
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat γ * nInf P (infEmbA α + x) * g) := by
  classical
  have hupper (a b : ℂ) : upperM ℂ a * upperM ℂ b = upperM ℂ b * upperM ℂ a := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hcomm (y : InfinitePlace F → ℂ) :
      P.tc.rat (upperGL α) * nInf P y = nInf P y * P.tc.rat (upperGL α) := by
    obtain ⟨r, hq, hf, hc⟩ := P.nS_components
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y)
    have hf1 (v : FinPlace F) : P.compF v r = 1 := by simpa using hf v
    have hRP : P.ratRP (upperGL α) * r = r * P.ratRP (upperGL α) := by
      apply P.comp_ext
      · intro v
        simp only [map_mul, hf1, mul_one, one_mul]
      · intro w
        have hu : Matrix.GeneralLinearGroup.map w.embedding (upperGL α) =
            upperM ℂ (w.embedding α) := by
          apply Units.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.GeneralLinearGroup.map, upperGL, upperM]
        rw [map_mul, map_mul, P.compC_ratRP, hc, hu]
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg (fun a : GL (Fin 2) ℂ => (QuotientGroup.mk a : PGL2 ℂ))
          (hupper (w.embedding α) (y w))
    simpa only [map_mul, P.q_ratRP, hq, nInf] using congrArg P.q hRP
  have hni (y z : InfinitePlace F → ℂ) : nInf P (y + z) = nInf P y * nInf P z := by
    dsimp only [nInf]
    have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y + z) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) +
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), z) := by simp
    rw [hp, ofAdd_add, map_mul]
  have hy : (infEmbA α + x) + (-infEmbA α) = x := by abel
  have hfactor : (P.tc.rat γ * nInf P (infEmbA α + x) * g) *
      (g⁻¹ * nFin P α * g) = P.tc.rat (γ * upperGL α) * nInf P x * g := by
    dsimp only [nFin]
    calc
      _ = P.tc.rat γ * (nInf P (infEmbA α + x) * P.tc.rat (upperGL α)) *
          nInf P (-infEmbA α) * g := by group
      _ = P.tc.rat γ * (P.tc.rat (upperGL α) * nInf P (infEmbA α + x)) *
          nInf P (-infEmbA α) * g := by rw [← hcomm]
      _ = (P.tc.rat γ * P.tc.rat (upperGL α)) *
          (nInf P (infEmbA α + x) * nInf P (-infEmbA α)) * g := by group
      _ = (P.tc.rat γ * P.tc.rat (upperGL α)) * nInf P x * g := by rw [← hni, hy]
      _ = _ := by rw [map_mul]
  simpa only [hfactor] using hfix (P.tc.rat γ * nInf P (infEmbA α + x) * g)

/-- Summable translated-domain norm integrals justify global integration over an ideal lattice. -/
theorem ideal_domain_integral_tiling
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (_hB : MeasurableSet B) (hBK : B ⊆ K)
    (hBd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) B volume)
    (f : (InfinitePlace F → ℂ) → ℂ) (hf : Continuous f)
    (hsum : Summable (fun ξ : (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ∫ x in B, ‖f (infEmbA (ξ : F) + x)‖)) :
    Integrable f ∧
      (∫ x : InfinitePlace F → ℂ, f x) =
        ∑' ξ : (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
          ∫ x in B, f (infEmbA (ξ : F) + x) := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let H := (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let L := H.map (infEmbA (F := F)).toAddMonoidHom
  let e : H ≃+ L := H.equivMapOfInjective (infEmbA (F := F)).toAddMonoidHom
    (infEmbA (F := F)).injective
  let : Countable L := e.symm.injective.countable
  have heval (ξ : H) : (e ξ : InfinitePlace F → ℂ) = infEmbA (ξ : F) := rfl
  have hint (ξ : H) : IntegrableOn
      (fun x : InfinitePlace F → ℂ => f (infEmbA (ξ : F) + x)) B := by
    exact (ContinuousOn.integrableOn_compact hK
      (hf.comp (continuous_const.add continuous_id)).continuousOn).mono_set hBK
  have hlin : (∫⁻ x : InfinitePlace F → ℂ, ENNReal.ofReal ‖f x‖) =
      ∑' ξ : H, ∫⁻ x in B, ENNReal.ofReal ‖f (infEmbA (ξ : F) + x)‖ := by
    calc
      _ = ∑' t : L, ∫⁻ x in B, ENNReal.ofReal ‖f ((t : InfinitePlace F → ℂ) + x)‖ :=
        hBd.lintegral_eq_tsum'' (fun x => ENNReal.ofReal ‖f x‖)
      _ = ∑' ξ : H, ∫⁻ x in B, ENNReal.ofReal ‖f ((e ξ : InfinitePlace F → ℂ) + x)‖ :=
        (e.toEquiv.tsum_eq _).symm
      _ = _ := by simp only [heval]
  have hnormint (ξ : H) :
      (∫⁻ x in B, ENNReal.ofReal ‖f (infEmbA (ξ : F) + x)‖) =
        ENNReal.ofReal (∫ x in B, ‖f (infEmbA (ξ : F) + x)‖) :=
    (ofReal_integral_eq_lintegral_ofReal (hint ξ).norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _)).symm
  have hnonneg (ξ : H) : 0 ≤ ∫ x in B, ‖f (infEmbA (ξ : F) + x)‖ :=
    integral_nonneg fun x => norm_nonneg _
  have hfinite : (∫⁻ x : InfinitePlace F → ℂ, ENNReal.ofReal ‖f x‖) < ⊤ := by
    rw [hlin]
    simp_rw [hnormint]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]
    exact ENNReal.ofReal_lt_top
  have hintglobal : Integrable f :=
    ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_norm f).2 hfinite⟩
  refine ⟨hintglobal, ?_⟩
  calc
    _ = ∑' t : L, ∫ x in B, f ((t : InfinitePlace F → ℂ) + x) :=
      hBd.integral_eq_tsum'' f hintglobal
    _ = ∑' ξ : H, ∫ x in B, f ((e ξ : InfinitePlace F → ℂ) + x) :=
      (e.toEquiv.tsum_eq _).symm
    _ = _ := by simp only [heval, H]

/-- Rational big-cell periods unfold to globally integrable archimedean summands. -/
theorem eisenstein_bigCell_unfold_periods
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hfix : ∀ α ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P α * g)) = scalarOf P G Fs.f Fs.fC h)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K)
    (hBd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) B volume)
    (δ : Fˣ ⧸ G.Δ) :
    (∀ η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
      Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
          nInf P x * g))) ∧
    Summable (fun η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
          nInf P x * g)‖) ∧
    (∑' ξ : F, ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * nInf P x * g)) =
      ∑' η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
        ∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
          (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
            nInf P x * g) := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let J := (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let Q := F ⧸ J
  let f (ξ : F) (x : InfinitePlace F → ℂ) : ℂ := scalarOf P G Fs.f Fs.fC
    (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * nInf P x * g)
  obtain ⟨e, _, hbig⟩ := rational_bruhat_coset_equiv P G
  obtain ⟨_, habs, _⟩ := eisenstein_integral_tsum_on_compact P G hs Fs g K hK B hB hBK
  have hrep (ξ : F) (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * nInf P x * g) = f ξ x := by
    let γ := diagGL (Quotient.out δ) * weylGL * upperGL ξ
    have hb : γ * (Quotient.out (e (Sum.inr (δ, ξ))))⁻¹ ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp
        (Quotient.exact ((Quotient.out_eq (e (Sum.inr (δ, ξ)))).trans (hbig δ ξ)))
    dsimp only [f]
    simpa only [γ, map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (γ * (Quotient.out (e (Sum.inr (δ, ξ))))⁻¹) hb
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * (nInf P x * g))).symm
  have hrepNorm (ξ : F) :
      (∫ x in B, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * nInf P x * g)‖) =
        ∫ x in B, ‖f ξ x‖ := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg norm (hrep ξ x)
  have hinj : Function.Injective (fun ξ : F => e (Sum.inr (δ, ξ))) :=
    e.injective.comp (Sum.inr_injective.comp (Prod.mk_right_injective δ))
  have hnormSeries : Summable (fun ξ : F => ∫ x in B, ‖f ξ x‖) :=
    (habs.comp_injective hinj).congr hrepNorm
  have hcomplexSeries : Summable (fun ξ : F => ∫ x in B, f ξ x) :=
    hnormSeries.of_norm_bounded fun ξ => norm_integral_le_integral_norm _
  have hcont (ξ : F) : Continuous (f ξ) :=
    scalarOf_unipotent_continuous P G Fs g
      (diagGL (Quotient.out δ) * weylGL * upperGL ξ)
  have hupper (u v : F) : upperGL (u + v) = upperGL u * upperGL v := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hperiod (ξ : F) (α : J) (x : InfinitePlace F → ℂ) :
      f (ξ + (α : F)) x = f ξ (infEmbA (α : F) + x) := by
    dsimp only [f]
    have hm : diagGL (Quotient.out δ) * weylGL * upperGL (ξ + (α : F)) =
        (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * upperGL (α : F) := by
      simp only [hupper, mul_assoc]
    rw [hm]
    exact scalarOf_rational_period_translate P G Fs g
      (diagGL (Quotient.out δ) * weylGL * upperGL ξ) (α : F) x
      (hfix (α : F) α.property)
  let r (p : Q × J) : F := Quotient.out p.1 + (p.2 : F)
  have hrclass (p : Q × J) : (QuotientAddGroup.mk (r p) : Q) = p.1 := by
    calc
      _ = QuotientAddGroup.mk (Quotient.out p.1) := by
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        have hd : r p - Quotient.out p.1 = (p.2 : F) := by dsimp only [r]; abel
        simpa only [hd] using p.2.property
      _ = p.1 := QuotientAddGroup.out_eq' p.1
  have hrbij : Function.Bijective r := by
    constructor
    · intro p q hpq
      have hq : p.1 = q.1 := by
        calc
          p.1 = (QuotientAddGroup.mk (r p) : Q) := (hrclass p).symm
          _ = QuotientAddGroup.mk (r q) := congrArg (fun z : F => (QuotientAddGroup.mk z : Q)) hpq
          _ = q.1 := hrclass q
      have ha : p.2 = q.2 := by
        apply Subtype.ext
        dsimp only [r] at hpq
        rw [hq] at hpq
        exact add_left_cancel hpq
      exact Prod.ext hq ha
    · intro ξ
      let η : Q := QuotientAddGroup.mk ξ
      have ha : ξ - Quotient.out η ∈ J :=
        QuotientAddGroup.eq_iff_sub_mem.mp ((QuotientAddGroup.out_eq' η).symm)
      refine ⟨(η, ⟨ξ - Quotient.out η, ha⟩), ?_⟩
      change Quotient.out η + (ξ - Quotient.out η) = ξ
      abel
  let ep : F ≃ Q × J := (Equiv.ofBijective r hrbij).symm
  have hep (p : Q × J) : ep.symm p = Quotient.out p.1 + (p.2 : F) := rfl
  have hpairNorm : Summable (fun p : Q × J =>
      ∫ x in B, ‖f (Quotient.out p.1 + (p.2 : F)) x‖) := by
    simpa only [Function.comp_def, hep] using hnormSeries.comp_injective ep.symm.injective
  have hshiftNorm (p : Q × J) :
      (∫ x in B, ‖f (Quotient.out p.1 + (p.2 : F)) x‖) =
        ∫ x in B, ‖f (Quotient.out p.1) (infEmbA (p.2 : F) + x)‖ := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg norm (hperiod (Quotient.out p.1) p.2 x)
  have htranslatedNorm : Summable (fun p : Q × J =>
      ∫ x in B, ‖f (Quotient.out p.1) (infEmbA (p.2 : F) + x)‖) :=
    hpairNorm.congr hshiftNorm
  have ht (η : Q) : Integrable (f (Quotient.out η)) ∧
      (∫ x : InfinitePlace F → ℂ, f (Quotient.out η) x) =
        ∑' α : J, ∫ x in B, f (Quotient.out η) (infEmbA (α : F) + x) :=
    ideal_domain_integral_tiling 𝔞 K hK B hB hBK hBd
      (f (Quotient.out η)) (hcont (Quotient.out η)) (htranslatedNorm.prod_factor η)
  let L := J.map (infEmbA (F := F)).toAddMonoidHom
  let ea : J ≃+ L := J.equivMapOfInjective (infEmbA (F := F)).toAddMonoidHom
    (infEmbA (F := F)).injective
  let : Countable L := ea.symm.injective.countable
  have heval (α : J) : (ea α : InfinitePlace F → ℂ) = infEmbA (α : F) := rfl
  have hnormTiling (η : Q) :
      (∫ x : InfinitePlace F → ℂ, ‖f (Quotient.out η) x‖) =
        ∑' α : J, ∫ x in B, ‖f (Quotient.out η) (infEmbA (α : F) + x)‖ := by
    calc
      _ = ∑' t : L, ∫ x in B, ‖f (Quotient.out η) ((t : InfinitePlace F → ℂ) + x)‖ :=
        hBd.integral_eq_tsum'' (fun x => ‖f (Quotient.out η) x‖) (ht η).1.norm
      _ = ∑' α : J, ∫ x in B, ‖f (Quotient.out η) ((ea α : InfinitePlace F → ℂ) + x)‖ :=
        (ea.toEquiv.tsum_eq _).symm
      _ = _ := by simp only [heval]
  have hglobalNorm : Summable (fun η : Q =>
      ∫ x : InfinitePlace F → ℂ, ‖f (Quotient.out η) x‖) :=
    htranslatedNorm.prod.congr (fun η => (hnormTiling η).symm)
  have hpairComplex : Summable (fun p : Q × J => ∫ x in B, f (ep.symm p) x) :=
    hcomplexSeries.comp_injective ep.symm.injective
  refine ⟨?_, ?_, ?_⟩
  · intro η
    exact (ht η).1
  · simpa only [f, Q, J] using hglobalNorm
  · change (∑' ξ : F, ∫ x in B, f ξ x) =
      ∑' η : Q, ∫ x : InfinitePlace F → ℂ, f (Quotient.out η) x
    calc
      _ = ∑' p : Q × J, ∫ x in B, f (ep.symm p) x := (ep.symm.tsum_eq _).symm
      _ = ∑' η : Q, ∑' α : J, ∫ x in B, f (ep.symm (η, α)) x := hpairComplex.tsum_prod
      _ = _ := by
        apply tsum_congr
        intro η
        calc
          _ = ∑' α : J, ∫ x in B, f (Quotient.out η) (infEmbA (α : F) + x) := by
            apply tsum_congr
            intro α
            rw [hep]
            apply integral_congr_ae
            filter_upwards [] with x
            exact hperiod (Quotient.out η) α x
          _ = _ := (ht η).2.symm

/-- Rational unipotent representatives can be shifted to finite coordinates under global integration. -/
theorem scalarOf_finitePeriod_arch_integral
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G)
    (γ : GL (Fin 2) F) (ξ : F)
    (hint : Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g))) :
    Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat γ * nFin P ξ * nInf P x * g)) ∧
    (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g)) =
      (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
        (P.tc.rat γ * nFin P ξ * nInf P x * g)) ∧
    (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g)‖) =
      ∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat γ * nFin P ξ * nInf P x * g)‖ := by
  have hni (y z : InfinitePlace F → ℂ) : nInf P (y + z) = nInf P y * nInf P z := by
    dsimp only [nInf]
    have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y + z) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) +
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), z) := by simp
    rw [hp, ofAdd_add, map_mul]
  have hfactor (x : InfinitePlace F → ℂ) :
      P.tc.rat γ * nFin P ξ * nInf P x * g =
        P.tc.rat (γ * upperGL ξ) * nInf P (-infEmbA ξ + x) * g := by
    dsimp only [nFin]
    calc
      _ = (P.tc.rat γ * P.tc.rat (upperGL ξ)) *
          (nInf P (-infEmbA ξ) * nInf P x) * g := by group
      _ = (P.tc.rat γ * P.tc.rat (upperGL ξ)) *
          nInf P (-infEmbA ξ + x) * g := by rw [← hni]
      _ = _ := by rw [map_mul]
  have heq (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat γ * nFin P ξ * nInf P x * g) =
        scalarOf P G Fs.f Fs.fC
          (P.tc.rat (γ * upperGL ξ) * nInf P (-infEmbA ξ + x) * g) := by
    rw [hfactor]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [heq] using hint.comp_add_left (-infEmbA ξ)
  · simp_rw [heq]
    exact (integral_add_left_eq_self
      (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
        (P.tc.rat (γ * upperGL ξ) * nInf P x * g)) (-infEmbA ξ)).symm
  · simp_rw [heq]
    exact (integral_add_left_eq_self
      (fun x : InfinitePlace F → ℂ => ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (γ * upperGL ξ) * nInf P x * g)‖) (-infEmbA ξ)).symm

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
