import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Eis
import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.Plan
import ArtinPrimitiveRoots.Theta.Proofs.«TH-CUSP».Plan
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Helpers
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GOOD-SUBGROUP».Helpers

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-REDUCTION -/

section Reduction

open MeasureTheory

variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- `a(y)` at the complex places, `y_w > 0` (junk `1` otherwise). -/
def aInf (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ) : P.tc.G :=
  if hy : ∀ w, 0 < y w then
    ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w =>
      P.tc.aS (S.atComplex w (Units.mk0 ((y w : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')))).prod
  else 1

/-- The classical function on `X = (ℍ³)^r` attached to `Ψ : G → ℂ` and a finite-adelic point `g`:
`z = (x_w + j y_w)_w ↦ Ψ(n_∞(x) a_∞(y) g)`. -/
def classicalOf (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (z : ArtinPrimitiveRoots.A1.Spec.X F) : ℂ :=
  Ψ (nInf P (fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z w)) *
    aInf P (fun w => ArtinPrimitiveRoots.A1.Spec.height (z w)) * g)

/-- The level `K_f(T0, m)`: `q x` with `x_v ∈ Kc(m_v)` on `T0`, `x_v ∈ Kmax_v` off `T0`, and
trivial complex components. -/
def levelSet (P : CoverPackage D S H A) (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0)
    (m : FinPlace F → ℕ) : Set P.tc.G :=
  {g | ∃ x : P.RP, P.q x = g ∧ (∀ w, P.compC w x = 1) ∧
    (∀ v ∈ T0, P.compF v x ∈ (P.loc v).Kc (m v)) ∧
    ∀ v (hv : v ∉ T0), P.compF v x ∈ (P.tame v (fun h => hv (hT0 h))).Kmax}

/-- The archimedean maximal compact `PU(2)^r` inside `G`. -/
def infCompact (P : CoverPackage D S H A) : Set P.tc.G :=
  {g | ∃ x : P.RP, P.q x = g ∧ (∀ v, P.compF v x = 1) ∧
    ∀ w, ∃ k : GL (Fin 2) ℂ, (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      P.compC w x = QuotientGroup.mk k}

/-- Geometric form of finite classical components, also exposing the actual factorization. -/
theorem th_classical_geometric_components (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) :
    ∃ J : Finset P.tc.G,
      (∀ j ∈ J, ∃ r : P.RP, P.q r = j ∧ ∀ w, P.compC w r = 1) ∧
      ∀ g, ∃ γ : GL (Fin 2) F, ∃ j ∈ J,
        ∃ x : InfinitePlace F → ℂ, ∃ y : InfinitePlace F → ℝ,
          (∀ w, 0 < y w) ∧ ∃ ki ∈ infCompact P,
            ∃ kf ∈ levelSet P T0 hT0 m,
              P.tc.rat γ * g = nInf P x * aInf P y * j * (ki * kf) := by
  classical
  obtain ⟨J, hJ, hfinite⟩ := th_classical_finite_components P T0 hT0 m hm
  refine ⟨J.image P.q, ?_, ?_⟩
  · intro j hj
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨r, rfl, hJ r hr⟩
  · intro g
    obtain ⟨r, hqr⟩ := P.q_surj g
    obtain ⟨γ, j, hj, kf, ⟨hkfC, hkfT, hkfO⟩, ζ, hζfin, hζprod, hf⟩ := hfinite r
    choose x y hy k hk hc using
      fun w => th_classical_pgl_reconstruction (P.compC w (P.ratRP γ * r))
    obtain ⟨ki, hkiF, hkiC⟩ := P.comp_surj (fun _ => 1)
      (fun w => QuotientGroup.mk (k w)) (by
        apply Set.finite_empty.subset
        intro v hv
        obtain ⟨hv, hbad⟩ := hv
        exact (hbad (P.tame v hv).Kmax.one_mem).elim)
    obtain ⟨a, hqa, haF, haC⟩ := th_classical_arch_lift P x y hy
    have harch : th_classical_archTerm P y hy = aInf P y := by
      simp only [aInf, dif_pos hy]
      rfl
    rw [harch] at hqa
    have he : P.q (P.ratRP γ * r) = P.q (a * j * (ki * kf)) := by
      apply (P.q_eq _ _).mpr
      refine ⟨ζ, hζfin, hζprod, ?_, ?_⟩
      · intro v
        simpa only [map_mul, haF, hkiF, one_mul] using hf v
      · intro w
        simpa only [map_mul, haC, hJ j hj, hkiC, hkfC, mul_one,
          ← QuotientGroup.mk_mul] using hc w
    refine ⟨γ, P.q j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, x, y, hy,
      P.q ki, ⟨ki, rfl, hkiF, fun w => ⟨k w, hk w, hkiC w⟩⟩,
      P.q kf, ⟨kf, rfl, hkfC, hkfT, hkfO⟩, ?_⟩
    simpa only [map_mul, P.q_ratRP, hqr, hqa] using he

/-- **red:components** (strong approximation for `SL₂`, finiteness of `F^×\𝔸_f^×/det K_f 𝔸_f^{×2}`):
finitely many finite-adelic points `g_j`; an automorphic, level- and `PU(2)^r`-invariant function
vanishing on all `g_∞ g_j` vanishes. C7 of `sol-gate-theta` requires the prescribed level to be at
least `m0` on `T0`. -/
theorem exists_classical_components (P : CoverPackage D S H A) (T0 : Finset (FinPlace F))
    (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) :
    ∃ J : Finset P.tc.G, (∀ gj ∈ J, ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1) ∧
      ∀ Ψ : P.tc.G → ℂ, (∀ γ g, Ψ (P.tc.rat γ * g) = Ψ g) →
        (∀ g, ∀ k ∈ levelSet P T0 hT0 m, Ψ (g * k) = Ψ g) →
        (∀ g, ∀ k ∈ infCompact P, Ψ (g * k) = Ψ g) →
        (∀ gj ∈ J, ∀ z, classicalOf P Ψ gj z = 0) → ∀ g, Ψ g = 0 := by
  obtain ⟨J, hJ, hgeom⟩ := th_classical_geometric_components P T0 hT0 m hm
  refine ⟨J, hJ, ?_⟩
  intro Ψ hAut hLevel hInf hzero g
  obtain ⟨γ, j, hj, x, y, hy, ki, hki, kf, hkf, hfac⟩ := hgeom g
  have hsection : Ψ (nInf P x * aInf P y * j) = 0 := by
    have hz := hzero j hj (Spec.ptX' F x y)
    simpa only [classicalOf, Spec.ptX', Spec.horiz_pt _ _ (hy _),
      Spec.height_pt _ _ (hy _)] using hz
  calc
    Ψ g = Ψ (P.tc.rat γ * g) := (hAut γ g).symm
    _ = Ψ (nInf P x * aInf P y * j * (ki * kf)) := congrArg Ψ hfac
    _ = Ψ (nInf P x * aInf P y * j) := by
      rw [← mul_assoc, hLevel _ kf hkf, hInf _ ki hki]
    _ = 0 := hsection

/-- **red:congruence** (Kubota's splitting on `Γ(N₀)`, archimedean Iwasawa, free action): for each
`g_j` there is a finite-index, freely acting `Γ'' ≤ SL₂(O_F)` with
`rat(γ) n_∞(x) a_∞(y) g_j = n_∞(x′) a_∞(y′) g_j k_∞ k`, `(x′, y′)` the coordinates of `γ • z`.
C7 of `sol-gate-theta` restricts the level to the guaranteed open range. -/
theorem exists_good_subgroup [IsTotallyComplex F] (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) (gj : P.tc.G)
    (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1) :
    ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)), Γ.FiniteIndex ∧
      ArtinPrimitiveRoots.A1.Spec.FreeAction F Γ ∧
      ∀ γ ∈ Γ, ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
        ∃ k ∈ levelSet P T0 hT0 m, ∃ kinf ∈ infCompact P,
          P.tc.rat (Matrix.SpecialLinearGroup.toGL
              (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * nInf P x * aInf P y * gj =
            nInf P (fun w => ArtinPrimitiveRoots.A1.Spec.horiz
                ((γ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) w)) *
              aInf P (fun w => ArtinPrimitiveRoots.A1.Spec.height
                ((γ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) w)) * gj * (kinf * k) := by
  classical
  obtain ⟨j, hqj, hjC⟩ := hgj
  obtain ⟨Γ, hindex, hfree, hfinite⟩ := th_good_finite_level P T0 hT0 m hm j
  refine ⟨Γ, hindex, hfree, ?_⟩
  intro γ hγ x y hy
  obtain ⟨kf, ⟨hkfC, hkfT, hkfO⟩, ζ, hζfin, hζprod, hf⟩ := hfinite γ hγ
  choose k hk hy' hc using fun w => th_classical_sl_reconstruction
    (Spec.toInf F (Spec.toSLF F γ) w) (x w) (y w) (hy w)
  let x' : InfinitePlace F → ℂ := fun w => Spec.horiz ((γ • Spec.ptX' F x y) w)
  let y' : InfinitePlace F → ℝ := fun w => Spec.height ((γ • Spec.ptX' F x y) w)
  have hpos : ∀ w, 0 < y' w := hy'
  obtain ⟨ki, hkiF, hkiC⟩ := P.comp_surj (fun _ => 1)
    (fun w => QuotientGroup.mk (k w)) (by
      apply Set.finite_empty.subset
      intro v hv
      obtain ⟨hv, hbad⟩ := hv
      exact (hbad (P.tame v hv).Kmax.one_mem).elim)
  obtain ⟨a, hqa, haF, haC⟩ := th_classical_arch_lift P x y hy
  obtain ⟨a', hqa', haF', haC'⟩ := th_classical_arch_lift P x' y' hpos
  have harch : th_classical_archTerm P y hy = aInf P y := by
    simp only [aInf, dif_pos hy]
    rfl
  have harch' : th_classical_archTerm P y' hpos = aInf P y' := by
    simp only [aInf, dif_pos hpos]
    rfl
  rw [harch] at hqa
  rw [harch'] at hqa'
  have he : P.q (P.ratRP (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F γ)) * a * j) =
      P.q (a' * j * (ki * kf)) := by
    apply (P.q_eq _ _).mpr
    refine ⟨ζ, hζfin, hζprod, ?_, ?_⟩
    · intro v
      simpa only [map_mul, haF, haF', hkiF, mul_one, one_mul] using hf v
    · intro w
      simp only [map_mul, P.compC_ratRP, haC, haC', hjC, hkiC, hkfC, mul_one,
        ← QuotientGroup.mk_mul]
      have hmap : Matrix.GeneralLinearGroup.map w.embedding
          (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F γ)) =
          Matrix.SpecialLinearGroup.toGL (Spec.toInf F (Spec.toSLF F γ) w) := by
        ext i j
        rfl
      rw [hmap]
      have hact : (γ • Spec.ptX' F x y) w =
          (Spec.toInf F (Spec.toSLF F γ) w) • Spec.pt (x w) (y w) := rfl
      simpa only [← QuotientGroup.mk_mul, x', y', hact] using hc w
  refine ⟨P.q kf, ⟨kf, rfl, hkfC, hkfT, hkfO⟩, P.q ki,
    ⟨ki, rfl, hkiF, fun w => ⟨k w, hk w, hkiC w⟩⟩, ?_⟩
  simpa only [map_mul, P.q_ratRP, hqa, hqa', hqj, mul_assoc] using he

/-- **red:decompose** (P-SPEC obligation (1)): for sections with spherical complex components and a
uniform level, on the component of `g_j` the adelic Eisenstein series is a finite combination of
P-SPEC Eisenstein series of one good `Γ''`, with coefficients holomorphic on `Re s > 0`; the adelic
series converges absolutely for `Re s > 1/2`. C6/C7 of `sol-gate-theta` strengthen the datum and
require every prescribed level to satisfy its `m0` bound. -/
theorem red_decompose [IsTotallyComplex F] (P : CoverPackage D S H A) (G : GlobalDatum P)
    (sec : ∀ s : ℂ, GlobalSection P G s) (T0 : Finset (FinPlace F)) (hT0 : ∀ s, (sec s).T0 = T0)
    (hsub : S.Sf ⊆ T0) (hC : ∀ s w, (sec s).fC w = sphC s) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v)
    (hlevel : ∀ s, ∀ g, ∀ k ∈ levelSet P T0 hsub m,
      scalarOf P G (sec s).f (sec s).fC (g * k) = scalarOf P G (sec s).f (sec s).fC g)
    (han : ∀ v (g : (P.loc v).L), AnalyticOnNhd ℂ (fun s => (sec s).f v g) {s | 0 < s.re})
    (gj : P.tc.G) (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1) :
    ∃ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)), Γ.FiniteIndex ∧
      ArtinPrimitiveRoots.A1.Spec.FreeAction F Γ ∧
      ∃ (ι : Type) (_ : Fintype ι) (σ : ι → Matrix.SpecialLinearGroup (Fin 2) F) (c : ι → ℂ → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) {s | 0 < s.re}) ∧
        ∀ s : ℂ, 1 / 2 < s.re → ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
          (∀ w, 0 < y w) →
          (Summable fun γ : Quotient (QuotientGroup.rightRel (Bstar G)) =>
            ‖scalarOf P G (sec s).f (sec s).fC (P.tc.rat (Quotient.out γ) * (nInf P x * aInf P y * gj))‖) ∧
          eisenstein P G (sec s) (nInf P x * aInf P y * gj) =
            ∑ i, c i s * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ (σ i) s
              (ArtinPrimitiveRoots.A1.Spec.ptX' F x y) := by
  have hgood := exists_good_subgroup P T0 hsub m hm gj hgj
  obtain ⟨d⟩ := red_decompose_part1 P G (aInf P) rfl T0 hsub m hm gj hgj
    (by simpa only [redLevel, levelSet, redCompact, infCompact] using hgood)
  obtain ⟨Ds, b, hb, hzero, hterm⟩ := th_decompose_part2 P G sec T0 hT0 hsub hC m hm
    (by simpa only [redLevel, levelSet] using hlevel) han (aInf P) rfl gj hgj d
  letI := d.fintype
  letI := d.hfinite
  refine ⟨d.Γ, d.hfinite, d.hfree, d.ι, d.fintype, d.σ,
    (fun i s => ∑ δ ∈ Ds i, b i δ s), ?_, ?_⟩
  · intro i
    exact Finset.analyticOnNhd_fun_sum (Ds i) (fun δ _ => hb i δ)
  · intro s hs x y hy
    exact th_decompose_part3 d.Γ d.σ d.e Ds (fun i δ => b i δ s)
      (fun q => scalarOf P G (sec s).f (sec s).fC
        (P.tc.rat (Quotient.out q) * (nInf P x * aInf P y * gj)))
      s hs (ArtinPrimitiveRoots.A1.Spec.ptX' F x y)
      (fun i δ hδ => hzero i δ hδ s) (hterm s hs x y hy)

/-- **red:constant-term**: vanishing adelic constant coefficients (over every adapted lattice at
every point) give vanishing classical constant terms at every cusp and height, in the form of
P-SPEC `res_lincomb_eq_zero`. C8 of `sol-gate-theta` requires finite index and an adapted period at
each point. The `sol-gate-theta2` correction adds the adelic automorphy, right compact invariance,
and finite-adelic component used by the blueprint's cusp reduction. -/
theorem classical_constTerm_eq_zero [IsTotallyComplex F] (P : CoverPackage D S H A)
    (Ψ : P.tc.G → ℂ) (gj : P.tc.G)
    (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1)
    (hAut : ∀ γ g, Ψ (P.tc.rat γ * g) = Ψ g)
    (hInf : ∀ g, ∀ k ∈ infCompact P, Ψ (g * k) = Ψ g)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    (hfinite : Γ.FiniteIndex)
    (hlevel : ∀ g : P.tc.G, ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F,
      𝔞 ≠ 0 ∧ ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        Ψ (h * (g⁻¹ * nFin P ξ * g)) = Ψ h)
    (hΓ : ∀ γ ∈ Γ, ∀ z, classicalOf P Ψ gj (γ • z) = classicalOf P Ψ gj z)
    (hΨ : ∀ (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (Pd : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 → (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h, Ψ (h * (g⁻¹ * nFin P ξ * g)) = Ψ h) →
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
        Pd volume → Bornology.IsBounded Pd → torusCoeff P Ψ g Pd 0 = 0) :
    ∀ (τ : Matrix.SpecialLinearGroup (Fin 2) F) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      ∃ Pτ : Set (InfinitePlace F → ℂ),
        IsAddFundamentalDomain (ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) Pτ volume ∧
        ∫ x in Pτ, classicalOf P Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) = 0 := by
  intro τ y hy
  obtain ⟨g', htransport⟩ := classical_constTerm_eq_zero_part1 P (aInf P) rfl Ψ gj hgj hAut
    (by simpa only [infCompact] using hInf) τ y hy
  obtain ⟨𝔞, P₀, Pτ, h𝔞, hfix, hle, hindex, hP₀, hbounded, hvol, hPτ⟩ :=
    th_cusp_part2 P Ψ g' Γ hfinite τ hlevel
  have hcoeff := hΨ g' 𝔞 P₀ h𝔞 hfix hP₀ hbounded
  have hnorm : ((((volume P₀).toReal)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (inv_ne_zero hvol.ne')
  have hzero' : ∫ x in P₀, Ψ (nInf P x * g') = 0 := by
    have hproduct : ((((volume P₀).toReal)⁻¹ : ℝ) : ℂ) *
        (∫ x in P₀, Ψ (nInf P x * g')) = 0 := by
      simpa [torusCoeff, psiInf, psiC] using hcoeff
    exact (mul_eq_zero.mp hproduct).resolve_left hnorm
  refine ⟨Pτ, hPτ, ?_⟩
  change ∫ x in Pτ, cuspClassical P (aInf P) Ψ gj
    (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) = 0
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have hcount : (ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ :
      Set (InfinitePlace F → ℂ)).Countable := by
    change ((ArtinPrimitiveRoots.A1.Spec.infEmb F) ''
      (ArtinPrimitiveRoots.A1.Spec.cuspLattice F Γ τ : Set F)).Countable
    exact (Set.to_countable _).image _
  letI : Countable (ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) := hcount.to_subtype
  apply th_cusp_part3 _ _ hle hindex P₀ Pτ hP₀ hPτ
    (fun x => cuspClassical P (aInf P) Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y))
  · exact th_cusp_periodic P (aInf P) Ψ gj Γ
      (by simpa only [cuspClassical, classicalOf] using hΓ) τ y hy
  · simpa only [htransport] using hzero'

end Reduction

end ArtinPrimitiveRoots.A1.Theta
