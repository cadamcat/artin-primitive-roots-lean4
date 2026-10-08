import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.LocalWhit
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».LocalModel
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.GoodFactor
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.GaussBound
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.SphericalBound
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.QuotientCoordinates
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.ValuationGeometry
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.OrdinaryClasses
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.IdealEncoding
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.RationalEncoding
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.IdealMajorant
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.LocalProduct

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

/-- Choose the exceptional or tame local model at each finite place. -/
theorem globalLocal_models (hSt : ∀ v, SteinbergAt H v) :
    ∀ v : FinPlace F, Nonempty (GlobalLocalModel D H v (v ∉ S.Sf)) := by
  intro v
  by_cases hv : v ∈ S.Sf
  · obtain ⟨L, hc, hl⟩ := globalLocal_lagrangian D H v
    obtain ⟨M, _⟩ := globalLocal_wild_model D H v L hc hl
    simpa only [hv, not_true_eq_false] using
      (show Nonempty (GlobalLocalModel D H v False) from ⟨M⟩)
  · simpa only [hv, not_false_eq_true] using
      globalLocal_tame_model D H v (hSt v) (fun h => hv (S.over6 v h))

/-- **eis:global-datum** (existence). The strengthened datum is required by C6 of
`sol-gate-theta`. -/
theorem exists_globalDatum (P : CoverPackage D S H A) (hSt : ∀ v, SteinbergAt H v) :
    Nonempty (GlobalDatum P) := by
  classical
  let M : ∀ v, GlobalLocalModel D H v (v ∉ S.Sf) :=
    fun v => Classical.choice (globalLocal_models hSt v)
  exact ⟨{
    T := fun v => (M v).T
    B := fun v hv => (M v).B hv
    Alag := fun v => (M v).Alag
    alag_cubes := fun v => (M v).cubes
    alag_lagrangian := fun v => (M v).lagrangian
    lam := fun v => (M v).lam
    ω := fun _ _ => 1
    lam_equiv := by intro v y hy x; simpa using (M v).lam_fixed y hy x
    lam_ne := fun v => (M v).lam_ne
    alag_tame := fun v hv => (M v).alag_tame hv
    ω_tame := by intros; rfl
    lam_tame := fun v hv => (M v).lam_tame hv
    ω_rational := by intros; simp
  }⟩

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

/-- **eis:converge** (via P-REDUCTION and P-SPEC `eisSeries_majorant`): absolute convergence for
`Re s > 1/2`. C6 of `sol-gate-theta` strengthens the input datum to exclude divergent cube repeats. -/
theorem eisenstein_summable (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G) :
    Summable fun γ : Quotient (QuotientGroup.rightRel (Bstar G)) =>
      ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out γ) * g)‖ := by
  sorry

/-- **eis:automorphic**: in the convergence region `E` is automorphic, genuine, and right-invariant
under every element fixing all local sections. -/
theorem eisenstein_automorphic (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) :
    (∀ γ g, eisenstein P G Fs (P.tc.rat γ * g) = eisenstein P G Fs g) ∧
    (∀ ζ g, eisenstein P G Fs (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * eisenstein P G Fs g) ∧
    (∀ k : P.tc.G, (∀ h, scalarOf P G Fs.f Fs.fC (h * k) = scalarOf P G Fs.f Fs.fC h) →
      ∀ g, eisenstein P G Fs (g * k) = eisenstein P G Fs g) := by
  sorry

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

/-- The local Whittaker factor is one outside the exceptional support. -/
theorem whit_good_factor (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x : P.RP) (δ : Fˣ) (v : FinPlace F) (hv : v ∉ Fs.T0)
    (hu : IsLocUnit v (toLoc v δ))
    (hk : P.compF v x ∈ (P.tame v (fun h => hv (Fs.sub h))).Kmax) :
    G.lam v ((G.T v).σa (toLoc v δ)
      (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) = 1 := by
  have hvS : v ∉ S.Sf := fun h => hv (Fs.sub h)
  have hmem : toLoc v δ ∈ G.Alag v :=
    (G.alag_tame v hvS (toLoc v δ)).2 ⟨0, toLoc v δ, hu, by simp⟩
  have hfixed : ∀ z, G.lam v ((G.T v).σa (toLoc v δ) z) = G.lam v z := by
    intro z
    rw [G.lam_equiv v (toLoc v δ) hmem z, G.ω_tame v hvS (toLoc v δ) hmem, one_mul]
  exact whit_good_local_factor (P.loc v) (P.tame v hvS) (G.T v) (G.B v hvS) A (μ v)
    (fun h => hvS (S.over6 v h)) (fun h => hvS (S.different_mem v h)) s (Fs.f v)
    (Fs.f_sec v) (Fs.f_sph v hv).1 (Fs.f_sph v hv).2 (G.lam v) (G.lam_tame v hvS)
    (toLoc v δ) hfixed (P.compF v x) hk

/-- A fixed lift and rational torus element have only finitely many nonidentity factors. -/
theorem whit_finite_mulSupport (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x : P.RP) (δ : Fˣ) :
    (Function.mulSupport fun v => G.lam v ((G.T v).σa (toLoc v δ)
      (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v))))).Finite := by
  refine ((Fs.T0.finite_toSet.union (P.comp_restricted x)).union
    (whit_rational_nonunit_finite δ)).subset ?_
  intro v hv
  by_contra hvout
  have hvT : v ∉ Fs.T0 := by
    intro h
    exact hvout (Or.inl (Or.inl h))
  have hvS : v ∉ S.Sf := fun h => hvT (Fs.sub h)
  have hu : IsLocUnit v (toLoc v δ) := by
    by_contra h
    exact hvout (Or.inr h)
  have hk : P.compF v x ∈ (P.tame v hvS).Kmax := by
    by_contra h
    exact hvout (Or.inl (Or.inr ⟨hvS, h⟩))
  exact hv (whit_good_factor P G μ Fs x δ v hvT hu hk)

/-- The unfolded summand evaluated at a specified restricted-product lift. -/
def whitLiftTerm (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x : P.RP) (δ : Fˣ ⧸ G.Δ) : ℂ :=
  (∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
    (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v))))) *
    ∏ w, jacquetC (rtr (P.compC w x) (Fs.fC w))

/-- Changing finitely many local Jacquet vectors preserves absolute convergence. -/
theorem whit_jacquet_family_summable (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x : P.RP)
    (E : Finset (FinPlace F)) (hE : Fs.T0 ⊆ E)
    (hcomp : ∀ v (hv : v ∉ E),
      P.compF v x ∈ (P.tame v (fun h => hv (hE (Fs.sub h)))).Kmax)
    (z : ∀ v : FinPlace F, (G.T v).V)
    (hz : ∀ v, v ∉ E → z v =
      jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v))) :
    Summable (fun δ : Fˣ ⧸ G.Δ =>
      ‖∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (z v))‖) := by
  have hfin (v : FinPlace F) : Finite ((v.adicCompletion F)ˣ ⧸ G.Alag v) := by
    obtain ⟨w, hw⟩ : ∃ w : (G.T v).V, G.lam v w ≠ 0 := by
      by_contra h
      push Not at h
      apply G.lam_ne v
      ext w
      exact h w
    letI : Nontrivial (G.T v).V := ⟨⟨w, 0, by
      intro h
      apply hw
      rw [h, map_zero]⟩⟩
    exact whit_alag_quotient_finite (G.T v) (G.Alag v) (G.alag_cubes v)
  have hbounds (v : FinPlace F) : ∃ c : ℝ, 0 ≤ c ∧
      ∀ t : (v.adicCompletion F)ˣ, ‖G.lam v ((G.T v).σa t (z v))‖ ≤ c := by
    let R := (G.T v).σa_finite.toFinset
    refine ⟨∑ ρ ∈ R, ‖G.lam v (ρ (z v))‖,
      Finset.sum_nonneg (fun ρ _ => norm_nonneg _), ?_⟩
    intro t
    apply Finset.single_le_sum (f := fun ρ => ‖G.lam v (ρ (z v))‖)
      (a := (G.T v).σa t) (fun ρ _ => norm_nonneg _)
    exact (G.T v).σa_finite.mem_toFinset.mpr ⟨t, rfl⟩
  choose c hc hbound using hbounds
  let a (v : FinPlace F) (δ : Fˣ ⧸ G.Δ) : ℂ :=
    G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (z v))
  refine whit_local_product_summable G.Alag E
    (fun v hv => G.alag_tame v (fun h => hv (hE (Fs.sub h))))
    (fun v _ => hfin v) a ?_ (2 * s.re) (by linarith) c
    (fun v _ => hc v) (fun δ v _ => hbound v (toLoc v (Quotient.out δ))) ?_
  · intro δ
    refine (E.finite_toSet.union
      (whit_finite_mulSupport P G μ Fs x (Quotient.out δ))).subset ?_
    intro v hv
    by_cases hvE : v ∈ E
    · exact Or.inl hvE
    · refine Or.inr ?_
      change G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (z v)) ≠ 1 at hv
      change G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) ≠ 1
      simpa only [hz v hvE] using hv
  · intro δ v hv
    have hvT : v ∉ Fs.T0 := fun h => hv (hE h)
    have hvS : v ∉ S.Sf := fun h => hvT (Fs.sub h)
    dsimp [a]
    rw [hz v hv]
    have hdec := (whit_ordv_geometry v).2.2.2.2 (toLoc v (Quotient.out δ))
    have hloc := whit_spherical_factor_norm_le (P.loc v) (P.tame v hvS)
      (G.T v) (G.B v hvS) A (μ v)
      (fun h => hvS (S.over6 v h)) (fun h => hvS (S.different_mem v h))
      s (Fs.f v) (Fs.f_sec v) (Fs.f_sph v hvT).1 (Fs.f_sph v hvT).2
      (G.lam v) (G.lam_tame v hvS)
      (ordv v (toLoc v (Quotient.out δ))) (unitPart v (toLoc v (Quotient.out δ)))
      hdec.1 (P.compF v x) (hcomp v hv)
    rw [← hdec.2] at hloc
    convert hloc using 1 <;> first | rfl | simp only [neg_mul]

/-- Absolute convergence of the unfolded series at any lift. -/
theorem whitLiftTerm_summable (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x : P.RP) :
    Summable (fun δ : Fˣ ⧸ G.Δ => ‖whitLiftTerm P G μ Fs x δ‖) := by
  let E := Fs.T0 ∪ (P.comp_restricted x).toFinset
  have hE : Fs.T0 ⊆ E := Finset.subset_union_left
  have hcomp (v : FinPlace F) (hv : v ∉ E) :
      P.compF v x ∈ (P.tame v (fun h => hv (hE (Fs.sub h)))).Kmax := by
    by_contra hk
    apply hv
    apply Finset.mem_union_right
    exact (P.comp_restricted x).mem_toFinset.mpr
      ⟨(fun h => hv (hE (Fs.sub h))), hk⟩
  have hsum := whit_jacquet_family_summable P G μ hs Fs x E hE hcomp
    (fun v => jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))
    (fun _ _ => rfl)
  simpa only [whitLiftTerm, norm_mul] using
    hsum.mul_right ‖∏ w, jacquetC (rtr (P.compC w x) (Fs.fC w))‖

/-- Central phases of a lift cancel in the local Jacquet product. -/
theorem whit_atLift (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x : P.RP) :
    whittakerE P G μ Fs (P.q x) = (κF F)⁻¹ * ∑' δ, whitLiftTerm P G μ Fs x δ := by
  classical
  let y := Function.surjInv P.q_surj (P.q x)
  have hq : P.q y = P.q x := Function.surjInv_eq P.q_surj (P.q x)
  obtain ⟨ζ, hζ, hprod, hF, hC⟩ := (P.q_eq y x).1 hq
  let ev : rootsOfUnity 3 ℂ →* ℂ :=
    { toFun := fun z => ((z : ℂˣ) : ℂ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hev : (Function.mulSupport fun v => ev (ζ v)).Finite := by
    refine hζ.subset ?_
    intro v hv
    contrapose! hv
    simp only [Function.mem_mulSupport, not_not] at hv ⊢
    rw [hv, ev.map_one]
  have hevprod : (∏ᶠ v, ev (ζ v)) = 1 := by
    rw [← ev.map_finprod hζ, hprod, ev.map_one]
  have hlocal (δ : Fˣ) (v : FinPlace F) :
      G.lam v ((G.T v).σa (toLoc v δ)
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v y) (Fs.f v)))) =
      ev (ζ v) * G.lam v ((G.T v).σa (toLoc v δ)
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) := by
    have htr : rtr ((P.loc v).z (ζ v) * P.compF v x) (Fs.f v) =
        rtr ((P.loc v).z (ζ v)) (rtr (P.compF v x) (Fs.f v)) := by
      funext h
      simp only [rtr, mul_assoc]
    rw [hF v, htr, (jacquet_equiv (P.loc v) (G.T v) A (μ v) s
      (rtr (P.compF v x) (Fs.f v)) ((Fs.f_sec v).rtr (P.compF v x))).2 (ζ v)]
    simp only [map_smul, smul_eq_mul]
    rfl
  unfold whittakerE
  apply congrArg (fun z : ℂ => (κF F)⁻¹ * z)
  apply tsum_congr
  intro δ
  change whitLiftTerm P G μ Fs y δ = whitLiftTerm P G μ Fs x δ
  unfold whitLiftTerm
  have hfinite :
      (∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v y) (Fs.f v))))) =
      ∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) := by
    simp_rw [hlocal]
    rw [finprod_mul_distrib hev (whit_finite_mulSupport P G μ Fs x (Quotient.out δ)),
      hevprod, one_mul]
  rw [hfinite]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  rw [hC w]

/-- The small cell vanishes and the big cell tiles the archimedean integral. -/
theorem whit_unfold_integral (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1)
    (x : P.RP) (hx : P.q x = P.tc.rat (diagGL ν) * g) :
    torusCoeff P (eisenstein P G Fs) g Pd (ν : F) =
      (κF F)⁻¹ * ∑' δ, whitLiftTerm P G μ Fs x δ := by
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
  obtain ⟨x, hx⟩ := P.q_surj (P.tc.rat (diagGL ν) * g)
  rw [← hx, whit_atLift P G μ hs Fs x]
  exact whit_unfold_integral P G μ hs Fs g 𝔞 h𝔞 hfix Pd hPd ν hν x hx

/-- Genuineness follows by inserting the center into one local component. -/
theorem whit_center (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (ζ : rootsOfUnity 3 ℂ) (g : P.tc.G) :
    whittakerE P G μ Fs (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * whittakerE P G μ Fs g := by
  sorry

theorem whit_unipotentS (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (u : S.FS) (g : P.tc.G) :
    whittakerE P G μ Fs (P.tc.nS (Multiplicative.ofAdd u) * g) =
      S.e A u * whittakerE P G μ Fs g := by
  sorry

theorem whit_unipotentExterior (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (v : FinPlace F) (hv : v ∉ S.Sf)
    (u : v.adicCompletion F) (g : P.tc.G) :
    whittakerE P G μ Fs (P.tc.n v (Multiplicative.ofAdd u) * g) =
      A.ψ v u * whittakerE P G μ Fs g := by
  sorry

theorem whit_rightInvariant (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (k : P.tc.G)
    (hk : ∀ h, scalarOf P G Fs.f Fs.fC (h * k) = scalarOf P G Fs.f Fs.fC h)
    (g : P.tc.G) : whittakerE P G μ Fs (g * k) = whittakerE P G μ Fs g := by
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
  exact ⟨whit_center P G μ hs Fs, whit_unipotentS P G μ hs Fs,
    whit_unipotentExterior P G μ hs Fs, whit_rightInvariant P G μ hs Fs⟩

/-- The exterior Jacquet product, which stays fixed as the S-part varies. -/
def whitExteriorTerm (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x0 : P.RP) (δ : Fˣ ⧸ G.Δ) : ℂ :=
  ∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, G.lam v.1 ((G.T v.1).σa
    (toLoc v.1 (Quotient.out δ))
    (jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x0) (Fs.f v.1))))

def whitTensorTerm (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x0 : P.RP) (z : ∀ v : S.Sf, (G.T v.1).V) (δ : Fˣ ⧸ G.Δ) : ℂ :=
  whitExteriorTerm P G μ Fs x0 δ *
    ∏ v : S.Sf, G.lam v.1 ((G.T v.1).σa (toLoc v.1 (Quotient.out δ)) (z v))

/-- Summability on basis tensors extends to every tensor in the finite dimensional S-part. -/
theorem whitTensorTerm_summable (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x0 : P.RP) (z : ∀ v : S.Sf, (G.T v.1).V) :
    Summable (fun δ : Fˣ ⧸ G.Δ => ‖whitTensorTerm P G μ Fs x0 z δ‖) := by
  let E := Fs.T0 ∪ (P.comp_restricted x0).toFinset
  have hE : Fs.T0 ⊆ E := Finset.subset_union_left
  have hcomp (v : FinPlace F) (hv : v ∉ E) :
      P.compF v x0 ∈ (P.tame v (fun h => hv (hE (Fs.sub h)))).Kmax := by
    by_contra hk
    apply hv
    apply Finset.mem_union_right
    exact (P.comp_restricted x0).mem_toFinset.mpr
      ⟨(fun h => hv (hE (Fs.sub h))), hk⟩
  let w (v : FinPlace F) : (G.T v).V :=
    if hv : v ∈ S.Sf then z ⟨v, hv⟩
    else jacquet (P.loc v) A (μ v) (rtr (P.compF v x0) (Fs.f v))
  have hw (v : FinPlace F) (hv : v ∉ E) : w v =
      jacquet (P.loc v) A (μ v) (rtr (P.compF v x0) (Fs.f v)) := by
    have hvS : v ∉ S.Sf := fun h => hv (hE (Fs.sub h))
    simp only [w, dif_neg hvS]
  have hsum := whit_jacquet_family_summable P G μ hs Fs x0 E hE hcomp w hw
  let a (δ : Fˣ ⧸ G.Δ) (v : FinPlace F) : ℂ :=
    G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (w v))
  have hfin (δ : Fˣ ⧸ G.Δ) : (Function.mulSupport (a δ)).Finite := by
    refine (S.Sf.finite_toSet.union
      (whit_finite_mulSupport P G μ Fs x0 (Quotient.out δ))).subset ?_
    intro v hv
    by_cases hvS : v ∈ S.Sf
    · exact Or.inl hvS
    · refine Or.inr ?_
      change G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (w v)) ≠ 1 at hv
      change G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x0) (Fs.f v)))) ≠ 1
      simpa only [w, dif_neg hvS] using hv
  have heq (δ : Fˣ ⧸ G.Δ) : (∏ᶠ v, a δ v) = whitTensorTerm P G μ Fs x0 z δ := by
    have hsplit := finprod_mem_union' (f := a δ)
      (show Disjoint (S.Sf : Set (FinPlace F)) (S.Sf : Set (FinPlace F))ᶜ
        from disjoint_compl_right)
      ((hfin δ).subset (fun _ hv => hv.2))
      ((hfin δ).subset (fun _ hv => hv.2))
    simp only [Set.union_compl_self, finprod_mem_univ] at hsplit
    rw [← finprod_set_coe_eq_finprod_mem (S.Sf : Set (FinPlace F)),
      ← finprod_set_coe_eq_finprod_mem (S.Sf : Set (FinPlace F))ᶜ] at hsplit
    change (∏ᶠ v, a δ v) = (∏ᶠ v : S.Sf, a δ v.1) *
      (∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, a δ v.1) at hsplit
    rw [finprod_eq_prod_of_fintype (fun v : S.Sf => a δ v.1)] at hsplit
    have hS : (∏ v : S.Sf, a δ v.1) =
        ∏ v : S.Sf, G.lam v.1 ((G.T v.1).σa (toLoc v.1 (Quotient.out δ)) (z v)) := by
      apply Finset.prod_congr rfl
      intro v _
      simp only [a, w, dif_pos v.property]
    have hExt : (∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, a δ v.1) =
        whitExteriorTerm P G μ Fs x0 δ := by
      unfold whitExteriorTerm
      apply finprod_congr
      intro v
      simp only [a, w, dif_neg v.property]
    rw [hS, hExt] at hsplit
    simpa only [whitTensorTerm, mul_comm] using hsplit
  change Summable (fun δ : Fˣ ⧸ G.Δ => ‖∏ᶠ v, a δ v‖) at hsum
  exact hsum.congr (fun δ => congrArg norm (heq δ))

/-- The summable delta-series defines a multilinear form by tsum_add and tsum_smul. -/
theorem whit_tensor_multilinear (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x0 : P.RP) :
    ∃ Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ,
      ∀ z, Λ z = (κF F)⁻¹ * ∑' δ, whitTensorTerm P G μ Fs x0 z δ := by
  let term (δ : Fˣ ⧸ G.Δ) :
      MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ :=
    whitExteriorTerm P G μ Fs x0 δ •
      (MultilinearMap.mkPiAlgebra ℂ S.Sf ℂ).compLinearMap
        (fun v => (G.lam v.1).comp
          ((G.T v.1).σa (toLoc v.1 (Quotient.out δ))))
  have hterm (δ : Fˣ ⧸ G.Δ) (z : ∀ v : S.Sf, (G.T v.1).V) :
      term δ z = whitTensorTerm P G μ Fs x0 z δ := by
    rfl
  have hsum (z : ∀ v : S.Sf, (G.T v.1).V) : Summable (fun δ => term δ z) := by
    simpa only [hterm] using (whitTensorTerm_summable P G μ hs Fs x0 z).of_norm
  let Λ0 : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ :=
    { toFun := fun z => ∑' δ, term δ z
      map_update_add' := by
        intro _ z v x y
        simp_rw [MultilinearMap.map_update_add]
        exact (hsum (Function.update z v x)).tsum_add (hsum (Function.update z v y))
      map_update_smul' := by
        intro _ z v c x
        simp_rw [MultilinearMap.map_update_smul]
        exact (hsum (Function.update z v x)).tsum_const_smul c }
  refine ⟨(κF F)⁻¹ • Λ0, ?_⟩
  intro z
  change (κF F)⁻¹ * (∑' δ, term δ z) =
    (κF F)⁻¹ * ∑' δ, whitTensorTerm P G μ Fs x0 z δ
  simp_rw [hterm]

/-- Separate the finite S-product and the fixed exterior product at a common lift. -/
theorem whit_tensor_formula (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x0 : P.RP) (Fs' : GlobalSection P G s) (x : P.RP)
    (hext : ∀ v, v ∉ S.Sf → Fs'.f v = Fs.f v) (hC : Fs'.fC = Fs.fC)
    (hx : ∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0) :
    whittakerE P G μ Fs' (P.q x) =
      ((κF F)⁻¹ * ∑' δ, whitTensorTerm P G μ Fs x0
        (fun v => jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x) (Fs'.f v.1))) δ) *
      ∏ w, jacquetC (rtr (P.compC w x) (Fs'.fC w)) := by
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
  obtain ⟨Λ, hΛ⟩ := whit_tensor_multilinear P G μ hs Fs x0
  refine ⟨Λ, ?_⟩
  intro Fs' x hext hC hx
  rw [hΛ]
  exact whit_tensor_formula P G μ hs Fs x0 Fs' x hext hC hx

end Eis

end ArtinPrimitiveRoots.A1.Theta
