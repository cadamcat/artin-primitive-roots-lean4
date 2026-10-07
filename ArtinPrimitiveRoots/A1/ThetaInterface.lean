import ArtinPrimitiveRoots.A1.Analytic

/-!
# A1 interface, §8: the cubic theta input, consumer form `th:theta-interface` (T1–T7)

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 8. The cubic theta input: consumer form `th:theta-interface` (T1–T7) -/

/-- A matrix helper: `diag(ν,1) ∈ GL₂(F)`. -/
def diagGL (ν : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ν : F), 0; 0, 1] (by simp [Matrix.det_fin_two])

/-- `n(x) ∈ GL₂(F)`. -/
def upperGL (x : F) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [Matrix.det_fin_two])

/-- `w ∈ GL₂(F)`. -/
def weylGL : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

/-- Scalar matrices. -/
def scalarGL (c : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(c : F), 0; 0, (c : F)]
    (by simp [Matrix.det_fin_two])

/-- The local residue symbol on a local unit, through a global approximant (02:237–244). -/
def localChi (D : FieldData F) (v : FinPlace F) (u : (v.adicCompletion F)ˣ) : ℂ :=
  if h : ∃ u0 : 𝓞 F, u0 ∉ v.asIdeal ∧
      Valued.v ((u : v.adicCompletion F) - algebraMap F _ (algebraMap (𝓞 F) F u0)) < 1
  then chi D v (algebraMap (𝓞 F) F h.choose) else 0

/-- Order of a local unit: `x = ϖ^{ord x}·(unit)`. -/
def ordv (v : FinPlace F) (x : (v.adicCompletion F)ˣ) : ℤ :=
  -Multiplicative.toAdd (WithZero.unzero (Valuation.ne_zero_iff _ |>.mpr x.ne_zero :
    Valued.v (x : v.adicCompletion F) ≠ 0))

/-- The unit part `x·ϖ_v^{-ord x}` for the fixed global uniformizer `unif v`. -/
def unitPart (v : FinPlace F) (x : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ :=
  x * (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ (-ordv v x)

/-- The exterior effective torus law `C_𝔭(ϖ^{e1}u, ϖ^{e2}u') = χ(u)^{2e2} χ(u')^{-2e1}` (04:395–399,
from eq:theta-effective-cocycle). -/
def extCocycle (D : FieldData F) (v : FinPlace F) (x y : (v.adicCompletion F)ˣ) : ℂ :=
  localChi D v (unitPart v x) ^ (2 * ordv v y) * localChi D v (unitPart v y) ^ (-(2 * ordv v x))

/-- `μ3(ℂ)` element from a value of `H_S²` (read through `σ0`). -/
def muThree (D : FieldData F) (ζ : rootsOfUnity 6 F) : rootsOfUnity 3 ℂ :=
  rootsOfUnity.mkOfPowEq (D.σ0 ((((ζ ^ 2 : rootsOfUnity 6 F) : Fˣ) : F))) (by
    have h6 : (((ζ : Fˣ) : F)) ^ 6 = 1 := by
      have := (mem_rootsOfUnity 6 (ζ : Fˣ)).mp ζ.2
      have := congrArg (fun u : Fˣ => (u : F)) this
      simpa using this
    rw [← map_pow]
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    rw [← pow_mul, show 2 * 3 = 6 by norm_num, h6, map_one])

/-- **T1: the cover API.** An abstract group `G` (the adelic cover of `PGL₂(𝔸_F)`), central `μ3`
identified with `μ3(ℂ)` through `ι = σ0⁻¹` (forced by eq:theta-effective-cocycle), the S-part
(`nS, aS, wS, nbarS`), exterior local elements (`n v, a v, w v, nbar v` for `v ∉ S`), the exterior
compact subgroup `Kext = Π_{v∉S} κ_v(PGL₂(O_v))`, and the rational splitting `rat`.
Every field used by A2's §4 (A2 blueprint T2 request) is a field here. C10 of `sol-gate-theta`
attaches the restricted-product quotient topology to the cover. -/
structure ThetaCover (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (A : AddCharData F) where
  G : Type
  [grp : Group G]
  /-- The topology induced by the restricted-product quotient in `CoverPackage`, as required by
  C10 of `sol-gate-theta`. -/
  topology : TopologicalSpace G
  topGroup : @IsTopologicalGroup G topology grp
  z : rootsOfUnity 3 ℂ →* G
  z_inj : Function.Injective z
  z_central : ∀ ζ g, z ζ * g = g * z ζ
  -- S-part
  GS : Subgroup G
  nS : Multiplicative S.FS →* G
  aS : S.FSˣ → G
  wS : G
  nbarS : Multiplicative S.FS →* G
  nS_mem : ∀ x, nS x ∈ GS
  aS_mem : ∀ y, aS y ∈ GS
  wS_mem : wS ∈ GS
  nbarS_mem : ∀ x, nbarS x ∈ GS
  /-- eq:reflection-S-cocycle: `a(x)a(y) = C_S(x,y) a(xy)`, `C_S = H_S²`. -/
  aS_mul : ∀ x y, aS x * aS y = z (muThree D (S.HS H x y)) * aS (x * y)
  /-- eq:theta-lift-identities at S. -/
  liftS_na : ∀ (x : S.FS) (y : S.FSˣ),
    nS (Multiplicative.ofAdd x) * aS y = aS y * nS (Multiplicative.ofAdd (x * ↑y⁻¹))
  liftS_wa : ∀ y, wS * aS y * wS⁻¹ = aS y⁻¹
  liftS_wn : ∀ H : S.FSˣ, wS * nS (Multiplicative.ofAdd (H : S.FS)) =
    nS (Multiplicative.ofAdd ((H⁻¹ : S.FSˣ) : S.FS)) * aS (-(H⁻¹ * H⁻¹)) *
      nbarS (Multiplicative.ofAdd ((H⁻¹ : S.FSˣ) : S.FS))
  -- exterior places
  Gloc : FinPlace F → Subgroup G
  n : (v : FinPlace F) → Multiplicative (v.adicCompletion F) →* G
  a : (v : FinPlace F) → (v.adicCompletion F)ˣ → G
  w : FinPlace F → G
  nbar : (v : FinPlace F) → Multiplicative (v.adicCompletion F) →* G
  n_mem : ∀ v x, n v x ∈ Gloc v
  a_mem : ∀ v y, a v y ∈ Gloc v
  w_mem : ∀ v, w v ∈ Gloc v
  nbar_mem : ∀ v x, nbar v x ∈ Gloc v
  /-- different places commute; exterior places commute with the S-part. -/
  comm_loc : ∀ v v', v ≠ v' → ∀ g ∈ Gloc v, ∀ h ∈ Gloc v', g * h = h * g
  comm_S : ∀ v, v ∉ S.Sf → ∀ g ∈ Gloc v, ∀ h ∈ GS, g * h = h * g
  /-- exterior effective torus law (04:395–399). -/
  a_mul : ∀ v, v ∉ S.Sf → ∀ x y, ∃ ζ : rootsOfUnity 3 ℂ,
    ((ζ : ℂˣ) : ℂ) = extCocycle D v x y ∧ a v x * a v y = z ζ * a v (x * y)
  lift_na : ∀ v (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ),
    n v (Multiplicative.ofAdd x) * a v y = a v y * n v (Multiplicative.ofAdd (x * ↑y⁻¹))
  lift_wa : ∀ v y, w v * a v y * (w v)⁻¹ = a v y⁻¹
  lift_wn : ∀ v (H : (v.adicCompletion F)ˣ), w v * n v (Multiplicative.ofAdd (H : v.adicCompletion F)) =
    n v (Multiplicative.ofAdd ((H⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *
      a v (-(H⁻¹ * H⁻¹)) * nbar v (Multiplicative.ofAdd ((H⁻¹ : (v.adicCompletion F)ˣ) : _))
  /-- exterior compact subgroup and its generators (KP Prop 0.1.3; 10:102–105, 245–248). -/
  Kext : Subgroup G
  Kext_comm_S : ∀ k ∈ Kext, ∀ h ∈ GS, k * h = h * k
  n_Kext : ∀ v, v ∉ S.Sf → ∀ x ∈ v.adicCompletionIntegers F, n v (Multiplicative.ofAdd x) ∈ Kext
  a_Kext : ∀ v, v ∉ S.Sf → ∀ u : (v.adicCompletion F)ˣ,
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F → a v u ∈ Kext
  w_Kext : ∀ v, v ∉ S.Sf → w v ∈ Kext
  nbar_Kext : ∀ v, v ∉ S.Sf → ∀ x : v.adicCompletion F, Valued.v x < 1 →
    nbar v (Multiplicative.ofAdd x) ∈ Kext
  -- rational splitting and its decomposition into S-part and exterior part
  rat : GL (Fin 2) F →* G
  rat_scalar : ∀ c : Fˣ, rat (scalarGL c) = 1
  aExt : Fˣ → G
  nExt : Multiplicative F →* G
  wExt : G
  rat_diag : ∀ ν : Fˣ, rat (diagGL ν) = aS (S.diagU ν) * aExt ν
  rat_upper : ∀ x : F, rat (upperGL x) = nS (Multiplicative.ofAdd (S.diag x)) * nExt (Multiplicative.ofAdd x)
  rat_weyl : rat weylGL = wS * wExt
  wExt_Kext : wExt ∈ Kext
  aExt_unit : ∀ γ ∈ S.US, aExt γ ∈ Kext
  /-- `aExt ν = Π_{v∈T} a_v(ν) · k` with `k ∈ Kext` commuting with the local groups at `T`. -/
  aExt_split : ∀ (ν : Fˣ) (T : Finset (FinPlace F)), (∀ v ∈ T, v ∉ S.Sf) →
    (∀ v : FinPlace F, v ∉ S.Sf → v ∉ T → residue v (ν : F) ≠ 0 ∧ residue v ((ν⁻¹ : Fˣ) : F) ≠ 0) →
    ∃ k ∈ Kext, (∀ v ∈ T, ∀ g ∈ Gloc v, k * g = g * k) ∧
      aExt ν = (T.toList.map fun v => a v (toLoc v ν)).prod * k
  nExt_split : ∀ (x : F) (T : Finset (FinPlace F)), (∀ v ∈ T, v ∉ S.Sf) →
    (∀ v : FinPlace F, v ∉ S.Sf → v ∉ T → HeightOneSpectrum.valuation F v x ≤ 1) →
    ∃ k ∈ Kext, (∀ v ∈ T, ∀ g ∈ Gloc v, k * g = g * k) ∧
      nExt (Multiplicative.ofAdd x) =
        (T.toList.map fun v => n v (Multiplicative.ofAdd (algebraMap F _ x))).prod * k
  wExt_split : ∀ (T : Finset (FinPlace F)), (∀ v ∈ T, v ∉ S.Sf) →
    ∃ k ∈ Kext, (∀ v ∈ T, ∀ g ∈ Gloc v, k * g = g * k) ∧ wExt = (T.toList.map w).prod * k

attribute [instance] ThetaCover.grp

/-- The archimedean unipotent orbit in a theta cover; C11 of `sol-gate-theta` uses it for joint
root-orbit regularity. -/
def ThetaCover.nInf {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {A : AddCharData F} (C : ThetaCover D S H A) (x : InfinitePlace F → ℂ) : C.G :=
  C.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x))

/-- An admissible S-character (03:441–447): continuous unitary character of `F_S^×`, trivial on
`U_S`, locally constant on the finite part, angular `ω_{m_w}` (`m_w = ±1`) at complex places. -/
structure SChar (S : SData F CE condη) where
  L : S.FSˣ →* ℂˣ
  cont : Continuous fun y => ((L y : ℂˣ) : ℂ)
  unitary : ∀ y, ‖((L y : ℂˣ) : ℂ)‖ = 1
  trivial_US : ∀ γ ∈ S.US, L (S.diagU γ) = 1
  m : InfinitePlace F → ℤ
  hm : ∀ w, m w = 1 ∨ m w = -1
  angular : ∀ w (y : ℂˣ), ((L (S.atComplex w y) : ℂˣ) : ℂ) = omegaAng (m w) y

/-- The exterior Gauss value `g_{2,𝔭} = q^{-1/2} Σ_{x mod 𝔭} χ_𝔭(x)² ψ_𝔭(x/ϖ)` (03:139–143),
for the fixed global uniformizer `unif v`. -/
def g2 (D : FieldData F) (A : AddCharData F) (v : FinPlace F) : ℂ :=
  ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v (algebraMap (𝓞 F) F x.out) 2 *
      A.ψ v (algebraMap F _ (algebraMap (𝓞 F) F x.out / unif v))

/-- eq:theta-local-values (03:147–157): the normalized spherical Whittaker table. -/
def sphericalTable (D : FieldData F) (A : AddCharData F) (v : FinPlace F) (e : ℤ)
    (u : (v.adicCompletion F)ˣ) : ℂ :=
  let q : ℝ := Ideal.absNorm v.asIdeal
  localChi D v u ^ (2 * e) *
    (if e < 0 then 0
     else if e % 3 = 0 then ((q ^ (-(e / 3 : ℤ) : ℝ) : ℝ) : ℂ)
     else if e % 3 = 1 then ((q ^ (-((e / 3 : ℤ) : ℝ) - 1 / 2) : ℝ) : ℂ) * g2 D A v
     else 0)

/-- **T2–T7** for a fixed finite family `𝓛` of admissible S-characters, on a fixed cover `C`.
Corrected per rev-theta with archimedean smoothness and locally uniform Fourier convergence; C10/C11
of `sol-gate-theta` fix the topology and add joint root smoothness. -/
structure ThetaFamily {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {A : AddCharData F} (C : ThetaCover D S H A) (𝓛 : Finset (SChar S)) where
  /-- The topology used to state compact-uniform convergence. -/
  topology : TopologicalSpace C.G
  /-- C10 of `sol-gate-theta`: use the restricted-product quotient topology fixed by the cover. -/
  topology_spec : topology = C.topology
  θ : SChar S → C.G → ℂ
  θN : SChar S → C.G → ℂ
  W : SChar S → C.G → ℂ
  WS : SChar S → C.G → ℂ
  Wv : FinPlace F → C.G → ℂ
  /-- T2: genuine, automorphic, right `Kext`-invariant, continuous in the S-torus variable. -/
  genuine : ∀ L ∈ 𝓛, ∀ ζ g, θ L (C.z ζ * g) = ((ζ : ℂˣ) : ℂ) * θ L g
  automorphic : ∀ L ∈ 𝓛, ∀ γ g, θ L (C.rat γ * g) = θ L g
  right_Kext : ∀ L ∈ 𝓛, ∀ g, ∀ k ∈ C.Kext, θ L (g * k) = θ L g
  cont : ∀ L ∈ 𝓛, ∀ g h, Continuous fun y : S.FSˣ => θ L (g * C.aS y * h)
  /-- Smoothness along each archimedean root subgroup. -/
  archSmooth : ∀ L ∈ 𝓛, ∀ (g : C.G) (w : InfinitePlace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => θ L (g * C.nS
        (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), Pi.single w z))))
  /-- Joint smoothness of both root variables, required by C11 of `sol-gate-theta` for mixed
  derivatives in `Rderiv`. -/
  jointRootSmooth : ∀ L ∈ 𝓛, ∀ g : C.G,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) =>
        θ L (C.nInf p.1 * g * C.nInf p.2))
  /-- T3: Fourier expansion along `N`, constant term, and its invariances. -/
  fourier : ∀ L ∈ 𝓛, ∀ g, Summable (fun ν : Fˣ => W L (C.rat (diagGL ν) * g)) ∧
    θ L g = θN L g + ∑' ν : Fˣ, W L (C.rat (diagGL ν) * g)
  /-- The Fourier expansion converges uniformly on compact sets in the chosen topology. -/
  fourierLocallyUniform : ∀ L ∈ 𝓛, ∀ K : Set C.G, @IsCompact C.G topology K →
    ∀ ε : ℝ, 0 < ε → ∃ F₀ : Finset Fˣ, ∀ F' : Finset Fˣ, F₀ ⊆ F' → ∀ g ∈ K,
      ‖θ L g - θN L g -
        ∑ ν ∈ F', W L (C.rat (diagGL ν) * g)‖ < ε
  θN_left : ∀ L ∈ 𝓛, ∀ (b : GL (Fin 2) F), (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
    ∀ g, θN L (C.rat b * g) = θN L g
  θN_right : ∀ L ∈ 𝓛, ∀ g, ∀ k ∈ C.Kext, θN L (g * k) = θN L g
  θN_genuine : ∀ L ∈ 𝓛, ∀ ζ g, θN L (C.z ζ * g) = ((ζ : ℂˣ) : ℂ) * θN L g
  cont_N : ∀ L ∈ 𝓛, ∀ g h, Continuous fun y : S.FSˣ => θN L (g * C.aS y * h)
  /-- T4: factorization of the Whittaker coefficient at a rational torus translate, with an
  optional rational Weyl element, an S-part `gS ∈ GS`, and local elements at finitely many
  exterior places. -/
  factor : ∀ L ∈ 𝓛, ∀ (ν : Fˣ) (ε : Bool) (gS : C.G), gS ∈ C.GS →
    ∀ (T : Finset (FinPlace F)), (∀ v ∈ T, v ∉ S.Sf) → ∀ (g : FinPlace F → C.G),
      (∀ v ∈ T, g v ∈ C.Gloc v) →
      W L (C.rat (diagGL ν) * (if ε then C.rat weylGL else 1) * gS * (T.toList.map g).prod) =
        WS L (C.aS (S.diagU ν) * (if ε then C.wS else 1) * gS) *
          (∏ v ∈ T, Wv v (C.a v (toLoc v ν) * (if ε then C.w v else 1) * g v)) *
          ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T), Wv v (C.a v (toLoc v ν))
  /-- exterior spherical Whittaker functions: equivariance, right invariance, table. -/
  Wv_genuine : ∀ v, v ∉ S.Sf → ∀ ζ g, Wv v (C.z ζ * g) = ((ζ : ℂˣ) : ℂ) * Wv v g
  Wv_equiv : ∀ v, v ∉ S.Sf → ∀ x g, Wv v (C.n v (Multiplicative.ofAdd x) * g) = A.ψ v x * Wv v g
  Wv_right : ∀ v, v ∉ S.Sf → ∀ g, ∀ k ∈ C.Kext, k ∈ C.Gloc v → Wv v (g * k) = Wv v g
  Wv_table : ∀ v, v ∉ S.Sf → ∀ (e : ℤ) (u : (v.adicCompletion F)ˣ),
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    Wv v (C.a v ((toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e * u)) =
      sphericalTable D A v e u
  WS_equiv : ∀ L ∈ 𝓛, ∀ x g, WS L (C.nS (Multiplicative.ofAdd x) * g) = S.e A x * WS L g
  /-- `WS` is genuine (added 2026-10-07, A2 alignment M-1: needed by `rf:forward-frequencies`,
  `rf:S-unfolding`). -/
  WS_genuine : ∀ L ∈ 𝓛, ∀ (ζ : rootsOfUnity 3 ℂ) (g : C.G), WS L (C.z ζ * g) = ((ζ : ℂˣ) : ℂ) * WS L g
  /-- T5: the chosen S-Whittaker function. -/
  U : Set (∀ v : S.Sf, v.1.adicCompletion F)
  U_spec : IsOpen U ∧ IsCompact U ∧ (1 ∈ U) ∧
    (∀ y ∈ U, ∀ v : S.Sf, y v ∈ v.1.adicCompletionIntegers F) ∧
    (∀ y ∈ U, ∀ v : S.Sf, Valued.v (y v) = 1) ∧
    (∀ y ∈ U, ∃ c : ∀ v : S.Sf, v.1.adicCompletion F, y = c ^ 6) ∧
    (∀ L ∈ 𝓛, ∀ y : S.FSˣ, y.1.1 ∈ U → (∀ w, y.1.2 w = 1) → L.L y = 1)
  cS : InfinitePlace F → ℝ
  cS_pos : ∀ w, 0 < cS w
  T5 : ∀ L ∈ 𝓛, ∀ y : S.FSˣ, WS L (C.aS y) =
    (if (y : S.FS).1 ∈ U then (1 : ℂ) else 0) *
      ∏ w : InfinitePlace F, ((Complex.normSq ((y : S.FS).2 w) : ℝ) : ℂ) *
        omegaAng (L.m w) ((y : S.FS).2 w) *
        (besselK (1 / 3) (cS w * ‖(y : S.FS).2 w‖) : ℂ)
  /-- T6: the Weyl-rotated S-function is a finite sum of products of local factors satisfying
  the hypotheses of lem:sheet-profile with one `δ > 0`. -/
  δ : ℝ
  δ_pos : 0 < δ
  T6 : ∀ L ∈ 𝓛, ∃ (J : ℕ) (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ),
    (∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)) ∧ (∀ ℓ w, SheetHypC δ (fc ℓ w)) ∧
    ∀ y : S.FSˣ, WS L (C.aS y * C.wS) =
      ∑ ℓ : Fin J, (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
        ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w)
  /-- T7: the constant term is radial at every complex place. -/
  T7 : ∀ L ∈ 𝓛, ∀ (w : InfinitePlace F) (zc : ℂˣ), ‖(zc : ℂ)‖ = 1 →
    ∀ g, θN L (C.aS (S.atComplex w zc) * g) = θN L g

end ArtinPrimitiveRoots.A1
