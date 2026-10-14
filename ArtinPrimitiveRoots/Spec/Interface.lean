import Mathlib

/-!
# P-SPEC interface

Spectral input of route C, narrowed to what
P-RES / P-REDUCTION / P-EIS / P-ASSEMBLE consume (cited below by node ID `spec:*`).

Scope (BP §1): for a totally complex number field `F`, a finite-index subgroup `Γ ≤ SL(2, 𝓞 F)` acting
freely on `X F = (ℍ³)^{places}`, any scaling matrix `σ ∈ SL(2,F)` and any real `0 < s₁ ≤ 1/2`, the
Eisenstein series `E_{Γ,σ}(s,z) = Σ_{γ ∈ Γ_σ\Γ} N(σ⁻¹γz)^{1+2s}` (normalized parameter: abscissa `1/2`,
theta point `s₁ = 1/6`) continues analytically to the connected domain `contDomain s₁ ε`
(a strip in the upper half-plane, the ball `B(5/2,1/2)` where the series converges, and a punctured
ball at `s₁`), has at most a simple pole at `s₁`, and its residue is smooth, `Γ`-invariant, square
integrable, an eigenfunction of every partial Laplacian; finite linear combinations of residues with
vanishing constant terms vanish. No character `χ` (consumers pass to the kernel of the multiplier),
no functional equation, no continuation beyond `Re s > 0`.

Conventions:
* `H3 := SL(2,ℂ) ⧸ SU(2)`; a point is `pt x y` (`x ∈ ℂ`, `y > 0`), `height (pt x y) = y`,
  `horiz (pt x y) = x`. Same carrier as OAI `CubicEisenstein.HyperbolicSpace`
  (OAI/NumberTheory/DirichletL/Eisenstein/HyperbolicSpace.lean:80, 97).
* `X F := InfinitePlace F → H3`; `SL(2,F)` acts through `w.embedding` at each place.
* `normHeight z = ∏_w height (z w)` (ordinary product; `= |y|_∞^{1/2}` in adelic normalization), so the
  seed `normHeight^{1+2s} = |y|_∞^{1/2+s}` and the sum Laplacian eigenvalue is `r(1-4s²)`.
* Every `sorry` below is a theorem owned by the node named in its docstring.
-/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

/-! ## 1. Hyperbolic 3-space `H3 = SL(2,ℂ)/SU(2)` (node `spec:h3-basics`) -/

/-- `SU(2)` inside `SL(2,ℂ)` (same carrier and proof as OAI `CubicEisenstein.compactSubgroup`,
HyperbolicSpace.lean:80). -/
def SU2 : Subgroup SL(2,ℂ) where
  carrier := {k | (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ}
  one_mem' := (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
  mul_mem' := by
    intro a b ha hb
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem ha hb
  inv_mem' := by
    intro k hk
    have hinv : (k⁻¹ : SL(2,ℂ)) * k = 1 := inv_mul_cancel k
    have hmat : ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg
          (fun a : SL(2,ℂ) => (a : Matrix (Fin 2) (Fin 2) ℂ)) hinv
    have he := Matrix.left_inv_eq_left_inv hmat (Matrix.mem_unitaryGroup_iff'.mp hk)
    change ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [he]
    exact Unitary.star_mem hk

/-- Hyperbolic 3-space. -/
abbrev H3 := SL(2,ℂ) ⧸ SU2

instance : MeasurableSpace H3 := borel H3
instance : BorelSpace H3 := ⟨rfl⟩

/-- The positive Hermitian matrix `g g*` of the point `gK` (well defined since `k k* = 1`). -/
def herm : H3 → Matrix (Fin 2) (Fin 2) ℂ :=
  Quotient.lift (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ))
    (by
      intro g h hgh
      have hk : ((g⁻¹ * h : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
        QuotientGroup.leftRel_apply.mp hgh
      have hh : (h : Matrix (Fin 2) (Fin 2) ℂ) =
          (g : Matrix (Fin 2) (Fin 2) ℂ) * ((g⁻¹ * h : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
      have hu := Matrix.mem_unitaryGroup_iff.mp hk
      change (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) =
        (h : Matrix (Fin 2) (Fin 2) ℂ) * star (h : Matrix (Fin 2) (Fin 2) ℂ)
      rw [hh, star_mul, mul_assoc, ← mul_assoc _ (star _) (star _), hu, one_mul])

/-- Height `y` of a point: `(g g*)₁₁ = |c|² + |d|² = 1/y` (OAI `hyperbolicHeight`, HyperbolicSpace.lean:149). -/
def height (z : H3) : ℝ := ((herm z 1 1).re)⁻¹

/-- Horizontal coordinate `x = (g g*)₀₁ / (g g*)₁₁ = (a c̄ + b d̄)/(|c|² + |d|²)`. -/
def horiz (z : H3) : ℂ := herm z 0 1 / herm z 1 1

/-- `n(x) a(y)` normalized in `SL(2,ℂ)`: `!![√y, x/√y; 0, 1/√y]`. -/
def ptMat (x : ℂ) (y : ℝ) (hy : 0 < y) : SL(2,ℂ) :=
  ⟨!![(Real.sqrt y : ℂ), x / (Real.sqrt y : ℂ); 0, 1 / (Real.sqrt y : ℂ)], by
    have h : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

/-- The point with horizontal coordinate `x` and height `y` (junk value `o` if `y ≤ 0`). -/
def pt (x : ℂ) (y : ℝ) : H3 :=
  if hy : 0 < y then (QuotientGroup.mk (ptMat x y hy) : H3) else (QuotientGroup.mk 1 : H3)

/-- Sanity check of the coordinates (owner `spec:h3-basics`). -/
theorem height_pt (x : ℂ) (y : ℝ) (hy : 0 < y) : height (pt x y) = y := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  simp only [height, pt, dite_eq_left, hy]
  change ((((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
    star ((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) 1 1).re⁻¹ = y
  simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  exact Real.mul_self_sqrt hy.le

/-- Sanity check of the coordinates (owner `spec:h3-basics`). -/
theorem horiz_pt (x : ℂ) (y : ℝ) (hy : 0 < y) : horiz (pt x y) = x := by
  have hs : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
  simp only [horiz, pt, dite_eq_left, hy]
  change (((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
    star ((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 /
    (((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
    star ((ptMat x y hy : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 = x
  simp [ptMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.conj_ofReal]
  field_simp


/-! ## 2. The product space and the action of `SL(2,F)` (node `spec:X-action`) -/

variable (F : Type) [Field F] [NumberField F]

/-- `(ℍ³)^r`, indexed by the (complex) infinite places. -/
abbrev X := InfinitePlace F → H3

/-- `SL(2,F) → Π_w SL(2,ℂ)` through the chosen embedding of each place. -/
def toInf : SL(2,F) →* (InfinitePlace F → SL(2,ℂ)) :=
  MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map w.embedding

/-- `SL(2, 𝓞 F) → SL(2, F)`. -/
def toSLF : SL(2, 𝓞 F) →* SL(2, F) := Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) F)

instance instMulActionSLF : MulAction (SL(2,F)) (X F) := MulAction.compHom (X F) (toInf F)

instance instMulActionSLO : MulAction (SL(2, 𝓞 F)) (X F) :=
  MulAction.compHom (X F) ((toInf F).comp (toSLF F))

/-- `N(z) = ∏_w y_w`. -/
def normHeight (z : X F) : ℝ := ∏ w, height (z w)

/-- Coordinates `(x_w, y_w)_w`. -/
abbrev Coord := InfinitePlace F → ℂ × ℝ

/-- The coordinate chart's inverse (junk outside `posSet`). -/
def ptX (p : Coord F) : X F := fun w => pt (p w).1 (p w).2

/-- The same with separate horizontal and height vectors. -/
def ptX' (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) : X F := fun w => pt (x w) (y w)

/-- Coordinates of a point. -/
def coordsX (z : X F) : Coord F := fun w => (horiz (z w), height (z w))

/-- The open set of admissible coordinates. -/
def posSet : Set (Coord F) := {p | ∀ w, 0 < (p w).2}

/-- Hyperbolic volume `∏_w y_w^{-3} dx_w dy_w` (node `spec:volume`; per factor OAI `hyperbolicVolume`,
HyperbolicVolume.lean:218, invariance :470). -/
def volX : Measure (X F) :=
  Measure.map (ptX F) ((volume.restrict (posSet F)).withDensity
    fun p => ENNReal.ofReal (∏ w, ((p w).2 ^ 3)⁻¹))

open scoped Classical in
/-- Partial (place-`w`) hyperbolic Laplacian `-y_w²(∂²_{x_w,1}+∂²_{x_w,2}+∂²_{y_w}) + y_w ∂_{y_w}`
in coordinates; `Δ_w y_w^a = a(2-a) y_w^a`. -/
def partialLap (w : InfinitePlace F) (f : X F → ℂ) (z : X F) : ℂ :=
  let p := coordsX F z
  let g : Coord F → ℂ := f ∘ ptX F
  let e1 : Coord F := Pi.single w ((1 : ℂ), (0 : ℝ))
  let e2 : Coord F := Pi.single w (Complex.I, (0 : ℝ))
  let e3 : Coord F := Pi.single w ((0 : ℂ), (1 : ℝ))
  ((p w).2 : ℂ) * fderiv ℝ g p e3 - ((p w).2 : ℂ) ^ 2 * (iteratedFDeriv ℝ 2 g p ![e1, e1] +
      iteratedFDeriv ℝ 2 g p ![e2, e2] + iteratedFDeriv ℝ 2 g p ![e3, e3])

/-! ## 3. Subgroups, cusps, the Eisenstein series (nodes `spec:cusp-*`, `spec:eis-*`) -/

/-- The upper triangular subgroup `B(F) ∩ SL(2,F)`. -/
def borelSL : Subgroup SL(2,F) where
  carrier := {g | g 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [ha]

/-- `n(b)`, as a homomorphism from `Multiplicative F`. -/
def upperHom : Multiplicative F →* SL(2,F) where
  toFun b := ⟨!![1, Multiplicative.toAdd b; 0, 1], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![1, Multiplicative.toAdd (a * b); 0, 1] =
      !![1, Multiplicative.toAdd a; 0, 1] * !![1, Multiplicative.toAdd b; 0, 1]
    rw [Matrix.mul_fin_two]
    simp [add_comm]

/-- The cusp stabilizer `Γ_σ = {γ ∈ Γ : σ⁻¹γσ upper triangular}`. -/
def cuspStab (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) : Subgroup Γ :=
  (borelSL F).comap ((MulAut.conj σ⁻¹).toMonoidHom.comp ((toSLF F).comp Γ.subtype))

/-- Right cosets `Γ_σ \ Γ`. -/
abbrev CuspCosets (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) :=
  Quotient (QuotientGroup.rightRel (cuspStab F Γ σ))

/-- The term `N(σ⁻¹ γ z)^{1+2s}` at a chosen representative (independent of it: `spec:eis-def`). -/
def eisTerm (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) (s : ℂ) (z : X F) (q : CuspCosets F Γ σ) : ℂ :=
  ((normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2, 𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * s)

/-- The Eisenstein series of `Γ` at the cusp `σ ∞`, normalized parameter (abscissa `Re s = 1/2`). -/
def eisSeries (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) (s : ℂ) (z : X F) : ℂ :=
  ∑' q : CuspCosets F Γ σ, eisTerm F Γ σ s z q

/-- `Γ` acts freely on `X F` (consumers intersect with `congrSubgroup N` of `exists_free_congr`). -/
def FreeAction (Γ : Subgroup SL(2, 𝓞 F)) : Prop :=
  ∀ γ ∈ Γ, ∀ z : X F, γ • z = z → γ = 1

/-- The principal congruence subgroup `Γ(N)`. -/
def congrSubgroup (N : Ideal (𝓞 F)) : Subgroup SL(2, 𝓞 F) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk N)).ker

/-- The translation lattice `{b ∈ F : σ n(b) σ⁻¹ ∈ Γ}` of the cusp `σ∞`. -/
def cuspLattice (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) : AddSubgroup F :=
  AddSubgroup.toSubgroup.symm ((Γ.map (toSLF F)).comap ((MulAut.conj σ).toMonoidHom.comp (upperHom F)))

/-- `F → ℂ^{places}`. -/
def infEmb : F →+* (InfinitePlace F → ℂ) := RingHom.pi fun w => w.embedding

/-- The cusp lattice inside `ℂ^{places}` (a full lattice: `spec:cusp-lattice`). -/
def cuspTranslations (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) : AddSubgroup (InfinitePlace F → ℂ) :=
  (cuspLattice F Γ σ).map (infEmb F).toAddMonoidHom

/-- The continuation domain: a strip in the upper half-plane, the convergence ball `B(5/2,1/2)` and
the punctured ball `B(s₁,ε) ∖ {s₁}` (open, preconnected: `spec:domain`). -/
def contDomain (s₁ ε : ℝ) : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 4 ∧ 0 < s.im ∧ s.im < 1} ∪ Metric.ball (5 / 2 : ℂ) (1 / 2) ∪
    (Metric.ball (s₁ : ℂ) ε \ {(s₁ : ℂ)})

variable [IsTotallyComplex F]

/-! ## 4. Statements (all `sorry`; owner node in the docstring) -/









/-- **The consumer object.** The continuation of `E_{Γ,σ}` to `contDomain s₁ ε` and its residue at
`s₁`, with the properties P-RES, P-REDUCTION and P-ASSEMBLE use (BP §1.3). `E` is unique
(`ContinuedEisenstein.E_eq`). -/
structure ContinuedEisenstein (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) (s₁ : ℝ) where
  ε : ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ s₁
  E : ℂ → X F → ℂ
  /-- agreement with the series where it converges absolutely -/
  E_series : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ z, E s z = eisSeries F Γ σ s z
  E_invariant : ∀ s ∈ contDomain s₁ ε, ∀ γ ∈ Γ, ∀ z, E s (γ • z) = E s z
  E_smooth : ∀ s ∈ contDomain s₁ ε, ContDiffOn ℝ ∞ (fun p => E s (ptX F p)) (posSet F)
  /-- analytic on the domain, with every coordinate derivative, locally uniformly in `z`
  (values in bounded continuous functions on a compact coordinate set `K`) -/
  E_analytic : ∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F → ∀ (n : ℕ) (v : Fin n → Coord F),
    ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ (contDomain s₁ ε) ∧
      ∀ s ∈ contDomain s₁ ε, ∀ p : K, Φ s p = iteratedFDeriv ℝ n (fun q => E s (ptX F q)) p v
  res : X F → ℂ
  /-- at most a simple pole at `s₁`, with residue `res`, with every coordinate derivative,
  locally uniformly in `z` -/
  laurent : ∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F → ∀ (n : ℕ) (v : Fin n → Coord F),
    ∃ Ψ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Ψ (Metric.ball (s₁ : ℂ) ε) ∧
      (∀ p : K, Ψ s₁ p = iteratedFDeriv ℝ n (fun q => res (ptX F q)) p v) ∧
      ∀ s ∈ Metric.ball (s₁ : ℂ) ε, s ≠ s₁ → ∀ p : K,
        Ψ s p = (s - s₁) * iteratedFDeriv ℝ n (fun q => E s (ptX F q)) p v
  res_smooth : ContDiffOn ℝ ∞ (fun p => res (ptX F p)) (posSet F)
  res_invariant : ∀ γ ∈ Γ, ∀ z, res (γ • z) = res z
  /-- eigenfunction of every partial Laplacian: `Δ_w res = (1+2s₁)(1-2s₁) res` -/
  res_eigen : ∀ w z, partialLap F w res z = (1 - 4 * (s₁ : ℂ) ^ 2) * res z
  /-- square integrable on `Γ\X` -/
  res_sq : ∀ D : Set (X F), IsFundamentalDomain Γ D (volX F) →
    IntegrableOn (fun z => ‖res z‖ ^ 2) D (volX F)



/-- `spec:api` (restriction to a smaller `ε`, e.g. a common `ε` for finitely many cusps). -/
theorem ContinuedEisenstein.exists_restrict {Γ : Subgroup SL(2, 𝓞 F)} {σ : SL(2,F)} {s₁ : ℝ}
    (d : ContinuedEisenstein F Γ σ s₁) (ε' : ℝ) (h0 : 0 < ε') (h : ε' ≤ d.ε) :
    ∃ d' : ContinuedEisenstein F Γ σ s₁, d'.ε = ε' ∧ d'.E = d.E ∧ d'.res = d.res := by
  have hdom : contDomain s₁ ε' ⊆ contDomain s₁ d.ε := by
    intro z hz
    simp only [contDomain, Set.mem_union] at hz ⊢
    have hball : ∀ z ∈ Metric.ball (s₁ : ℂ) ε', z ∈ Metric.ball (s₁ : ℂ) d.ε :=
      Metric.ball_subset_ball h
    aesop
  have hball : Metric.ball (s₁ : ℂ) ε' ⊆ Metric.ball (s₁ : ℂ) d.ε :=
    Metric.ball_subset_ball h
  refine ⟨{
    ε := ε'
    ε_pos := h0
    ε_le := h.trans d.ε_le
    E := d.E
    E_series := d.E_series
    E_invariant := ?_
    E_smooth := ?_
    E_analytic := ?_
    res := d.res
    laurent := ?_
    res_smooth := d.res_smooth
    res_invariant := d.res_invariant
    res_eigen := d.res_eigen
    res_sq := d.res_sq
  }, rfl, rfl, rfl⟩
  · exact fun s hs γ hγ z => d.E_invariant s (hdom hs) γ hγ z
  · exact fun s hs => d.E_smooth s (hdom hs)
  · intro K hK hKP n v
    obtain ⟨Φ, hΦ, hvalue⟩ := d.E_analytic K hK hKP n v
    refine ⟨Φ, hΦ.mono hdom, ?_⟩
    intro s hs p
    exact hvalue s (hdom hs) p
  · intro K hK hKP n v
    obtain ⟨Ψ, hΨ, hcenter, hvalue⟩ := d.laurent K hK hKP n v
    refine ⟨Ψ, hΨ.mono hball, hcenter, ?_⟩
    intro s hs hne p
    exact hvalue s (hball hs) hne p


end ArtinPrimitiveRoots.A1.Spec
