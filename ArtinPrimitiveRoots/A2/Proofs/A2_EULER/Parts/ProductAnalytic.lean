import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

private def e_e_partialProduct (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (η : HeckeChar F) (U : FrequencyData S D η) (u : U.U)
    (V : Finset (FinPlace F)) (p : Triple) : ℂ :=
  ∏ v ∈ V.attach, if hv : v.1 ∉ S.Sf then
    normalizedLocal R η U u v.1 hv (p 0) (p 1) (p 2) else 1

private lemma e_e_partialProduct_differentiableOn
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (η : HeckeChar F)
    (U : FrequencyData S D η) (u : U.U)
    (hlocal : ∀ u v hv, DifferentiableOn ℂ (fun p : Triple =>
      normalizedLocal R η U u v hv (p 0) (p 1) (p 2)) {p | eulerNeighborhood p})
    (V : Finset (FinPlace F)) :
    DifferentiableOn ℂ (e_e_partialProduct R η U u V) {p | eulerNeighborhood p} := by
  classical
  unfold e_e_partialProduct
  generalize V.attach = W
  induction W using Finset.induction_on with
  | empty => simpa using (differentiableOn_const (c := (1 : ℂ)))
  | @insert v W hv ih =>
    simp only [Finset.prod_insert hv]
    apply DifferentiableOn.mul ?_ ih
    by_cases h : v.1 ∉ S.Sf
    · simpa [h] using hlocal u v.1 h
    · simpa [h] using (differentiableOn_const (c := (1 : ℂ)))

private lemma e_e_eulerNeighborhood_isOpen :
    IsOpen {p : Triple | eulerNeighborhood p} := by
  have h0 : Continuous fun p : Triple => (p 0).re :=
    Complex.continuous_re.comp (continuous_apply 0)
  have h1 : Continuous fun p : Triple => (p 1).re :=
    Complex.continuous_re.comp (continuous_apply 1)
  have h2 : Continuous fun p : Triple => (p 2).re :=
    Complex.continuous_re.comp (continuous_apply 2)
  have hξ : IsOpen {p : Triple | (998 / 1000 - 1 / 100000 : ℝ) < (p 0).re} :=
    isOpen_lt continuous_const h0
  have hw₁ : IsOpen {p : Triple | (3 / 1000 - 1 / 100000 : ℝ) < (p 1).re} :=
    isOpen_lt continuous_const h1
  have hz₁ : IsOpen {p : Triple | (4 / 10 - 1 / 100000 : ℝ) < (p 2).re} :=
    isOpen_lt continuous_const h2
  have hw₂ : IsOpen {p : Triple | (95 / 100 - 1 / 100000 : ℝ) < (p 1).re} :=
    isOpen_lt continuous_const h1
  have hz₂ : IsOpen {p : Triple | (16 / 100 - 1 / 100000 : ℝ) < (p 2).re} :=
    isOpen_lt continuous_const h2
  unfold eulerNeighborhood
  simpa only [Set.ofPred_and, Set.ofPred_or, Set.inter_assoc] using
    ((hξ.inter hw₁).inter hz₁).union ((hξ.inter hw₂).inter hz₂)

private lemma e_e_partialProduct_deriv_cauchy_at
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (η : HeckeChar F)
    (U : FrequencyData S D η) (u : U.U) (HC : EulerCorrection R η U)
    (hcompact : ∀ u (K : Set Triple), IsCompact K → K ⊆ {p | eulerNeighborhood p} →
      ∀ ε : ℝ, 0 < ε → ∃ V : Finset (FinPlace F), ∀ V' : Finset (FinPlace F),
        V ⊆ V' → ∀ p ∈ K,
        ‖e_e_partialProduct R η U u V' p - HC.H u p‖ < ε)
    (hfinite : ∀ V, DifferentiableOn ℂ (e_e_partialProduct R η U u V)
      {p | eulerNeighborhood p})
    (x : Triple) (hx : eulerNeighborhood x) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ {p | eulerNeighborhood p} ∧ UniformCauchySeqOn
      (fun V p => fderiv ℂ (e_e_partialProduct R η U u V) p)
      atTop (Metric.ball x r) := by
  classical
  obtain ⟨R₀, hR₀, hball⟩ :=
    Metric.isOpen_iff.mp e_e_eulerNeighborhood_isOpen x hx
  let K : Set Triple := Metric.closedBall x (R₀ / 2)
  have hKcompact : IsCompact K := isCompact_closedBall x _
  have hKsub : K ⊆ {p | eulerNeighborhood p} := by
    intro z hz
    have hz' : dist x z ≤ R₀ / 2 := by
      simpa [K, dist_comm] using hz
    apply hball
    exact Metric.mem_ball.mpr (by rw [dist_comm]; linarith)
  refine ⟨R₀ / 4, by positivity, ?_, ?_⟩
  · intro y hy
    apply hball
    have hy' : dist x y < R₀ / 4 := by
      simpa [dist_comm] using Metric.mem_ball.mp hy
    exact Metric.mem_ball.mpr (by simpa [dist_comm] using lt_trans hy' (by linarith))
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let δ : ℝ := ε * (R₀ / 8) / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨W, hW⟩ := hcompact u K hKcompact hKsub δ hδ
  refine ⟨W, ?_⟩
  intro V hWV V' hWV' y hy
  have hy' : dist x y < R₀ / 4 := by
    simpa [dist_comm] using Metric.mem_ball.mp hy
  have hballSubK : Metric.ball y (R₀ / 8) ⊆ K := by
    intro z hz
    change dist z x ≤ R₀ / 2
    have hz' : dist y z < R₀ / 8 := by
      simpa [dist_comm] using Metric.mem_ball.mp hz
    apply le_of_lt
    calc
      dist z x = dist x z := dist_comm _ _
      _ ≤ dist x y + dist y z := dist_triangle _ _ _
      _ < R₀ / 4 + R₀ / 8 := add_lt_add hy' hz'
      _ < R₀ / 2 := by linarith
  have hballSub : Metric.ball y (R₀ / 8) ⊆ {p | eulerNeighborhood p} :=
    hballSubK.trans hKsub
  have hV : W ⊆ V := by simpa [Finset.le_iff_subset] using hWV
  have hV' : W ⊆ V' := by simpa [Finset.le_iff_subset] using hWV'
  let g : Triple → ℂ := fun z => e_e_partialProduct R η U u V z -
    e_e_partialProduct R η U u V' z
  have hgsmall : ∀ z ∈ K, ‖g z‖ < 2 * δ := by
    intro z hzK
    have hA := hW V hV z hzK
    have hB := hW V' hV' z hzK
    calc
      ‖g z‖ = ‖(e_e_partialProduct R η U u V z - HC.H u z) -
          (e_e_partialProduct R η U u V' z - HC.H u z)‖ := by
        simp only [g]; congr 1; ring
      _ ≤ ‖e_e_partialProduct R η U u V z - HC.H u z‖ +
          ‖e_e_partialProduct R η U u V' z - HC.H u z‖ := norm_sub_le _ _
      _ < δ + δ := add_lt_add hA hB
      _ = 2 * δ := by ring
  have hyK : y ∈ K := hballSubK (Metric.mem_ball_self (by positivity))
  have hmap : Set.MapsTo g (Metric.ball y (R₀ / 8)) (Metric.closedBall (g y) (4 * δ)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := hgsmall z (hballSubK hz)
    have h2 := hgsmall y hyK
    calc
      ‖g z - g y‖ ≤ ‖g z‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 4 * δ := by linarith
  have hdiffD : DifferentiableOn ℂ g (Metric.ball y (R₀ / 8)) :=
    (hfinite V).sub (hfinite V') |>.mono hballSub
  have hschwarz : ‖fderiv ℂ g y‖ ≤ (4 * δ) / (R₀ / 8) :=
    Complex.norm_fderiv_le_div_of_mapsTo_ball hdiffD hmap (by positivity)
  have hyΩ : eulerNeighborhood y := hballSub (Metric.mem_ball_self (by positivity))
  have hVy : DifferentiableAt ℂ (e_e_partialProduct R η U u V) y :=
    (hfinite V y hyΩ).differentiableAt
      (e_e_eulerNeighborhood_isOpen.mem_nhds hyΩ)
  have hV'y : DifferentiableAt ℂ (e_e_partialProduct R η U u V') y :=
    (hfinite V' y hyΩ).differentiableAt
      (e_e_eulerNeighborhood_isOpen.mem_nhds hyΩ)
  have hbound : dist (fderiv ℂ (e_e_partialProduct R η U u V) y)
      (fderiv ℂ (e_e_partialProduct R η U u V') y) ≤ (4 * δ) / (R₀ / 8) := by
    rw [dist_eq_norm, ← fderiv_fun_sub hVy hV'y]
    exact hschwarz
  have hratio : (4 * δ) / (R₀ / 8) < ε := by
    have hpos : 0 < R₀ / 8 := by positivity
    have : (4 * δ) / (R₀ / 8) = ε / 2 := by
      dsimp [δ]; field_simp; ring
    rw [this]; linarith
  exact lt_of_le_of_lt hbound hratio

theorem product_analytic (HC : EulerCorrection R η U)
    (hlocal : ∀ u v hv, DifferentiableOn ℂ (fun p : Triple =>
      normalizedLocal R η U u v hv (p 0) (p 1) (p 2)) {p | eulerNeighborhood p})
    (hcompact : ∀ u (K : Set Triple), IsCompact K → K ⊆ {p | eulerNeighborhood p} →
      ∀ ε : ℝ, 0 < ε → ∃ V : Finset (FinPlace F), ∀ V' : Finset (FinPlace F), V ⊆ V' →
        ∀ p ∈ K, ‖(∏ v ∈ V'.attach, if hv : v.1 ∉ S.Sf then
          normalizedLocal R η U u v.1 hv (p 0) (p 1) (p 2) else 1) - HC.H u p‖ < ε) :
    ∀ u, DifferentiableOn ℂ (HC.H u) {p | eulerNeighborhood p} := by
  classical
  intro u
  let f : Finset (FinPlace F) → Triple → ℂ := fun V p =>
    e_e_partialProduct R η U u V p
  let df : Finset (FinPlace F) → Triple → Triple →L[ℂ] ℂ := fun V p =>
    fderiv ℂ (f V) p
  let dfLim : Triple → Triple →L[ℂ] ℂ := fun p => lim (Filter.map (fun V => df V p) atTop)
  have hfinite : ∀ V, DifferentiableOn ℂ (f V) {p | eulerNeighborhood p} := by
    intro V
    simpa [f] using e_e_partialProduct_differentiableOn R η U u hlocal V
  have hconvK : ∀ K, K ⊆ {p | eulerNeighborhood p} → IsCompact K →
      TendstoUniformlyOn f (HC.H u) atTop K := by
    intro K hK hKcompact
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨V, hV⟩ := hcompact u K hKcompact hK ε hε
    refine Filter.eventually_atTop.2 ⟨V, ?_⟩
    intro V' hVV' p hp
    have hsubset : V ⊆ V' := by simpa [Finset.le_iff_subset] using hVV'
    have happrox := hV V' hsubset p hp
    simpa [dist_eq_norm, norm_sub_rev, f, e_e_partialProduct] using happrox
  have hΩopen : IsOpen {p : Triple | eulerNeighborhood p} :=
    e_e_eulerNeighborhood_isOpen
  have hconv : TendstoLocallyUniformlyOn f (HC.H u) atTop
      {p | eulerNeighborhood p} :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩopen).2 hconvK
  have hderiv_cauchy : ∀ x, eulerNeighborhood x →
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ {p | eulerNeighborhood p} ∧
      UniformCauchySeqOn df atTop (Metric.ball x r) := by
    intro x hx
    simpa [df, f] using
      e_e_partialProduct_deriv_cauchy_at R η U u HC
        (by
          intro u' K hK hKsub ε hε
          simpa [e_e_partialProduct] using hcompact u' K hK hKsub ε hε)
        (fun V => by simpa [f] using hfinite V) x hx
  have hderiv_pointwise : ∀ x, eulerNeighborhood x →
      Tendsto (fun V => df V x) atTop (𝓝 (dfLim x)) := by
    intro x hx
    obtain ⟨r, hr, _, hC⟩ := hderiv_cauchy x hx
    have hCx := hC.cauchy_map (Metric.mem_ball_self hr)
    change Filter.map (fun V => df V x) atTop ≤ 𝓝 (dfLim x)
    exact hCx.le_nhds_lim
  have hderiv_uniform : ∀ x, eulerNeighborhood x →
      TendstoUniformlyOnFilter df dfLim atTop (𝓝 x) := by
    intro x hx
    obtain ⟨r, hr, hball, hC⟩ := hderiv_cauchy x hx
    have hCf : UniformCauchySeqOnFilter df atTop (𝓝 x) :=
      hC.uniformCauchySeqOnFilter.mono_right
        (Filter.le_principal_iff.mpr (Metric.ball_mem_nhds x hr))
    have hpt : ∀ᶠ y in 𝓝 x, Tendsto (fun V => df V y) atTop (𝓝 (dfLim y)) := by
      filter_upwards [Metric.ball_mem_nhds x hr] with y hy
      exact hderiv_pointwise y (hball hy)
    exact hCf.tendstoUniformlyOnFilter_of_tendsto hpt
  have hderiv_local : TendstoLocallyUniformlyOn df dfLim atTop
      {p | eulerNeighborhood p} :=
    (tendstoLocallyUniformlyOn_iff_filter).2 fun x hx =>
      (hderiv_uniform x hx).mono_right nhdsWithin_le_nhds
  have hfd : ∀ x, eulerNeighborhood x → HasFDerivAt (HC.H u) (dfLim x) x := by
    intro x hx
    exact hasFDerivAt_of_tendstoLocallyUniformlyOn hΩopen hderiv_local
      (fun V z hz => ((hfinite V z hz).differentiableAt (hΩopen.mem_nhds hz)).hasFDerivAt)
      (fun z hz => hconv.tendsto_at hz) hx
  intro x hx
  exact (hfd x hx).differentiableAt.differentiableWithinAt

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
