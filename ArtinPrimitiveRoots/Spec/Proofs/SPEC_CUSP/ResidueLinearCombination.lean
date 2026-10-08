import ArtinPrimitiveRoots.Spec.Proofs.SPEC_API.Existence
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_API.Uniqueness
import ArtinPrimitiveRoots.Spec.ReductionExtra
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.GroundState

/-! Common spectral data for the C3 residue argument. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField Matrix MeasureTheory
open ArtinPrimitiveRoots.A1.Spec
open Classical
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.spec_domcusp_sol

private theorem secondCountableX_C3 {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] : SecondCountableTopology (X F) := by
  rcases (G1_h3_basics (F := F)) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, _⟩⟩
  exact e.symm.secondCountableTopology

private theorem secondCountableH3_C3 (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] : SecondCountableTopology H3 := by
  letI : SecondCountableTopology (X F) := secondCountableX_C3 (F := F)
  let w₀ : InfinitePlace F := Classical.choice inferInstance
  let c : H3 → X F := fun z _ => z
  let eval : X F → H3 := fun z => z w₀
  have hc : Continuous c := by
    change Continuous (fun z : H3 => fun _ : InfinitePlace F => z)
    apply continuous_pi
    intro w
    exact continuous_id
  have heval : Continuous eval := continuous_apply w₀
  have hleft : Function.LeftInverse eval c := by
    intro z
    simp [eval, c]
  exact hleft.isEmbedding heval hc |>.secondCountableTopology

private theorem borelSpaceX_C3 {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] : BorelSpace (X F) := by
  letI : SecondCountableTopology H3 := secondCountableH3_C3 F
  letI : BorelSpace H3 := ⟨rfl⟩
  letI : Countable (InfinitePlace F) := Finite.to_countable
  change BorelSpace (∀ w : InfinitePlace F, H3)
  exact Pi.borelSpace

private theorem continuousH3Action_C3 (g : SL(2,ℂ)) :
    Continuous (fun z : H3 => g • z) := by
  have hmul : Continuous (fun h : SL(2,ℂ) => g * h) := by
    apply Continuous.subtype_mk
    change Continuous (fun h : SL(2,ℂ) =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ))
    exact continuous_const.mul continuous_subtype_val
  apply (QuotientGroup.isQuotientMap_mk SU2).continuous_iff.mpr
  exact continuous_quotient_mk'.comp hmul

private theorem continuousSL2FAction_C3 {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,F)) :
    Continuous (fun z : X F => g • z) := by
  apply continuous_pi
  intro w
  exact (continuousH3Action_C3 (toInf F g w)).comp (continuous_apply w)

private theorem c3_normHeight_action_smooth {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,F)) :
    ContDiffOn ℝ ∞ (fun p => normHeight F (g • ptX F p)) (posSet F) := by
  let den : InfinitePlace F → Coord F → ℝ := fun w p =>
    Complex.normSq (w.embedding (g 1 0) * (p w).1 + w.embedding (g 1 1)) +
      Complex.normSq (w.embedding (g 1 0)) * (p w).2 ^ 2
  have hden_smooth (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun p => den w p) (posSet F) := by
    let f : Coord F → ℂ := fun p =>
      w.embedding (g 1 0) * (p w).1 + w.embedding (g 1 1)
    have hf : ContDiffOn ℝ ∞ f (posSet F) := by
      dsimp [f]
      fun_prop
    have hre : ContDiffOn ℝ ∞ (fun p => (f p).re) (posSet F) := by
      have h := Complex.reCLM.contDiff.comp_contDiffOn hf
      convert h using 1 <;> ext p <;> rfl
    have him : ContDiffOn ℝ ∞ (fun p => (f p).im) (posSet F) := by
      have h := Complex.imCLM.contDiff.comp_contDiffOn hf
      convert h using 1 <;> ext p <;> rfl
    have hnorm : ContDiffOn ℝ ∞ (fun p => Complex.normSq (f p)) (posSet F) := by
      simpa [Complex.normSq_apply, pow_two] using (hre.mul hre).add (him.mul him)
    have hc : ContDiffOn ℝ ∞ (fun _ : Coord F => Complex.normSq (w.embedding (g 1 0)))
        (posSet F) := contDiffOn_const
    have hy : ContDiffOn ℝ ∞ (fun p : Coord F => (p w).2) (posSet F) := by fun_prop
    have hsecond : ContDiffOn ℝ ∞
        (fun p => Complex.normSq (w.embedding (g 1 0)) * (p w).2 ^ 2) (posSet F) := by
      simpa [pow_two] using hc.mul (hy.mul hy)
    simpa [den, f, Complex.normSq_apply] using hnorm.add hsecond
  have hden_pos (w : InfinitePlace F) (p : Coord F) (hp : p ∈ posSet F) :
      0 < den w p := by
    have hy : 0 < (p w).2 := hp w
    have hheight : 0 < height ((g • ptX F p) w) := by
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos ((g • ptX F p) w)
    have hformula := height_smul_ptX'_at g (fun v => (p v).1) (fun v => (p v).2)
      (fun v => hp v) w
    have heq : height ((g • ptX F p) w) = (p w).2 / den w p := by
      change height ((g • ptX' F (fun v => (p v).1) (fun v => (p v).2)) w) = _
      simpa [den] using hformula
    rw [heq] at hheight
    exact (div_pos_iff_of_pos_left hy).mp hheight
  let quot : InfinitePlace F → Coord F → ℝ := fun w p => (p w).2 / den w p
  have hquot (w : InfinitePlace F) :
      ContDiffOn ℝ ∞ (fun p => quot w p) (posSet F) := by
    dsimp [quot]
    apply ContDiffOn.div
    · fun_prop
    · exact hden_smooth w
    · intro p hp
      exact (hden_pos w p hp).ne'
  have hprod : ContDiffOn ℝ ∞ (fun p => ∏ w : InfinitePlace F, quot w p) (posSet F) := by
    simpa using (contDiffOn_prod (t := (Finset.univ : Finset (InfinitePlace F)))
      (fun w hw => hquot w))
  apply hprod.congr
  intro p hp
  have hformula := (G2_x_action (F := F)).1 g (fun w => (p w).1) (fun w => (p w).2)
    (fun w => hp w)
  change normHeight F (g • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = _
  simpa [quot, den] using hformula

private theorem c3_chartEquiv {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] :
    ∃ e : {p : Coord F // p ∈ posSet F} ≃ₜ X F,
      (∀ p, e p = ptX F p.1) ∧ (∀ z, (e.symm z).1 = coordsX F z) := by
  rcases G1_h3_basics (F := F) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hcoords⟩
  exact hcoords

private theorem c3_posSet_open {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem c3_locallyCompactX {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] : LocallyCompactSpace (X F) := by
  classical
  obtain ⟨e, _, _⟩ := c3_chartEquiv (F := F)
  letI : LocallyCompactSpace {p : Coord F // p ∈ posSet F} :=
    (c3_posSet_open (F := F)).locallyCompactSpace
  exact e.symm.isOpenEmbedding.locallyCompactSpace

private def c3_cosetHeight {F : Type} [Field F] [NumberField F]
    {Γ : Subgroup SL(2,𝓞 F)} {σ : SL(2,F)}
    (q : CuspCosets F Γ σ) (z : X F) : ℝ :=
  normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))

private theorem c3_normHeight_action_continuous {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,F)) :
    Continuous (fun z : X F => normHeight F (g • z)) := by
  obtain ⟨e, he, hecoords⟩ := c3_chartEquiv (F := F)
  have hp : Continuous (fun z : X F => (e.symm z).1) :=
    continuous_subtype_val.comp e.symm.continuous
  have hmaps : ∀ z, (e.symm z).1 ∈ posSet F := fun z => (e.symm z).property
  have hcont : Continuous
      (fun z : X F => normHeight F (g • ptX F (e.symm z).1)) :=
    (c3_normHeight_action_smooth (F := F) g).continuousOn.comp_continuous hp hmaps
  have heq : (fun z : X F => normHeight F (g • z)) =
      (fun z : X F => normHeight F (g • ptX F (e.symm z).1)) := by
    funext z
    have hz : ptX F ((e.symm z).1) = z := by
      calc
        _ = e (e.symm z) := (he (e.symm z)).symm
        _ = z := e.apply_symm_apply z
    exact (congrArg (fun x => normHeight F (g • x)) hz).symm
  rw [heq]
  exact hcont

private theorem c3_cosetHeight_continuous {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] {Γ : Subgroup SL(2,𝓞 F)} {σ : SL(2,F)}
    (q : CuspCosets F Γ σ) : Continuous (c3_cosetHeight q) := by
  let g : SL(2,F) := σ⁻¹ * toSLF F (q.out : Γ)
  have hcont := c3_normHeight_action_continuous (F := F) g
  have heq : c3_cosetHeight q = fun z => normHeight F (g • z) := by
    funext z
    change normHeight F (σ⁻¹ • (toSLF F (q.out : Γ) • z)) =
      normHeight F (g • z)
    simp [g, mul_smul]
  rw [heq]
  exact hcont

private theorem c3_largeHeightCosets_finite {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (K : Set (X F)) (hK : IsCompact K)
    (A₀ : ℝ) (hA₀ : 1 ≤ A₀) :
    {q : CuspCosets F Γ σ | ∃ z ∈ K, A₀ < c3_cosetHeight q z}.Finite := by
  classical
  obtain ⟨m, hm, hbound⟩ := (E2_eis_converge Γ σ).1 K hK 1 1 (by norm_num)
  have hsmall : ∀ᶠ q : CuspCosets F Γ σ in Filter.cofinite, ‖m q‖ < 1 := by
    have h := hm.tendsto_cofinite_zero.eventually
      (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    simpa [Metric.mem_ball, dist_eq_norm] using h
  have hexception : {q : CuspCosets F Γ σ | ¬ ‖m q‖ < 1}.Finite := by
    simpa only [Filter.eventually_cofinite] using hsmall
  apply hexception.subset
  intro q hq
  simp only [Set.mem_setOf_eq] at hq ⊢
  obtain ⟨z, hzK, hz⟩ := hq
  have hheight : 1 < c3_cosetHeight q z := lt_of_le_of_lt hA₀ hz
  have hterm : 1 ≤ ‖eisTerm F Γ σ (1 : ℂ) z q‖ := by
    have hp : 0 < c3_cosetHeight q z := by linarith
    have htermEq : eisTerm F Γ σ (1 : ℂ) z q =
        ((c3_cosetHeight q z : ℝ) : ℂ) ^ (3 : ℂ) := by
      change ((c3_cosetHeight q z : ℝ) : ℂ) ^
        (1 + 2 * (1 : ℂ)) = ((c3_cosetHeight q z : ℝ) : ℂ) ^ (3 : ℂ)
      congr 1
      norm_num
    rw [htermEq]
    have hpow : (((c3_cosetHeight q z : ℝ) : ℂ) ^ (3 : ℂ)) =
        ((c3_cosetHeight q z : ℝ) : ℂ) ^ 3 := by simp
    rw [hpow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hp.le]
    nlinarith [sq_nonneg (c3_cosetHeight q z - 1)]
  have hmge : 1 ≤ m q := by
    have := hbound z hzK (1 : ℂ) (by norm_num) (by norm_num) q
    exact hterm.trans this
  have : 1 ≤ ‖m q‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hmge)]
    exact hmge
  exact not_lt_of_ge this

private theorem c3_partialLap_zero_of_open_zero
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (w : InfinitePlace F) (f : X F → ℂ) (U : Set (X F)) (hU : IsOpen U)
    {z : X F} (hz : z ∈ U) (hzero : ∀ x ∈ U, f x = 0) :
    partialLap F w f z = 0 := by
  classical
  obtain ⟨e, hept, hecoords⟩ := c3_chartEquiv (F := F)
  let Pos := {p : Coord F // p ∈ posSet F}
  let V : Set Pos := e ⁻¹' U
  have hV : IsOpen V := hU.preimage e.continuous
  let W : Set (Coord F) := Subtype.val '' V
  have hW : IsOpen W := (c3_posSet_open (F := F)).isOpenMap_subtype_val V hV
  let p : Coord F := coordsX F z
  have hpPos : p ∈ posSet F := by
    dsimp [p]
    rw [← hecoords z]
    exact (e.symm z).property
  have hpcoord : (e.symm z).1 = p := hecoords z
  have hpW : p ∈ W := ⟨e.symm z, by simpa [V] using hz, hpcoord⟩
  have hptU : ∀ q ∈ W, ptX F q ∈ U := by
    intro q hq
    rcases hq with ⟨q', hq', hqq'⟩
    change e q' ∈ U at hq'
    rw [← hqq', ← hept q']
    exact hq'
  have hcoordZero (q : Coord F) (hq : q ∈ W) : f (ptX F q) = 0 :=
    hzero (ptX F q) (hptU q hq)
  have hcoordLocal (q : Coord F) (hq : q ∈ W) :
      (fun r : Coord F => f (ptX F r)) =ᶠ[𝓝 q] 0 := by
    filter_upwards [hW.mem_nhds hq] with r hr
    exact hcoordZero r hr
  have hderivLocal (q : Coord F) (hq : q ∈ W) :
      fderiv ℝ (fun r : Coord F => f (ptX F r)) q = 0 := by
    rw [(hcoordLocal q hq).fderiv_eq]
    simp
  have hfirst : fderiv ℝ (f ∘ ptX F) p = 0 := by
    simpa [Function.comp_def, p] using hderivLocal p hpW
  have hderivEventually : (fun q : Coord F =>
      fderiv ℝ (fun r : Coord F => f (ptX F r)) q) =ᶠ[𝓝 p] 0 := by
    filter_upwards [hW.mem_nhds hpW] with q hq
    exact hderivLocal q hq
  have hsecond : fderiv ℝ (fderiv ℝ (fun q : Coord F => f (ptX F q))) p = 0 := by
    rw [hderivEventually.fderiv_eq]
    simp
  let e1 : Coord F := Pi.single w ((1 : ℂ), (0 : ℝ))
  let e2 : Coord F := Pi.single w (Complex.I, (0 : ℝ))
  let e3 : Coord F := Pi.single w ((0 : ℂ), (1 : ℝ))
  have hsecondEval (a b : Coord F) :
      iteratedFDeriv ℝ 2 (fun q : Coord F => f (ptX F q)) p ![a, b] = 0 := by
    rw [iteratedFDeriv_two_apply, hsecond]
    simp
  change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (f ∘ ptX F) (coordsX F z) e3 -
        ((coordsX F z w).2 : ℂ) ^ 2 *
          (iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e1, e1] +
            iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e2, e2] +
            iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e3, e3]) = 0
  rw [hfirst]
  have hs1 : iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e1, e1] = 0 := by
    simpa [Function.comp_def, p] using hsecondEval e1 e1
  have hs2 : iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e2, e2] = 0 := by
    simpa [Function.comp_def, p] using hsecondEval e2 e2
  have hs3 : iteratedFDeriv ℝ 2 (f ∘ ptX F) (coordsX F z) ![e3, e3] = 0 := by
    simpa [Function.comp_def, p] using hsecondEval e3 e3
  rw [hs1, hs2, hs3]
  simp

private theorem c3_partialLap_congr_open
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (w : InfinitePlace F) (f g : X F → ℂ) (U : Set (X F)) (hU : IsOpen U)
    {z : X F} (hz : z ∈ U) (heq : ∀ x ∈ U, f x = g x) :
    partialLap F w f z = partialLap F w g z := by
  classical
  obtain ⟨e, hept, hecoords⟩ := c3_chartEquiv (F := F)
  let Pos := {p : Coord F // p ∈ posSet F}
  let V : Set Pos := e ⁻¹' U
  have hV : IsOpen V := hU.preimage e.continuous
  let W : Set (Coord F) := Subtype.val '' V
  have hW : IsOpen W := (c3_posSet_open (F := F)).isOpenMap_subtype_val V hV
  let p : Coord F := coordsX F z
  have hpPos : p ∈ posSet F := by
    dsimp [p]
    rw [← hecoords z]
    exact (e.symm z).property
  have hpW : p ∈ W := ⟨e.symm z, by simpa [V] using hz, hecoords z⟩
  have hpt : ptX F p = z := by
    have hpcoord : (e.symm z).1 = p := hecoords z
    calc
      ptX F p = ptX F (e.symm z).1 := by rw [hpcoord]
      _ = e (e.symm z) := (hept (e.symm z)).symm
      _ = z := e.apply_symm_apply z
  have hcoordsPt : coordsX F (ptX F p) = p := by
    rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, hcoords, _, _, _, _, _⟩
    exact hcoords p hpPos
  have hptU : ∀ q ∈ W, ptX F q ∈ U := by
    intro q hq
    rcases hq with ⟨q', hq', hqq'⟩
    change e q' ∈ U at hq'
    rw [← hqq', ← hept q']
    exact hq'
  have hEq : (fun q : Coord F => f (ptX F q)) =ᶠ[𝓝 p]
      (fun q => g (ptX F q)) := by
    filter_upwards [hW.mem_nhds hpW] with q hq
    exact heq (ptX F q) (hptU q hq)
  have hfirst := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq
  have hsecond := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 2).self_of_nhds
  rw [← hpt]
  dsimp [partialLap]
  simp only [Function.comp_def]
  rw [hcoordsPt]
  rw [hfirst, hsecond]

private theorem c3_eisSeedDefect_zero_of_notTail
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA₀A : A₀ < A)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) (s : ℂ) (z : X F)
    (hz : z ∉ cuspTail F Γ σ A₀) :
    eisSeedDefect F Γ σ τ s z = 0 := by
  classical
  letI : LocallyCompactSpace (X F) := c3_locallyCompactX (F := F)
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds z
  obtain ⟨U, hUK, hU, hzU⟩ := mem_nhds_iff.mp hKmem
  have hlarge := c3_largeHeightCosets_finite Γ σ K hK A₀ hA₀
  let S : Set (CuspCosets F Γ σ) :=
    {q | ∃ z' ∈ K, A₀ < c3_cosetHeight q z'}
  have hS : S.Finite := by simpa [S] using hlarge
  letI : Fintype S := hS.fintype
  let V : Set (X F) := ⋂ q : S, {z' | c3_cosetHeight q.1 z' < A}
  have hVopen : IsOpen V := by
    apply isOpen_iInter_of_finite
    intro q
    exact isOpen_lt (c3_cosetHeight_continuous q.1) continuous_const
  have hzK : z ∈ K := hUK hzU
  have hlowAtZ (q : CuspCosets F Γ σ) : c3_cosetHeight q z ≤ A₀ := by
    by_contra h
    have hlt : A₀ < c3_cosetHeight q z := lt_of_not_ge h
    exact hz ⟨q.out, hlt⟩
  have hzV : z ∈ V := by
    simp only [V, Set.mem_iInter]
    intro q
    exact (hlowAtZ q.1).trans_lt hA₀A
  let W : Set (X F) := U ∩ V
  have hW : IsOpen W := hU.inter hVopen
  have hzW : z ∈ W := ⟨hzU, hzV⟩
  have hheight_lt (z' : X F) (hz' : z' ∈ W) (q : CuspCosets F Γ σ) :
      c3_cosetHeight q z' < A := by
    by_cases hq : q ∈ S
    · have hqV : z' ∈ V := hz'.2
      exact (Set.mem_iInter.mp hqV) ⟨q, hq⟩
    · have hqK : z' ∈ K := hUK hz'.1
      have hle : c3_cosetHeight q z' ≤ A₀ := by
        by_contra h
        have hlt : A₀ < c3_cosetHeight q z' := lt_of_not_ge h
        exact hq ⟨z', hqK, hlt⟩
      exact hle.trans_lt hA₀A
  have hseedZero (z' : X F) (hz' : z' ∈ W) : eisSeed F Γ σ τ s z' = 0 := by
    have hterm (q : CuspCosets F Γ σ) : seedTerm F Γ σ τ s z' q = 0 := by
      have htau : τ (c3_cosetHeight q z') = 0 :=
        hτ.2.2.1 _ (le_of_lt (hheight_lt z' hz' q))
      have htau' : τ
          (normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z'))) = 0 := by
        simpa [c3_cosetHeight] using htau
      simp [seedTerm, htau']
    simp [eisSeed, hterm]
  have hlapZero (z' : X F) (hz' : z' ∈ W) : totalLap F (eisSeed F Γ σ τ s) z' = 0 := by
    rw [totalLap]
    apply Finset.sum_eq_zero
    intro w hw
    exact c3_partialLap_zero_of_open_zero w (eisSeed F Γ σ τ s) W hW hz' hseedZero
  rw [eisSeedDefect, hlapZero z hzW, hseedZero z hzW]
  simp

private theorem c3_partialLap_invariant
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (f : X F → ℂ)
    (hfInv : IsGammaInvariant F Γ f) (hf : IsSmoothX F f)
    (γ : Γ) (w : InfinitePlace F) (z : X F) :
    partialLap F w f ((γ : SL(2,𝓞 F)) • z) = partialLap F w f z := by
  let gAct : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F (γ : SL(2,𝓞 F)))
  have hact (x : X F) : actAtPlaces F gAct x = (γ : SL(2,𝓞 F)) • x := rfl
  have hcomp : (fun x => f (actAtPlaces F gAct x)) = f := by
    funext x
    rw [hact]
    exact hfInv γ γ.property x
  have hzeroSmooth : IsSmoothX F (fun _ : X F => (0 : ℂ)) := by
    change ContDiffOn ℝ ∞ (fun _ : Coord F => (0 : ℂ)) (posSet F)
    fun_prop
  have hzeroCompact : HasCompactSupportX F (fun _ : X F => (0 : ℂ)) := by
    refine ⟨∅, isCompact_empty, ?_⟩
    simp
  have hcomm := (G5_green_x f (fun _ : X F => (0 : ℂ)) hf hzeroSmooth hzeroCompact).2.2
    gAct f hf w z
  calc
    partialLap F w f ((γ : SL(2,𝓞 F)) • z) =
        partialLap F w f (actAtPlaces F gAct z) := by rw [hact]
    _ = partialLap F w (fun x => f (actAtPlaces F gAct x)) z := hcomm.symm
    _ = partialLap F w f z := by rw [hcomp]

private theorem c3_eisSeedDefect_invariant
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (s : ℂ) (τ : ℝ → ℝ)
    (hseed : IsSmoothX F (eisSeed F Γ σ τ s) ∧
      IsGammaInvariant F Γ (eisSeed F Γ σ τ s)) :
    IsGammaInvariant F Γ (eisSeedDefect F Γ σ τ s) := by
  intro γ hγ z
  have hLap : totalLap F (eisSeed F Γ σ τ s)
        ((γ : SL(2,𝓞 F)) • z) =
      totalLap F (eisSeed F Γ σ τ s) z := by
    unfold totalLap
    apply Finset.sum_congr rfl
    intro w hw
    exact c3_partialLap_invariant Γ _ hseed.2 hseed.1 ⟨γ, hγ⟩ w z
  simp only [eisSeedDefect]
  rw [hLap, hseed.2 γ hγ z]

private theorem ae_eq_of_invariant_on_fundamentalDomain_C3
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F))
    (f g : X F → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ z, f ((γ : SL(2,𝓞 F)) • z) = f z)
    (hg : ∀ γ ∈ Γ, ∀ z, g ((γ : SL(2,𝓞 F)) • z) = g z)
    (hfg : ∀ᵐ z ∂(volX F), z ∈ D → f z = g z) :
    ∀ᵐ z ∂(volX F), f z = g z := by
  have hRow : Countable (Fin 2 → 𝓞 F) := by
    have hset : (Set.univ : Set (Fin 2 → 𝓞 F)).Countable := by
      have h := Set.countable_univ_pi (π := fun _ : Fin 2 => 𝓞 F)
        (s := fun _ => Set.univ) (by intro i; exact Set.countable_univ)
      simpa using h
    letI : Countable (↥(Set.univ : Set (Fin 2 → 𝓞 F))) := hset.to_subtype
    exact Countable.of_equiv _ (Equiv.Set.univ _)
  have hMatrix : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    letI : Countable (Fin 2 → 𝓞 F) := hRow
    have hset : (Set.univ : Set (Matrix (Fin 2) (Fin 2) (𝓞 F))).Countable := by
      have h := Set.countable_univ_pi (π := fun _ : Fin 2 => (Fin 2 → 𝓞 F))
        (s := fun _ => Set.univ) (by intro i; exact Set.countable_univ)
      simpa [Matrix] using h
    letI : Countable (↥(Set.univ : Set (Matrix (Fin 2) (Fin 2) (𝓞 F)))) :=
      hset.to_subtype
    exact Countable.of_equiv _ (Equiv.Set.univ _)
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := hMatrix
  letI : Countable (SL(2,𝓞 F)) := Subtype.val_injective.countable
  letI : Countable Γ := Subtype.val_injective.countable
  letI : BorelSpace (X F) := borelSpaceX_C3 (F := F)
  have hmp (γ : Γ) : MeasurePreserving
      (fun z : X F => (γ : SL(2,𝓞 F)) • z) (volX F) (volX F) := by
    have hfun : (fun z : X F => (γ : SL(2,𝓞 F)) • z) =
        (fun z : X F => toSLF F (γ : SL(2,𝓞 F)) • z) := by
      funext z
      rfl
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact (continuousSL2FAction_C3 (toSLF F (γ : SL(2,𝓞 F)))).measurable
    · rw [hfun]
      exact (G3_volume (F := F)).1 (toInf F (toSLF F (γ : SL(2,𝓞 F))))
  have htrans : ∀ᵐ z ∂(volX F),
      ∀ γ : Γ, (γ : SL(2,𝓞 F)) • z ∈ D →
        f ((γ : SL(2,𝓞 F)) • z) = g ((γ : SL(2,𝓞 F)) • z) := by
    apply ae_all_iff.2
    intro γ
    exact (hmp γ).quasiMeasurePreserving.tendsto_ae hfg
  filter_upwards [hD.ae_covers, htrans] with z hzcover hztrans
  obtain ⟨γ, hγ⟩ := hzcover
  calc
    f z = f ((γ : SL(2,𝓞 F)) • z) := (hf γ γ.property z).symm
    _ = g ((γ : SL(2,𝓞 F)) • z) := hztrans γ hγ
    _ = g z := hg γ γ.property z


structure C3SpectralSetup (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (s₁ : ℝ) where
  siegel : SiegelData F Γ
  D : Set (X F)
  hD : IsFundamentalDomain Γ D (volX F)
  E : FAEnergySpace (L2Space F D) (GradientL2Space F D)
  context : EnergyContext F Γ D E
  gap : SpectralGapData E s₁
  lam : ℝ
  hLam : lam = placeCount F * (1 - 4 * s₁ ^ 2)
  hlam_nonneg : 0 ≤ lam
  N : Submodule ℂ E.V
  hN : N = (E.A (lam : ℂ)).toLinearMap.ker
  P : E.V →L[ℂ] E.V
  hP : P.range = N ∧ P.comp P = P ∧ IsSelfAdjoint P
  hPnorm : ∀ G₀ : L2Space F D,
    (‖E.M (P (E.M.adjoint G₀))‖ ^ 2 : ℂ) =
      (((lam + 1)⁻¹ : ℝ) : ℂ) *
        inner ℂ G₀ (E.M (P (E.M.adjoint G₀)))
  κ : ℝ
  hκ : κ = (lam + 1) / (8 * placeCount F * s₁)

theorem c3_spectral_setup {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (hfree : FreeAction F Γ)
    (s₁ : ℝ) (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2) :
    Nonempty (C3SpectralSetup F Γ s₁) := by
  classical
  obtain ⟨d_siegel⟩ := exists_siegelData Γ hfree
  let D := fundamentalDomainCandidate F Γ (SiegelData.unionSet F d_siegel)
  have hD : IsFundamentalDomain Γ D (volX F) := (R12_fund_domain Γ hfree d_siegel).2.1
  obtain ⟨A₁, hA₁_ge, hsep_d⟩ := (R10_cusp_separation Γ).2.1 d_siegel
  let A := max A₁ (1 + 1 / (8 * s₁ ^ 2))
  have hA : 0 < A := by
    have hA₁pos : 0 < A₁ := lt_of_lt_of_le one_pos hA₁_ge
    dsimp [A]
    positivity
  have hA₁_le_A : A₁ ≤ A := le_max_left _ _
  have hA_ge_one : 1 ≤ A := hA₁_ge.trans hA₁_le_A
  have hA_threshold : 1 / (8 * s₁ ^ 2) < A := by
    have hlt : 1 / (8 * s₁ ^ 2) < 1 + 1 / (8 * s₁ ^ 2) := by linarith
    exact hlt.trans_le (le_max_right _ _)
  obtain ⟨k₀, hkSmooth, hkNonneg, hkSupport, hkNonzero⟩ := radialKernel_bump
  obtain ⟨toL2, gradL2, hmass_rep, hgradient_rep, _⟩ := (T2_tests Γ D hD).2
  obtain ⟨E, e, _, _, _⟩ :=
    T4_energy_space Γ D hD toL2 gradL2 hmass_rep hgradient_rep
  let A₀d : d_siegel.ι → ℝ := fun _ => A₁
  have hA₀d : ∀ i, 0 < A₀d i := by
    intro i
    dsimp [A₀d]
    exact lt_of_lt_of_le one_pos hA₁_ge
  have hA₀dsep : ∀ i j : d_siegel.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A₀d i ≤ normHeight F ((d_siegel.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀d j ≤ normHeight F ((d_siegel.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d_siegel.σ i) := by
    intro i j γ γ' z hi hj
    exact hsep_d A₁ le_rfl i j γ γ' z hi hj
  have hA₀d_le_A : ∀ i, A₀d i ≤ A := by
    intro i
    dsimp [A₀d]
    exact hA₁_le_A
  obtain ⟨K, hK, C₀, hC₀, R, hRcompact, hRestimate, _⟩ :=
    T7_ground_state Γ D hD d_siegel A₀d hA₀d hA₀dsep E e A hA₀d_le_A
  let a : ℝ := placeCount F * (1 - 1 / (2 * A))
  have ha : 0 < a := by
    dsimp [a]
    have hplace : 0 < placeCount F := by
      unfold placeCount
      positivity
    have hAhalf : 1 / (2 * A) < 1 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * A)).2
      nlinarith [hA_ge_one]
    exact mul_pos hplace (by linarith)
  let c : ℝ := a⁻¹
  let C : ℝ := C₀ / a
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; exact div_nonneg hC₀ ha.le
  have hestimate : ∀ x : E.V,
      ‖E.M x‖ ^ 2 ≤ c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := by
    intro x
    have heq : c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 =
        (‖E.Gr x‖ ^ 2 + C₀ * ‖R x‖ ^ 2) / a := by
      dsimp [c, C]
      field_simp [ha.ne']
    calc
      ‖E.M x‖ ^ 2 ≤
          (‖E.Gr x‖ ^ 2 + C₀ * ‖R x‖ ^ 2) / a :=
        (le_div_iff₀ ha).2 (by simpa [a, mul_comm] using hRestimate x)
      _ = c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := heq.symm
  have hbelow : placeCount F * (1 - 4 * s₁ ^ 2) < 1 / c := by
    have hproduct : 1 < 8 * s₁ ^ 2 * A := by
      have := (div_lt_iff₀ (by positivity : 0 < 8 * s₁ ^ 2)).mp hA_threshold
      nlinarith
    have hratio : 1 / (2 * A) < 4 * s₁ ^ 2 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * A)).2
      nlinarith
    have hplace : 0 < placeCount F := by
      unfold placeCount
      positivity
    have hcoef : 1 - 4 * s₁ ^ 2 < 1 - 1 / (2 * A) := by linarith
    have hlt : placeCount F * (1 - 4 * s₁ ^ 2) < a := by
      dsimp [a]
      exact mul_lt_mul_of_pos_left hcoef hplace
    have hcinv : 1 / c = a := by dsimp [c]; field_simp
    rw [hcinv]
    exact hlt
  let gap : SpectralGapData E s₁ := {
    K := R
    compact := hRcompact
    c := c
    C := C
    c_pos := hc
    C_nonneg := hC
    estimate := hestimate
    below := hbelow }
  let lam : ℝ := placeCount F * (1 - 4 * s₁ ^ 2)
  have hLam : lam = placeCount F * (1 - 4 * s₁ ^ 2) := rfl
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    have hplace : 0 ≤ placeCount F := by
      unfold placeCount
      positivity
    have hsquare : s₁ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [h₀, h₁]
    nlinarith
  let N : Submodule ℂ E.V := (E.A (lam : ℂ)).toLinearMap.ker
  obtain ⟨P, hPproj, hPrange, hPself, hPnorm⟩ :=
    (F2_resolvent E R hRcompact c C hc hC hestimate).2.2.2.2.2.2
      lam hlam_nonneg hbelow
  let κ : ℝ := (lam + 1) / (8 * placeCount F * s₁)
  have hκ : κ = (lam + 1) / (8 * placeCount F * s₁) := rfl
  exact ⟨{
    siegel := d_siegel
    D := D
    hD := hD
    E := E
    context := e
    gap := gap
    lam := lam
    hLam := hLam
    hlam_nonneg := hlam_nonneg
    N := N
    hN := rfl
    P := P
    hP := ⟨hPrange, hPproj, hPself⟩
    hPnorm := hPnorm
    κ := κ
    hκ := hκ }⟩

set_option maxHeartbeats 2000000 in
theorem c3_projected_continuation
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (s₁ : ℝ) (setup : C3SpectralSetup F Γ s₁)
    (hfree : FreeAction F Γ) (σ : SL(2,F))
    (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2)
    (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA₀A : A₀ ≤ A)
    (hsep₀ : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (k₀ τ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkNonneg : ∀ t, 0 ≤ k₀ t)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (hkNonzero : ∃ t, k₀ t ≠ 0) (hτ : IsCuspCutoff A τ)
    (G : ℂ → L2Space F setup.D) (hG : AnalyticOnNhd ℂ G Set.univ)
    (hsource : ∀ s, ∀ᵐ z ∂(volX F), z ∈ setup.D →
      G s z = eisSeedDefect F Γ σ τ s z)
    (hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s) ∧
      IsGammaInvariant F Γ (eisSeed F Γ σ τ s) ∧
      ∀ z, totalLap F (eisSeed F Γ σ τ s) z -
        spectralParameter F s * eisSeed F Γ σ τ s z =
          eisSeedDefect F Γ σ τ s z) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ s₁ ∧
      ∃ d : ContinuedEisenstein F Γ σ s₁,
        d.res = (fun z => (radialTransform F k₀ (1 + 2 * s₁))⁻¹ *
          smoothingOperator F k₀ (l2Lift F Γ setup.D
            (-setup.κ • (setup.E.M.comp (setup.P.comp setup.E.M.adjoint))
              (G (s₁ : ℂ)))) z) ∧
        d.res =ᵐ[volX F] l2Lift F Γ setup.D
          (-setup.κ • (setup.E.M.comp (setup.P.comp setup.E.M.adjoint))
            (G (s₁ : ℂ))) := by
  classical
  let D := setup.D
  let E := setup.E
  let e := setup.context
  let N := setup.N
  let P := setup.P
  let κ := setup.κ
  let lam := setup.lam
  have hA : 0 < A := by linarith
  have hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ := by
    intro γ γ' z hγ hγ'
    exact hsep₀ γ γ' z (hA₀A.trans hγ) (hA₀A.trans hγ')
  let cut : CutoffData F Γ σ τ := {
    A₀ := A₀
    A := A
    A₀_ge := hA₀
    A_ge := hA₀A
    separation := hsep₀
    cutoff := hτ }
  have hP : P.range = N ∧ P.comp P = P ∧ IsSelfAdjoint P ∧
      N = (E.A (lam : ℂ)).toLinearMap.ker := by
    exact ⟨setup.hP.1, setup.hP.2.1, setup.hP.2.2, setup.hN⟩
  obtain ⟨ε, hεpos, hεle, hu, hres, hbaseE7⟩ :=
    E7_l2_cont Γ D setup.hD σ s₁ h₀ h₁ E e setup.gap G hG τ cut hsource
      lam setup.hLam P N hP κ setup.hκ
  let u : ℂ → L2Space F D := fun s =>
    faResolvent E (spectralParameter F s) (-G s)
  let θ : L2Space F D :=
    -κ • (E.M.comp (P.comp E.M.adjoint)) (G (s₁ : ℂ))
  have hbase : S3_unsmoothed_base Γ σ D τ u := by
    intro s hs
    let f : X F → ℂ := fun z => eisSeed F Γ σ τ s z + l2Lift F Γ D (u s) z
    let g : X F → ℂ := fun z => eisSeries F Γ σ s z
    have hf : ∀ γ ∈ Γ, ∀ z, f ((γ : SL(2,𝓞 F)) • z) = f z := by
      intro γ hγ z
      dsimp [f]
      rw [(hseed s).2.1 γ hγ z, ((T1_l2 Γ D setup.hD).1 (u s)).2 γ hγ z]
    have hsre : 1 / 2 < s.re := by
      have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := by
        simpa [Metric.mem_ball] using hs
      rw [dist_eq_norm] at hdist
      have hre : |(s - (5 / 2 : ℂ)).re| < 1 / 2 :=
        lt_of_le_of_lt (Complex.abs_re_le_norm _) hdist
      have hreal := (abs_lt.mp hre).1
      norm_num at hreal
      linarith
    have hg : ∀ γ ∈ Γ, ∀ z, g ((γ : SL(2,𝓞 F)) • z) = g z := by
      intro γ hγ z
      dsimp [g]
      exact (E2_eis_converge Γ σ).2.1 s hsre γ hγ z
    have hfgD : ∀ᵐ z ∂(volX F), z ∈ D → f z = g z :=
      Filter.Eventually.mono (hbaseE7 s hs) (fun z hz hzD => by
        dsimp [f, g]
        rw [hz hzD]
        ring)
    exact ae_eq_of_invariant_on_fundamentalDomain_C3 Γ D setup.hD f g hf hg hfgD
  have hS2 := S2_smoothing_seed Γ σ k₀ hkSmooth hkNonneg hkSupport hkNonzero
  have hnorm_contDomain : ∀ s ∈ contDomain s₁ ε, ‖s‖ ≤ 5 := by
    intro s hs
    simp only [contDomain, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hs
    rcases hs with (⟨hre, hrel, him, himl⟩ | hball) | ⟨hball, _⟩
    · have hsdecomp : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I :=
        (Complex.re_add_im s).symm
      rw [hsdecomp]
      calc
        ‖(s.re : ℂ) + (s.im : ℂ) * Complex.I‖ ≤
            ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |s.re| + |s.im| := by simp [Complex.norm_real]
        _ = s.re + s.im := by rw [abs_of_pos hre, abs_of_pos him]
        _ ≤ 5 := by linarith
    · have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := by
        simpa [Metric.mem_ball] using hball
      have htriangle : ‖s‖ ≤ ‖s - (5 / 2 : ℂ)‖ + ‖(5 / 2 : ℂ)‖ := by
        calc
          ‖s‖ = ‖(s - (5 / 2 : ℂ)) + (5 / 2 : ℂ)‖ := by congr 1 <;> ring
          _ ≤ _ := norm_add_le _ _
      rw [dist_eq_norm] at hdist
      have hcenter : ‖(5 / 2 : ℂ)‖ = 5 / 2 := by norm_num
      linarith [htriangle, hcenter]
    · have hdist : dist s (s₁ : ℂ) < ε := by
        simpa [Metric.mem_ball] using hball
      have htriangle : ‖s‖ ≤ ‖s - (s₁ : ℂ)‖ + ‖(s₁ : ℂ)‖ := by
        calc
          ‖s‖ = ‖(s - (s₁ : ℂ)) + (s₁ : ℂ)‖ := by congr 1 <;> ring
          _ ≤ _ := norm_add_le _ _
      rw [dist_eq_norm] at hdist
      have hcenter : ‖(s₁ : ℂ)‖ = s₁ := by
        rw [Complex.norm_real, Real.norm_of_nonneg h₀.le]
      linarith [htriangle, hcenter, hεle, h₁]
  have hnorm_center : ‖(s₁ : ℂ)‖ ≤ 5 := by
    rw [Complex.norm_real, Real.norm_of_nonneg h₀.le]
    linarith [h₁]
  have hhat : ∀ s ∈ contDomain s₁ ε,
      radialTransform F k₀ (1 + 2 * s) ≠ 0 := by
    intro s hs
    have hfactor : radialTransform₀ k₀ (1 + 2 * s) ≠ 0 := by
      have hp := hS2.2.2.1 s (hnorm_contDomain s hs)
      intro hz
      rw [hz] at hp
      simp at hp
    rw [radialTransform]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hfactor)
  have hhatCenter : radialTransform F k₀ (1 + 2 * (s₁ : ℂ)) ≠ 0 := by
    have hfactor : radialTransform₀ k₀ (1 + 2 * (s₁ : ℂ)) ≠ 0 := by
      have hp := hS2.2.2.1 (s₁ : ℂ) hnorm_center
      intro hz
      rw [hz] at hp
      simp at hp
    rw [radialTransform]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hfactor)
  have hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ z,
      smoothingOperator F k₀
        (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w) z =
      radialTransform F k₀ (1 + 2 * s) * eisSeries F Γ σ s z := by
    intro s hs z
    have hsre : 1 / 2 < s.re := by
      have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := by
        simpa [Metric.mem_ball] using hs
      rw [dist_eq_norm] at hdist
      have hre : |s.re - 5 / 2| ≤ ‖s - (5 / 2 : ℂ)‖ := by
        simpa using (Complex.abs_re_le_norm (s - (5 / 2 : ℂ)))
      have hreal := abs_lt.mp (lt_of_le_of_lt hre hdist)
      have : s.re > 2 := by linarith [hreal.1]
      linarith
    have hlocal : ∀ W : Set (X F), IsCompact W →
        ∀ᵐ w ∂(volX F), w ∈ W →
          eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w = eisSeries F Γ σ s w := by
      intro W hW
      exact Filter.Eventually.mono (hbase s hs) (fun w hw _ => hw)
    have hsmoothEq := smoothing_representative_independent k₀ hkSmooth hkSupport
      (fun w => eisSeed F Γ σ τ s w + l2Lift F Γ D (u s) w)
      (eisSeries F Γ σ s) hlocal z
    rw [hsmoothEq]
    exact hS2.2.2.2 s hsre z
  obtain ⟨d, _, _, hres_d, hidentity⟩ :=
    S3_continuation Γ hfree σ s₁ h₀ h₁ D setup.hD k₀ τ hkSmooth hkSupport
      A hA hsep hτ u θ ε ⟨hεpos, hεle⟩ hu hhat hhatCenter hres hbase hseries
  have hraw := ArtinPrimitiveRoots.Proofs.spec_cont_sol.s3_residue_ae_lift
    Γ D setup.hD σ τ A hA hsep hτ k₀ hkSmooth hkSupport u θ s₁ ε
      hεpos hhatCenter hres hidentity
  refine ⟨ε, hεpos, hεle, d, ?_, ?_⟩
  · exact hres_d
  · change d.res =ᵐ[volX F] l2Lift F Γ D θ
    rw [hres_d]
    exact hraw

def C3TailFormula {F : Type} [Field F] [NumberField F]
    {Γ : Subgroup SL(2,𝓞 F)} {σ : SL(2,F)} {A₀ : ℝ} (τ : ℝ → ℝ) : Prop :=
  ∀ s z, z ∈ cuspTail F Γ σ A₀ →
    ∃ γ : Γ,
      eisSeedDefect F Γ σ τ s z =
        -(placeCount F : ℂ) *
          (((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ 2 *
              deriv (deriv (fun t : ℝ => (τ t : ℂ)))
                (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ) +
            (1 + 4 * s) *
              ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) *
              deriv (fun t : ℝ => (τ t : ℂ))
                (normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) ) *
          ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^
            (1 + 2 * s)

private def c3CutoffRadialWeight (A : ℝ) (τ : ℝ → ℝ) (a : ℝ) (t : ℝ) : ℝ :=
  τ t * (max t (A / 2)) ^ a

private theorem c3CutoffRadialWeight_smooth {A : ℝ} (hA : 0 < A)
    {τ : ℝ → ℝ} (hτ : IsCuspCutoff A τ) (a : ℝ) :
    ContDiff ℝ ∞ (c3CutoffRadialWeight A τ a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t < A
  · have hloc : c3CutoffRadialWeight A τ a =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_Iio.mem_nhds ht)] with x hx
      simp [c3CutoffRadialWeight, hτ.2.2.1 x (le_of_lt hx)]
    exact contDiffAt_const.congr_of_eventuallyEq hloc
  · have htA : A ≤ t := le_of_not_gt ht
    have hhalf : A / 2 < t := by linarith
    have hloc : c3CutoffRadialWeight A τ a =ᶠ[𝓝 t]
        (fun x => τ x * x ^ a) := by
      filter_upwards [isOpen_Ioi.mem_nhds hhalf] with x hx
      have hx' : A / 2 < x := by simpa using hx
      simp [c3CutoffRadialWeight, max_eq_left (le_of_lt hx')]
    have hpow : ContDiffAt ℝ ∞ (fun x : ℝ => x ^ a) t :=
      Real.contDiffAt_rpow_const_of_ne (ne_of_gt (by linarith [hA, htA]))
    have hbase : ContDiffAt ℝ ∞ (fun x : ℝ => τ x * x ^ a) t :=
      hτ.1.contDiffAt.mul hpow
    exact hbase.congr_of_eventuallyEq hloc

private theorem c3CutoffRadialWeight_eq_raw {A : ℝ} (hA : 0 < A)
    {τ : ℝ → ℝ} (hτ : IsCuspCutoff A τ) (a t : ℝ) :
    c3CutoffRadialWeight A τ a t = τ t * t ^ a := by
  by_cases ht : t ≤ A
  · simp [c3CutoffRadialWeight, hτ.2.2.1 t ht]
  · have hhalf : A / 2 ≤ t := by linarith
    simp [c3CutoffRadialWeight, max_eq_left hhalf]

private theorem c3_rawCutoffPower_deriv {A : ℝ} {τ : ℝ → ℝ}
    (hτ : IsCuspCutoff A τ) {a t : ℝ} (ha : 1 ≤ a) :
    deriv (fun x => τ x * x ^ a) t =
      deriv τ t * t ^ a + τ t * (a * t ^ (a - 1)) := by
  have hτD : HasDerivAt τ (deriv τ t) t :=
    (hτ.1.differentiable (by norm_num) t).hasDerivAt
  have hpowD : HasDerivAt (fun x : ℝ => x ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (x := t) (p := a) (Or.inr ha)
  exact (hτD.mul hpowD).deriv

private theorem c3_rawCutoffPower_secondDeriv {A : ℝ} {τ : ℝ → ℝ}
    (hτ : IsCuspCutoff A τ) {a t : ℝ} (ha : 1 ≤ a) (ht : t ≠ 0) :
    deriv (deriv (fun x => τ x * x ^ a)) t =
      deriv (deriv τ) t * t ^ a +
        2 * a * deriv τ t * t ^ (a - 1) +
          τ t * (a * (a - 1) * t ^ (a - 2)) := by
  have hτD : HasDerivAt τ (deriv τ t) t :=
    (hτ.1.differentiable (by norm_num) t).hasDerivAt
  have hτsmooth' : ContDiff ℝ ∞ (deriv τ) := hτ.1.deriv'
  have hτ'D : HasDerivAt (deriv τ) (deriv (deriv τ) t) t :=
    (hτsmooth'.differentiable (by norm_num) t).hasDerivAt
  have hpowD : HasDerivAt (fun x : ℝ => x ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (x := t) (p := a) (Or.inr ha)
  have hpow'D : HasDerivAt (fun x : ℝ => x ^ (a - 1))
      ((a - 1) * t ^ (a - 2)) t :=
    by
      simpa only [show a - 1 - 1 = a - 2 by ring] using
        Real.hasDerivAt_rpow_const (x := t) (p := a - 1) (Or.inl ht)
  have hfirst : (deriv (fun x => τ x * x ^ a)) =
      (fun x => deriv τ x * x ^ a + τ x * (a * x ^ (a - 1)) ) := by
    funext x
    exact c3_rawCutoffPower_deriv hτ (a := a) (t := x) ha
  rw [hfirst]
  have hprod₁ := hτ'D.mul hpowD
  have hprod₂ := hτD.mul (hpow'D.const_mul a)
  have hsum := hprod₁.add hprod₂
  have h := hsum.deriv
  calc
    deriv (fun x => deriv τ x * x ^ a + τ x * (a * x ^ (a - 1))) t =
        (deriv (deriv τ) t * t ^ a + deriv τ t * (a * t ^ (a - 1))) +
          (deriv τ t * (a * t ^ (a - 1)) +
            τ t * (a * ((a - 1) * t ^ (a - 2)))) := h
    _ = _ := by ring

private theorem c3_cutoffRadialWeight_deriv_at {A : ℝ} (hA : 0 < A)
    {τ : ℝ → ℝ} (hτ : IsCuspCutoff A τ) {a t : ℝ}
    (ha : 1 ≤ a) (ht : A / 2 < t) :
    deriv (c3CutoffRadialWeight A τ a) t =
      deriv τ t * t ^ a + τ t * (a * t ^ (a - 1)) := by
  have hEq : c3CutoffRadialWeight A τ a =ᶠ[𝓝 t] (fun x => τ x * x ^ a) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    have hx' : A / 2 < x := by simpa using hx
    simp [c3CutoffRadialWeight, max_eq_left (le_of_lt hx')]
  rw [hEq.deriv_eq]
  exact c3_rawCutoffPower_deriv hτ (a := a) (t := t) ha

private theorem c3_cutoffRadialWeight_secondDeriv_at {A : ℝ} (hA : 0 < A)
    {τ : ℝ → ℝ} (hτ : IsCuspCutoff A τ) {a t : ℝ}
    (ha : 1 ≤ a) (ht : A / 2 < t) (ht0 : t ≠ 0) :
    deriv (deriv (c3CutoffRadialWeight A τ a)) t =
      deriv (deriv τ) t * t ^ a +
        2 * a * deriv τ t * t ^ (a - 1) +
          τ t * (a * (a - 1) * t ^ (a - 2)) := by
  have hlocal (x : ℝ) (hx : A / 2 < x) :
      c3CutoffRadialWeight A τ a =ᶠ[𝓝 x] (fun u => τ u * u ^ a) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
    have hu' : A / 2 < u := by simpa using hu
    simp [c3CutoffRadialWeight, max_eq_left (le_of_lt hu')]
  have hderivAt (x : ℝ) (hx : A / 2 < x) :
      deriv (c3CutoffRadialWeight A τ a) x =
        deriv (fun u => τ u * u ^ a) x := (hlocal x hx).deriv_eq
  have hderivEventually :
      (fun x => deriv (c3CutoffRadialWeight A τ a) x) =ᶠ[𝓝 t]
        (fun x => deriv (fun u => τ u * u ^ a) x) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact hderivAt x hx
  rw [hderivEventually.deriv_eq]
  exact c3_rawCutoffPower_secondDeriv hτ ha ht0

private theorem c3_cutoff_deriv_zero {A : ℝ} {τ : ℝ → ℝ}
    (hτ : IsCuspCutoff A τ) {t : ℝ} (ht : t ≤ A) :
    deriv (fun x : ℝ => (τ x : ℂ)) t = 0 := by
  refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic A t ht)
  refine (hasDerivWithinAt_const t (Set.Iic A) (0 : ℂ)).congr_of_mem ?_ ht
  intro x hx
  simp [hτ.2.2.1 x hx]

private theorem c3_cutoff_secondDeriv_zero {A : ℝ} {τ : ℝ → ℝ}
    (hτ : IsCuspCutoff A τ) {t : ℝ} (ht : t ≤ A) :
    deriv (deriv (fun x : ℝ => (τ x : ℂ))) t = 0 := by
  refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic A t ht)
  refine (hasDerivWithinAt_const t (Set.Iic A) (0 : ℂ)).congr_of_mem ?_ ht
  intro x hx
  simp [c3_cutoff_deriv_zero hτ hx]

structure C3CuspData {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex] (s₁ : ℝ)
    (setup : C3SpectralSetup F Γ s₁) (hfree : FreeAction F Γ) (σ : SL(2,F)) where
  A₀ : ℝ
  A : ℝ
  A₀_ge : 1 ≤ A₀
  A₀_le_A : A₀ ≤ A
  A₀_lt_A : A₀ < A
  A_pos : 0 < A
  separation : ∀ γ γ' : Γ, ∀ z : X F,
    A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
    A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
    γ' * γ⁻¹ ∈ cuspStab F Γ σ
  τ : ℝ → ℝ
  hτ : IsCuspCutoff A τ
  k₀ : ℝ → ℝ
  G : ℂ → L2Space F setup.D
  hG : AnalyticOnNhd ℂ G Set.univ
  hsource : ∀ s, ∀ᵐ z ∂(volX F), z ∈ setup.D →
    G s z = eisSeedDefect F Γ σ τ s z
  hseed : ∀ s, IsSmoothX F (eisSeed F Γ σ τ s) ∧
    IsGammaInvariant F Γ (eisSeed F Γ σ τ s) ∧
    ∀ z, totalLap F (eisSeed F Γ σ τ s) z -
      spectralParameter F s * eisSeed F Γ σ τ s z =
        eisSeedDefect F Γ σ τ s z
  hseedAnalytic : ∀ K : Set (Coord F), IsCompact K → K ⊆ posSet F →
    ∀ n : ℕ, ∀ v : Fin n → Coord F,
      ∃ Φ : ℂ → (K →ᵇ ℂ), AnalyticOnNhd ℂ Φ Set.univ ∧
        ∀ s p, Φ s p = iteratedFDeriv ℝ n
          (fun q => eisSeed F Γ σ τ s (ptX F q)) p v
  htail : C3TailFormula (F := F) (Γ := Γ) (σ := σ) (A₀ := A₀) τ
  ε : ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ s₁
  d : ContinuedEisenstein F Γ σ s₁
  d_res : d.res = (fun z => (radialTransform F k₀ (1 + 2 * s₁))⁻¹ *
      smoothingOperator F k₀
        (l2Lift F Γ setup.D
          (-setup.κ • (setup.E.M.comp (setup.P.comp setup.E.M.adjoint))
            (G (s₁ : ℂ)))) z)
  d_res_ae : d.res =ᵐ[volX F] l2Lift F Γ setup.D
    (-setup.κ • (setup.E.M.comp (setup.P.comp setup.E.M.adjoint))
      (G (s₁ : ℂ)))

private theorem c3_defect_supported_in_cuspTail
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex] {σ : SL(2,F)}
    {A₀ A : ℝ} {τ : ℝ → ℝ}
    (hA₀ : 1 ≤ A₀) (hA₀A : A₀ < A) (hτ : IsCuspCutoff A τ)
    (htail : C3TailFormula (F := F) (Γ := Γ) (σ := σ) (A₀ := A₀) τ)
    (s : ℂ) :
    {z | eisSeedDefect F Γ σ τ s z ≠ 0} ⊆ cuspTail F Γ σ A := by
  intro z hz
  by_contra hnot
  by_cases hnot₀ : z ∉ cuspTail F Γ σ A₀
  · exact hz (c3_eisSeedDefect_zero_of_notTail Γ σ A₀ A hA₀ hA₀A τ hτ s z hnot₀)
  · have hzTail₀ : z ∈ cuspTail F Γ σ A₀ := not_not.mp hnot₀
    obtain ⟨γ, hformula⟩ := htail s z hzTail₀
    have hheight : normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ A := by
      by_contra h
      exact hnot ⟨γ, lt_of_not_ge h⟩
    change eisSeedDefect F Γ σ τ s z ≠ 0 at hz
    rw [hformula] at hz
    simp [c3_cutoff_deriv_zero hτ hheight,
      c3_cutoff_secondDeriv_zero hτ hheight] at hz

theorem c3_cusp_data {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (s₁ : ℝ) (setup : C3SpectralSetup F Γ s₁) (hfree : FreeAction F Γ)
    (σ : SL(2,F)) (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2)
    (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkNonneg : ∀ t, 0 ≤ k₀ t)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (hkNonzero : ∃ t, k₀ t ≠ 0) :
    Nonempty (C3CuspData s₁ setup hfree σ) := by
  classical
  obtain ⟨Aσ, hAσ, hsepσ⟩ := (R10_cusp_separation Γ).1 σ
  obtain ⟨Ad, hAd, hsepd⟩ := (R10_cusp_separation Γ).2.1 setup.siegel
  let A := max (max Aσ Ad) (1 + 1 / (8 * s₁ ^ 2)) + 1
  have hAσA : Aσ ≤ A := by
    dsimp [A]
    have hle : Aσ ≤ max (max Aσ Ad) (1 + 1 / (8 * s₁ ^ 2)) :=
      (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hAdA : Ad ≤ A := by
    dsimp [A]
    have hle : Ad ≤ max (max Aσ Ad) (1 + 1 / (8 * s₁ ^ 2)) :=
      (le_max_right _ _).trans (le_max_left _ _)
    linarith
  have hAσLtA : Aσ < A := by
    dsimp [A]
    have hle : Aσ ≤ max (max Aσ Ad) (1 + 1 / (8 * s₁ ^ 2)) :=
      (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hA_pos : 0 < A := by
    dsimp [A]
    have hAσ_pos : 0 < Aσ := lt_of_lt_of_le one_pos hAσ
    positivity
  let τ := cuspCutoff A
  have hτ : IsCuspCutoff A τ := isCuspCutoff_cuspCutoff hA_pos
  have hsep₀ : ∀ γ γ' : Γ, ∀ z : X F,
      Aσ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      Aσ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ :=
    hsepσ Aσ le_rfl
  rcases E5_seed Γ setup.D setup.hD σ Aσ A hAσ hAσA hsep₀ τ hτ with
    ⟨_, hseed, _, ⟨G, hG, hsource⟩, hseedAnalytic, htail⟩
  obtain ⟨ε, hεpos, hεle, d, hres, hresAE⟩ :=
    c3_projected_continuation s₁ setup hfree σ h₀ h₁
      Aσ A hAσ hAσA hsep₀ k₀ τ hkSmooth hkNonneg hkSupport hkNonzero hτ
      G hG hsource hseed
  exact ⟨{
    A₀ := Aσ
    A := A
    A₀_ge := hAσ
    A₀_le_A := hAσA
    A₀_lt_A := hAσLtA
    A_pos := hA_pos
    separation := hsep₀
    τ := τ
    hτ := hτ
    k₀ := k₀
    G := G
    hG := hG
    hsource := hsource
    hseed := hseed
    hseedAnalytic := hseedAnalytic
    htail := htail
    ε := ε
    ε_pos := hεpos
    ε_le := hεle
    d := d
    d_res := hres
    d_res_ae := hresAE }⟩

private def cuspExtensionZ {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    Submodule ℤ (InfinitePlace F → ℂ) :=
  Submodule.span ℤ (cuspTranslationExtensionComplex F Γ σ : Set (InfinitePlace F → ℂ))

private theorem c3_cuspExtension_fullZLattice {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    IsFullZLattice (cuspExtensionZ Γ σ) := by
  classical
  let E := InfinitePlace F → ℂ
  let b := complexIntegerLatticeBasis (F := F)
  let L₀ : Submodule ℤ E := Submodule.span ℤ (Set.range b)
  obtain ⟨m, hm, hmlower⟩ := (R1_cusp_lattice Γ σ).1
  obtain ⟨D, hD, _, hExtD⟩ := (R1_cusp_lattice Γ σ).2.1
  let scale : E →ₗ[ℝ] E := (D : ℝ) • LinearMap.id
  have hinc : cuspLattice F Γ σ ≤ cuspTranslationExtension F Γ σ :=
    (R1_cusp_lattice Γ σ).2.2.2.1.2.1
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hscaleCont : Continuous scale := LinearMap.continuous_of_finiteDimensional _
  have hscaleInj : Function.Injective scale := by
    intro x y hxy
    have h := congrArg (fun z : E => (D : ℝ)⁻¹ • z) hxy
    simpa [scale, smul_smul, hDne] using h
  let U : Submodule ℤ E := ZLattice.comap ℝ L₀ scale
  letI : DiscreteTopology L₀ := inferInstance
  have hUdisc : DiscreteTopology U :=
    ZLattice.comap_discreteTopology ℝ L₀ hscaleCont hscaleInj
  have hupper : cuspExtensionZ Γ σ ≤ U := by
    change Submodule.span ℤ (cuspTranslationExtensionComplex F Γ σ : Set E) ≤ U
    apply Submodule.span_le.mpr
    intro x hx
    rcases AddSubgroup.mem_map.mp hx with ⟨μ, hμ, rfl⟩
    obtain ⟨a, ha⟩ := hExtD μ hμ
    change (D : ℝ) • infEmb F μ ∈ L₀
    have hemb := congrArg (infEmb F) ha
    rw [infEmb_nat_mul] at hemb
    rw [hemb]
    exact infEmb_ringInteger_mem_span a
  letI : DiscreteTopology (cuspExtensionZ Γ σ) :=
    DiscreteTopology.of_subset hUdisc hupper
  have hmulmem (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
      (m : ℝ) • b i ∈ cuspExtensionZ Γ σ := by
    apply Submodule.subset_span
    apply AddSubgroup.mem_map.mpr
    refine ⟨algebraMap (𝓞 F) F ((m : 𝓞 F) * RingOfIntegers.basis F i),
      hinc (hmlower _), ?_⟩
    change infEmb F (algebraMap (𝓞 F) F
      ((m : 𝓞 F) * RingOfIntegers.basis F i)) = (m : ℝ) • b i
    rw [(algebraMap (𝓞 F) F).map_mul, map_natCast, infEmb_nat_mul]
    rw [complexIntegerLatticeBasis_apply]
  have hspan : Submodule.span ℝ (cuspExtensionZ Γ σ : Set E) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hreal := Submodule.subset_span (R := ℝ) (hmulmem i)
    have hs := (Submodule.span ℝ (cuspExtensionZ Γ σ : Set E)).smul_mem
      (m : ℝ)⁻¹ hreal
    simpa [smul_smul, hmne] using hs
  exact ⟨inferInstance, ⟨hspan⟩⟩

theorem c3_extension_fundamentalDomain {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P ∧
        MeasurableSet P ∧ Bornology.IsBounded P := by
  classical
  let L := cuspExtensionZ Γ σ
  rcases c3_cuspExtension_fullZLattice Γ σ with ⟨hdisc, hZ⟩
  letI : DiscreteTopology L := hdisc
  letI : IsZLattice ℝ L := hZ
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  let bZ := Module.Free.chooseBasis ℤ L
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ L) :=
    Module.Free.ChooseBasisIndex.fintype ℤ L
  let b := bZ.ofZLatticeBasis ℝ
  let P := ZSpan.fundamentalDomain b
  have hspan : Submodule.span ℤ (Set.range b) = L :=
    bZ.ofZLatticeBasis_span ℝ
  have hL : L = (cuspTranslationExtensionComplex F Γ σ).toIntSubmodule := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by intro x hx; exact hx)
    · intro x hx
      exact Submodule.subset_span hx
  have hLadd : L.toAddSubgroup = cuspTranslationExtensionComplex F Γ σ := by
    simpa using congrArg Submodule.toAddSubgroup hL
  have hspanAdd : (Submodule.span ℤ (Set.range b)).toAddSubgroup = L.toAddSubgroup :=
    congrArg Submodule.toAddSubgroup hspan
  have hfdL : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup P
      (volume : Measure (InfinitePlace F → ℂ)) := by
    simpa [P] using
      (ZSpan.isAddFundamentalDomain' b (volume : Measure (InfinitePlace F → ℂ)))
  have hfd : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P := by
    rw [← hLadd, ← hspanAdd]
    exact hfdL
  exact ⟨P, hfd, ZSpan.fundamentalDomain_measurableSet b,
    ZSpan.fundamentalDomain_isBounded b⟩

local instance (priority := 1000) c3LogSpaceAddGroup {F : Type} [Field F] [NumberField F] :
    AddGroup (NumberField.Units.dirichletUnitTheorem.logSpace F) :=
  Pi.normedAddCommGroup.toAddGroup

private def cuspUnitLogGroup {F : Type} [Field F] [NumberField F]
    (E : Subgroup ((𝓞 F)ˣ)) : AddSubgroup (NumberField.Units.dirichletUnitTheorem.logSpace F) :=
  E.toAddSubgroup.map (NumberField.Units.logEmbedding F)

private theorem c3_unitLog_fullZLattice {F : Type} [Field F] [NumberField F]
    (E : Subgroup ((𝓞 F)ˣ)) [E.FiniteIndex] :
    IsFullZLattice
      (E := NumberField.Units.dirichletUnitTheorem.logSpace F)
      (cuspUnitLogGroup E).toIntSubmodule := by
  classical
  let V := NumberField.Units.dirichletUnitTheorem.logSpace F
  let U := NumberField.Units.unitLattice F
  letI : DiscreteTopology U := NumberField.Units.instDiscrete_unitLattice F
  letI : IsZLattice ℝ U := NumberField.Units.instZLattice_unitLattice F
  let bZ := NumberField.Units.basisUnitLattice F
  let b := bZ.ofZLatticeBasis ℝ U
  let L : Submodule ℤ V := (cuspUnitLogGroup E).toIntSubmodule
  let n : ℕ := E.index
  have hn0 : n ≠ 0 := by
    dsimp [n]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hsubset : L ≤ U := by
    change (cuspUnitLogGroup E : Set V) ⊆ U
    intro x hx
    rcases AddSubgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    exact Submodule.mem_map.mpr ⟨u, trivial, rfl⟩
  have hdisc : DiscreteTopology L := DiscreteTopology.of_subset ‹DiscreteTopology U› hsubset
  letI : DiscreteTopology L := hdisc
  have hmul (i : Fin (NumberField.Units.rank F)) :
      (n : ℝ) • b i ∈ L := by
    have hbi : b i ∈ U := by
      rw [← bZ.ofZLatticeBasis_span ℝ U]
      exact Submodule.subset_span ⟨i, rfl⟩
    change b i ∈ Submodule.map (NumberField.Units.logEmbedding F).toIntLinearMap ⊤ at hbi
    obtain ⟨u, -, hu⟩ := Submodule.mem_map.mp hbi
    have hE : (u.toMul ^ n) ∈ E := by
      dsimp [n]
      exact E.pow_index_mem u.toMul
    have hpow : Additive.ofMul (u.toMul ^ n) ∈ E.toAddSubgroup := hE
    have hpowAdd : Additive.ofMul (u.toMul ^ n) = n • u := by simp
    have hlogNat : NumberField.Units.logEmbedding F (Additive.ofMul (u.toMul ^ n)) =
        n • b i := by
      rw [hpowAdd, map_nsmul]
      change NumberField.Units.logEmbedding F u = b i at hu
      rw [hu]
    have hlog : NumberField.Units.logEmbedding F (Additive.ofMul (u.toMul ^ n)) =
        (n : ℝ) • b i := by
      simpa only [Nat.cast_smul_eq_nsmul] using hlogNat
    change (n : ℝ) • b i ∈ cuspUnitLogGroup E
    exact AddSubgroup.mem_map.mpr ⟨Additive.ofMul (u.toMul ^ n), hpow, hlog⟩
  have hspan : Submodule.span ℝ (L : Set V) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hreal := Submodule.subset_span (R := ℝ) (hmul i)
    have hs := (Submodule.span ℝ (L : Set V)).smul_mem (n : ℝ)⁻¹ hreal
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    simpa [smul_smul, hnreal] using hs
  exact ⟨hdisc, ⟨hspan⟩⟩

private theorem c3_unitLog_fundamentalDomain {F : Type} [Field F] [NumberField F]
    (E : Subgroup ((𝓞 F)ˣ)) [E.FiniteIndex] :
    ∃ P : Set (NumberField.Units.dirichletUnitTheorem.logSpace F),
      IsAddFundamentalDomain (cuspUnitLogGroup E) P ∧ MeasurableSet P ∧
        (∀ x, ∃ t ∈ cuspUnitLogGroup E, t + x ∈ P) ∧
        (∀ x t t', t ∈ cuspUnitLogGroup E → t' ∈ cuspUnitLogGroup E →
          t + x ∈ P → t' + x ∈ P → t = t') := by
  classical
  let H := cuspUnitLogGroup E
  let L := H.toIntSubmodule
  rcases c3_unitLog_fullZLattice E with ⟨hdisc, hZ⟩
  letI : DiscreteTopology L := hdisc
  letI : IsZLattice ℝ L := hZ
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  let bZ := Module.Free.chooseBasis ℤ L
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ L) :=
    Module.Free.ChooseBasisIndex.fintype ℤ L
  let b := bZ.ofZLatticeBasis ℝ
  let P := ZSpan.fundamentalDomain b
  have hspan : Submodule.span ℤ (Set.range b) = L := bZ.ofZLatticeBasis_span ℝ
  have hL : L = H.toIntSubmodule := rfl
  have hLadd : L.toAddSubgroup = H := by
    change (H.toIntSubmodule).toAddSubgroup = H
    exact AddSubgroup.toIntSubmodule_toAddSubgroup H
  have hspanAdd : (Submodule.span ℤ (Set.range b)).toAddSubgroup = L.toAddSubgroup :=
    congrArg Submodule.toAddSubgroup hspan
  have hfdL : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup P
      (volume : Measure (NumberField.Units.dirichletUnitTheorem.logSpace F)) := by
    simpa [P] using
      (ZSpan.isAddFundamentalDomain' b
        (volume : Measure (NumberField.Units.dirichletUnitTheorem.logSpace F)))
  have hfd : IsAddFundamentalDomain H P := by
    rw [← hLadd, ← hspanAdd]
    exact hfdL
  have hcover : ∀ x, ∃ t ∈ H, t + x ∈ P := by
    intro x
    obtain ⟨t, ht, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
    have htH : (t : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈ H := by
      have htL : (t : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈ L :=
        (congrArg (fun S : Submodule ℤ
          (NumberField.Units.dirichletUnitTheorem.logSpace F) =>
          (t : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈ S) hspan).mp t.property
      have ht' : (t : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈ L.toAddSubgroup := htL
      simpa [hLadd] using ht'
    refine ⟨t, htH, ?_⟩
    change (t : NumberField.Units.dirichletUnitTheorem.logSpace F) + x ∈ P
    rw [← vadd_eq_add]
    exact ht
  have hunique : ∀ x t t', t ∈ H → t' ∈ H →
      t + x ∈ P → t' + x ∈ P → t = t' := by
    intro x t t' ht ht' htx ht'x
    have htL : t ∈ L := by change t ∈ H.toIntSubmodule; exact ht
    have ht'L : t' ∈ L := by change t' ∈ H.toIntSubmodule; exact ht'
    have htSpan : (t : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈
        Submodule.span ℤ (Set.range b) := by rw [hspan]; exact htL
    have ht'Span : (t' : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈
        Submodule.span ℤ (Set.range b) := by rw [hspan]; exact ht'L
    let u : ↥(Submodule.span ℤ (Set.range b)) := ⟨t, htSpan⟩
    let u' : ↥(Submodule.span ℤ (Set.range b)) := ⟨t', ht'Span⟩
    have huP : u +ᵥ x ∈ P := by change (t : _) + x ∈ P; exact htx
    have hu'P : u' +ᵥ x ∈ P := by change (t' : _) + x ∈ P; exact ht'x
    exact congrArg Subtype.val
      ((ZSpan.exist_unique_vadd_mem_fundamentalDomain b x).unique huP hu'P)
  exact ⟨P, hfd, ZSpan.fundamentalDomain_measurableSet b, hcover, hunique⟩

private def c3HeightLog {F : Type} [Field F] [NumberField F]
    (y : InfinitePlace F → ℝ) :
    NumberField.Units.dirichletUnitTheorem.logSpace F :=
  fun w => Real.log (y w.1)

private theorem c3_unitHeight_section {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) :
    ∃ Y : Set (InfinitePlace F → ℝ),
      MeasurableSet Y ∧
      (∀ y ∈ Y, ∀ w, 0 < y w) ∧
      (∀ y, (∀ w, 0 < y w) →
        ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧
          unitHeightAction F ε y ∈ Y ∧
          ∀ ε' : (𝓞 F)ˣ, ε' ∈ cuspUnits F Γ σ →
            unitHeightAction F ε' y ∈ Y → ε' = ε ∨ ε' = -ε) := by
  classical
  let E : Subgroup ((𝓞 F)ˣ) := cuspUnits F Γ σ
  letI : E.FiniteIndex := (R2_cusp_units Γ hfree σ).1
  obtain ⟨P, hP, hPmeas, hPcover, hPunique⟩ := c3_unitLog_fundamentalDomain E
  let Y : Set (InfinitePlace F → ℝ) :=
    {y | (∀ w, 0 < y w) ∧ c3HeightLog y ∈ P}
  have hposMeas : MeasurableSet {y : InfinitePlace F → ℝ | ∀ w, 0 < y w} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun w =>
      (isOpen_Ioi.measurableSet).preimage (measurable_pi_apply w)
  have hlogMeas : Measurable (c3HeightLog (F := F)) := by
    apply measurable_pi_iff.mpr
    intro w
    exact Real.measurable_log.comp (measurable_pi_apply w.1)
  have hYmeas : MeasurableSet Y := by
    dsimp [Y]
    rw [Set.setOf_and]
    exact hposMeas.inter (hPmeas.preimage hlogMeas)
  have hEmbed (ε : (𝓞 F)ˣ) (w : InfinitePlace F) :
      w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) ≠ 0 := by
    intro h
    apply ε.ne_zero
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    apply w.embedding.injective
    simpa using h
  have hlogAct (ε : (𝓞 F)ˣ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w)
      (w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
      Real.log (unitHeightAction F ε y w.1) =
        Real.log (y w.1) +
          NumberField.Units.logEmbedding F (Additive.ofMul ε) w := by
    let a : ℝ := ‖w.1.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖
    have ha : 0 < a := norm_pos_iff.mpr (hEmbed ε w.1)
    have hyw : 0 < y w.1 := hy w.1
    have hnormSq : Complex.normSq
        (w.1.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) = a ^ 2 := by
      simp [a, Complex.normSq_eq_norm_sq]
    have hlogEmb :
        NumberField.Units.logEmbedding F (Additive.ofMul ε) w = 2 * Real.log a := by
      rw [NumberField.Units.dirichletUnitTheorem.logEmbedding_component]
      simp [a, IsTotallyComplex.mult_eq, InfinitePlace.norm_embedding_eq]
    calc
      Real.log (unitHeightAction F ε y w.1) =
          Real.log (a ^ 2 * y w.1) := by
            change Real.log (Complex.normSq
              (w.1.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w.1) = _
            rw [hnormSq]
      _ = Real.log (a ^ 2) + Real.log (y w.1) :=
        Real.log_mul (pow_ne_zero 2 ha.ne') hyw.ne'
      _ = Real.log (y w.1) + 2 * Real.log a := by rw [Real.log_pow]; norm_num; ring
      _ = _ := by rw [hlogEmb]
  have hlogActVec (ε : (𝓞 F)ˣ) (y : InfinitePlace F → ℝ)
      (hy : ∀ w, 0 < y w) :
      c3HeightLog (unitHeightAction F ε y) =
        c3HeightLog y + NumberField.Units.logEmbedding F (Additive.ofMul ε) := by
    funext w
    exact hlogAct ε y hy w
  refine ⟨Y, hYmeas, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    let x := c3HeightLog y
    obtain ⟨t, ht, htP⟩ := hPcover x
    rcases AddSubgroup.mem_map.mp ht with ⟨u, hu, hlogu⟩
    let ε : (𝓞 F)ˣ := u.toMul
    have hε : ε ∈ E := hu
    have hlogε : NumberField.Units.logEmbedding F (Additive.ofMul ε) = t := by
      simpa [ε] using hlogu
    have hYε : unitHeightAction F ε y ∈ Y := by
      change (∀ w, 0 < unitHeightAction F ε y w) ∧
        c3HeightLog (unitHeightAction F ε y) ∈ P
      refine ⟨?_, ?_⟩
      · intro w
        unfold unitHeightAction
        exact mul_pos (Complex.normSq_pos.mpr (hEmbed ε w)) (hy w)
      · rw [hlogActVec ε y hy, hlogε]
        simpa [x, add_comm] using htP
    refine ⟨ε, hε, hYε, ?_⟩
    intro ε' hε' hYε'
    have hlogε' : NumberField.Units.logEmbedding F (Additive.ofMul ε') ∈ E.toAddSubgroup.map
        (NumberField.Units.logEmbedding F) := by
      exact AddSubgroup.mem_map.mpr ⟨Additive.ofMul ε', hε', rfl⟩
    have hlogεmem : NumberField.Units.logEmbedding F (Additive.ofMul ε) ∈ E.toAddSubgroup.map
        (NumberField.Units.logEmbedding F) := by
      exact AddSubgroup.mem_map.mpr ⟨Additive.ofMul ε, hε, rfl⟩
    have hlog0P : c3HeightLog y + NumberField.Units.logEmbedding F
        (Additive.ofMul ε) ∈ P := by
      simpa [hlogActVec ε y hy] using hYε.2
    have hlog1P : c3HeightLog y + NumberField.Units.logEmbedding F
        (Additive.ofMul ε') ∈ P := by
      simpa [hlogActVec ε' y hy] using hYε'.2
    have hEq :
        NumberField.Units.logEmbedding F (Additive.ofMul ε) =
          NumberField.Units.logEmbedding F (Additive.ofMul ε') :=
      hPunique (c3HeightLog y)
        (NumberField.Units.logEmbedding F (Additive.ofMul ε))
        (NumberField.Units.logEmbedding F (Additive.ofMul ε'))
        hlogεmem hlogε' (by simpa [add_comm] using hlog0P)
        (by simpa [add_comm] using hlog1P)
    let η : (𝓞 F)ˣ := ε' * ε⁻¹
    have hlogη : NumberField.Units.logEmbedding F (Additive.ofMul η) = 0 := by
      have hprod : Additive.ofMul (ε' * ε⁻¹) =
          Additive.ofMul ε' - Additive.ofMul ε := by
        ext
        simp [div_eq_mul_inv]
      rw [show η = ε' * ε⁻¹ by rfl, hprod, map_sub, hEq]
      simp
    have hηtors : η ∈ NumberField.Units.torsion F :=
      (NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff).mp hlogη
    have hηfinite : IsOfFinOrder η := by
      change η ∈ CommGroup.torsion ((𝓞 F)ˣ) at hηtors
      exact (CommGroup.mem_torsion η).mp hηtors
    have hηE : η ∈ E := by
      dsimp [η, E]
      exact mul_mem hε' (inv_mem hε)
    obtain ⟨_, _, ⟨_, _, _, hsign, _⟩⟩ := R2_cusp_units Γ hfree σ
    have hηsign := hsign η hηE hηfinite
    rcases hηsign with hηone | hηneg
    · left
      dsimp [η] at hηone
      calc
        ε' = (ε' * ε⁻¹) * ε := by group
        _ = ε := by rw [hηone]; simp
    · right
      dsimp [η] at hηneg
      calc
        ε' = (ε' * ε⁻¹) * ε := by group
        _ = (-1) * ε := by rw [hηneg]
        _ = -ε := by simp

private theorem c3_ordinaryFundamentalDomain_of_extension
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (P' : Set (InfinitePlace F → ℂ))
    (hP' : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P')
    (hP'meas : MeasurableSet P')
    (hP'bound : Bornology.IsBounded P')
    (μ₀ : F) (hμ₀ : μ₀ ∈ cuspTranslationExtension F Γ σ)
    (hcoset : ∀ μ ∈ cuspTranslationExtension F Γ σ,
      μ ∈ cuspLattice F Γ σ ∨ μ - μ₀ ∈ cuspLattice F Γ σ)
    (hμ₀not : μ₀ ∉ cuspLattice F Γ σ) :
    IsAddFundamentalDomain (cuspTranslations F Γ σ)
      (P' ∪ (-infEmb F μ₀ +ᵥ P')) ∧
      Bornology.IsBounded (P' ∪ (-infEmb F μ₀ +ᵥ P')) ∧
      MeasurableSet (P' ∪ (-infEmb F μ₀ +ᵥ P')) := by
  classical
  let G := cuspTranslationExtensionComplex F Γ σ
  let H := cuspTranslations F Γ σ
  let v₀ := infEmb F μ₀
  let v₀G : G := ⟨v₀, AddSubgroup.mem_map.mpr ⟨μ₀, hμ₀, rfl⟩⟩
  let Q : Set (InfinitePlace F → ℂ) := P' ∪ (-v₀ +ᵥ P')
  have hOrdExt : H ≤ G := by
    intro x hx
    rcases AddSubgroup.mem_map.mp hx with ⟨μ, hμ, rfl⟩
    exact AddSubgroup.mem_map.mpr ⟨μ,
      (R1_cusp_lattice Γ σ).2.2.2.1.2.1 hμ, rfl⟩
  have hshiftMeas : MeasurableSet (-v₀ +ᵥ P') := by
    have heq : (-v₀ +ᵥ P') = (fun x => v₀ + x) ⁻¹' P' := by
      ext x
      simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm, add_left_comm]
    rw [heq]
    exact hP'meas.preimage (continuous_const.add continuous_id).measurable
  have hQmeas : MeasurableSet Q := by
    dsimp [Q]
    exact hP'meas.union hshiftMeas
  have hcover : ∀ᵐ x : InfinitePlace F → ℂ ∂volume, ∃ h : H, h +ᵥ x ∈ Q := by
    filter_upwards [hP'.ae_covers] with x hx
    rcases hx with ⟨t, ht⟩
    rcases AddSubgroup.mem_map.mp t.property with ⟨μ, hμ, htEq⟩
    have htP : infEmb F μ + x ∈ P' := by
      have heq : t = infEmb F μ := by simpa using htEq.symm
      change (t : InfinitePlace F → ℂ) + x ∈ P' at ht
      rw [heq] at ht
      exact ht
    rcases hcoset μ hμ with hμOrd | hμDiff
    · let h : H := ⟨infEmb F μ, AddSubgroup.mem_map.mpr ⟨μ, hμOrd, rfl⟩⟩
      refine ⟨h, ?_⟩
      change infEmb F μ + x ∈ Q
      exact Or.inl htP
    · let ν := μ - μ₀
      have hνOrd : ν ∈ cuspLattice F Γ σ := hμDiff
      let h : H := ⟨infEmb F ν, AddSubgroup.mem_map.mpr ⟨ν, hνOrd, rfl⟩⟩
      refine ⟨h, ?_⟩
      change infEmb F ν + x ∈ Q
      right
      apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
      simp only [neg_neg, vadd_eq_add]
      have hsum : v₀ + infEmb F ν = infEmb F μ := by
        simp [v₀, ν, map_sub]
      rw [← add_assoc, hsum]
      exact htP
  have hQdisjoint : ∀ h : H, h ≠ 0 → AEDisjoint volume (h +ᵥ Q) Q := by
    intro h hh
    let hG : G := ⟨(h : InfinitePlace F → ℂ), hOrdExt h.property⟩
    have hGne : hG ≠ 0 := by
      intro hz
      apply hh
      have hval : (h : InfinitePlace F → ℂ) = 0 := by
        simpa [hG] using congrArg Subtype.val hz
      exact Subtype.ext hval
    have hv₀notOrd : v₀ ∉ H := by
      intro hv
      rcases AddSubgroup.mem_map.mp hv with ⟨μ, hμ, hEq⟩
      have hμeq : μ₀ = μ := by
        apply (infEmb F).injective
        simpa [v₀] using hEq.symm
      exact hμ₀not (by rw [hμeq]; exact hμ)
    have hv₀Gne : v₀G ≠ 0 := by
      intro hz
      have hval : v₀ = 0 := by simpa [v₀G] using congrArg Subtype.val hz
      have hμ₀zero : μ₀ = 0 := by
        apply (infEmb F).injective
        simpa [v₀] using hval
      exact hμ₀not (by rw [hμ₀zero]; exact (cuspLattice F Γ σ).zero_mem)
    have hGneV₀ : hG ≠ v₀G := by
      intro hz
      have hval : (h : InfinitePlace F → ℂ) = v₀ := by
        simpa [hG, v₀G] using congrArg Subtype.val hz
      exact hv₀notOrd (by rw [← hval]; exact h.property)
    have hdiffne : hG - v₀G ≠ 0 := by
      intro hz
      exact hGneV₀ (sub_eq_zero.mp hz)
    have h00 : AEDisjoint volume (hG +ᵥ P') P' := by
      have htmp := hP'.aedisjoint (i := hG) (j := 0) hGne
      change AEDisjoint volume (hG +ᵥ P') ((0 : G) +ᵥ P') at htmp
      simpa using htmp
    have h01 : AEDisjoint volume (hG +ᵥ P') ((-v₀G) +ᵥ P') := by
      apply hP'.aedisjoint (i := hG) (j := -v₀G)
      intro heq
      have hval : (h : InfinitePlace F → ℂ) = -v₀ := by
        simpa [hG, v₀G] using congrArg Subtype.val heq
      have hneg : -(h : InfinitePlace F → ℂ) = v₀ := by
        rw [hval]
        simp
      exact hv₀notOrd (by rw [← hneg]; exact H.neg_mem h.property)
    have h10 : AEDisjoint volume ((hG - v₀G) +ᵥ P') P' := by
      have htmp := hP'.aedisjoint (i := hG - v₀G) (j := 0) hdiffne
      change AEDisjoint volume ((hG - v₀G) +ᵥ P') ((0 : G) +ᵥ P') at htmp
      simpa using htmp
    have h11 : AEDisjoint volume ((hG - v₀G) +ᵥ P') ((-v₀G) +ᵥ P') := by
      apply hP'.aedisjoint (i := hG - v₀G) (j := -v₀G)
      intro heq
      have hzero : hG = 0 := by
        have := congrArg (fun t : G => t + v₀G) heq
        simpa [sub_add_cancel] using this
      exact hGne hzero
    have hleft₁ := h00.union_right h01
    have hleft₂ := h10.union_right h11
    have hleft := hleft₁.union_left hleft₂
    have hsets :
        h +ᵥ Q =
          (((hG : InfinitePlace F → ℂ) +ᵥ P') ∪
            (((hG - v₀G : G) : InfinitePlace F → ℂ) +ᵥ P')) := by
      ext x
      simp [Q, hG, v₀, v₀G, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      have hfirst : -h +ᵥ x = x + -(h : InfinitePlace F → ℂ) := by
        change -(h : InfinitePlace F → ℂ) + x =
          x + -(h : InfinitePlace F → ℂ)
        abel
      have hsecond : (-h +ᵥ x) + (infEmb F μ₀) =
          x + (-h + (infEmb F μ₀)) := by
        change (-(h : InfinitePlace F → ℂ) + x) + infEmb F μ₀ =
          x + (-(h : InfinitePlace F → ℂ) + infEmb F μ₀)
        abel
      constructor
      · rintro (h₁ | h₂)
        · rw [hfirst] at h₁
          exact Or.inl h₁
        · rw [hsecond] at h₂
          exact Or.inr h₂
      · rintro (h₁ | h₂)
        · rw [← hfirst] at h₁
          exact Or.inl h₁
        · rw [← hsecond] at h₂
          exact Or.inr h₂
    rw [hsets]
    exact hleft
  have hqmp (h : H) :
      MeasureTheory.Measure.QuasiMeasurePreserving
        ((h +ᵥ ·) : (InfinitePlace F → ℂ) → _) volume volume :=
    (measurePreserving_add_left volume (h : InfinitePlace F → ℂ)).quasiMeasurePreserving
  have hfd := IsAddFundamentalDomain.mk'' hQmeas.nullMeasurableSet hcover hQdisjoint hqmp
  have hshiftBound : Bornology.IsBounded (-v₀ +ᵥ P') := by
    have heq : -v₀ +ᵥ P' = ({-v₀} : Set (InfinitePlace F → ℂ)) + P' := by
      ext x
      simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm]
    rw [heq]
    exact Bornology.IsBounded.add Bornology.isBounded_singleton hP'bound
  have hQbound : Bornology.IsBounded Q := hP'bound.union hshiftBound
  refine ⟨?_, hQbound, hQmeas⟩
  simpa [Q, v₀] using hfd

private theorem c3_countable_addSubgroup_image
    {F : Type} [Field F] [NumberField F] (A : AddSubgroup F) :
    Countable (A.map (infEmb F).toAddMonoidHom) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have hcount : (Set.range (infEmb F)).Countable := Set.countable_range _
  have hsub : (A.map (infEmb F).toAddMonoidHom : Set (InfinitePlace F → ℂ)) ⊆
      Set.range (infEmb F) := by
    intro x hx
    rcases AddSubgroup.mem_map.mp hx with ⟨μ, hμ, rfl⟩
    exact ⟨μ, rfl⟩
  exact (hcount.mono hsub).to_subtype

private theorem c3_height_pos (z : H3) : 0 < height z := by
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos z

private theorem c3_horiz_smul_borel {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,ℂ)) (hg : g 1 0 = 0) (z : H3) :
    horiz (g • z) = (g 0 0) ^ 2 * horiz z + g 0 0 * g 0 1 := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, hg] at h
    simpa using h
  have ha : g 0 0 ≠ 0 := by
    intro h
    simp [h] at hdet
  have hd : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hz11 : herm z 1 1 ≠ 0 := by
    intro h
    have hpos := c3_height_pos z
    simp [height, h] at hpos
  have hstar : star ((g 0 0)⁻¹) ≠ 0 := star_ne_zero.mpr (inv_ne_zero ha)
  have hherm := (G1_h3_basics (F := F)).2.2.2.1 g z
  have h01 := congrArg (fun H : Matrix (Fin 2) (Fin 2) ℂ => H 0 1) hherm
  have h11 := congrArg (fun H : Matrix (Fin 2) (Fin 2) ℂ => H 1 1) hherm
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hg] at h01 h11
  unfold horiz
  rw [h01, h11, hd]
  field_simp [ha, hz11, hstar]
  <;> ring

private theorem c3_height_smul_borel {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2,ℂ)) (hg : g 1 0 = 0) (z : H3) :
    height (g • z) = Complex.normSq (g 0 0) * height z := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, hg] at h
    simpa using h
  have hd : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have h := (G1_h3_basics (F := F)).2.2.1 g (horiz z) (height z) (c3_height_pos z)
  rw [(G1_h3_basics (F := F)).2.2.2.2.2.1 z] at h
  simpa [hg, hd, Complex.normSq_inv, div_eq_mul_inv, mul_comm] using h

private theorem c3_cuspUnitMatrix_action {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (ε : (𝓞 F)ˣ) (μ : F)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    cuspUnitMatrix F ε μ • ptX' F x y =
      ptX' F (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
        w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
        (unitHeightAction F ε y) := by
  funext w
  let g : SL(2,ℂ) := Matrix.SpecialLinearGroup.map w.embedding (cuspUnitMatrix F ε μ)
  change g • pt (x w) (y w) = _
  have hcoeg : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (cuspUnitMatrix F ε μ : Matrix (Fin 2) (Fin 2) F).map w.embedding :=
    Matrix.SpecialLinearGroup.map_apply_coe w.embedding (cuspUnitMatrix F ε μ)
  have hg : g 1 0 = 0 := by
    change (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
    rw [hcoeg]
    simp [Matrix.map_apply, cuspUnitMatrix]
  calc
    _ = pt (horiz (g • pt (x w) (y w))) (height (g • pt (x w) (y w))) :=
      ((G1_h3_basics (F := F)).2.2.2.2.2.1 _).symm
    _ = _ := by
      rw [c3_horiz_smul_borel (F := F) g hg, c3_height_smul_borel (F := F) g hg,
        (G1_h3_basics (F := F)).1 _ _ (hy w),
        (G1_h3_basics (F := F)).2.1 _ _ (hy w)]
      simp [hcoeg, Matrix.map_apply, cuspUnitMatrix, unitHeightAction, ptX']

private theorem c3_signedMatrix_action {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (ε : (𝓞 F)ˣ) (μ : F)
    (hε : (algebraMap (𝓞 F) F (ε : 𝓞 F)) ^ 2 = 1)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    signedCuspTranslationMatrix F ε μ hε • ptX' F x y =
      ptX' F (fun w => x w + w.embedding μ) y := by
  have hinv : (algebraMap (𝓞 F) F (ε : 𝓞 F))⁻¹ =
      algebraMap (𝓞 F) F (ε : 𝓞 F) :=
    (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hε)).symm
  have hmatrix : signedCuspTranslationMatrix F ε μ hε =
      cuspUnitMatrix F ε (algebraMap (𝓞 F) F (ε : 𝓞 F) * μ) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [signedCuspTranslationMatrix, cuspUnitMatrix, hinv]
  rw [hmatrix, c3_cuspUnitMatrix_action ε _ x y hy]
  funext w
  have hw : (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 = 1 := by
    rw [← map_pow, hε, map_one]
  have hn : Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) = 1 := by
    have hs := congrArg (fun z : ℂ => ‖z‖) hw
    simpa only [norm_pow, norm_one, Complex.normSq_eq_norm_sq] using hs
  have hx : (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
      w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) *
        w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F) * μ) = x w + w.embedding μ := by
    rw [map_mul]
    calc
      _ = (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * (x w + w.embedding μ) := by ring
      _ = _ := by rw [hw]; simp
  change pt _ _ = pt _ _
  dsimp only
  rw [hx]
  simp [unitHeightAction, hn]

private theorem c3_cusp_conjugate_action {F : Type} [Field F] [NumberField F]
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (γ : Γ) (b : SL(2,F))
    (hb : σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = b) (z : X F) :
    (γ : SL(2,𝓞 F)) • (σ • z) = σ • (b • z) := by
  have hmul : toSLF F (γ : SL(2,𝓞 F)) * σ = σ * b := by
    have h := congrArg (fun g : SL(2,F) => σ * g) hb
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h
  change toSLF F (γ : SL(2,𝓞 F)) • (σ • z) = σ • (b • z)
  rw [← mul_smul, hmul, mul_smul]

private theorem c3_unitHeightAction_product {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F]
    (ε : (𝓞 F)ˣ) (y : InfinitePlace F → ℝ) :
    (∏ w : InfinitePlace F, unitHeightAction F ε y w) = ∏ w, y w := by
  have hnorm : absUnitNorm F ε = 1 := by
    simpa [absUnitNorm, absFieldNorm_eq_abs_norm] using (NumberField.Units.norm F ε)
  unfold unitHeightAction
  rw [Finset.prod_mul_distrib]
  have hprod : ∏ w : InfinitePlace F,
      Complex.normSq (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) = 1 := by
    simpa [absUnitNorm, absFieldNorm, Complex.normSq_eq_norm_sq] using hnorm
  rw [hprod, one_mul]

private theorem c3_normHeight_ptX' {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) : normHeight F (ptX' F x y) = ∏ w, y w := by
  have h := (G2_x_action (F := F)).1 (1 : SL(2,F)) x y hy
  simpa using h

private def c3Hessian {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (f : Coord F → ℝ) (p : Coord F) (v w : Coord F) : ℝ :=
  (fderiv ℝ (fun y => fderiv ℝ f y) p v) w

private theorem c3Hessian_eq_iteratedFDeriv
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (f : Coord F → ℝ) (p v w : Coord F) :
    c3Hessian f p v w = iteratedFDeriv ℝ 2 f p ![v, w] := by
  rw [c3Hessian, iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rw [show Fin.init ![v, w] 0 = v from rfl]
  rw [show ![v, w] (Fin.last 1) = w from rfl]

private theorem c3Hessian_mul {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] {f g : Coord F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p v w : Coord F) :
    c3Hessian (fun x => f x * g x) p v w =
      f p * c3Hessian g p v w + g p * c3Hessian f p v w +
        fderiv ℝ f p v * fderiv ℝ g p w + fderiv ℝ g p v * fderiv ℝ f p w := by
  have hf' (x : Coord F) := (hf.differentiable (by simp) x).hasFDerivAt
  have hg' (x : Coord F) := (hg.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (fun z => f z * g z) y) =
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    funext y
    exact ((hf' y).mul (hg' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hgd : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hd := ((hf' p).smul (hgd p).hasFDerivAt).add
    ((hg' p).smul (hfd p).hasFDerivAt)
  unfold c3Hessian
  change ((fderiv ℝ (fun y => fderiv ℝ (fun z => f z * g z) y) p v) w) = _
  rw [hG]
  change ((fderiv ℝ ((f • fun y => fderiv ℝ g y) +
    g • fun y => fderiv ℝ f y) p v) w) = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  ring

private theorem c3Hessian_scalar_comp {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] {f : Coord F → ℝ} {g g' g'' : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t) (p v w : Coord F) :
    c3Hessian (g ∘ f) p v w =
      g'' (f p) * fderiv ℝ f p v * fderiv ℝ f p w +
        g' (f p) * c3Hessian f p v w := by
  have hf' (x : Coord F) := (hf.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (g ∘ f) y) =
      (fun y => g' (f y) • fderiv ℝ f y) := by
    funext y
    exact ((hg (f y)).comp_hasFDerivAt y (hf' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp)
  have hd := ((hg' (f p)).comp_hasFDerivAt p (hf' p)).smul
    (hfd p).hasFDerivAt
  unfold c3Hessian
  change ((fderiv ℝ (fun y => fderiv ℝ (g ∘ f) y) p v) w) = _
  rw [hG]
  change ((fderiv ℝ ((g' ∘ f) • fun y => fderiv ℝ f y) p v) w) = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, smul_eq_mul, Function.comp_apply]
  ring

private def c3CoordY {F : Type} [Field F] [NumberField F]
    (v : InfinitePlace F) (p : Coord F) : ℝ := (p v).2

private def c3CoordYCLM {F : Type} [Field F] [NumberField F]
    (v : InfinitePlace F) : Coord F →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℂ ℝ).comp
    (ContinuousLinearMap.proj (R := ℝ) (ι := InfinitePlace F) v)

private theorem c3CoordY_smooth {F : Type} [Field F] [NumberField F]
    (v : InfinitePlace F) : ContDiff ℝ ∞ (c3CoordY (F := F) v) := by
  fun_prop [c3CoordY]

private theorem c3CoordY_deriv {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (v : InfinitePlace F) (p : Coord F)
    (w : InfinitePlace F) (j : Fin 3) :
    fderiv ℝ (c3CoordY (F := F) v) p (placeDirection F w j) =
      if v = w ∧ j = 2 then 1 else 0 := by
  have hlin : c3CoordY (F := F) v = c3CoordYCLM (F := F) v := by rfl
  rw [hlin, (c3CoordYCLM (F := F) v).hasFDerivAt.fderiv]
  fin_cases j <;> by_cases hvw : v = w <;>
    simp [c3CoordYCLM, placeDirection, Pi.single, Function.update, hvw, eq_comm]

private theorem c3CoordY_hessian {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (v : InfinitePlace F) (p : Coord F)
    (w : InfinitePlace F) (j : Fin 3) :
    c3Hessian (c3CoordY (F := F) v) p (placeDirection F w j)
      (placeDirection F w j) = 0 := by
  have hder (x : Coord F) : fderiv ℝ (c3CoordY (F := F) v) x =
      c3CoordYCLM (F := F) v :=
    (c3CoordYCLM (F := F) v).hasFDerivAt.fderiv
  unfold c3Hessian
  change (fderiv ℝ (fun x => fderiv ℝ (c3CoordY (F := F) v) x) p
    (placeDirection F w j)) (placeDirection F w j) = 0
  rw [show (fun x => fderiv ℝ (c3CoordY (F := F) v) x) =
      fun _ => c3CoordYCLM (F := F) v from funext hder]
  simp

private def c3CoordHeightProd {F : Type} [Field F] [NumberField F]
    (s : Finset (InfinitePlace F)) (p : Coord F) : ℝ :=
  ∏ v ∈ s, c3CoordY (F := F) v p

private theorem c3CoordHeightProd_smooth {F : Type} [Field F] [NumberField F]
    (s : Finset (InfinitePlace F)) : ContDiff ℝ ∞ (c3CoordHeightProd (F := F) s) := by
  unfold c3CoordHeightProd
  exact contDiff_prod (fun v hv => c3CoordY_smooth v)

private theorem c3CoordHeightProd_fderiv {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (s : Finset (InfinitePlace F)) (w : InfinitePlace F)
    (j : Fin 3) (p : Coord F) :
    fderiv ℝ (c3CoordHeightProd (F := F) s) p (placeDirection F w j) =
      if j = 2 ∧ w ∈ s then
        ∏ v ∈ s.erase w, c3CoordY (F := F) v p else 0 := by
  classical
  have hformula : fderiv ℝ (c3CoordHeightProd (F := F) s) p =
      ∑ v ∈ s, (∏ q ∈ s.erase v, c3CoordY (F := F) q p) •
        fderiv ℝ (c3CoordY (F := F) v) p := by
    unfold c3CoordHeightProd
    exact fderiv_finsetProd (fun v hv =>
      (c3CoordY_smooth (F := F) v).differentiable (by simp) p)
  rw [hformula]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [c3CoordY_deriv]
  by_cases hj : j = 2 <;> by_cases hw : w ∈ s <;> simp [hj, hw]

private theorem c3CoordHeightProd_hessian {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (s : Finset (InfinitePlace F)) (w : InfinitePlace F)
    (j : Fin 3) (p : Coord F) :
    c3Hessian (c3CoordHeightProd (F := F) s) p
      (placeDirection F w j) (placeDirection F w j) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change (fderiv ℝ (fun y => fderiv ℝ (fun _ : Coord F => (1 : ℝ)) y) p
        (placeDirection F w j)) (placeDirection F w j) = 0
      simp [c3Hessian]
  | @insert i s his ih =>
      have hprod : c3CoordHeightProd (F := F) (insert i s) = fun p =>
          c3CoordY (F := F) i p * c3CoordHeightProd (F := F) s p := by
        funext p
        simp [c3CoordHeightProd, his]
      rw [hprod, c3Hessian_mul (c3CoordY_smooth (F := F) i)
        (c3CoordHeightProd_smooth (F := F) s)]
      rw [ih, c3CoordY_hessian]
      rw [c3CoordHeightProd_fderiv, c3CoordY_deriv]
      by_cases hiw : i = w
      · have hws : w ∉ s := by simpa [hiw] using his
        simp [hiw, hws]
      · simp [hiw]

private theorem c3FDeriv_ofReal {F : Type} [Field F] [NumberField F]
    {u : Coord F → ℝ} (p v : Coord F) (hu : DifferentiableAt ℝ u p) :
    fderiv ℝ (fun q => (u q : ℂ)) p v = (fderiv ℝ u p v : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp p hu.hasFDerivAt
  change (fderiv ℝ (Complex.ofRealCLM ∘ u) p) v = _
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

private theorem c3IteratedFDeriv_ofReal {F : Type} [Field F] [NumberField F]
    {u : Coord F → ℝ} (p v w : Coord F) (hu : ContDiff ℝ ∞ u) :
    iteratedFDeriv ℝ 2 (fun q => (u q : ℂ)) p ![v, w] =
      (iteratedFDeriv ℝ 2 u p ![v, w] : ℂ) := by
  have h := (Complex.ofRealCLM).iteratedFDeriv_comp_left
    (f := u) (x := p) hu.contDiffAt (by norm_num : 2 ≤ (∞ : ℕ∞ω))
  have happ := congrArg (fun D => D ![v, w]) h
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at happ
  have hfun : (fun q => (u q : ℂ)) = Complex.ofRealCLM ∘ u := rfl
  rw [hfun]
  exact happ

private theorem c3FDeriv_realCompAt {F : Type} [Field F] [NumberField F]
    {u : Coord F → ℝ} {ψ ψ' : ℝ → ℝ}
    (p v : Coord F) (hu : DifferentiableAt ℝ u p)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) :
    fderiv ℝ (ψ ∘ u) p v = ψ' (u p) * fderiv ℝ u p v := by
  have hcomp := (hψ (u p)).hasFDerivAt.comp p hu.hasFDerivAt
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply]
  ring

private def c3CoordHeight {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (p : Coord F) : ℝ := ∏ v : InfinitePlace F, (p v).2

private theorem c3NormHeight_ptX {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (p : Coord F) (hp : p ∈ posSet F) :
    normHeight F (ptX F p) = c3CoordHeight (F := F) p := by
  unfold normHeight c3CoordHeight ptX
  simp only [height]
  congr 1
  funext w
  exact (G1_h3_basics (F := F)).1 (p w).1 (p w).2 (hp w)

private theorem c3PartialLap_realChart {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (u : Coord F → ℝ) (hu : ContDiff ℝ ∞ u)
    (p : Coord F) (hp : p ∈ posSet F) (w : InfinitePlace F) :
    partialLap F w (fun z => (u (coordsX F z) : ℂ)) (ptX F p) =
      ((p w).2 : ℂ) * (fderiv ℝ u p (placeDirection F w 2) : ℂ) -
        ((p w).2 : ℂ) ^ 2 *
          ((c3Hessian u p (placeDirection F w 0) (placeDirection F w 0) : ℂ) +
            (c3Hessian u p (placeDirection F w 1) (placeDirection F w 1) : ℂ) +
            (c3Hessian u p (placeDirection F w 2) (placeDirection F w 2) : ℂ)) := by
  have hcoords : coordsX F (ptX F p) = p := by
    rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, hcoords, _, _, _, _, _⟩
    exact hcoords p hp
  have hEq : (fun q : Coord F =>
      ((u (coordsX F (ptX F q)) : ℝ) : ℂ)) =ᶠ[𝓝 p] (fun q => (u q : ℂ)) := by
    filter_upwards [c3_posSet_open.mem_nhds hp] with q hq
    rw [(G1_h3_basics (F := F)).2.2.2.2.2.2.1 q hq]
  have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 2).self_of_nhds
  dsimp [partialLap]
  simp only [Function.comp_def]
  rw [hcoords]
  simp only [placeDirection]
  rw [h1]
  rw [c3FDeriv_ofReal _ _ (hu.differentiable (by simp) p)]
  rw [h2]
  rw [c3IteratedFDeriv_ofReal p (Pi.single w (1, 0)) (Pi.single w (1, 0)) hu,
    c3IteratedFDeriv_ofReal p (Pi.single w (Complex.I, 0)) (Pi.single w (Complex.I, 0)) hu,
    c3IteratedFDeriv_ofReal p (Pi.single w (0, 1)) (Pi.single w (0, 1)) hu]
  simp only [c3Hessian_eq_iteratedFDeriv]

private theorem c3PartialLap_normHeightBase {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (p : Coord F) (hp : p ∈ posSet F) (w : InfinitePlace F) :
    partialLap F w (fun z => (ψ (normHeight F z) : ℂ)) (ptX F p) =
      ((c3CoordHeight p * deriv ψ (c3CoordHeight p) -
        c3CoordHeight p ^ 2 * deriv (deriv ψ) (c3CoordHeight p) : ℝ) : ℂ) := by
  let H : Coord F → ℝ := c3CoordHeight (F := F)
  let u : Coord F → ℝ := ψ ∘ H
  have hHs : ContDiff ℝ ∞ H := by
    dsimp [H]
    exact c3CoordHeightProd_smooth Finset.univ
  have hu : ContDiff ℝ ∞ u := hψ.comp hHs
  have hchart : (fun q : Coord F => ((ψ (normHeight F (ptX F q)) : ℝ) : ℂ)) =ᶠ[𝓝 p]
      (fun q => (u q : ℂ)) := by
    filter_upwards [c3_posSet_open.mem_nhds hp] with q hq
    rw [c3NormHeight_ptX q hq]
    rfl
  have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hchart
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hchart 2).self_of_nhds
  have hψder : ContDiff ℝ ∞ (deriv ψ) := hψ.deriv'
  have hψHas (t : ℝ) : HasDerivAt ψ (deriv ψ t) t :=
    (hψ.differentiable (by simp) t).hasDerivAt
  have hψderHas (t : ℝ) : HasDerivAt (deriv ψ) (deriv (deriv ψ) t) t :=
    (hψder.differentiable (by simp) t).hasDerivAt
  have hHgrad (j : Fin 3) :
      fderiv ℝ H p (placeDirection F w j) =
        if j = 2 then ∏ v ∈ Finset.univ.erase w, c3CoordY (F := F) v p else 0 := by
    rw [show H = c3CoordHeightProd (F := F) Finset.univ by
      funext q; simp [H, c3CoordHeight, c3CoordHeightProd, c3CoordY]]
    rw [c3CoordHeightProd_fderiv]
    by_cases hj : j = 2
    · simp [hj]
    · simp [hj]
  have hHhess (j : Fin 3) :
      c3Hessian H p (placeDirection F w j) (placeDirection F w j) = 0 := by
    rw [show H = c3CoordHeightProd (F := F) Finset.univ by
      funext q; simp [H, c3CoordHeight, c3CoordHeightProd, c3CoordY]]
    exact c3CoordHeightProd_hessian Finset.univ w j p
  have hHderivErase :
      (p w).2 * (∏ v ∈ Finset.univ.erase w, c3CoordY (F := F) v p) = H p := by
    rw [show H = c3CoordHeightProd (F := F) Finset.univ by
      funext q; simp [H, c3CoordHeight, c3CoordHeightProd, c3CoordY]]
    change (p w).2 * (∏ v ∈ Finset.univ.erase w, c3CoordY (F := F) v p) =
      ∏ v ∈ Finset.univ, c3CoordY (F := F) v p
    exact Finset.mul_prod_erase Finset.univ (fun v => c3CoordY (F := F) v p)
      (Finset.mem_univ w)
  have hUgrad (j : Fin 3) :
      fderiv ℝ u p (placeDirection F w j) =
        deriv ψ (H p) * fderiv ℝ H p (placeDirection F w j) := by
    exact c3FDeriv_realCompAt p (placeDirection F w j)
      (hHs.differentiable (by simp) p) hψHas
  have hUhess (j : Fin 3) :
      c3Hessian u p (placeDirection F w j) (placeDirection F w j) =
        deriv (deriv ψ) (H p) *
          fderiv ℝ H p (placeDirection F w j) *
          fderiv ℝ H p (placeDirection F w j) +
        deriv ψ (H p) * c3Hessian H p (placeDirection F w j) (placeDirection F w j) := by
    exact c3Hessian_scalar_comp hHs hψHas hψderHas p _ _
  have hreal : partialLap F w (fun z => (u (coordsX F z) : ℂ)) (ptX F p) =
      ((H p * deriv ψ (H p) - H p ^ 2 * deriv (deriv ψ) (H p) : ℝ) : ℂ) := by
    rw [c3PartialLap_realChart u hu p hp w]
    rw [hUgrad 2]
    rw [hUhess 0, hUhess 1, hUhess 2]
    simp_rw [hHhess, hHgrad]
    push_cast
    have hprodC :
        (↑(p w).2 : ℂ) *
            (∏ i ∈ Finset.univ.erase w, (c3CoordY (F := F) i p : ℂ)) =
          (H p : ℂ) := by
      exact_mod_cast hHderivErase
    have hfirst :
        (↑(p w).2 : ℂ) *
            (((deriv (ψ : ℝ → ℝ) (H p) : ℝ) : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (c3CoordY (F := F) i p : ℂ)) =
          (H p : ℂ) * ((deriv (ψ : ℝ → ℝ) (H p) : ℝ) : ℂ) := by
      calc
        _ = ((deriv (ψ : ℝ → ℝ) (H p) : ℝ) : ℂ) *
            ((↑(p w).2 : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (c3CoordY (F := F) i p : ℂ)) := by ring
        _ = _ := by rw [hprodC]; ring
    have hsecond :
        (↑(p w).2 : ℂ) ^ 2 *
            (((deriv (deriv (ψ : ℝ → ℝ) : ℝ → ℝ) (H p) : ℝ) : ℂ) *
              (∏ i ∈ Finset.univ.erase w, (c3CoordY (F := F) i p : ℂ)) ^ 2) =
          (H p : ℂ) ^ 2 * ((deriv (deriv (ψ : ℝ → ℝ) : ℝ → ℝ) (H p) : ℝ) : ℂ) := by
      calc
        _ = ((deriv (deriv (ψ : ℝ → ℝ) : ℝ → ℝ) (H p) : ℝ) : ℂ) *
            ((↑(p w).2 : ℂ) *
              ∏ i ∈ Finset.univ.erase w, (c3CoordY (F := F) i p : ℂ)) ^ 2 := by ring
        _ = _ := by rw [hprodC]; ring
    ring_nf
    linear_combination hfirst - hsecond
  have hfun : (fun z => (ψ (normHeight F z) : ℂ)) =
      (fun z => (u (coordsX F z) : ℂ)) := by
    funext z
    have hpz : coordsX F z ∈ posSet F := by
      intro w
      change 0 < height (z w)
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
    have hptz : ptX F (coordsX F z) = z := by
      rcases G1_h3_basics (F := F) with
        ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
      exact hpt z
    have hnormz : normHeight F z = c3CoordHeight (coordsX F z) := by
      calc
        normHeight F z = normHeight F (ptX F (coordsX F z)) :=
          congrArg (normHeight F) hptz.symm
        _ = c3CoordHeight (coordsX F z) := c3NormHeight_ptX (coordsX F z) hpz
    exact congrArg (fun t : ℝ => (ψ t : ℂ)) hnormz
  rw [hfun]
  simpa [H, u] using hreal

private theorem c3PartialLap_normHeight_at {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (z : X F) (w : InfinitePlace F) :
    partialLap F w (fun x => (ψ (normHeight F x) : ℂ)) z =
      ((normHeight F z * deriv ψ (normHeight F z) -
        normHeight F z ^ 2 * deriv (deriv ψ) (normHeight F z) : ℝ) : ℂ) := by
  let p := coordsX F z
  have hp : p ∈ posSet F := by
    intro w
    change 0 < height (z w)
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : ptX F p = z := by
    rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, hpt, _, _, _, _⟩
    exact hpt z
  have hN : c3CoordHeight (F := F) p = normHeight F z := by
    calc
      c3CoordHeight (F := F) p = normHeight F (ptX F p) := (c3NormHeight_ptX p hp).symm
      _ = normHeight F z := congrArg (normHeight F) hpt
  rw [← hpt]
  rw [c3PartialLap_normHeightBase ψ hψ p hp w]
  simp [hN, hpt]

private theorem c3PartialLap_normHeight_action {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (g : SL(2,F)) (z : X F) (w : InfinitePlace F) :
    partialLap F w (fun x => (ψ (normHeight F (g • x)) : ℂ)) z =
      ((normHeight F (g • z) * deriv ψ (normHeight F (g • z)) -
        normHeight F (g • z) ^ 2 * deriv (deriv ψ) (normHeight F (g • z)) : ℝ) : ℂ) := by
  let zero : X F → ℂ := fun _ => 0
  have hzsm : IsSmoothX F zero := by
    change ContDiffOn ℝ ∞ (fun _ => (0 : ℂ)) (posSet F)
    exact contDiffOn_const
  have hzcompact : HasCompactSupportX F zero := by
    refine ⟨∅, isCompact_empty, ?_⟩
    simp [zero]
  have h0 := G5_green_x zero zero hzsm hzsm hzcompact
  let F₀ : X F → ℂ := fun x => (ψ (normHeight F x) : ℂ)
  have hF₀ : IsSmoothX F F₀ := by
    change ContDiffOn ℝ ∞ (fun p => (ψ (normHeight F (ptX F p)) : ℂ)) (posSet F)
    have hnorm : IsSmoothRealX F (normHeight F) := by
      change ContDiffOn ℝ ∞ (fun p => normHeight F (ptX F p)) (posSet F)
      have hprod : ContDiff ℝ ∞ (c3CoordHeight (F := F)) := by
        rw [show c3CoordHeight (F := F) = c3CoordHeightProd (F := F) Finset.univ by
          funext q; simp [c3CoordHeight, c3CoordHeightProd, c3CoordY]]
        exact c3CoordHeightProd_smooth Finset.univ
      apply hprod.contDiffOn.congr
      intro p hp
      exact c3NormHeight_ptX p hp
    have hreal : ContDiffOn ℝ ∞ (fun p => ψ (normHeight F (ptX F p))) (posSet F) :=
      hψ.comp_contDiffOn hnorm
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hreal
  let gPlaces : InfinitePlace F → SL(2,ℂ) := toInf F g
  have hcomm := h0.2.2 gPlaces F₀ hF₀ w z
  calc
    partialLap F w (fun x => (ψ (normHeight F (g • x)) : ℂ)) z =
        partialLap F w (fun x => F₀ (actAtPlaces F gPlaces x)) z := by rfl
    _ = partialLap F w F₀ (actAtPlaces F gPlaces z) := hcomm
    _ = _ := by
      rw [show actAtPlaces F gPlaces z = g • z from rfl]
      exact c3PartialLap_normHeight_at ψ hψ (g • z) w

private theorem c3_cuspStab_normHeight {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (δ : cuspStab F Γ σ) (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) :
    normHeight F (σ⁻¹ • ((δ.1 : SL(2,𝓞 F)) • (σ • ptX' F x y))) = ∏ w, y w := by
  obtain ⟨ε, hε, μ, hform⟩ := cuspStab_unit_form Γ σ δ
  have hmove := c3_cusp_conjugate_action Γ σ δ.1 (cuspUnitMatrix F ε μ) hform
    (ptX' F x y)
  have hEmbed (w : InfinitePlace F) :
      w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) ≠ 0 := by
    intro h
    apply ε.ne_zero
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    apply w.embedding.injective
    simpa using h
  have hy' : ∀ w, 0 < unitHeightAction F ε y w := by
    intro w
    unfold unitHeightAction
    exact mul_pos (Complex.normSq_pos.mpr (hEmbed w)) (hy w)
  calc
    normHeight F (σ⁻¹ • ((δ.1 : SL(2,𝓞 F)) • (σ • ptX' F x y))) =
        normHeight F (cuspUnitMatrix F ε μ • ptX' F x y) := by
          rw [hmove]
          simp
    _ = normHeight F
        (ptX' F (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
          w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
          (unitHeightAction F ε y)) := by rw [c3_cuspUnitMatrix_action ε μ x y hy]
    _ = ∏ w, unitHeightAction F ε y w := c3_normHeight_ptX' _ _ hy'
    _ = ∏ w, y w := c3_unitHeightAction_product ε y

private theorem c3_cuspStab_normHeight_action {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (δ : cuspStab F Γ σ) (z : X F) :
    normHeight F (σ⁻¹ • ((δ.1 : SL(2,𝓞 F)) • (σ • z))) =
      normHeight F z := by
  have htri : σ⁻¹ * toSLF F (δ.1 : SL(2,𝓞 F)) * σ ∈ borelSL F := by
    simpa [cuspStab, MulAut.conj_apply] using δ.property
  let b : SL(2,F) := σ⁻¹ * toSLF F (δ.1 : SL(2,𝓞 F)) * σ
  have hform : σ⁻¹ * toSLF F (δ.1 : SL(2,𝓞 F)) * σ = b := rfl
  have hmove := c3_cusp_conjugate_action Γ σ δ.1 b hform z
  have hnorm := ((G2_x_action (F := F)).2.2.1 (δ.1 : SL(2,𝓞 F)) σ htri).2
  calc
    normHeight F (σ⁻¹ • ((δ.1 : SL(2,𝓞 F)) • (σ • z))) =
        normHeight F (σ⁻¹ • (σ • (b • z))) := by rw [hmove]
    _ = normHeight F (b • z) := by simp
    _ = normHeight F z := hnorm z

private theorem c3_normHeight_pos {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (z : X F) : 0 < normHeight F z := by
  unfold normHeight
  apply Finset.prod_pos
  intro w hw
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private def c3_identityCuspCoset {F : Type} [Field F] [NumberField F]
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) : CuspCosets F Γ σ :=
  Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (1 : Γ)

private theorem c3_identityCuspCoset_stab {F : Type} [Field F] [NumberField F]
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) :
    (c3_identityCuspCoset Γ σ).out ∈ cuspStab F Γ σ := by
  let q₀ := c3_identityCuspCoset Γ σ
  have hrel : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (1 : Γ) =
      Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q₀.out := by
    calc
      _ = q₀ := rfl
      _ = _ := (Quotient.out_eq' q₀).symm
  have hmem : q₀.out ∈ cuspStab F Γ σ := by
    simpa using
      (QuotientGroup.rightRel_apply.mp (Quotient.exact hrel))
  simpa [q₀] using hmem

private theorem c3_identityCuspCoset_height {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (z : X F) :
    c3_cosetHeight (c3_identityCuspCoset Γ σ) z = normHeight F (σ⁻¹ • z) := by
  let q₀ := c3_identityCuspCoset Γ σ
  have hstab : q₀.out ∈ cuspStab F Γ σ := c3_identityCuspCoset_stab Γ σ
  have h := c3_cuspStab_normHeight_action Γ σ ⟨q₀.out, hstab⟩ (σ⁻¹ • z)
  simpa [c3_cosetHeight, q₀, c3_identityCuspCoset] using h

private theorem c3_seed_eq_identity_on_high_cusp
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (A₀ A : ℝ)
    (hA₀A : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) (s : ℂ) (z : X F)
    (hz : A₀ < normHeight F (σ⁻¹ • z)) :
    eisSeed F Γ σ τ s z =
      seedTerm F Γ σ τ s z (c3_identityCuspCoset Γ σ) := by
  classical
  let q₀ := c3_identityCuspCoset Γ σ
  have htermZero (q : CuspCosets F Γ σ) (hq : q ≠ q₀) :
      seedTerm F Γ σ τ s z q = 0 := by
    by_contra hzero
    have hτne : τ (c3_cosetHeight q z) ≠ 0 := by
      intro hτzero
      apply hzero
      have hτzero' : τ
          (normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))) = 0 := by
        simpa [c3_cosetHeight] using hτzero
      simp [seedTerm, hτzero']
    have hgt : A < c3_cosetHeight q z := by
      by_contra hle
      exact hτne (hτ.2.2.1 _ (le_of_not_gt hle))
    have hqA₀ : A₀ ≤ c3_cosetHeight q z := hA₀A.trans hgt.le
    have hstabInv : (1 : Γ) * q.out⁻¹ ∈ cuspStab F Γ σ := by
      simpa using hsep q.out 1 z hqA₀ (by simpa using hz.le)
    have hrel : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out =
        Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (1 : Γ) :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr hstabInv)
    have hqeq : q = q₀ := by
      calc
        q = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out :=
          (Quotient.out_eq q).symm
        _ = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (1 : Γ) := hrel
        _ = q₀ := rfl
    exact hq hqeq
  unfold eisSeed
  exact tsum_eq_single q₀ htermZero

private theorem c3_seedTerm_identity_eq_radial
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2,𝓞 F)} {σ : SL(2,F)} {A₀ A : ℝ}
    {τ : ℝ → ℝ} (hA : 0 < A) (hτ : IsCuspCutoff A τ)
    (s₁ : ℝ) (z : X F) :
    seedTerm F Γ σ τ (s₁ : ℂ) z (c3_identityCuspCoset Γ σ) =
      ((c3CutoffRadialWeight A τ (1 + 2 * s₁)
        (normHeight F (σ⁻¹ • z)) : ℝ) : ℂ) := by
  let q₀ := c3_identityCuspCoset Γ σ
  let H := normHeight F (σ⁻¹ • z)
  have hq₀ : c3_cosetHeight q₀ z = H := c3_identityCuspCoset_height Γ σ z
  have hH : 0 < H := c3_normHeight_pos (σ⁻¹ • z)
  have hexp : (1 : ℂ) + 2 * (s₁ : ℂ) = ((1 + 2 * s₁ : ℝ) : ℂ) := by
    push_cast
    ring
  have hpow : ((H : ℂ) ^ (1 + 2 * (s₁ : ℂ))) =
      (((H ^ (1 + 2 * s₁) : ℝ) : ℂ)) := by
    rw [hexp]
    exact (Complex.ofReal_cpow hH.le (1 + 2 * s₁)).symm
  change ((τ (c3_cosetHeight q₀ z) : ℝ) : ℂ) *
      ((c3_cosetHeight q₀ z : ℝ) : ℂ) ^ (1 + 2 * (s₁ : ℂ)) =
    ((c3CutoffRadialWeight A τ (1 + 2 * s₁) H : ℝ) : ℂ)
  rw [hq₀, hpow]
  have hraw := c3CutoffRadialWeight_eq_raw hA hτ (1 + 2 * s₁) H
  calc
    ((τ H : ℝ) : ℂ) * ((H ^ (1 + 2 * s₁) : ℝ) : ℂ) =
        ((τ H * H ^ (1 + 2 * s₁) : ℝ) : ℂ) := (Complex.ofReal_mul _ _).symm
    _ = ((c3CutoffRadialWeight A τ (1 + 2 * s₁) H : ℝ) : ℂ) :=
      congrArg Complex.ofReal hraw.symm

private theorem c3_radialLaplacianCoefficient {A : ℝ} (hA : 0 < A)
    {τ : ℝ → ℝ} (hτ : IsCuspCutoff A τ) (s₁ T : ℝ)
    (hs : 0 < s₁) (hT : A / 2 < T) :
    T * deriv (c3CutoffRadialWeight A τ (1 + 2 * s₁)) T -
        T ^ 2 * deriv (deriv (c3CutoffRadialWeight A τ (1 + 2 * s₁))) T -
          (1 - 4 * s₁ ^ 2) * c3CutoffRadialWeight A τ (1 + 2 * s₁) T =
      -((T ^ 2 * deriv (deriv τ) T + (1 + 4 * s₁) * T * deriv τ T) *
        T ^ (1 + 2 * s₁)) := by
  let a : ℝ := 1 + 2 * s₁
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hTpos : 0 < T := lt_trans (by linarith [hA]) hT
  have hTne : T ≠ 0 := hTpos.ne'
  have hψ1 := c3_cutoffRadialWeight_deriv_at hA hτ (a := a) (t := T) ha hT
  have hψ2 := c3_cutoffRadialWeight_secondDeriv_at hA hτ
    (a := a) (t := T) ha hT hTne
  have hψ0 := c3CutoffRadialWeight_eq_raw hA hτ a T
  have hpow1 : T ^ (a - 1) = T ^ a / T := by
    simpa [pow_one] using Real.rpow_sub hTpos a 1
  have hpow2 : T ^ (a - 2) = T ^ a / T ^ 2 := by
    simpa [pow_two] using Real.rpow_sub hTpos a 2
  have hparam : 1 - 4 * s₁ ^ 2 = a * (2 - a) := by dsimp [a]; ring
  rw [hψ1, hψ2, hψ0, hpow1, hpow2, hparam]
  field_simp [hTne]
  ring

private theorem c3_eisSeed_eq_identity_on_high_cusp
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (A₀ A : ℝ)
    (hA₀A : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) (s : ℂ) (z : X F)
    (hz : A₀ < normHeight F (σ⁻¹ • z)) :
    eisSeed F Γ σ τ s z =
      seedTerm F Γ σ τ s z (c3_identityCuspCoset Γ σ) := by
  classical
  let q₀ := c3_identityCuspCoset Γ σ
  have htermZero (q : CuspCosets F Γ σ) (hq : q ≠ q₀) :
      seedTerm F Γ σ τ s z q = 0 := by
    by_contra hzero
    have hτne : τ (c3_cosetHeight q z) ≠ 0 := by
      intro hτzero
      apply hzero
      have hτzero' : τ
          (normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))) = 0 := by
        simpa [c3_cosetHeight] using hτzero
      simp [seedTerm, hτzero']
    have hgt : A < c3_cosetHeight q z := by
      by_contra hle
      exact hτne (hτ.2.2.1 _ (le_of_not_gt hle))
    have hqA₀ : A₀ ≤ c3_cosetHeight q z := hA₀A.trans hgt.le
    have hstabInv : (1 : Γ) * q.out⁻¹ ∈ cuspStab F Γ σ := by
      simpa using hsep q.out 1 z hqA₀ (by simpa using hz.le)
    have hrel : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out =
        Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (1 : Γ) :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr hstabInv)
    have hqeq : q = q₀ := by
      calc
        q = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out :=
          (Quotient.out_eq q).symm
        _ = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (1 : Γ) := hrel
        _ = q₀ := rfl
    exact hq hqeq
  unfold eisSeed
  exact tsum_eq_single q₀ htermZero

private def c3RadialDefectCoefficient (τ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (t ^ 2 * deriv (deriv τ) t +
    (1 + 4 * s) * t * deriv τ t) *
      t ^ (1 + 2 * s)

private theorem c3_eisSeedDefect_radial_on_cusp
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (A₀ A : ℝ)
    (hA₀A : A₀ ≤ A) (hA : 0 < A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : IsCuspCutoff A τ) (s₁ : ℝ) (hs₁ : 0 < s₁)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w)
    (hT : A < ∏ w, y w) :
    eisSeedDefect F Γ σ τ (s₁ : ℂ) (σ • ptX' F x y) =
      (((-(placeCount F * c3RadialDefectCoefficient τ s₁ (∏ w, y w)) : ℝ) : ℂ)) := by
  let T : ℝ := ∏ w, y w
  let a : ℝ := 1 + 2 * s₁
  let ψ : ℝ → ℝ := c3CutoffRadialWeight A τ a
  let z : X F := σ • ptX' F x y
  have hTpos : 0 < T := Finset.prod_pos fun w hw => hy w
  have hHeight : normHeight F (σ⁻¹ • z) = T := by
    dsimp [z, T]
    calc
      normHeight F (σ⁻¹ • (σ • ptX' F x y)) = normHeight F (ptX' F x y) := by simp
      _ = ∏ w, y w := c3_normHeight_ptX' x y hy
  have hzHigh : A₀ < normHeight F (σ⁻¹ • z) := by rw [hHeight]; exact hA₀A.trans_lt hT
  let U : Set (X F) := {z' | A₀ < normHeight F (σ⁻¹ • z')}
  have hU : IsOpen U :=
    isOpen_lt continuous_const (c3_normHeight_action_continuous (F := F) σ⁻¹)
  have hzU : z ∈ U := hzHigh
  have hseedEq : ∀ z' ∈ U,
      eisSeed F Γ σ τ (s₁ : ℂ) z' =
        ((ψ (normHeight F (σ⁻¹ • z')) : ℝ) : ℂ) := by
    intro z' hz'
    calc
      eisSeed F Γ σ τ (s₁ : ℂ) z' =
          seedTerm F Γ σ τ (s₁ : ℂ) z' (c3_identityCuspCoset Γ σ) :=
        c3_eisSeed_eq_identity_on_high_cusp Γ σ A₀ A hA₀A hsep τ hτ
          (s₁ : ℂ) z' hz'
      _ = ((ψ (normHeight F (σ⁻¹ • z')) : ℝ) : ℂ) := by
        simpa [ψ, a] using c3_seedTerm_identity_eq_radial
          (Γ := Γ) (σ := σ) (A₀ := A₀) (A := A) hA hτ s₁ z'
  have hψsmooth : ContDiff ℝ ∞ ψ := c3CutoffRadialWeight_smooth hA hτ a
  have hpartial (w : InfinitePlace F) :
      partialLap F w (eisSeed F Γ σ τ (s₁ : ℂ)) z =
        ((T * deriv ψ T - T ^ 2 * deriv (deriv ψ) T : ℝ) : ℂ) := by
    calc
      partialLap F w (eisSeed F Γ σ τ (s₁ : ℂ)) z =
          partialLap F w (fun z' => ((ψ (normHeight F (σ⁻¹ • z')) : ℝ) : ℂ)) z :=
        c3_partialLap_congr_open w (eisSeed F Γ σ τ (s₁ : ℂ))
          (fun z' => ((ψ (normHeight F (σ⁻¹ • z')) : ℝ) : ℂ)) U hU hzU hseedEq
      _ = _ := by
        have h := c3PartialLap_normHeight_action ψ hψsmooth σ⁻¹ z w
        rw [hHeight] at h
        exact h
  have htotal : totalLap F (eisSeed F Γ σ τ (s₁ : ℂ)) z =
      ((placeCount F : ℝ) : ℂ) *
        ((T * deriv ψ T - T ^ 2 * deriv (deriv ψ) T : ℝ) : ℂ) := by
    unfold totalLap
    simp_rw [hpartial]
    simp [placeCount]
    ring
  have hseedAt : eisSeed F Γ σ τ (s₁ : ℂ) z = ((ψ T : ℝ) : ℂ) := by
    calc
      eisSeed F Γ σ τ (s₁ : ℂ) z =
          ((ψ (normHeight F (σ⁻¹ • z)) : ℝ) : ℂ) := hseedEq z hzU
      _ = ((ψ T : ℝ) : ℂ) := by rw [hHeight]
  have hradial := c3_radialLaplacianCoefficient hA hτ s₁ T hs₁
    (by dsimp [T]; linarith [hA, hT])
  have hcomplex : eisSeedDefect F Γ σ τ (s₁ : ℂ) z =
      ((placeCount F : ℝ) *
        ((T * deriv ψ T - T ^ 2 * deriv (deriv ψ) T) -
          (1 - 4 * s₁ ^ 2) * ψ T) : ℂ) := by
    rw [eisSeedDefect, htotal, hseedAt]
    simp [spectralParameter, placeCount, ψ, a, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_pow]
    ring
  have hradialFormula :
      T * deriv ψ T - T ^ 2 * deriv (deriv ψ) T -
          (1 - 4 * s₁ ^ 2) * ψ T =
        -c3RadialDefectCoefficient τ s₁ T := by
    simpa [ψ, a, c3RadialDefectCoefficient] using hradial
  have hradialMul : placeCount F *
      (T * deriv ψ T - T ^ 2 * deriv (deriv ψ) T -
        (1 - 4 * s₁ ^ 2) * ψ T) =
      -(placeCount F * c3RadialDefectCoefficient τ s₁ T) := by
    calc
      _ = placeCount F * (-c3RadialDefectCoefficient τ s₁ T) :=
        congrArg (fun q : ℝ => placeCount F * q) hradialFormula
      _ = _ := by ring
  have hradialC :
      ((placeCount F *
        (T * deriv ψ T - T ^ 2 * deriv (deriv ψ) T -
          (1 - 4 * s₁ ^ 2) * ψ T) : ℝ) : ℂ) =
        ((-(placeCount F * c3RadialDefectCoefficient τ s₁ T) : ℝ) : ℂ) :=
    congrArg Complex.ofReal hradialMul
  rw [hcomplex]
  exact_mod_cast hradialMul

private theorem c3_cuspTranslation_realized {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (t : cuspTranslationExtensionComplex F Γ σ) :
    ∃ γ : Γ, ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
      (∀ w, 0 < y w) →
      (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) =
        σ • ptX' F (x + (t : InfinitePlace F → ℂ)) y := by
  rcases AddSubgroup.mem_map.mp t.property with ⟨μ, hμ, ht⟩
  rcases ((R1_cusp_lattice Γ σ).2.2.1 μ).mp hμ with ⟨ε, hε, γ, hγ⟩
  refine ⟨γ, ?_⟩
  intro x y hy
  rw [c3_cusp_conjugate_action Γ σ γ _ hγ, c3_signedMatrix_action ε μ hε x y hy]
  have ht' : (fun w : InfinitePlace F => w.embedding μ) = (t : InfinitePlace F → ℂ) := ht
  rw [← ht']
  rfl

private theorem c3_integrableOn_bounded_continuous
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (S : Set (InfinitePlace F → ℂ)) (hSmeas : MeasurableSet S)
    (hSbound : Bornology.IsBounded S) (f : (InfinitePlace F → ℂ) → ℂ)
    (hf : Continuous f) : IntegrableOn f S volume := by
  letI : Finite (InfinitePlace F) := inferInstance
  letI : Countable (InfinitePlace F) := Finite.to_countable
  letI : ProperSpace (InfinitePlace F → ℂ) := inferInstance
  have hclose : IsCompact (closure S) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hSbound.closure⟩
  have hmeasure : volume S ≠ (⊤ : ENNReal) := by
    apply ne_of_lt
    exact (measure_mono subset_closure).trans_lt hclose.measure_lt_top
  obtain ⟨M, hM⟩ := hclose.exists_bound_of_continuousOn (f := f) hf.continuousOn
  apply Measure.integrableOn_of_bounded hmeasure hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hSmeas] with x hx
  exact hM x (subset_closure hx)

private theorem c3_setIntegral_translate
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (a : InfinitePlace F → ℂ) (S : Set (InfinitePlace F → ℂ))
    (hSmeas : MeasurableSet S) (f : (InfinitePlace F → ℂ) → ℂ)
    (hf : ∀ x, f (a + x) = f x) :
    ∫ x in a +ᵥ S, f x ∂volume = ∫ x in S, f x ∂volume := by
  have himage : a +ᵥ S = (fun x : InfinitePlace F → ℂ => a + x) '' S := by
    ext x
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm]
  rw [himage]
  calc
    ∫ x in (fun x : InfinitePlace F → ℂ => a + x) '' S, f x ∂volume =
        ∫ x in S, f (a + x) ∂volume :=
      (measurePreserving_add_left volume a).setIntegral_image_emb
        (measurableEmbedding_addLeft a) f S
    _ = ∫ x in S, f x ∂volume :=
      setIntegral_congr_fun hSmeas (fun x hx => hf x)

private theorem c3_continuous_of_smooth
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (f : X F → ℂ) (hf : IsSmoothX F f) : Continuous f := by
  obtain ⟨e, he, _⟩ := c3_chartEquiv (F := F)
  have hp : Continuous (fun z : X F => (e.symm z).1) :=
    continuous_subtype_val.comp e.symm.continuous
  have hmaps : ∀ z, (e.symm z).1 ∈ posSet F := fun z => (e.symm z).property
  have hcont : Continuous (fun z : X F => f (ptX F (e.symm z).1)) :=
    hf.continuousOn.comp_continuous hp hmaps
  have heq : f = fun z => f (ptX F (e.symm z).1) := by
    funext z
    have hz : ptX F ((e.symm z).1) = z := by
      calc
        _ = e (e.symm z) := (he (e.symm z)).symm
        _ = z := e.apply_symm_apply z
    exact congrArg f hz |>.symm
  rw [heq]
  exact hcont

private theorem c3_continuous_ptX'_horizontal
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    Continuous (fun x : InfinitePlace F → ℂ => ptX' F x y) := by
  obtain ⟨e, he, _⟩ := c3_chartEquiv (F := F)
  let p : (InfinitePlace F → ℂ) → Coord F := fun x w => (x w, y w)
  have hp : Continuous p := by fun_prop
  have hpPos (x : InfinitePlace F → ℂ) : p x ∈ posSet F := fun w => hy w
  have hpSub : Continuous (fun x => (⟨p x, hpPos x⟩ : {p : Coord F // p ∈ posSet F})) :=
    hp.subtype_mk hpPos
  have heq : (fun x : InfinitePlace F → ℂ => ptX' F x y) =
      fun x => e (⟨p x, hpPos x⟩) := by
    funext x
    calc
      ptX' F x y = ptX F (p x) := by
        funext w
        rfl
      _ = e ⟨p x, hpPos x⟩ := (he ⟨p x, hpPos x⟩).symm
  rw [heq]
  exact e.continuous.comp hpSub

private def c3_residueTheta
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2,𝓞 F)} {ι : Type} [Fintype ι]
    (s₁ : ℝ) (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁)
    (c : ι → ℂ) (z : X F) : ℂ := ∑ i, c i * (d i).res z

private theorem c3_memLp_of_integrable_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (f : α → E) (hf : AEStronglyMeasurable f μ)
    (hint : Integrable (fun x => ‖f x‖ ^ 2) μ) : MemLp f 2 μ := by
  rw [← integrable_norm_rpow_iff hf (by norm_num) (by norm_num)]
  simpa using hint

private theorem c3_l2Lift_eq_on_D
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F)) (u : L2Space F D) :
    ∀ᵐ z ∂(volX F), z ∈ D → l2Lift F Γ D u z = u z := by
  classical
  have hRow : Countable (Fin 2 → 𝓞 F) := by
    have hset : (Set.univ : Set (Fin 2 → 𝓞 F)).Countable := by
      have h := Set.countable_univ_pi (π := fun _ : Fin 2 => 𝓞 F)
        (s := fun _ => Set.univ) (by intro i; exact Set.countable_univ)
      simpa using h
    letI : Countable (↥(Set.univ : Set (Fin 2 → 𝓞 F))) := hset.to_subtype
    exact Countable.of_equiv _ (Equiv.Set.univ _)
  have hMatrix : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    letI : Countable (Fin 2 → 𝓞 F) := hRow
    have hset : (Set.univ : Set (Matrix (Fin 2) (Fin 2) (𝓞 F))).Countable := by
      have h := Set.countable_univ_pi (π := fun _ : Fin 2 => (Fin 2 → 𝓞 F))
        (s := fun _ => Set.univ) (by intro i; exact Set.countable_univ)
      simpa [Matrix] using h
    letI : Countable (↥(Set.univ : Set (Matrix (Fin 2) (Fin 2) (𝓞 F)))) :=
      hset.to_subtype
    exact Countable.of_equiv _ (Equiv.Set.univ _)
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := hMatrix
  letI : Countable (SL(2,𝓞 F)) := Subtype.val_injective.countable
  letI : Countable Γ := Subtype.val_injective.countable
  have hUnique : ∀ᵐ z ∂(volX F).restrict D, ∀ γ : Γ,
      (γ : SL(2,𝓞 F)) • z ∈ D → γ = 1 := by
    rw [ae_all_iff]
    intro γ
    by_cases hγ : γ = 1
    · filter_upwards [] with z hz
      exact hγ
    · have hne : (1 : Γ) ≠ γ⁻¹ := by
        intro h
        have h' := congrArg (fun x : Γ => x⁻¹) h
        have h'' : (1 : Γ) = γ := by simpa using h'
        exact hγ h''.symm
      have hdisj : AEDisjoint (volX F) D ((γ⁻¹ : Γ) • D) := by
        have h := hD.aedisjoint hne
        change AEDisjoint (volX F) ((1 : Γ) • D) ((γ⁻¹ : Γ) • D) at h
        simpa using h
      have hNo : ∀ᵐ z ∂(volX F), z ∈ D → z ∉ (γ⁻¹ : Γ) • D := by
        filter_upwards [hdisj.sdiff_ae_eq_left] with z hzDiff
        intro hzD
        exact (hzDiff.mpr hzD).2
      have hNoRestrict : ∀ᵐ z ∂(volX F).restrict D,
          z ∉ (γ⁻¹ : Γ) • D := by
        filter_upwards [hNo.filter_mono ae_restrict_le,
          ae_restrict_mem₀ hD.nullMeasurableSet] with z hzNo hzD
        exact hzNo hzD
      filter_upwards [hNoRestrict] with z hzNo hzγ
      have hzInv : z ∈ (γ⁻¹ : Γ) • D := by
        refine Set.mem_smul_set.mpr ⟨(γ : SL(2,𝓞 F)) • z, hzγ, ?_⟩
        change ((γ⁻¹ : Γ) : SL(2,𝓞 F)) •
          ((γ : SL(2,𝓞 F)) • z) = z
        simp
      exact False.elim (hzNo hzInv)
  have hEqRestrict : ∀ᵐ z ∂(volX F).restrict D,
      l2Lift F Γ D u z = u z := by
    filter_upwards [hUnique, ae_restrict_mem₀ hD.nullMeasurableSet] with z hzUnique hzD
    change (∑' γ : Γ,
        if (γ : SL(2,𝓞 F)) • z ∈ D then u ((γ : SL(2,𝓞 F)) • z) else 0) = u z
    rw [tsum_eq_single (1 : Γ)]
    · simp [hzD]
    · intro γ hγ
      have hnot : (γ : SL(2,𝓞 F)) • z ∉ D := by
        intro hmem
        exact hγ (hzUnique γ hmem)
      simp [hnot]
  exact (ae_restrict_iff'₀ hD.nullMeasurableSet).mp hEqRestrict

private theorem c3_residueTheta_memLp
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F))
    (s₁ : ℝ) {ι : Type} [Fintype ι] (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁) (c : ι → ℂ) :
    MemLp (c3_residueTheta s₁ σ d c) 2 ((volX F).restrict D) := by
  classical
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  let μD := (volX F).restrict D
  have hresMem (i : ι) : MemLp (d i).res 2 μD := by
    have hmeas : AEStronglyMeasurable (d i).res μD := by
      exact (c3_continuous_of_smooth (d i).res (d i).res_smooth).aestronglyMeasurable
    apply c3_memLp_of_integrable_sq μD (d i).res hmeas
    change IntegrableOn (fun z => ‖(d i).res z‖ ^ 2) D (volX F)
    exact (d i).res_sq D hD
  have hterm (i : ι) : MemLp (fun z => c i * (d i).res z) 2 μD :=
    (hresMem i).const_mul (c i)
  have hsum₀ := memLp_finsetSum' (Finset.univ : Finset ι)
    (fun i hi => hterm i)
  have hsum : MemLp (fun z => ∑ i, c i * (d i).res z) 2 μD := by
    convert hsum₀ using 1
    funext z
    simp
  change MemLp (fun z => ∑ i, c i * (d i).res z) 2
    ((volX F).restrict D)
  exact hsum

private theorem c3_source_mul_integrableOn
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) (D : Set (X F))
    (hD : IsFundamentalDomain Γ D (volX F))
    (u : L2Space F D) (source f : X F → ℂ)
    (hsource : ∀ᵐ z ∂(volX F), z ∈ D → u z = source z)
    (hf : Continuous f)
    (hfSq : IntegrableOn (fun z => ‖f z‖ ^ 2) D (volX F)) :
    IntegrableOn (fun z => star (source z) * f z) D (volX F) := by
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  let μD := (volX F).restrict D
  have huMem : MemLp u 2 μD := Lp.memLp u
  have huSq : Integrable (fun z => ‖u z‖ ^ 2) μD :=
    huMem.integrable_norm_pow (by norm_num)
  have hsourceD : u =ᵐ[μD] source := by
    change u =ᵐ[(volX F).restrict D] source
    exact (ae_restrict_iff'₀ hD.nullMeasurableSet).2 hsource
  have hsourceSq : Integrable (fun z => ‖source z‖ ^ 2) μD := by
    apply huSq.congr
    filter_upwards [hsourceD] with z hz
    rw [hz]
  have hsourceMeas : AEStronglyMeasurable source μD := by
    exact huMem.aestronglyMeasurable.congr hsourceD
  have hsourceMem : MemLp source 2 μD :=
    c3_memLp_of_integrable_sq μD source hsourceMeas hsourceSq
  have hfMeas : AEStronglyMeasurable f μD := hf.aestronglyMeasurable
  have hfMem : MemLp f 2 μD := by
    apply c3_memLp_of_integrable_sq μD f hfMeas
    change Integrable (fun z => ‖f z‖ ^ 2) μD
    exact hfSq
  have hprod : Integrable (fun z => star (source z) * f z) μD :=
    hsourceMem.star.integrable_mul hfMem
  change IntegrableOn (fun z => star (source z) * f z) D (volX F)
  exact hprod

private theorem c3_hct_zero_on_extension_fd
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w)
    (f : X F → ℂ) (hfInv : IsGammaInvariant F Γ f)
    (hfcont : Continuous (fun x => f (σ • ptX' F x y)))
    (hct : ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P ∧
        ∫ x in P, f (σ • ptX' F x y) ∂volume = 0)
    (P' : Set (InfinitePlace F → ℂ))
    (hP' : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P')
    (hP'meas : MeasurableSet P') (hP'bound : Bornology.IsBounded P') :
    ∫ x in P', f (σ • ptX' F x y) ∂volume = 0 := by
  classical
  let H := cuspTranslations F Γ σ
  let G := cuspTranslationExtensionComplex F Γ σ
  letI : Countable H := by
    change Countable ((cuspLattice F Γ σ).map (infEmb F).toAddMonoidHom)
    exact c3_countable_addSubgroup_image (cuspLattice F Γ σ)
  letI : Countable G := by
    change Countable ((cuspTranslationExtension F Γ σ).map (infEmb F).toAddMonoidHom)
    exact c3_countable_addSubgroup_image (cuspTranslationExtension F Γ σ)
  let φ : (InfinitePlace F → ℂ) → ℂ := fun x => f (σ • ptX' F x y)
  have hφInvExt : ∀ t : G, ∀ x, φ ((t : InfinitePlace F → ℂ) + x) = φ x := by
    intro t x
    obtain ⟨γ, hγ⟩ := c3_cuspTranslation_realized Γ σ t
    have hact := hγ x y hy
    have hcomm : (t : InfinitePlace F → ℂ) + x = x + (t : InfinitePlace F → ℂ) := by abel
    change f (σ • ptX' F ((t : InfinitePlace F → ℂ) + x) y) =
      f (σ • ptX' F x y)
    rw [hcomm, ← hact]
    exact hfInv γ γ.property (σ • ptX' F x y)
  have hφInvOrd : ∀ t : H, ∀ x, φ ((t : InfinitePlace F → ℂ) + x) = φ x := by
    intro t x
    have ht : (t : InfinitePlace F → ℂ) ∈ G := by
      rcases AddSubgroup.mem_map.mp t.property with ⟨μ, hμ, hμt⟩
      rw [hμt.symm]
      apply AddSubgroup.mem_map.mpr
      exact ⟨μ, (R1_cusp_lattice Γ σ).2.2.2.1.2.1 hμ, rfl⟩
    exact hφInvExt ⟨t, ht⟩ x
  obtain ⟨P, hP, hPzero⟩ := hct
  obtain ⟨μ₀, hμ₀, hcoset⟩ := (R1_cusp_lattice Γ σ).2.2.2.1.2.2
  by_cases hμ₀ord : μ₀ ∈ cuspLattice F Γ σ
  · have hExtOrd : cuspTranslationExtension F Γ σ ≤ cuspLattice F Γ σ := by
      intro μ hμ
      rcases hcoset μ hμ with hμord | hμdiff
      · exact hμord
      · have heq : μ = (μ - μ₀) + μ₀ := by abel
        rw [heq]
        exact (cuspLattice F Γ σ).add_mem hμdiff hμ₀ord
    have hOrdExt : cuspLattice F Γ σ ≤ cuspTranslationExtension F Γ σ :=
      (R1_cusp_lattice Γ σ).2.2.2.1.2.1
    have hEq : cuspTranslationExtension F Γ σ = cuspLattice F Γ σ :=
      le_antisymm hExtOrd hOrdExt
    have hGroups : H = G := by
      dsimp [H, G, cuspTranslations, cuspTranslationExtensionComplex]
      rw [hEq]
    have hP'ord : IsAddFundamentalDomain H P' := by
      rw [hGroups]
      exact hP'
    have hP'int : IntegrableOn φ P' volume :=
      c3_integrableOn_bounded_continuous P' hP'meas hP'bound φ hfcont
    have hEqInt := hP'ord.setIntegral_eq hP hφInvOrd
    rw [hEqInt, hPzero]
  · let v₀ : InfinitePlace F → ℂ := infEmb F μ₀
    have hμ₀not : μ₀ ∉ cuspLattice F Γ σ := hμ₀ord
    obtain ⟨hQ, hQbound, hQmeas⟩ := c3_ordinaryFundamentalDomain_of_extension
      Γ σ P' hP' hP'meas hP'bound μ₀ hμ₀ hcoset hμ₀not
    let Q : Set (InfinitePlace F → ℂ) := P' ∪ (-v₀ +ᵥ P')
    have hQint : IntegrableOn φ Q volume :=
      c3_integrableOn_bounded_continuous Q hQmeas hQbound φ hfcont
    have hQzero : ∫ x in Q, φ x ∂volume = 0 := by
      have hEqInt := hQ.setIntegral_eq hP hφInvOrd
      rw [hEqInt, hPzero]
    have hv₀G : v₀ ∈ G := AddSubgroup.mem_map.mpr ⟨μ₀, hμ₀, rfl⟩
    let v₀G : G := ⟨v₀, hv₀G⟩
    have hv₀Gne : v₀G ≠ 0 := by
      intro hzero
      have hv₀ : v₀ = 0 := by simpa [v₀G] using congrArg Subtype.val hzero
      have hμ₀zero : μ₀ = 0 := by
        apply (infEmb F).injective
        simpa [v₀] using hv₀
      exact hμ₀not (by rw [hμ₀zero]; exact (cuspLattice F Γ σ).zero_mem)
    have hdisj : AEDisjoint volume P' (-v₀ +ᵥ P') := by
      have hne : (0 : G) ≠ -v₀G := by
        intro hzero
        apply hv₀Gne
        exact neg_eq_zero.mp hzero.symm
      have htmp := hP'.aedisjoint (i := (0 : G)) (j := -v₀G) hne
      change AEDisjoint volume ((0 : G) +ᵥ P') ((-v₀G) +ᵥ P') at htmp
      have hshift : ((-v₀G : G) +ᵥ P') = (-v₀ +ᵥ P') := by
        ext x
        simp [v₀G, v₀, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      simpa only [zero_vadd, hshift] using htmp
    have hshiftMeas : MeasurableSet (-v₀ +ᵥ P') := by
      have heq : (-v₀ +ᵥ P') = (fun x => v₀ + x) ⁻¹' P' := by
        ext x
        simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm, add_left_comm]
      rw [heq]
      exact hP'meas.preimage (continuous_const.add continuous_id).measurable
    have hP'int : IntegrableOn φ P' volume := hQint.mono_set Set.subset_union_left
    have hshiftInt : IntegrableOn φ (-v₀ +ᵥ P') volume :=
      hQint.mono_set Set.subset_union_right
    have hunion := setIntegral_union₀ hdisj hshiftMeas.nullMeasurableSet hP'int hshiftInt
    have hshiftEq : ∫ x in -v₀ +ᵥ P', φ x ∂volume = ∫ x in P', φ x ∂volume :=
      c3_setIntegral_translate (-v₀) P' hP'meas φ (fun x => by
        have h := hφInvExt (-v₀G) x
        simpa [v₀, v₀G] using h)
    have hdouble : (0 : ℂ) =
        (∫ x in P', φ x ∂volume) + (∫ x in P', φ x ∂volume) := by
      calc
        0 = ∫ x in Q, φ x ∂volume := hQzero.symm
        _ = (∫ x in P', φ x ∂volume) +
            (∫ x in -v₀ +ᵥ P', φ x ∂volume) := by
              simpa [Q] using hunion
        _ = _ := by rw [hshiftEq]
    have hzero2 : (2 : ℂ) * (∫ x in P', φ x ∂volume) = 0 := by
      calc
        (2 : ℂ) * (∫ x in P', φ x ∂volume) =
            (∫ x in P', φ x ∂volume) + (∫ x in P', φ x ∂volume) := by ring
        _ = 0 := hdouble.symm
    exact (mul_eq_zero.mp hzero2).resolve_left (by norm_num)

private theorem c3_residueTheta_hct_zero
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (hfree : FreeAction F Γ)
    (s₁ : ℝ) {ι : Type} [Fintype ι] (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁) (c : ι → ℂ)
    (hct : ∀ (τ : SL(2,F)) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      ∃ P : Set (InfinitePlace F → ℂ),
        IsAddFundamentalDomain (cuspTranslations F Γ τ) P ∧
          ∫ x in P, (∑ i, c i * (d i).res (τ • ptX' F x y)) = 0)
    (P' : Set (InfinitePlace F → ℂ))
    (hP' : ∀ τ : SL(2,F), IsAddFundamentalDomain
      (cuspTranslationExtensionComplex F Γ τ) P')
    (hP'meas : ∀ τ : SL(2,F), MeasurableSet P')
    (hP'bound : ∀ τ : SL(2,F), Bornology.IsBounded P')
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) (τ : SL(2,F)) :
    ∫ x in P', c3_residueTheta s₁ σ d c (τ • ptX' F x y) ∂volume = 0 := by
  classical
  let f : X F → ℂ := c3_residueTheta s₁ σ d c
  have hfInv : IsGammaInvariant F Γ f := by
    intro γ hγ z
    simp only [f, c3_residueTheta]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(d i).res_invariant γ hγ z]
  have hresCont (i : ι) : Continuous (d i).res :=
    c3_continuous_of_smooth (d i).res (d i).res_smooth
  have hfcont : Continuous f := by
    change Continuous (fun z => ∑ i, c i * (d i).res z)
    exact continuous_finsetSum Finset.univ (by
      intro i hi
      exact continuous_const.mul (hresCont i))
  have hHor : Continuous (fun x => τ • ptX' F x y) :=
    (continuousSL2FAction_C3 τ).comp (c3_continuous_ptX'_horizontal y hy)
  have hhorCont : Continuous (fun x => f (τ • ptX' F x y)) := by
    change Continuous (f ∘ (fun x => τ • ptX' F x y))
    exact hfcont.comp hHor
  have hct' : ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ τ) P ∧
        ∫ x in P, f (τ • ptX' F x y) ∂volume = 0 := by
    obtain ⟨P, hP, hzero⟩ := hct τ y hy
    exact ⟨P, hP, by simpa [f, c3_residueTheta] using hzero⟩
  exact c3_hct_zero_on_extension_fd Γ τ y hy f hfInv hhorCont hct'
    P' (hP' τ) (hP'meas τ) (hP'bound τ)

private theorem c3_cuspTail_isOpen {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (A : ℝ) :
    IsOpen (cuspTail F Γ σ A) := by
  have heq : cuspTail F Γ σ A =
      ⋃ γ : Γ, {z | A < normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))} := by
    ext z
    simp [cuspTail]
  rw [heq]
  apply isOpen_iUnion
  intro γ
  let g : SL(2,F) := σ⁻¹ * toSLF F (γ : SL(2,𝓞 F))
  have hfun : (fun z => normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))) =
      (fun z => normHeight F (g • z)) := by
    funext z
    change normHeight F (σ⁻¹ • ((toSLF F (γ : SL(2,𝓞 F)) ) • z)) =
      normHeight F ((σ⁻¹ * toSLF F (γ : SL(2,𝓞 F))) • z)
    rw [← mul_smul]
  have hset : {z | A < normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z))} =
      {z | A < normHeight F (g • z)} := by
    ext z
    simp only [Set.mem_setOf_eq]
    have hz := congrFun hfun z
    constructor
    · exact fun h => lt_of_lt_of_eq h hz
    · exact fun h => lt_of_lt_of_eq h hz.symm
  rw [hset]
  exact isOpen_lt continuous_const (c3_normHeight_action_continuous (F := F) g)

private theorem c3_residueTheta_continuous
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2,𝓞 F)} {ι : Type} [Fintype ι]
    (s₁ : ℝ) (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁) (c : ι → ℂ) :
    Continuous (c3_residueTheta s₁ σ d c) := by
  have hresCont (i : ι) : Continuous (d i).res :=
    c3_continuous_of_smooth (d i).res (d i).res_smooth
  change Continuous (fun z => ∑ i, c i * (d i).res z)
  exact continuous_finsetSum Finset.univ (by
    intro i hi
    exact continuous_const.mul (hresCont i))

private theorem c3_residueTheta_invariant
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    {Γ : Subgroup SL(2,𝓞 F)} {ι : Type} [Fintype ι]
    (s₁ : ℝ) (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁) (c : ι → ℂ) :
    IsGammaInvariant F Γ (c3_residueTheta s₁ σ d c) := by
  intro γ hγ z
  simp only [c3_residueTheta]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(d i).res_invariant γ hγ z]

private theorem c3_source_pairing_zero
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (hfree : FreeAction F Γ)
    (s₁ : ℝ) (hs₁ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2)
    (setup : C3SpectralSetup F Γ s₁)
    {ι : Type} [Fintype ι] (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁) (c : ι → ℂ)
    (hct : ∀ (τ : SL(2,F)) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      ∃ P : Set (InfinitePlace F → ℂ),
        IsAddFundamentalDomain (cuspTranslations F Γ τ) P ∧
          ∫ x in P, (∑ i, c i * (d i).res (τ • ptX' F x y)) = 0)
    (i : ι) (data : C3CuspData s₁ setup hfree (σ i))
    (thetaLp : L2Space F setup.D)
    (hThetaRep : ∀ᵐ z ∂((volX F).restrict setup.D),
      thetaLp z = c3_residueTheta s₁ σ d c z)
    (hThetaMem : MemLp (c3_residueTheta s₁ σ d c) 2
      ((volX F).restrict setup.D)) :
    inner ℂ (data.G (s₁ : ℂ)) thetaLp = 0 := by
  classical
  let θ : X F → ℂ := c3_residueTheta s₁ σ d c
  let source : X F → ℂ := eisSeedDefect F Γ (σ i) data.τ (s₁ : ℂ)
  let Gfun : X F → ℂ := fun z => star (source z) * θ z
  letI : OpensMeasurableSpace (X F) := sgOpensMeasurableX (F := F)
  have hθcont : Continuous θ := c3_residueTheta_continuous s₁ σ d c
  have hθinv : IsGammaInvariant F Γ θ := c3_residueTheta_invariant s₁ σ d c
  have hseed := data.hseed (s₁ : ℂ)
  have hsourceInv : IsGammaInvariant F Γ source :=
    c3_eisSeedDefect_invariant Γ (σ i) (s₁ : ℂ) data.τ ⟨hseed.1, hseed.2.1⟩
  have hGinv : IsGammaInvariant F Γ Gfun := by
    intro γ hγ z
    simp [Gfun, source, θ, hsourceInv γ hγ z, hθinv γ hγ z]
  have hthetaSq : IntegrableOn (fun z => ‖θ z‖ ^ 2) setup.D (volX F) := by
    have h := hThetaMem.integrable_norm_pow (by norm_num)
    change Integrable (fun z => ‖θ z‖ ^ 2) ((volX F).restrict setup.D)
    exact h
  have hprodInt : IntegrableOn Gfun setup.D (volX F) := by
    change IntegrableOn (fun z => star (source z) * θ z) setup.D (volX F)
    exact c3_source_mul_integrableOn Γ setup.D setup.hD
      (data.G (s₁ : ℂ)) source θ (data.hsource (s₁ : ℂ)) hθcont hthetaSq
  have hsupport : ∀ z ∉ cuspTail F Γ (σ i) data.A, Gfun z = 0 := by
    intro z hz
    have hdef : source z = 0 := by
      by_contra hne
      apply hz
      exact c3_defect_supported_in_cuspTail data.A₀_ge data.A₀_lt_A data.hτ
        data.htail (s₁ : ℂ) hne
    simp [Gfun, hdef]
  let Ydata := c3_unitHeight_section Γ hfree (σ i)
  obtain ⟨Y, hYmeas, hYpos, hYfd⟩ := Ydata
  obtain ⟨P', hP', hP'meas, hP'bound⟩ := c3_extension_fundamentalDomain Γ (σ i)
  have hGtailInt : IntegrableOn Gfun
      (setup.D ∩ cuspTail F Γ (σ i) data.A) (volX F) :=
    hprodInt.mono_set Set.inter_subset_left
  have hR14 := R14_cusp_fubini Γ setup.D setup.hD (σ i)
    data.A₀ data.A data.A₀_ge data.A₀_le_A data.separation
    Y hYmeas hYpos hYfd P' hP' hP'meas Gfun hGinv hGtailInt
  let S : Set (InfinitePlace F → ℝ) :=
    {y | y ∈ Y ∧ data.A < ∏ w, y w}
  have hSmeas : MeasurableSet S := by
    have hprod : Measurable (fun y : InfinitePlace F → ℝ => ∏ w, y w) := by fun_prop
    dsimp [S]
    rw [Set.setOf_and]
    exact hYmeas.inter ((isOpen_Ioi.measurableSet).preimage hprod)
  have hslice (y : InfinitePlace F → ℝ) (hyS : y ∈ S) :
      ∫ x in P', Gfun ((σ i) • ptX' F x y) ∂volume = 0 := by
    have hy : ∀ w, 0 < y w := hYpos y hyS.1
    have hHor : Continuous (fun x => (σ i) • ptX' F x y) :=
      (continuousSL2FAction_C3 (σ i)).comp
        (c3_continuous_ptX'_horizontal y hy)
    have hThetaHor : Continuous (fun x => θ ((σ i) • ptX' F x y)) := by
      change Continuous (θ ∘ (fun x => (σ i) • ptX' F x y))
      exact (c3_residueTheta_continuous s₁ σ d c).comp hHor
    have hθzero := c3_hct_zero_on_extension_fd Γ (σ i) y hy θ hθinv
      hThetaHor
      (by
        obtain ⟨Q, hQ, hQzero⟩ := hct (σ i) y hy
        exact ⟨Q, hQ, by simpa [θ, c3_residueTheta] using hQzero⟩)
      P' hP' hP'meas hP'bound
    let κ : ℂ := -((placeCount F *
      c3RadialDefectCoefficient data.τ s₁ (∏ w, y w) : ℝ) : ℂ)
    have hpoint (x : InfinitePlace F → ℂ) :
        Gfun ((σ i) • ptX' F x y) =
          star κ * θ ((σ i) • ptX' F x y) := by
      simp only [Gfun, source, θ, κ]
      rw [c3_eisSeedDefect_radial_on_cusp Γ (σ i) data.A₀ data.A
        data.A₀_le_A data.A_pos data.separation data.τ data.hτ s₁ hs₁ x y hy hyS.2]
      simp [κ]
    have hIeq : ∫ x in P', Gfun ((σ i) • ptX' F x y) ∂volume =
        ∫ x in P', star κ * θ ((σ i) • ptX' F x y) ∂volume :=
      setIntegral_congr_fun hP'meas fun x hx => hpoint x
    rw [hIeq, integral_const_mul, hθzero]
    simp
  have hRHSzero :
      ∫ y in S,
        (∫ x in P', Gfun ((σ i) • ptX' F x y) ∂volume) *
          (∏ w : InfinitePlace F, (y w ^ 3)⁻¹) ∂volume = 0 := by
    calc
      _ = ∫ y in S, (0 : ℂ) ∂volume := by
        apply setIntegral_congr_fun hSmeas
        intro y hyS
        change (∫ x in P', Gfun ((σ i) • ptX' F x y) ∂volume) *
          (∏ w : InfinitePlace F, (y w ^ 3)⁻¹) = 0
        rw [hslice y hyS]
        simp
      _ = 0 := by simp
  have hTailZero :
      ∫ z in setup.D ∩ cuspTail F Γ (σ i) data.A, Gfun z ∂(volX F) = 0 := by
    simpa [S] using hR14.trans hRHSzero
  have hTailMeas : MeasurableSet (cuspTail F Γ (σ i) data.A) :=
    (c3_cuspTail_isOpen Γ (σ i) data.A).measurableSet
  have hRestMeas : NullMeasurableSet
      (Set.diff setup.D (cuspTail F Γ (σ i) data.A)) (volX F) :=
    setup.hD.nullMeasurableSet.diff hTailMeas.nullMeasurableSet
  have hRestZero : ∫ z in Set.diff setup.D (cuspTail F Γ (σ i) data.A),
      Gfun z ∂(volX F) = 0 := by
    apply integral_eq_zero_of_ae
    exact (ae_restrict_iff'₀ hRestMeas).2 <|
      ae_of_all (volX F) fun z hz => hsupport z hz.2
  have hTailInt : IntegrableOn Gfun
      (setup.D ∩ cuspTail F Γ (σ i) data.A) (volX F) := hGtailInt
  have hRestInt : IntegrableOn Gfun
      (Set.diff setup.D (cuspTail F Γ (σ i) data.A)) (volX F) :=
    hprodInt.mono_set Set.sdiff_subset
  have hdisj : AEDisjoint (volX F)
      (setup.D ∩ cuspTail F Γ (σ i) data.A)
      (Set.diff setup.D (cuspTail F Γ (σ i) data.A)) :=
    (Set.disjoint_left.mpr fun z hz₁ hz₂ => hz₂.2 hz₁.2).aedisjoint
  have hunion := setIntegral_union₀ hdisj hRestMeas hTailInt hRestInt
  have hdecomp : (setup.D ∩ cuspTail F Γ (σ i) data.A) ∪
      Set.diff setup.D (cuspTail F Γ (σ i) data.A) = setup.D := by
    ext z
    change (z ∈ setup.D ∧ z ∈ cuspTail F Γ (σ i) data.A) ∨
      (z ∈ setup.D ∧ z ∉ cuspTail F Γ (σ i) data.A) ↔ z ∈ setup.D
    constructor
    · intro hz
      rcases hz with ⟨hzD, _⟩ | ⟨hzD, _⟩
      · exact hzD
      · exact hzD
    · intro hzD
      by_cases hzT : z ∈ cuspTail F Γ (σ i) data.A
      · exact Or.inl ⟨hzD, hzT⟩
      · exact Or.inr ⟨hzD, hzT⟩
  have hIntegralD : ∫ z in setup.D, Gfun z ∂(volX F) = 0 := by
    calc
      _ = ∫ z in (setup.D ∩ cuspTail F Γ (σ i) data.A) ∪
          Set.diff setup.D (cuspTail F Γ (σ i) data.A), Gfun z ∂(volX F) := by rw [hdecomp]
      _ = _ := by rw [hunion, hTailZero, hRestZero]; simp
  have hsourceD : data.G (s₁ : ℂ) =ᵐ[((volX F).restrict setup.D)]
      source := (ae_restrict_iff'₀ setup.hD.nullMeasurableSet).2
        (data.hsource (s₁ : ℂ))
  have hInnerEq : inner ℂ (data.G (s₁ : ℂ)) thetaLp =
      ∫ z in setup.D, Gfun z ∂(volX F) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hsourceD, hThetaRep] with z hzsource hztheta
    simp [Gfun, source, θ, hzsource, hztheta, mul_comm]
  rw [hInnerEq, hIntegralD]

theorem c3_cuspidal_core
    {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (s₁ : ℝ) (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2)
    {ι : Type} [Fintype ι] (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁) (c : ι → ℂ)
    (hct : ∀ (τ : SL(2,F)) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      ∃ P : Set (InfinitePlace F → ℂ),
        IsAddFundamentalDomain (cuspTranslations F Γ τ) P ∧
          ∫ x in P, (∑ i, c i * (d i).res (τ • ptX' F x y)) = 0) :
    ∀ z, ∑ i, c i * (d i).res z = 0 := by
  classical
  obtain ⟨setup⟩ := c3_spectral_setup Γ hfree s₁ h₀ h₁
  obtain ⟨k₀, hkSmooth, hkNonneg, hkSupport, hkNonzero⟩ := radialKernel_bump
  let data : ∀ i, C3CuspData s₁ setup hfree (σ i) := fun i =>
    Classical.choice (c3_cusp_data s₁ setup hfree (σ i) h₀ h₁
      k₀ hkSmooth hkNonneg hkSupport hkNonzero)
  let L := setup.E.M.comp (setup.P.comp setup.E.M.adjoint)
  let raw : ι → L2Space F setup.D := fun i =>
    -setup.κ • L ((data i).G (s₁ : ℂ))
  let Θ : L2Space F setup.D := ∑ i, c i • raw i
  let μ := (volX F).restrict setup.D
  have hresD (i : ι) : (d i).res =ᵐ[μ] raw i := by
    have heq := (continuedEisenstein_E_eq (d i) (data i).d h₁).2
    have ha : (d i).res =ᵐ[volX F] l2Lift F Γ setup.D (raw i) := by
      rw [heq]
      exact (data i).d_res_ae
    have hb := c3_l2Lift_eq_on_D Γ setup.D setup.hD (raw i)
    filter_upwards [ha.filter_mono ae_restrict_le,
      hb.filter_mono ae_restrict_le,
      ae_restrict_mem₀ setup.hD.nullMeasurableSet] with z hza hzb hzD
    exact hza.trans (hzb hzD)
  have htermRep (i : ι) :
      (fun z => (c i • raw i) z) =ᵐ[μ] (fun z => c i * (d i).res z) := by
    filter_upwards [Lp.coeFn_smul (c i) (raw i), hresD i] with z hz hr
    calc
      (c i • raw i) z = c i * raw i z := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hz
      _ = c i * (d i).res z := by rw [hr]
  have hThetaRep : ∀ᵐ z ∂μ, Θ z = c3_residueTheta s₁ σ d c z := by
    have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • raw i)
    have hterms := ae_all_iff.mpr htermRep
    filter_upwards [hsum, hterms] with z hz hzi
    calc
      Θ z = ∑ i, (c i • raw i) z := hz
      _ = ∑ i, c i * (d i).res z := Finset.sum_congr rfl (fun i _ => hzi i)
  have hThetaMem := c3_residueTheta_memLp Γ setup.D setup.hD s₁ σ d c
  have hpair (i : ι) : inner ℂ ((data i).G (s₁ : ℂ)) Θ = 0 :=
    c3_source_pairing_zero Γ hfree s₁ h₀ h₁ setup σ d c hct i (data i)
      Θ hThetaRep hThetaMem
  let G₀ : L2Space F setup.D :=
    ∑ i, c i • (-setup.κ • (data i).G (s₁ : ℂ))
  have hprojected : L G₀ = Θ := by
    dsimp only [G₀, Θ, raw]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, LinearMapClass.map_smul_of_tower]
  have hInnerG : inner ℂ G₀ Θ = 0 := by
    dsimp only [G₀]
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro i hi
    rw [inner_smul_left, inner_smul_left_eq_smul, hpair i]
    simp
  have hNorm := setup.hPnorm G₀
  change (‖L G₀‖ ^ 2 : ℂ) =
    (((setup.lam + 1)⁻¹ : ℝ) : ℂ) * inner ℂ G₀ (L G₀) at hNorm
  rw [hprojected, hInnerG, mul_zero] at hNorm
  have hNormSq : ‖Θ‖ ^ 2 = 0 := by exact_mod_cast hNorm
  have hNormZero : ‖Θ‖ = 0 := by nlinarith [norm_nonneg Θ]
  have hThetaZero : Θ = 0 := norm_eq_zero.mp hNormZero
  have hzeroAE : (fun z => Θ z) =ᵐ[μ] (fun _ => (0 : ℂ)) := by
    rw [hThetaZero]
    exact Lp.coeFn_zero ℂ 2 μ
  have hthetaD : c3_residueTheta s₁ σ d c =ᵐ[μ] (fun _ => (0 : ℂ)) := by
    filter_upwards [hThetaRep, hzeroAE] with z hr hz
    exact hr.symm.trans hz
  have hthetaGlobal := ae_eq_of_invariant_on_fundamentalDomain_C3 Γ setup.D
    setup.hD (c3_residueTheta s₁ σ d c) (fun _ => (0 : ℂ))
    (c3_residueTheta_invariant s₁ σ d c) (by intro γ hγ z; rfl)
    ((ae_restrict_iff'₀ setup.hD.nullMeasurableSet).mp hthetaD)
  letI : Measure.IsOpenPosMeasure (volX F) := ⟨(G3_volume (F := F)).2.2.2.1⟩
  have hthetaEq := Measure.eq_of_ae_eq hthetaGlobal
    (c3_residueTheta_continuous s₁ σ d c) continuous_const
  intro z
  exact congrFun hthetaEq z

end ArtinPrimitiveRoots.Proofs.spec_domcusp_sol

end
