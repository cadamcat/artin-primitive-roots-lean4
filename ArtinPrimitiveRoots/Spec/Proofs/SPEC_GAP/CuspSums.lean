import ArtinPrimitiveRoots.Spec.GeometryExtra
import ArtinPrimitiveRoots.Spec.ReductionExtra
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_GAP.HeightCutoff

/-! Local finiteness and calculus for the all-cusp height sums used by SPEC-GAP. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem specGap_posSet_open : IsOpen (posSet F) := by
  rw [posSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  have hc : Continuous (fun p : Coord F => (p w).2) := by fun_prop
  exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

private theorem specGap_locallyCompactX : LocallyCompactSpace (X F) := by
  classical
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩
  obtain ⟨e, he, hesymm⟩ := hchart
  letI : LocallyCompactSpace {p : Coord F // p ∈ posSet F} :=
    specGap_posSet_open.locallyCompactSpace
  exact e.symm.isOpenEmbedding.locallyCompactSpace

/-- The product height seen from a chosen cusp coset. -/
def specGapCosetHeight (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : CuspCosets F Γ σ) (z : X F) : ℝ :=
  normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))

/-- The positive denominator in the placewise height transformation. -/
def specGapHeightDenom (g : SL(2,F)) (p : Coord F) (w : InfinitePlace F) : ℝ :=
  Complex.normSq (w.embedding (g 1 0) * (p w).1 + w.embedding (g 1 1)) +
    Complex.normSq (w.embedding (g 1 0)) * (p w).2 ^ 2

private theorem normHeight_pos (z : X F) : 0 < normHeight F z := by
  unfold normHeight
  apply Finset.prod_pos
  intro w hw
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private theorem specGapHeightDenom_pos (g : SL(2,F)) (p : Coord F)
    (hp : p ∈ posSet F) (w : InfinitePlace F) : 0 < specGapHeightDenom g p w := by
  have hy : 0 < (p w).2 := hp w
  have hheight : 0 < height ((g • ptX' F (fun v => (p v).1) (fun v => (p v).2)) w) := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos
      ((g • ptX' F (fun v => (p v).1) (fun v => (p v).2)) w)
  have hformula := height_smul_ptX'_at g (fun v => (p v).1) (fun v => (p v).2)
    (fun v => hp v) w
  have heq : height ((g • ptX' F (fun v => (p v).1) (fun v => (p v).2)) w) =
      (p w).2 / specGapHeightDenom g p w := by
    simpa [specGapHeightDenom, ptX, ptX'] using hformula
  rw [heq] at hheight
  exact (div_pos_iff_of_pos_left hy).mp hheight

private theorem specGapHeightDenom_smooth (g : SL(2,F)) (w : InfinitePlace F) :
    ContDiffOn ℝ ∞ (fun p => specGapHeightDenom g p w) (posSet F) := by
  let f₁ : Coord F → ℂ := fun p =>
    w.embedding (g 1 0) * (p w).1 + w.embedding (g 1 1)
  have hf₁ : ContDiffOn ℝ ∞ f₁ (posSet F) := by
    dsimp [f₁]
    fun_prop
  have hre₁ : ContDiffOn ℝ ∞ (fun p => (f₁ p).re) (posSet F) := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn hf₁
    convert h using 1 <;> ext p <;> rfl
  have him₁ : ContDiffOn ℝ ∞ (fun p => (f₁ p).im) (posSet F) := by
    have h := Complex.imCLM.contDiff.comp_contDiffOn hf₁
    convert h using 1 <;> ext p <;> rfl
  have hy : ContDiffOn ℝ ∞ (fun p => (p w).2) (posSet F) := by fun_prop
  have hre₂ : ContDiffOn ℝ ∞ (fun _ : Coord F => (w.embedding (g 1 0)).re) (posSet F) :=
    contDiffOn_const
  have him₂ : ContDiffOn ℝ ∞ (fun _ : Coord F => (w.embedding (g 1 0)).im) (posSet F) :=
    contDiffOn_const
  have hrealSq := hre₁.mul hre₁
  have himSq := him₁.mul him₁
  have hrealConstSq := hre₂.mul hre₂
  have himConstSq := him₂.mul him₂
  have hySq := hy.mul hy
  have hsecond := (hrealConstSq.add himConstSq).mul hySq
  have hden : ContDiffOn ℝ ∞
      (fun p => (f₁ p).re * (f₁ p).re + (f₁ p).im * (f₁ p).im +
        ((w.embedding (g 1 0)).re * (w.embedding (g 1 0)).re +
          (w.embedding (g 1 0)).im * (w.embedding (g 1 0)).im) * ((p w).2 * (p w).2))
      (posSet F) := by
    have hc : ContDiffOn ℝ ∞ (fun p : Coord F =>
        ((w.embedding (g 1 0)).re * (w.embedding (g 1 0)).re +
          (w.embedding (g 1 0)).im * (w.embedding (g 1 0)).im) * ((p w).2 * (p w).2))
        (posSet F) := by
      simpa [Pi.add_apply] using hsecond
    exact (hrealSq.add himSq).add hc
  simpa [specGapHeightDenom, Complex.normSq_apply, f₁, pow_two, mul_comm] using hden

private theorem normHeight_action_coord (g : SL(2,F)) (p : Coord F)
    (hp : p ∈ posSet F) :
    normHeight F (g • ptX F p) =
      ∏ w : InfinitePlace F, (p w).2 / specGapHeightDenom g p w := by
  change normHeight F (g • ptX' F (fun w => (p w).1) (fun w => (p w).2)) = _
  have h := (G2_x_action (F := F)).1 g (fun w => (p w).1) (fun w => (p w).2) hp
  rw [Finset.prod_div_distrib]
  simpa [ptX, ptX', specGapHeightDenom] using h

private theorem normHeight_action_smooth (g : SL(2,F)) :
    IsSmoothRealX F (fun z => normHeight F (g • z)) := by
  change ContDiffOn ℝ ∞ (fun p => normHeight F (g • ptX F p)) (posSet F)
  let f : InfinitePlace F → Coord F → ℝ :=
    fun w p => (p w).2 / specGapHeightDenom g p w
  have hf (w : InfinitePlace F) : ContDiffOn ℝ ∞ (f w) (posSet F) := by
    apply ContDiffOn.div
    · fun_prop
    · exact specGapHeightDenom_smooth g w
    · intro p hp
      exact (specGapHeightDenom_pos g p hp w).ne'
  have hprod : ContDiffOn ℝ ∞ (fun p => ∏ w : InfinitePlace F, f w p) (posSet F) := by
    classical
    simpa [f] using (contDiffOn_prod (t := (Finset.univ : Finset (InfinitePlace F)))
      (fun w hw => hf w))
  exact hprod.congr (fun p hp => normHeight_action_coord g p hp)

private theorem cuspStab_conjugateHeight_invariant (Γ : Subgroup SL(2,𝓞 F))
    (σ : SL(2,F)) (δ : Γ) (hδ : δ ∈ cuspStab F Γ σ) (z : X F) :
    normHeight F ((σ⁻¹ * toSLF F ((δ : Γ) : SL(2,𝓞 F)) * σ) • z) = normHeight F z := by
  have hb : σ⁻¹ * toSLF F ((δ : Γ) : SL(2,𝓞 F)) * σ ∈ borelSL F := by
    simpa [cuspStab, MulAut.conj_apply] using hδ
  exact ((G2_x_action (F := F)).2.2.1
    ((δ : Γ) : SL(2,𝓞 F)) σ hb).2 z

private theorem specGapCosetHeight_rep_eq (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (a b : Γ) (hab : QuotientGroup.rightRel (cuspStab F Γ σ) a b) (z : X F) :
    normHeight F (σ⁻¹ • ((a : SL(2,𝓞 F)) • z)) =
      normHeight F (σ⁻¹ • ((b : SL(2,𝓞 F)) • z)) := by
  let δ : Γ := b * a⁻¹
  have hδ : δ ∈ cuspStab F Γ σ := by
    dsimp [δ]
    exact (QuotientGroup.rightRel_apply.mp hab)
  have hb : b = δ * a := by
    simp [δ, mul_assoc]
  have hconj :
      (σ⁻¹ * toSLF F ((δ : Γ) : SL(2,𝓞 F)) * σ) •
          (σ⁻¹ • ((a : SL(2,𝓞 F)) • z)) =
        σ⁻¹ • ((b : SL(2,𝓞 F)) • z) := by
    rw [hb]
    change (σ⁻¹ * toSLF F ((δ : Γ) : SL(2,𝓞 F)) * σ) •
          (σ⁻¹ • (toSLF F ((a : Γ) : SL(2,𝓞 F)) • z)) =
        σ⁻¹ • ((toSLF F ((δ : Γ) : SL(2,𝓞 F)) *
          toSLF F ((a : Γ) : SL(2,𝓞 F))) • z)
    simp only [smul_smul]
    congr 1
    group
  rw [← hconj]
  exact (cuspStab_conjugateHeight_invariant Γ σ δ hδ
    (σ⁻¹ • ((a : SL(2,𝓞 F)) • z))).symm

private def specGapCuspRightMul (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) : CuspCosets F Γ σ → CuspCosets F Γ σ :=
  Quotient.lift (fun a : Γ => Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (a * γ))
    (by
      intro a b hab
      have hab' : b * a⁻¹ ∈ cuspStab F Γ σ := QuotientGroup.rightRel_apply.mp hab
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      simpa [mul_assoc] using hab')

private def specGapCuspRightMulEquiv (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) : CuspCosets F Γ σ ≃ CuspCosets F Γ σ where
  toFun := specGapCuspRightMul Γ σ γ
  invFun := specGapCuspRightMul Γ σ γ⁻¹
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ a => simp [specGapCuspRightMul]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ a => simp [specGapCuspRightMul]

private theorem specGapCosetHeight_shift (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) (q : CuspCosets F Γ σ) (z : X F) :
    specGapCosetHeight Γ σ q (γ • z) =
      specGapCosetHeight Γ σ (specGapCuspRightMul Γ σ γ q) z := by
  induction q using Quotient.inductionOn with
  | _ a =>
      let q₁ : CuspCosets F Γ σ := Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (a * γ)
      have hq : specGapCuspRightMul Γ σ γ (Quotient.mk _ a) = q₁ := rfl
      have hrelA : QuotientGroup.rightRel (cuspStab F Γ σ)
          (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) a).out a :=
        Quotient.mk_out a
      have hleft := specGapCosetHeight_rep_eq Γ σ
        (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) a).out a hrelA (γ • z)
      have hrel : QuotientGroup.rightRel (cuspStab F Γ σ) q₁.out (a * γ) :=
        Quotient.mk_out (a * γ)
      have hrep := specGapCosetHeight_rep_eq Γ σ q₁.out (a * γ) hrel z
      change normHeight F (σ⁻¹ • ((Quotient.mk _ a).out • (γ • z))) =
        normHeight F (σ⁻¹ • (q₁.out • z))
      calc
        normHeight F (σ⁻¹ • ((Quotient.mk _ a).out • (γ • z))) =
            normHeight F (σ⁻¹ • ((a : SL(2,𝓞 F)) • (γ • z))) := hleft
        _ =
            normHeight F (σ⁻¹ • (((a * γ : Γ) : SL(2,𝓞 F)) • z)) := by
              change normHeight F (σ⁻¹ •
                  ((a : SL(2,𝓞 F)) • (((γ : Γ) : SL(2,𝓞 F)) • z))) =
                normHeight F (σ⁻¹ • (((a * γ : Γ) : SL(2,𝓞 F)) • z))
              rw [smul_smul]
              have hmul : ((a * γ : Γ) : SL(2,𝓞 F)) =
                  (a : SL(2,𝓞 F)) * (γ : SL(2,𝓞 F)) := rfl
              rw [← hmul]
        _ = normHeight F (σ⁻¹ • (q₁.out • z)) := hrep.symm

theorem specGapCosetHeight_pos (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : CuspCosets F Γ σ) (z : X F) : 0 < specGapCosetHeight Γ σ q z :=
  normHeight_pos _

theorem specGapCosetHeight_smooth (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : CuspCosets F Γ σ) : IsSmoothRealX F (specGapCosetHeight Γ σ q) := by
  let g : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  have hsmul (z : X F) :
      σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z) = g • z := by
    change σ⁻¹ • (toSLF F ((q.out : Γ) : SL(2,𝓞 F)) • z) = _
    rw [smul_smul]
  have hs : IsSmoothRealX F (fun z => normHeight F (g • z)) := normHeight_action_smooth g
  apply hs.congr
  intro p hp
  simp only [specGapCosetHeight, hsmul]

abbrev SpecGapCuspIndex (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (d : SiegelData F Γ) :=
  Σ i : d.ι, CuspCosets F Γ (d.σ i)

def specGapAllCuspHeight (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (d : SiegelData F Γ)
    (p : SpecGapCuspIndex Γ d) (z : X F) : ℝ :=
  specGapCosetHeight Γ (d.σ p.1) p.2 z

noncomputable def specGapAllCuspSum (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (d : SiegelData F Γ)
    (ψ : ℝ → ℝ) (z : X F) : ℝ :=
  ∑' p : SpecGapCuspIndex Γ d, ψ (specGapAllCuspHeight Γ d p z)

def specGapActiveCuspSet (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (d : SiegelData F Γ)
    (A : ℝ) (K : Set (X F)) : Set (SpecGapCuspIndex Γ d) :=
  Set.univ.sigma fun i =>
    {q : CuspCosets F Γ (d.σ i) | ∃ z ∈ K, A ≤ specGapCosetHeight Γ (d.σ i) q z}

private theorem specGapActiveCuspSet_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A) (K : Set (X F)) (hK : IsCompact K) :
    (specGapActiveCuspSet Γ d A K).Finite := by
  classical
  letI : Fintype d.ι := d.fintype
  obtain ⟨_, _, hR10⟩ := R10_cusp_separation Γ
  unfold specGapActiveCuspSet
  apply Set.Finite.sigma Set.finite_univ
  intro i hi
  exact hR10 (d.σ i) K hK A hA

private theorem specGapAllCuspWeight_summable (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A) (ψ : ℝ → ℝ)
    (hψzero : ∀ t ≤ A, ψ t = 0) (z : X F) :
    Summable (fun p : SpecGapCuspIndex Γ d =>
      ψ (specGapAllCuspHeight Γ d p z)) := by
  classical
  let K : Set (X F) := {z}
  have hK : IsCompact K := isCompact_singleton
  have hfinite := specGapActiveCuspSet_finite Γ d A hA K hK
  apply summable_of_hasFiniteSupport
  apply hfinite.subset
  intro p hp
  by_contra hnot
  have hlt : specGapAllCuspHeight Γ d p z < A := by
    by_contra hn
    have hge : A ≤ specGapAllCuspHeight Γ d p z := le_of_not_gt hn
    have hmem : p ∈ specGapActiveCuspSet Γ d A K := by
      rcases p with ⟨i, q⟩
      simp [specGapActiveCuspSet, K]
      exact hge
    exact hnot hmem
  exact hp (hψzero _ hlt.le)

theorem specGapAllCuspSum_invariant {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (ψ : ℝ → ℝ) (γ : Γ) (z : X F) :
    specGapAllCuspSum Γ d ψ ((γ : SL(2,𝓞 F)) • z) = specGapAllCuspSum Γ d ψ z := by
  classical
  let e : SpecGapCuspIndex Γ d ≃ SpecGapCuspIndex Γ d :=
    Equiv.sigmaCongrRight fun i => specGapCuspRightMulEquiv Γ (d.σ i) γ
  unfold specGapAllCuspSum
  rw [← e.tsum_eq (fun p => ψ (specGapAllCuspHeight Γ d p z))]
  apply tsum_congr
  intro p
  rcases p with ⟨i, q⟩
  exact congrArg ψ (specGapCosetHeight_shift Γ (d.σ i) γ q z)

theorem specGapAllCuspIndex_eq_of_separation {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A₀ : ℝ)
    (hsep : ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i))
    (p p' : SpecGapCuspIndex Γ d) (z : X F)
    (hp : A₀ ≤ specGapAllCuspHeight Γ d p z)
    (hp' : A₀ ≤ specGapAllCuspHeight Γ d p' z) : p = p' := by
  rcases p with ⟨i, q⟩
  rcases p' with ⟨j, q'⟩
  have hs := hsep i j q.out q'.out z hp hp'
  rcases hs with ⟨hij, hstab⟩
  subst j
  have hrel : QuotientGroup.rightRel (cuspStab F Γ (d.σ i)) q.out q'.out :=
    QuotientGroup.rightRel_apply.mpr hstab
  have hq : q = q' := q.out_eq.symm.trans ((Quotient.sound hrel).trans q'.out_eq)
  subst q'
  rfl

private theorem specGapAllCuspAtMostOne {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (z : X F) {p p' : SpecGapCuspIndex Γ d}
    (hp : A < specGapAllCuspHeight Γ d p z) (hp' : A < specGapAllCuspHeight Γ d p' z) :
    p = p' := by
  exact hsep p p' z hp.le hp'.le

theorem specGapAllCuspSum_eq_zero_or_term {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (ψ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hψzero : ∀ t ≤ A, ψ t = 0)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (z : X F) :
    (∀ p, ψ (specGapAllCuspHeight Γ d p z) = 0) ∨
      ∃ p, specGapAllCuspSum Γ d ψ z = ψ (specGapAllCuspHeight Γ d p z) := by
  classical
  by_cases hnone : ∀ p, ψ (specGapAllCuspHeight Γ d p z) = 0
  · exact Or.inl hnone
  · push_neg at hnone
    obtain ⟨p, hp⟩ := hnone
    refine Or.inr ⟨p, ?_⟩
    unfold specGapAllCuspSum
    rw [tsum_eq_single p]
    intro p' hne
    by_contra hp'
    have hlow : A < specGapAllCuspHeight Γ d p z := by
      by_contra h
      exact hp (hψzero _ (le_of_not_gt h))
    have hlow' : A < specGapAllCuspHeight Γ d p' z := by
      by_contra h
      exact hp' (hψzero _ (le_of_not_gt h))
    exact hne (hsep p p' z hlow.le hlow'.le).symm

theorem specGapAllCuspSum_bounds {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (ψ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hψzero : ∀ t ≤ A, ψ t = 0) (hψbounds : ∀ t, 0 ≤ ψ t ∧ ψ t ≤ 1)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (z : X F) : 0 ≤ specGapAllCuspSum Γ d ψ z ∧ specGapAllCuspSum Γ d ψ z ≤ 1 := by
  rcases specGapAllCuspSum_eq_zero_or_term d ψ A hA hψzero hsep z with hzero | ⟨p, hp⟩
  · rw [show specGapAllCuspSum Γ d ψ z = 0 by
      unfold specGapAllCuspSum
      calc
        _ = ∑' p, (0 : ℝ) := tsum_congr hzero
        _ = 0 := by simp]
    simp
  · rw [hp]
    exact hψbounds _

private theorem specGapActiveCuspSet_mem_of_height {Γ : Subgroup SL(2,𝓞 F)}
    [Γ.FiniteIndex] (d : SiegelData F Γ) (A : ℝ) (K : Set (X F))
    (p : SpecGapCuspIndex Γ d) (z : X F) (hz : z ∈ K)
    (hheight : A ≤ specGapAllCuspHeight Γ d p z) :
    p ∈ specGapActiveCuspSet Γ d A K := by
  rcases p with ⟨i, q⟩
  simp [specGapActiveCuspSet]
  exact ⟨z, hz, hheight⟩

private theorem specGapAllCuspSum_eq_finset {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (ψ : ℝ → ℝ) (A : ℝ)
    (hψzero : ∀ t ≤ A, ψ t = 0) (K : Set (X F))
    (hS : (specGapActiveCuspSet Γ d A K).Finite)
    (z : X F) (hz : z ∈ K) :
    specGapAllCuspSum Γ d ψ z =
      Finset.sum hS.toFinset (fun p => ψ (specGapAllCuspHeight Γ d p z)) := by
  classical
  unfold specGapAllCuspSum
  apply tsum_eq_sum (s := hS.toFinset)
  intro p hp
  have hlt : specGapAllCuspHeight Γ d p z < A := by
    by_contra hn
    exact hp (hS.mem_toFinset.mpr
      (specGapActiveCuspSet_mem_of_height d A K p z hz (le_of_not_gt hn)))
  exact hψzero _ hlt.le

private theorem specGapCosetWeight_smooth {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (i : d.ι) (q : CuspCosets F Γ (d.σ i)) :
    ContDiffOn ℝ ∞ (fun p : Coord F => ψ (specGapCosetHeight Γ (d.σ i) q (ptX F p)))
      (posSet F) := by
  exact hψ.comp_contDiffOn (specGapCosetHeight_smooth Γ (d.σ i) q)

private theorem specGap_ptX_continuousOn : ContinuousOn (ptX F) (posSet F) := by
  classical
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, _, _, _, _, hchart⟩
  obtain ⟨e, he, hesymm⟩ := hchart
  have heq : (posSet F).domRestrict (ptX F) = e := by
    funext p
    exact (he p).symm
  have hcont : Continuous ((posSet F).domRestrict (ptX F)) := heq ▸ e.continuous
  exact continuousOn_iff_continuous_domRestrict.mpr hcont

private theorem ptX_coordsX (z : X F) : ptX F (coordsX F z) = z := by
  rcases G1_h3_basics (F := F) with ⟨_, _, _, _, _, _, _, hptX, _, _, _, _⟩
  exact hptX z

private theorem coordsX_mem_posSet (z : X F) : coordsX F z ∈ posSet F := by
  intro w
  change 0 < height (z w)
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private theorem specGapAllCuspSum_locally_eq_finset {Γ : Subgroup SL(2,𝓞 F)}
    [Γ.FiniteIndex] (d : SiegelData F Γ) (ψ : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hψzero : ∀ t ≤ A, ψ t = 0) (z : X F) :
    ∃ S : Finset (SpecGapCuspIndex Γ d),
      specGapAllCuspSum Γ d ψ z =
        Finset.sum S (fun r => ψ (specGapAllCuspHeight Γ d r z)) ∧
      (fun p => specGapAllCuspSum Γ d ψ (ptX F p)) =ᶠ[𝓝[ posSet F ] (coordsX F z)]
        (fun p => Finset.sum S (fun r => ψ (specGapAllCuspHeight Γ d r (ptX F p)))) := by
  letI : LocallyCompactSpace (X F) := specGap_locallyCompactX
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := coordsX_mem_posSet z
  have hpt : ptX F p = z := ptX_coordsX z
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds z
  obtain ⟨U, hUK, hU, hzU⟩ := mem_nhds_iff.mp hKn
  let S : Set (SpecGapCuspIndex Γ d) := specGapActiveCuspSet Γ d A K
  have hS : S.Finite := specGapActiveCuspSet_finite Γ d A hA K hK
  let s : Finset (SpecGapCuspIndex Γ d) := hS.toFinset
  have hptU : ptX F p ∈ U := by rw [hpt]; exact hzU
  have hpt_event : ∀ᶠ p' in 𝓝[ posSet F ] p, ptX F p' ∈ U :=
    (specGap_ptX_continuousOn p hp).tendsto (IsOpen.mem_nhds hU hptU)
  have hEq : (fun p' => specGapAllCuspSum Γ d ψ (ptX F p')) =ᶠ[𝓝[ posSet F ] p]
      (fun p' => Finset.sum s (fun r => ψ (specGapAllCuspHeight Γ d r (ptX F p'))) ) := by
    filter_upwards [hpt_event] with p' hpu
    have hpK : ptX F p' ∈ K := hUK hpu
    have hsum := specGapAllCuspSum_eq_finset d ψ A hψzero K hS (ptX F p') hpK
    simpa [S, s] using hsum
  have hEqAt : specGapAllCuspSum Γ d ψ z =
      Finset.sum s (fun r => ψ (specGapAllCuspHeight Γ d r z)) := by
    have hzK : z ∈ K := hUK hzU
    exact specGapAllCuspSum_eq_finset d ψ A hψzero K hS z hzK
  exact ⟨s, hEqAt, hEq⟩

theorem specGapAllCuspSum_smooth {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (A : ℝ) (hA : 0 < A) (hψzero : ∀ t ≤ A, ψ t = 0) :
    IsSmoothRealX F (specGapAllCuspSum Γ d ψ) := by
  letI : LocallyCompactSpace (X F) := specGap_locallyCompactX
  change ContDiffOn ℝ ∞ (fun p => specGapAllCuspSum Γ d ψ (ptX F p)) (posSet F)
  intro p hp
  let z : X F := ptX F p
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds z
  obtain ⟨U, hUK, hU, hzU⟩ := mem_nhds_iff.mp hKn
  let S := specGapActiveCuspSet Γ d A K
  have hS : S.Finite := specGapActiveCuspSet_finite Γ d A hA K hK
  have hterm (r : SpecGapCuspIndex Γ d) :
      ContDiffOn ℝ ∞
        (fun p' : Coord F => ψ (specGapAllCuspHeight Γ d r (ptX F p')))
        (posSet F) := by
    rcases r with ⟨i, q⟩
    exact specGapCosetWeight_smooth d ψ hψ i q
  have hfiniteSum : ContDiffOn ℝ ∞
      (fun p' : Coord F =>
        Finset.sum hS.toFinset (fun r => ψ (specGapAllCuspHeight Γ d r (ptX F p'))))
      (posSet F) := by
    exact ContDiffOn.sum (fun r hr => hterm r)
  have hpt_event : ∀ᶠ p' in 𝓝[ posSet F ] p, ptX F p' ∈ U := by
    exact (specGap_ptX_continuousOn p hp).tendsto (IsOpen.mem_nhds hU hzU)
  have hEq :
      (fun p' => specGapAllCuspSum Γ d ψ (ptX F p')) =ᶠ[𝓝[ posSet F ] p]
        (fun p' => Finset.sum hS.toFinset (fun r =>
          ψ (specGapAllCuspHeight Γ d r (ptX F p')))) := by
    filter_upwards [hpt_event] with p' hpu
    have hpK : ptX F p' ∈ K := hUK hpu
    have hsum := specGapAllCuspSum_eq_finset d ψ A hψzero K hS (ptX F p') hpK
    simpa [S] using hsum
  have hEqAt : specGapAllCuspSum Γ d ψ (ptX F p) =
      Finset.sum hS.toFinset (fun r => ψ (specGapAllCuspHeight Γ d r (ptX F p))) := by
    exact specGapAllCuspSum_eq_finset d ψ A hψzero K hS z (hUK hzU)
  exact (hfiniteSum p hp).congr_of_eventuallyEq hEq hEqAt

private theorem fderiv_ofReal_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x : E) (v : E) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => (u y : ℂ)) x v = (fderiv ℝ u x v : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt
  have hh := h.fderiv
  change (fderiv ℝ (Complex.ofRealCLM ∘ u) x) v = _
  rw [hh]
  simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

private theorem fderiv_posfun_eq_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x : E) (v : E) (hu : ContDiffAt ℝ ∞ u x)
    (hpos : ∀ y, 0 < u y) :
    fderiv ℝ u x v = u x * fderiv ℝ (fun y => Real.log (u y)) x v := by
  have hlog : ContDiffAt ℝ ∞ (fun y => Real.log (u y)) x := hu.log (hpos x).ne'
  have hlogDiff : DifferentiableAt ℝ (fun y => Real.log (u y)) x := by
    exact hlog.differentiableAt (by norm_num)
  have hfun : u = fun y => Real.exp (Real.log (u y)) := by
    funext y
    exact (Real.exp_log (hpos y)).symm
  calc
    fderiv ℝ u x v = fderiv ℝ (fun y => Real.exp (Real.log (u y))) x v :=
      congrArg (fun f => fderiv ℝ f x v) hfun
    _ = (Real.exp (Real.log (u x)) •
        fderiv ℝ (fun y => Real.log (u y)) x) v :=
      congrArg (fun D => D v) (fderiv_exp hlogDiff)
    _ = u x * fderiv ℝ (fun y => Real.log (u y)) x v := by
      simp [Real.exp_log (hpos x), smul_eq_mul]

private theorem fderiv_real_comp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (u : E → ℝ) (x : E) (v : E)
    (hψ : DifferentiableAt ℝ ψ (u x)) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => ψ (u y)) x v = deriv ψ (u x) * fderiv ℝ u x v := by
  have hcomp := hψ.hasFDerivAt.comp x hu.hasFDerivAt
  have hcomp' := hcomp.fderiv
  calc
    fderiv ℝ (fun y => ψ (u y)) x v = fderiv ℝ ψ (u x) (fderiv ℝ u x v) := by
      change (fderiv ℝ (ψ ∘ u) x) v = _
      rw [hcomp']
      simp only [ContinuousLinearMap.comp_apply]
    _ = deriv ψ (u x) * fderiv ℝ u x v :=
      fderiv_eq_deriv_mul (f := ψ) (x := u x) (y := fderiv ℝ u x v)

private theorem fullGradient_real_comp (H : X F → ℝ) (hH : IsSmoothRealX F H)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (z : X F) :
    fullGradient F (fun x => (ψ (H x) : ℂ)) z =
      Complex.ofReal (deriv ψ (H z)) • fullGradient F (fun x => (H x : ℂ)) z := by
  ext wj
  rcases wj with ⟨w, j⟩
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := coordsX_mem_posSet z
  have hpt : ptX F p = z := ptX_coordsX z
  have hHbase : ContDiffOn ℝ ∞ (fun p' => H (ptX F p')) (posSet F) := hH
  have hHc : ContDiffAt ℝ ∞ (fun p' => H (ptX F p')) p :=
    hHbase.contDiffAt (specGap_posSet_open.mem_nhds hp)
  have hHdiff : DifferentiableAt ℝ (fun p' => H (ptX F p')) p :=
    hHc.differentiableAt (by norm_num)
  have hψAt : ContDiffAt ℝ ∞ ψ (H (ptX F p)) := hψ.contDiffAt
  have hψdiff : DifferentiableAt ℝ ψ (H (ptX F p)) :=
    hψAt.differentiableAt (by norm_num)
  have hcompdiff : DifferentiableAt ℝ (fun p' => ψ (H (ptX F p'))) p :=
    hψdiff.comp p hHdiff
  have hcomp := fderiv_real_comp_apply ψ (fun p' => H (ptX F p')) p
    (placeDirection F w j) hψdiff hHdiff
  have hcastComp := fderiv_ofReal_apply (fun p' => ψ (H (ptX F p'))) p
    (placeDirection F w j) hcompdiff
  have hcastH := fderiv_ofReal_apply (fun p' => H (ptX F p')) p
    (placeDirection F w j) hHdiff
  have hHval : H (ptX F p) = H z := congrArg H hpt
  change (p w).2 *
      fderiv ℝ (fun p' => (ψ (H (ptX F p')) : ℂ)) p
        (placeDirection F w j) =
    Complex.ofReal (deriv ψ (H z)) * ((p w).2 *
      fderiv ℝ (fun p' => (H (ptX F p') : ℂ)) p
        (placeDirection F w j))
  rw [hHval.symm]
  rw [hcastComp, hcomp, hcastH]
  simp only [Complex.ofReal_mul]
  ring

private theorem fullGradient_finset_sum {ι : Type*} (S : Finset ι)
    (f : ι → X F → ℂ) (hf : ∀ i ∈ S, IsSmoothX F (f i)) (z : X F) :
    fullGradient F (fun x => Finset.sum S (fun i => f i x)) z =
      Finset.sum S (fun i => fullGradient F (f i) z) := by
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := coordsX_mem_posSet z
  change WithLp.toLp 2 (fun wj : InfinitePlace F × Fin 3 => placeGradient F wj.1
      (fun x => Finset.sum S (fun i => f i x)) z wj.2) =
    Finset.sum S (fun i => WithLp.toLp 2
      (fun wj : InfinitePlace F × Fin 3 => placeGradient F wj.1 (f i) z wj.2))
  rw [← WithLp.toLp_sum]
  congr 1
  funext wj
  rcases wj with ⟨w, j⟩
  simp only [Finset.sum_apply, placeGradient]
  change ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (fun p' => Finset.sum S (fun i => f i (ptX F p')))
        (coordsX F z) (placeDirection F w j) =
    Finset.sum S (fun i => ((coordsX F z w).2 : ℂ) *
      fderiv ℝ (fun p' => f i (ptX F p')) (coordsX F z) (placeDirection F w j))
  rw [fderiv_fun_sum]
  · simp [Finset.mul_sum]
  · intro i hi
    have hfi : ContDiffOn ℝ ∞ (fun p' => f i (ptX F p')) (posSet F) := hf i hi
    exact (hfi.contDiffAt (specGap_posSet_open.mem_nhds hp)).differentiableAt (by norm_num)

private theorem finset_sum_le_at_most_one_nonzero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbounds : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ C)
    (huniq : ∀ i ∈ S, ∀ j ∈ S, f i ≠ 0 → f j ≠ 0 → i = j) :
    Finset.sum S f ≤ C := by
  classical
  by_cases hex : ∃ i ∈ S, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := hex
    rw [Finset.sum_eq_single i]
    · exact hbounds i hi |>.2
    · intro j hj hji
      by_contra hfj
      exact hji (huniq i hi j hj hfi hfj).symm
    · intro hnot
      exact (hnot hi).elim
  · have hzero : ∀ i ∈ S, f i = 0 := by
      intro i hi
      by_contra hfi
      exact hex ⟨i, hi, hfi⟩
    rw [Finset.sum_eq_zero hzero]
    exact hC

private theorem specGapAllCuspSum_fullGradient_eq_finset {Γ : Subgroup SL(2,𝓞 F)}
    [Γ.FiniteIndex] (d : SiegelData F Γ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (A : ℝ) (hA : 0 < A) (hψzero : ∀ t ≤ A, ψ t = 0) (z : X F) :
    ∃ S : Finset (SpecGapCuspIndex Γ d),
      fullGradient F (fun x => (specGapAllCuspSum Γ d ψ x : ℂ)) z =
        Finset.sum S (fun r => fullGradient F
          (fun x => (ψ (specGapAllCuspHeight Γ d r x) : ℂ)) z) := by
  classical
  obtain ⟨S, _, hEq⟩ := specGapAllCuspSum_locally_eq_finset d ψ A hA hψzero z
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := coordsX_mem_posSet z
  have hfilter : 𝓝[ posSet F ] p = 𝓝 p := nhdsWithin_eq_nhds.mpr
    (specGap_posSet_open.mem_nhds hp)
  have hEqNhds : (fun p' : Coord F => (specGapAllCuspSum Γ d ψ (ptX F p') : ℂ)) =ᶠ[𝓝 p]
      (fun p' : Coord F => Finset.sum S
        (fun r => (ψ (specGapAllCuspHeight Γ d r (ptX F p')) : ℂ))) := by
    have h := hEq
    rw [hfilter] at h
    filter_upwards [h] with p' hp'
    rw [hp', Complex.ofReal_sum]
  have hder := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEqNhds
  let fC : SpecGapCuspIndex Γ d → X F → ℂ :=
    fun r x => (ψ (specGapAllCuspHeight Γ d r x) : ℂ)
  have hfC : ∀ r ∈ S, IsSmoothX F (fC r) := by
    intro r hr
    rcases r with ⟨i, q⟩
    change ContDiffOn ℝ ∞
      (fun p' => (ψ (specGapCosetHeight Γ (d.σ i) q (ptX F p')) : ℂ)) (posSet F)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (specGapCosetWeight_smooth d ψ hψ i q)
  have hgradEq :
      fullGradient F (fun x => (specGapAllCuspSum Γ d ψ x : ℂ)) z =
        fullGradient F (fun x => Finset.sum S (fun r => fC r x)) z := by
    ext wj
    rcases wj with ⟨w, j⟩
    change (coordsX F z w).2 *
        fderiv ℝ (fun p' => (specGapAllCuspSum Γ d ψ (ptX F p') : ℂ)) p
          (placeDirection F w j) =
      (coordsX F z w).2 *
        fderiv ℝ (fun p' => Finset.sum S (fun r => fC r (ptX F p'))) p
          (placeDirection F w j)
    rw [hder]
  exact ⟨S, hgradEq.trans (fullGradient_finset_sum S fC hfC z)⟩

private theorem fullGradient_norm_sq_eq_totalGradNormSq (f : X F → ℂ) (z : X F) :
    ‖fullGradient F f z‖ ^ 2 = totalGradNormSq F f z := by
  rw [fullGradient, PiLp.norm_sq_eq_of_L2]
  simp [totalGradNormSq, placeGradNormSq, Complex.normSq_eq_norm_sq,
    Fintype.sum_prod_type]

private theorem logNormHeight_action_smooth (g : SL(2,F)) :
    IsSmoothX F (fun z => logNormHeight F (g • z)) := by
  change ContDiffOn ℝ ∞
    (fun p => (Real.log (normHeight F (g • ptX F p)) : ℂ)) (posSet F)
  have h := normHeight_action_smooth g
  have hlog : ContDiffOn ℝ ∞
      (fun p => Real.log (normHeight F (g • ptX F p))) (posSet F) :=
    h.log (fun p hp => (normHeight_pos (g • ptX F p)).ne')
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hlog

private theorem logNormHeight_smooth : IsSmoothX F (logNormHeight F) := by
  have h := logNormHeight_action_smooth (1 : SL(2,F))
  simpa using h

private theorem specGapCosetLogGradient_norm_sq (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : CuspCosets F Γ σ) (z : X F) :
    ‖fullGradient F (fun x => logNormHeight F
      ((σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) • x)) z‖ ^ 2 = placeCount F := by
  let g : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let gPlaces : InfinitePlace F → SL(2,ℂ) := toInf F g
  have hzero : IsSmoothX F (fun _ => (0 : ℂ)) := by
    change ContDiffOn ℝ ∞ (fun _ => (0 : ℂ)) (posSet F)
    exact contDiffOn_const
  have hG4 := G4_energy gPlaces (logNormHeight F) (fun _ => (0 : ℂ))
    logNormHeight_smooth hzero
  rw [fullGradient_norm_sq_eq_totalGradNormSq]
  calc
    totalGradNormSq F (fun x => logNormHeight F (g • x)) z =
        totalGradNormSq F (fun x => logNormHeight F (actAtPlaces F gPlaces x)) z := by
          rfl
    _ = totalGradNormSq F (logNormHeight F) (actAtPlaces F gPlaces z) := hG4.2.1 z
    _ = placeCount F := hG4.2.2 (actAtPlaces F gPlaces z)

private theorem specGapCosetHeight_gradient_norm (Γ : Subgroup SL(2,𝓞 F))
    (σ : SL(2,F)) (q : CuspCosets F Γ σ) (z : X F) :
    ‖fullGradient F (fun x => (specGapCosetHeight Γ σ q x : ℂ)) z‖ =
      specGapCosetHeight Γ σ q z * Real.sqrt (placeCount F) := by
  let g : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  let H : X F → ℝ := fun x => normHeight F (g • x)
  let L : X F → ℂ := fun x => logNormHeight F (g • x)
  have hsmul (x : X F) : σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • x) = g • x := by
    change σ⁻¹ • (toSLF F ((q.out : Γ) : SL(2,𝓞 F)) • x) = _
    rw [smul_smul]
  have hH : (fun x => specGapCosetHeight Γ σ q x) = H := by
    funext x
    simp only [specGapCosetHeight, H, hsmul]
  have hHvalue : specGapCosetHeight Γ σ q z = normHeight F (g • z) := by
    simpa [H] using congrFun hH z
  have hlogsq : ‖fullGradient F L z‖ ^ 2 = placeCount F := by
    simpa only [L] using specGapCosetLogGradient_norm_sq Γ σ q z
  have hlognorm : ‖fullGradient F L z‖ = Real.sqrt (placeCount F) := by
    have hp : 0 ≤ placeCount F := by
      unfold placeCount
      exact_mod_cast (Nat.zero_le (Fintype.card (InfinitePlace F)))
    have hsq : ‖fullGradient F L z‖ ^ 2 = (Real.sqrt (placeCount F)) ^ 2 := by
      rw [Real.sq_sqrt hp]
      exact hlogsq
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq
  have hfull : fullGradient F (fun x => (H x : ℂ)) z =
      (H z : ℂ) • fullGradient F L z := by
    ext wj
    rcases wj with ⟨w, j⟩
    let p : Coord F := coordsX F z
    have hp : p ∈ posSet F := coordsX_mem_posSet z
    have hpt : ptX F p = z := ptX_coordsX z
    have hHval : H (ptX F p) = H z := congrArg H hpt
    have hHbase : ContDiffOn ℝ ∞ (fun p' => H (ptX F p')) (posSet F) :=
      normHeight_action_smooth g
    have hHc : ContDiffAt ℝ ∞ (fun p' => H (ptX F p')) p :=
      hHbase.contDiffAt (specGap_posSet_open.mem_nhds hp)
    have hHcDiff : DifferentiableAt ℝ (fun p' => H (ptX F p')) p :=
      hHc.differentiableAt (by norm_num)
    have hHcPos : ∀ p', 0 < H (ptX F p') := fun p' => normHeight_pos _
    have hlogDiff : DifferentiableAt ℝ (fun p' => Real.log (H (ptX F p'))) p :=
      (hHc.log (hHcPos p).ne').differentiableAt (by norm_num)
    have hder : fderiv ℝ (fun p' => H (ptX F p')) p (placeDirection F w j) =
        H (ptX F p) * fderiv ℝ (fun p' => Real.log (H (ptX F p'))) p
          (placeDirection F w j) := by
      exact fderiv_posfun_eq_log _ p (placeDirection F w j) hHc (fun p' => hHcPos p')
    have hderC : fderiv ℝ (fun p' => (H (ptX F p') : ℂ)) p (placeDirection F w j) =
        (H (ptX F p) : ℂ) *
          fderiv ℝ (fun p' => (Real.log (H (ptX F p')) : ℂ)) p
            (placeDirection F w j) := by
      rw [fderiv_ofReal_apply _ _ _ hHcDiff,
        fderiv_ofReal_apply _ _ _ hlogDiff]
      simpa only [Complex.ofReal_mul] using
        congrArg (fun r : ℝ => (r : ℂ)) hder
    change (coordsX F z w).2 *
        fderiv ℝ (fun p' => (H (ptX F p') : ℂ)) (coordsX F z)
          (placeDirection F w j) =
      (H z : ℂ) * ((coordsX F z w).2 *
        fderiv ℝ (fun p' => logNormHeight F (g • ptX F p')) (coordsX F z)
          (placeDirection F w j))
    rw [hHval.symm]
    have hlogchart : (fun p' => logNormHeight F (g • ptX F p')) =
        (fun p' => (Real.log (H (ptX F p')) : ℂ)) := by
      funext p'
      rfl
    rw [hlogchart, hderC]
    ring
  have hHcomplex : (fun x => (specGapCosetHeight Γ σ q x : ℂ)) =
      (fun x => (H x : ℂ)) := by
    funext x
    exact congrArg Complex.ofReal (congrFun hH x)
  rw [hHcomplex, hfull, norm_smul,
    Complex.norm_of_nonneg (le_of_lt (normHeight_pos (g • z))), hlognorm]
  rw [hHvalue]

theorem specGapHeightCutoff_deriv_bound_on_support {A t : ℝ} (hA : 0 < A)
    (hτ : deriv (specGapHeightCutoff A) t ≠ 0) : A ≤ t ∧ t ≤ 2 * A := by
  constructor
  · by_contra h
    exact hτ (specGapHeightCutoff_deriv_eq_zero_of_lt hA (lt_of_not_ge h))
  · by_contra h
    exact hτ (specGapHeightCutoff_deriv_eq_zero_of_gt hA (lt_of_not_ge h))

theorem specGapCosetHeight_cutoff_gradient_bound {Γ : Subgroup SL(2,𝓞 F)}
    (σ : SL(2,F)) (q : CuspCosets F Γ σ) (A B : ℝ) (hA : 0 < A)
    (hB : 0 ≤ B) (hderiv : ∀ t, ‖deriv (specGapHeightCutoff A) t‖ ≤ B / A)
    (z : X F) :
    ‖fullGradient F
      (fun x => (specGapHeightCutoff A (specGapCosetHeight Γ σ q x) : ℂ)) z‖ ≤
        2 * B * Real.sqrt (placeCount F) := by
  let h := specGapCosetHeight Γ σ q z
  have hpos : 0 < h := specGapCosetHeight_pos Γ σ q z
  have hbound := specGapCosetHeight_gradient_norm Γ σ q z
  have hsmooth := specGapCosetHeight_smooth Γ σ q
  have hτ : ContDiff ℝ ∞ (specGapHeightCutoff A) :=
    (specGapHeightCutoff_isCuspCutoff hA).1
  have hcomp := fullGradient_real_comp (specGapCosetHeight Γ σ q) hsmooth
    (specGapHeightCutoff A) hτ z
  by_cases hd : deriv (specGapHeightCutoff A) h = 0
  · rw [hcomp]
    simp [h, hd]
    positivity
  · obtain ⟨_, h_le⟩ := specGapHeightCutoff_deriv_bound_on_support hA hd
    have hnormScalar :
        ‖Complex.ofReal (deriv (specGapHeightCutoff A) h)‖ =
          ‖deriv (specGapHeightCutoff A) h‖ := by
      calc
        _ = |deriv (specGapHeightCutoff A) h| := RCLike.norm_ofReal _
        _ = _ := (Real.norm_eq_abs _).symm
    rw [hcomp, norm_smul, hnormScalar]
    calc
      ‖deriv (specGapHeightCutoff A) h‖ *
          ‖fullGradient F (fun x => (specGapCosetHeight Γ σ q x : ℂ)) z‖ ≤
        (B / A) * (h * Real.sqrt (placeCount F)) := by
          rw [hbound]
          exact mul_le_mul_of_nonneg_right (hderiv h) (by positivity)
      _ ≤ (B / A) * ((2 * A) * Real.sqrt (placeCount F)) := by
          gcongr
      _ = 2 * B * Real.sqrt (placeCount F) := by
        field_simp [hA.ne']

theorem specGapAllCuspCutoff_gradient_bound {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (hderiv : ∀ t, ‖deriv (specGapHeightCutoff A) t‖ ≤ B / A)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (z : X F) :
    ‖fullGradient F (fun x =>
      (specGapAllCuspSum Γ d (specGapHeightCutoff A) x : ℂ)) z‖ ≤
        2 * B * Real.sqrt (placeCount F) := by
  classical
  let τ := specGapHeightCutoff A
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  obtain ⟨S, hdecomp⟩ := specGapAllCuspSum_fullGradient_eq_finset d τ
    hcut.1 A hA hcut.2.2.1 z
  let gradTerm : SpecGapCuspIndex Γ d → GradientField F := fun r =>
    fullGradient F (fun x => (τ (specGapAllCuspHeight Γ d r x) : ℂ)) z
  have hgradBound (r : SpecGapCuspIndex Γ d) : ‖gradTerm r‖ ≤ 2 * B * Real.sqrt (placeCount F) := by
    rcases r with ⟨i, q⟩
    exact specGapCosetHeight_cutoff_gradient_bound (d.σ i) q A B hA hB hderiv z
  have huniq : ∀ r ∈ S, ∀ r' ∈ S, gradTerm r ≠ 0 → gradTerm r' ≠ 0 → r = r' := by
    intro r hr r' hr' hne hne'
    have hderNe (s : SpecGapCuspIndex Γ d) (hneS : gradTerm s ≠ 0) :
        deriv τ (specGapAllCuspHeight Γ d s z) ≠ 0 := by
      intro hz
      have hsmooth : IsSmoothRealX F (fun x => specGapAllCuspHeight Γ d s x) := by
        rcases s with ⟨i, q⟩
        exact specGapCosetHeight_smooth Γ (d.σ i) q
      have heq := fullGradient_real_comp (fun x => specGapAllCuspHeight Γ d s x)
        hsmooth τ hcut.1 z
      have hzero : gradTerm s = 0 := by
        dsimp [gradTerm]
        simpa [τ, hz] using heq
      exact hneS hzero
    have hs := specGapHeightCutoff_deriv_bound_on_support hA (hderNe r hne)
    have hs' := specGapHeightCutoff_deriv_bound_on_support hA (hderNe r' hne')
    exact hsep r r' z hs.1 hs'.1
  have hsumBound : Finset.sum S (fun r => ‖gradTerm r‖) ≤
      2 * B * Real.sqrt (placeCount F) := by
    apply finset_sum_le_at_most_one_nonzero S (fun r => ‖gradTerm r‖)
      (2 * B * Real.sqrt (placeCount F)) (by positivity)
    · intro r hr
      exact ⟨norm_nonneg _, hgradBound r⟩
    · intro r hr r' hr' hnr hnr'
      have hgradNe (s : SpecGapCuspIndex Γ d) (hs : ‖gradTerm s‖ ≠ 0) :
          gradTerm s ≠ 0 := by
        intro hzero
        apply hs
        simp [hzero]
      exact huniq r hr r' hr' (hgradNe r hnr) (hgradNe r' hnr')
  calc
    ‖fullGradient F (fun x =>
        (specGapAllCuspSum Γ d τ x : ℂ)) z‖ =
        ‖Finset.sum S gradTerm‖ := by rw [hdecomp]
    _ ≤ Finset.sum S (fun r => ‖gradTerm r‖) := norm_sum_le _ _
    _ ≤ 2 * B * Real.sqrt (placeCount F) := hsumBound

/-- The residual all-cusp cutoff, equal to one on the compact part. -/
def specGapAllCuspRho (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (z : X F) : ℝ :=
  1 - specGapAllCuspSum Γ d (specGapHeightCutoff A) z

theorem specGapAllCuspRho_smooth {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A) :
    IsSmoothRealX F (specGapAllCuspRho Γ d A) := by
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  have hs := specGapAllCuspSum_smooth d (specGapHeightCutoff A) hcut.1 A hA hcut.2.2.1
  change ContDiffOn ℝ ∞ (fun p => 1 -
    specGapAllCuspSum Γ d (specGapHeightCutoff A) (ptX F p)) (posSet F)
  exact contDiffOn_const.sub hs

theorem specGapAllCuspRho_invariant {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (γ : Γ) (z : X F) :
    specGapAllCuspRho Γ d A ((γ : SL(2,𝓞 F)) • z) = specGapAllCuspRho Γ d A z := by
  simp [specGapAllCuspRho, specGapAllCuspSum_invariant]

theorem specGapAllCuspRho_bounds {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (z : X F) : 0 ≤ specGapAllCuspRho Γ d A z ∧ specGapAllCuspRho Γ d A z ≤ 1 := by
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  have hs := specGapAllCuspSum_bounds d (specGapHeightCutoff A) A hA hcut.2.2.1
    (fun t => specGapHeightCutoff_bounds (A := A) t) hsep z
  dsimp [specGapAllCuspRho]
  constructor <;> linarith

theorem specGapAllCuspRho_gradient_bound {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (hderiv : ∀ t, ‖deriv (specGapHeightCutoff A) t‖ ≤ B / A)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (z : X F) :
    ‖fullGradient F (fun x => (specGapAllCuspRho Γ d A x : ℂ)) z‖ ≤
      2 * B * Real.sqrt (placeCount F) := by
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  have hs := specGapAllCuspSum_smooth d (specGapHeightCutoff A) hcut.1 A hA hcut.2.2.1
  have hpsi : ContDiff ℝ ∞ (fun t : ℝ => 1 - t) := by fun_prop
  have hcomp := fullGradient_real_comp (specGapAllCuspSum Γ d (specGapHeightCutoff A)) hs
    (fun t => 1 - t) hpsi z
  have hderivNeg (t : ℝ) : deriv (fun s : ℝ => 1 - s) t = -1 := by
    simpa using ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).deriv
  have hgrad :
      fullGradient F (fun x => (specGapAllCuspRho Γ d A x : ℂ)) z =
        -fullGradient F (fun x =>
          (specGapAllCuspSum Γ d (specGapHeightCutoff A) x : ℂ)) z := by
    simpa [specGapAllCuspRho, hderivNeg] using hcomp
  rw [hgrad]
  simpa only [norm_neg] using
    (specGapAllCuspCutoff_gradient_bound d A B hA hB hderiv hsep z)

theorem specGapAllCuspRho_height_lt_double {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (z : X F) (hρ : specGapAllCuspRho Γ d A z ≠ 0)
    (p : SpecGapCuspIndex Γ d) : specGapAllCuspHeight Γ d p z < 2 * A := by
  by_contra hnot
  have hhigh : 2 * A ≤ specGapAllCuspHeight Γ d p z := le_of_not_gt hnot
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  have hτp : specGapHeightCutoff A (specGapAllCuspHeight Γ d p z) = 1 :=
    hcut.2.2.2 _ hhigh
  have hpgt : A < specGapAllCuspHeight Γ d p z := by
    by_contra hle
    have hzero := hcut.2.2.1 _ (le_of_not_gt hle)
    rw [hzero] at hτp
    norm_num at hτp
  have hsumEq : specGapAllCuspSum Γ d (specGapHeightCutoff A) z =
      specGapHeightCutoff A (specGapAllCuspHeight Γ d p z) := by
    classical
    unfold specGapAllCuspSum
    rw [tsum_eq_single p]
    intro p' hne
    by_contra hnonzero
    have hp'gt : A < specGapAllCuspHeight Γ d p' z := by
      by_contra hle
      exact hnonzero (hcut.2.2.1 _ (le_of_not_gt hle))
    exact hne (hsep p p' z (le_of_lt hpgt) (le_of_lt hp'gt)).symm
  have hρzero : specGapAllCuspRho Γ d A z = 0 := by
    simp [specGapAllCuspRho, hsumEq, hτp]
  exact hρ hρzero

theorem specGapAllCuspRho_mem_compactOrbit {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p')
    (z : X F) (hρ : specGapAllCuspRho Γ d A z ≠ 0) :
    z ∈ SiegelData.compactOrbit F d (2 * A) := by
  have hcutoffBound := specGapAllCuspRho_height_lt_double d A hA hsep z hρ
  have hR13 := (R13_compact_part Γ d).2 (2 * A) (by positivity) z
  apply hR13
  intro i γ
  let q : CuspCosets F Γ (d.σ i) :=
    Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) γ
  let p : SpecGapCuspIndex Γ d := ⟨i, q⟩
  have hrep : specGapCosetHeight Γ (d.σ i) q z =
      normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) := by
    exact specGapCosetHeight_rep_eq Γ (d.σ i) q.out γ (Quotient.mk_out γ) z
  have hp : specGapAllCuspHeight Γ d p z < 2 * A := hcutoffBound p
  change normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ 2 * A
  rw [← hrep]
  exact le_of_lt hp

theorem specGapAllCuspRho_support {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A)
    (hsep : ∀ p p' : SpecGapCuspIndex Γ d, ∀ z : X F,
      A ≤ specGapAllCuspHeight Γ d p z → A ≤ specGapAllCuspHeight Γ d p' z → p = p') :
    ∃ K : Set (X F), IsCompact K ∧
      {z | specGapAllCuspRho Γ d A z ≠ 0} ⊆ orbitSaturation F Γ K := by
  classical
  letI : Fintype d.ι := d.fintype
  let K : Set (X F) := ⋃ i, SiegelData.compactBox F d i (2 * A)
  have hbox (i : d.ι) : IsCompact (SiegelData.compactBox F d i (2 * A)) :=
    (R13_compact_part Γ d).1 (2 * A) (by positivity) i
  have hK : IsCompact K := by
    simpa [K] using isCompact_iUnion hbox
  refine ⟨K, hK, ?_⟩
  intro z hz
  have hzcompact := specGapAllCuspRho_mem_compactOrbit d A hA hsep z hz
  rcases hzcompact with ⟨i, hi⟩
  rcases hi with ⟨γ, x, hx, hγx⟩
  refine ⟨γ, x, ?_, hγx⟩
  exact Set.mem_iUnion.2 ⟨i, hx⟩

theorem fullGradient_mul (f g : X F → ℂ) (hf : IsSmoothX F f) (hg : IsSmoothX F g)
    (z : X F) :
    fullGradient F (fun x => f x * g x) z =
      f z • fullGradient F g z + g z • fullGradient F f z := by
  ext wj
  rcases wj with ⟨w, j⟩
  let p : Coord F := coordsX F z
  have hp : p ∈ posSet F := coordsX_mem_posSet z
  have hpt : ptX F p = z := ptX_coordsX z
  have hfAt : ContDiffAt ℝ ∞ (fun p' => f (ptX F p')) p :=
    hf.contDiffAt (specGap_posSet_open.mem_nhds hp)
  have hgAt : ContDiffAt ℝ ∞ (fun p' => g (ptX F p')) p :=
    hg.contDiffAt (specGap_posSet_open.mem_nhds hp)
  have hfDiff : DifferentiableAt ℝ (fun p' => f (ptX F p')) p :=
    hfAt.differentiableAt (by norm_num)
  have hgDiff : DifferentiableAt ℝ (fun p' => g (ptX F p')) p :=
    hgAt.differentiableAt (by norm_num)
  change (p w).2 * fderiv ℝ (fun p' => f (ptX F p') * g (ptX F p')) p
      (placeDirection F w j) =
    f z * ((p w).2 * fderiv ℝ (fun p' => g (ptX F p')) p (placeDirection F w j)) +
    g z * ((p w).2 * fderiv ℝ (fun p' => f (ptX F p')) p (placeDirection F w j))
  rw [fderiv_fun_mul hfDiff hgDiff]
  rw [← hpt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem specGapAllCuspRho_gradient_eq_neg_sum {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A) (z : X F) :
    fullGradient F (fun x => (specGapAllCuspRho Γ d A x : ℂ)) z =
      -fullGradient F (fun x =>
        (specGapAllCuspSum Γ d (specGapHeightCutoff A) x : ℂ)) z := by
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  have hs := specGapAllCuspSum_smooth d (specGapHeightCutoff A) hcut.1 A hA hcut.2.2.1
  have hpsi : ContDiff ℝ ∞ (fun t : ℝ => 1 - t) := by fun_prop
  have hcomp := fullGradient_real_comp (specGapAllCuspSum Γ d (specGapHeightCutoff A)) hs
    (fun t => 1 - t) hpsi z
  have hderivNeg (t : ℝ) : deriv (fun s : ℝ => 1 - s) t = -1 := by
    simpa using ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).deriv
  simpa [specGapAllCuspRho, hderivNeg] using hcomp

theorem specGapAllCuspRho_gradient_zero_of_below {Γ : Subgroup SL(2,𝓞 F)} [Γ.FiniteIndex]
    (d : SiegelData F Γ) (A : ℝ) (hA : 0 < A) (z : X F)
    (hbelow : ∀ p : SpecGapCuspIndex Γ d, specGapAllCuspHeight Γ d p z < A) :
    fullGradient F (fun x => (specGapAllCuspRho Γ d A x : ℂ)) z = 0 := by
  have hcut := specGapHeightCutoff_isCuspCutoff hA
  obtain ⟨S, hdecomp⟩ := specGapAllCuspSum_fullGradient_eq_finset d
    (specGapHeightCutoff A) hcut.1 A hA hcut.2.2.1 z
  have hterm (p : SpecGapCuspIndex Γ d) :
      fullGradient F (fun x =>
        (specGapHeightCutoff A (specGapAllCuspHeight Γ d p x) : ℂ)) z = 0 := by
    have hp : deriv (specGapHeightCutoff A) (specGapAllCuspHeight Γ d p z) = 0 :=
      specGapHeightCutoff_deriv_eq_zero_of_lt hA (hbelow p)
    have hsmooth : IsSmoothRealX F (fun x => specGapAllCuspHeight Γ d p x) := by
      rcases p with ⟨i, q⟩
      exact specGapCosetHeight_smooth Γ (d.σ i) q
    have hcomp := fullGradient_real_comp (fun x => specGapAllCuspHeight Γ d p x)
      hsmooth (specGapHeightCutoff A) hcut.1 z
    simpa [hp] using hcomp
  have hsumzero : fullGradient F (fun x =>
      (specGapAllCuspSum Γ d (specGapHeightCutoff A) x : ℂ)) z = 0 := by
    rw [hdecomp]
    apply Finset.sum_eq_zero
    intro p hp
    exact hterm p
  rw [specGapAllCuspRho_gradient_eq_neg_sum d A hA z, hsumzero]
  simp

private theorem specGapAllCuspHeight_eventually_below {Γ : Subgroup SL(2,𝓞 F)}
    [Γ.FiniteIndex] (d : SiegelData F Γ) (A₀ : ℝ) (hA₀ : 0 < A₀) (z : X F) :
    ∀ᶠ n : ℕ in atTop,
      ∀ p : SpecGapCuspIndex Γ d,
        specGapAllCuspHeight Γ d p z < A₀ + (n : ℝ) + 1 := by
  classical
  let K : Set (X F) := {z}
  let S := specGapActiveCuspSet Γ d A₀ K
  have hS : S.Finite := specGapActiveCuspSet_finite Γ d A₀ hA₀ K isCompact_singleton
  let s := hS.toFinset
  have hfinite : ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ s, specGapAllCuspHeight Γ d p z < A₀ + (n : ℝ) + 1 := by
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [] with n
        intro p hp
        simp at hp
    | @insert p s hnot ih =>
        obtain ⟨N, hN⟩ := exists_nat_gt
          (specGapAllCuspHeight Γ d p z - A₀ - 1)
        have he : ∀ᶠ n : ℕ in atTop,
            specGapAllCuspHeight Γ d p z < A₀ + (n : ℝ) + 1 := by
          filter_upwards [eventually_ge_atTop N] with n hn
          have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        filter_upwards [ih, he] with n hi he_n
        intro q hmem
        rcases Finset.mem_insert.mp hmem with heq | hmem
        · cases heq
          exact he_n
        · exact hi q hmem
  filter_upwards [hfinite] with n hn p
  by_cases hp : p ∈ S
  · exact hn p ((Set.Finite.mem_toFinset hS).2 hp)
  · have hbelow : specGapAllCuspHeight Γ d p z < A₀ := by
      by_contra hnot
      apply hp
      exact specGapActiveCuspSet_mem_of_height d A₀ K p z (by simp [K])
        (le_of_not_gt hnot)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hA₀n : A₀ ≤ A₀ + (n : ℝ) + 1 := by nlinarith
    exact lt_of_lt_of_le hbelow hA₀n

theorem specGapAllCuspRho_eventually_one_zero_grad {Γ : Subgroup SL(2,𝓞 F)}
    [Γ.FiniteIndex] (d : SiegelData F Γ) (A₀ : ℝ) (hA₀ : 0 < A₀) (z : X F) :
    ∀ᶠ n : ℕ in atTop,
      specGapAllCuspRho Γ d (A₀ + (n : ℝ) + 1) z = 1 ∧
      fullGradient F (fun x =>
        (specGapAllCuspRho Γ d (A₀ + (n : ℝ) + 1) x : ℂ)) z = 0 := by
  filter_upwards [specGapAllCuspHeight_eventually_below d A₀ hA₀ z] with n hbelow
  have hAn : 0 < A₀ + (n : ℝ) + 1 := by positivity
  have hcut := specGapHeightCutoff_isCuspCutoff hAn
  have hterms : ∀ p : SpecGapCuspIndex Γ d,
      specGapHeightCutoff (A₀ + (n : ℝ) + 1)
        (specGapAllCuspHeight Γ d p z) = 0 := by
    intro p
    exact hcut.2.2.1 _ (le_of_lt (hbelow p))
  have hsumzero : specGapAllCuspSum Γ d
      (specGapHeightCutoff (A₀ + (n : ℝ) + 1)) z = 0 := by
    unfold specGapAllCuspSum
    calc
      _ = ∑' p, (0 : ℝ) := tsum_congr hterms
      _ = 0 := by simp
  constructor
  · simp [specGapAllCuspRho, hsumzero]
  · exact specGapAllCuspRho_gradient_zero_of_below d _ hAn z hbelow

end ArtinPrimitiveRoots.A1.Spec

end
