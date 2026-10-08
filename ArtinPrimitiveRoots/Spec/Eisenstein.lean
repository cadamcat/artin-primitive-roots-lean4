import ArtinPrimitiveRoots.Spec.Reduction
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Eisenstein-series nodes E1--E7. This first stage states E1--E2. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private lemma eis_cusp_height_rightRel (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ γ' : Γ)
    (h : QuotientGroup.rightRel (cuspStab F Γ σ) γ γ') (z : X F) :
    normHeight F (σ⁻¹ • ((γ' : Γ) • z)) =
      normHeight F (σ⁻¹ • ((γ : Γ) • z)) := by
  have hstab : γ' * γ⁻¹ ∈ cuspStab F Γ σ :=
    QuotientGroup.rightRel_apply.mp h
  have htri := hstab
  simp only [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at htri
  let δ : Γ := γ' * γ⁻¹
  have hγ' : (γ' : Γ) • z = toSLF F ((γ' : Γ) : SL(2,𝓞 F)) • z := rfl
  have hγ : (γ : Γ) • z = toSLF F ((γ : Γ) : SL(2,𝓞 F)) • z := rfl
  have hgroup : γ' = δ * γ := by
    dsimp [δ]
    group
  have hcoerce : ((δ * γ : Γ) : SL(2,𝓞 F)) =
      (δ : SL(2,𝓞 F)) * (γ : SL(2,𝓞 F)) := rfl
  have hoperator :
      σ⁻¹ * toSLF F ((γ' : Γ) : SL(2,𝓞 F)) =
        (σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ) *
          (σ⁻¹ * toSLF F ((γ : Γ) : SL(2,𝓞 F))) := by
    calc
      σ⁻¹ * toSLF F ((γ' : Γ) : SL(2,𝓞 F)) =
          σ⁻¹ * toSLF F ((δ * γ : Γ) : SL(2,𝓞 F)) := by
            exact congrArg (fun x : Γ => σ⁻¹ * toSLF F (x : SL(2,𝓞 F))) hgroup
      _ = σ⁻¹ * toSLF F ((δ : SL(2,𝓞 F)) * (γ : SL(2,𝓞 F))) := by rw [hcoerce]
      _ = σ⁻¹ * (toSLF F (δ : SL(2,𝓞 F)) *
          toSLF F ((γ : Γ) : SL(2,𝓞 F))) := by rw [map_mul]
      _ = (σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ) *
          (σ⁻¹ * toSLF F ((γ : Γ) : SL(2,𝓞 F))) := by group
  have hmove :
      σ⁻¹ • ((γ' : Γ) • z) =
        (σ⁻¹ * toSLF F ((γ' * γ⁻¹ : Γ) : SL(2,𝓞 F)) * σ) •
          (σ⁻¹ • ((γ : Γ) • z)) := by
    rw [hγ', hγ]
    simp only [smul_smul]
    exact congrArg (fun g : SL(2,F) => g • z) hoperator
  rw [hmove]
  exact (G2_x_action.2.2.1 ((δ : Γ) : SL(2,𝓞 F)) σ htri).2 _

private lemma eis_bottomRow_ne_zero (g : SL(2,F)) : bottomRow F g ≠ (0, 0) := by
  intro h
  have h₁ : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := congrArg Prod.fst h
  have h₂ : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := congrArg Prod.snd h
  have hd : Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 := g.2
  rw [Matrix.det_fin_two] at hd
  simp [h₁, h₂] at hd

private lemma eis_hasDenominatorBound_exists (a : F) :
    ∃ D : ℕ, 0 < D ∧ HasDenominatorBound F D a := by
  have haQ : IsAlgebraic ℚ a :=
    (NumberField.isAlgebraic F).isAlgebraic a
  have haZ : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr haQ
  obtain ⟨D, b, hD, hb⟩ := haZ.exists_nsmul_eq (𝓞 F)
  refine ⟨D, Nat.pos_of_ne_zero hD, ⟨b, ?_⟩⟩
  change (D : F) * a = algebraMap (𝓞 F) F b
  calc
    (D : F) * a = D • a := by simp [Algebra.smul_def]
    _ = algebraMap (𝓞 F) F b := hb

private lemma eis_hasDenominatorBound_add {D : ℕ} {a b : F}
    (ha : HasDenominatorBound F D a) (hb : HasDenominatorBound F D b) :
    HasDenominatorBound F D (a + b) := by
  rcases ha with ⟨a', ha'⟩
  rcases hb with ⟨b', hb'⟩
  refine ⟨a' + b', ?_⟩
  change (D : F) * (a + b) = algebraMap (𝓞 F) F (a' + b')
  rw [map_add]
  rw [← ha', ← hb']
  ring

private lemma eis_hasDenominatorBound_mul_int {D : ℕ} {a : F}
    (ha : HasDenominatorBound F D a) (b : 𝓞 F) :
    HasDenominatorBound F D (a * algebraMap (𝓞 F) F b) := by
  rcases ha with ⟨a', ha'⟩
  refine ⟨a' * b, ?_⟩
  change (D : F) * (a * algebraMap (𝓞 F) F b) =
    algebraMap (𝓞 F) F (a' * b)
  calc
    (D : F) * (a * algebraMap (𝓞 F) F b) = ((D : F) * a) * algebraMap (𝓞 F) F b := by ring
    _ = algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F b := by rw [ha']
    _ = algebraMap (𝓞 F) F (a' * b) := by rw [map_mul]

private lemma eis_exists_common_denominator {ι : Type} [Fintype ι] (a : ι → F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, HasDenominatorBound F D (a i) := by
  classical
  choose d hd hdb using fun i : ι => eis_hasDenominatorBound_exists (a i)
  let D : ℕ := ∏ i : ι, d i
  have hD : 0 < D := by
    dsimp [D]
    exact Finset.prod_pos fun i hi => hd i
  refine ⟨D, hD, ?_⟩
  intro j
  let E : ℕ := ∏ i ∈ Finset.univ.erase j, d i
  have hfactor : D = d j * E := by
    dsimp [D, E]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    ring
  rcases hdb j with ⟨b, hb⟩
  refine ⟨(E : 𝓞 F) * b, ?_⟩
  change (D : F) * a j = algebraMap (𝓞 F) F ((E : 𝓞 F) * b)
  calc
    (D : F) * a j = (d j : F) * (E : F) * a j := by
      rw [hfactor, Nat.cast_mul]
    _ = (E : F) * ((d j : F) * a j) := by ring
    _ = (E : F) * algebraMap (𝓞 F) F b := by rw [hb]
    _ = algebraMap (𝓞 F) F ((E : 𝓞 F) * b) := by simp [map_mul]

private lemma eis_hasDenominatorBound_fixedMatrixBottomRow
    (σ σ' : SL(2,F)) (D : ℕ)
    (hcoeff : ∀ i j k : Fin 2,
      HasDenominatorBound F D (((σ⁻¹ : SL(2,F)) 1 i) * ((σ' : SL(2,F)) j k)))
    (γ : SL(2,𝓞 F)) (k : Fin 2) :
    HasDenominatorBound F D ((σ⁻¹ * toSLF F γ * σ') 1 k) := by
  let a : Fin 2 → F := fun i => (σ⁻¹ : SL(2,F)) 1 i
  let b : Fin 2 → F := fun j => (σ' : SL(2,F)) j k
  let t : Fin 2 → Fin 2 → F := fun i j =>
    (a i * b j) * algebraMap (𝓞 F) F (γ i j)
  have hterm (i j : Fin 2) : HasDenominatorBound F D (t i j) := by
    exact eis_hasDenominatorBound_mul_int (hcoeff i j k) (γ i j)
  have hsum : HasDenominatorBound F D
      ((t 0 0 + t 1 0) + (t 0 1 + t 1 1)) :=
    eis_hasDenominatorBound_add
      (eis_hasDenominatorBound_add (hterm 0 0) (hterm 1 0))
      (eis_hasDenominatorBound_add (hterm 0 1) (hterm 1 1))
  have hentry : ((σ⁻¹ * toSLF F γ * σ' : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 1 k =
      (t 0 0 + t 1 0) + (t 0 1 + t 1 1) := by
    simp [t, a, b, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, toSLF]
    ring
  rw [hentry]
  exact hsum

/-- E1 `spec:eis-def` — P-SPEC.md:237. The representative formula for an Eisenstein term and
injectivity of its bottom-row unit orbit map. -/
theorem E1_eis_def :
    (∀ (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (s : ℂ) (z : X F) (γ : Γ),
      eisTerm F Γ σ s z (Quotient.mk _ γ) =
        ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * s)) ∧
    (∀ (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ σ' : SL(2,F)),
      ∃ D : ℕ, 0 < D ∧
        (∀ q : CuspCosets F Γ σ,
          let r := bottomRow F (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * σ')
          r ≠ (0, 0) ∧ HasDenominatorBound F D r.1 ∧ HasDenominatorBound F D r.2) ∧
        ∀ q q' : CuspCosets F Γ σ,
          unitAssociatedRows F
            (bottomRow F (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * σ'))
            (bottomRow F (σ⁻¹ * toSLF F ((q'.out : Γ) : SL(2,𝓞 F)) * σ')) → q = q') := by
  constructor
  · intro Γ σ s z γ
    unfold eisTerm
    have hout :
        QuotientGroup.rightRel (cuspStab F Γ σ)
          (Quotient.out (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) γ)) γ :=
      Quotient.mk_out γ
    exact congrArg (fun t : ℝ => (t : ℂ) ^ (1 + 2 * s))
      (eis_cusp_height_rightRel Γ σ _ _ hout z).symm
  · intro Γ hΓ σ σ'
    let c : Fin 2 × Fin 2 × Fin 2 → F := fun ijk =>
      ((σ⁻¹ : SL(2,F)) 1 ijk.1) * ((σ' : SL(2,F)) ijk.2.1 ijk.2.2)
    obtain ⟨D, hD, hden⟩ := eis_exists_common_denominator c
    refine ⟨D, hD, ?_, ?_⟩
    · intro q
      dsimp
      let g : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * σ'
      refine ⟨eis_bottomRow_ne_zero g, ?_, ?_⟩
      · exact eis_hasDenominatorBound_fixedMatrixBottomRow σ σ' D
          (fun i j k => hden (i, j, k)) (q.out : Γ) 0
      · exact eis_hasDenominatorBound_fixedMatrixBottomRow σ σ' D
          (fun i j k => hden (i, j, k)) (q.out : Γ) 1
    · intro q q' horbit
      let A : SL(2,F) := σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * σ'
      let B : SL(2,F) := σ⁻¹ * toSLF F ((q'.out : Γ) : SL(2,𝓞 F)) * σ'
      let δ : Γ := q'.out * q.out⁻¹
      rcases horbit with ⟨ε, hrows⟩
      let u : F := algebraMap (𝓞 F) F (ε : 𝓞 F)
      have hu : u ≠ 0 := by
        intro hzero
        have hunit : u * algebraMap (𝓞 F) F ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) = 1 := by
          dsimp [u]
          rw [← map_mul]
          simp
        rw [hzero] at hunit
        simp at hunit
      have hrow0 : A 1 0 = u * B 1 0 := by
        simpa [A, B, u, bottomRow] using congrArg Prod.fst hrows
      have hrow1 : A 1 1 = u * B 1 1 := by
        simpa [A, B, u, bottomRow] using congrArg Prod.snd hrows
      have hBA : (B * A⁻¹) 1 0 = 0 := by
        change ((B * A⁻¹ : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
        rw [Matrix.mul_apply, Fin.sum_univ_two]
        simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.tail_cons]
        rw [hrow0, hrow1]
        ring
      have hδcoerce : (δ : SL(2,𝓞 F)) =
          ((q'.out : Γ) : SL(2,𝓞 F)) * ((q.out : Γ) : SL(2,𝓞 F))⁻¹ := rfl
      have hδmap : toSLF F (δ : SL(2,𝓞 F)) =
          toSLF F ((q'.out : Γ) : SL(2,𝓞 F)) *
            (toSLF F ((q.out : Γ) : SL(2,𝓞 F)))⁻¹ := by
        rw [hδcoerce, map_mul, map_inv]
      have hBAeq : B * A⁻¹ =
          σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ := by
        dsimp [A, B]
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hδmap]
        group
      have htri :
          σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ ∈ borelSL F := by
        change (σ⁻¹ * toSLF F (δ : SL(2,𝓞 F)) * σ) 1 0 = 0
        rw [← hBAeq]
        exact hBA
      have hstab : δ ∈ cuspStab F Γ σ := by
        simp only [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact htri
      calc
        q = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out :=
          (Quotient.out_eq q).symm
        _ = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q'.out :=
          Quotient.sound (QuotientGroup.rightRel_apply.mpr hstab)
        _ = q' := Quotient.out_eq q'

private lemma eis_height_pos (z : X F) (w : InfinitePlace F) : 0 < height (z w) := by
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private lemma eis_compact_coordinate_bounds {K : Set (X F)}
    (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ m M R : ℝ, 0 < m ∧ 0 < M ∧ 0 ≤ R ∧
      ∀ z ∈ K, ∀ w : InfinitePlace F,
        m ≤ height (z w) ∧ height (z w) ≤ M ∧ ‖horiz (z w)‖ ≤ R := by
  let yvec : X F → InfinitePlace F → ℝ := fun z w => height (z w)
  let yinv : X F → InfinitePlace F → ℝ := fun z w => (height (z w))⁻¹
  let xvec : X F → InfinitePlace F → ℂ := fun z w => horiz (z w)
  have hycoord (w : InfinitePlace F) : Continuous (fun z : X F => height (z w)) := by
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_continuous.comp (continuous_apply w)
  have hyinvcoord (w : InfinitePlace F) : Continuous (fun z : X F => (height (z w))⁻¹) :=
    (hycoord w).inv₀ fun z => (eis_height_pos z w).ne'
  have hxcoord (w : InfinitePlace F) : Continuous (fun z : X F => horiz (z w)) := by
    rw [horiz_eq_hyperbolicHorizontal]
    exact OAI.CubicEisenstein.hyperbolicHorizontal_continuous.comp (continuous_apply w)
  have hyvec : Continuous yvec := by
    apply continuous_pi
    exact hycoord
  have hyinv : Continuous yinv := by
    apply continuous_pi
    exact hyinvcoord
  have hxvec : Continuous xvec := by
    apply continuous_pi
    exact hxcoord
  let fy : X F → ℝ := fun z => ‖yvec z‖
  let fyinv : X F → ℝ := fun z => ‖yinv z‖
  let fx : X F → ℝ := fun z => ‖xvec z‖
  have hfy : Continuous fy := continuous_norm.comp hyvec
  have hfyinv : Continuous fyinv := continuous_norm.comp hyinv
  have hfx : Continuous fx := continuous_norm.comp hxvec
  obtain ⟨zM, hzM, hMmax⟩ := hK.exists_isMaxOn hKne hfy.continuousOn
  obtain ⟨zB, hzB, hBmax⟩ := hK.exists_isMaxOn hKne hfyinv.continuousOn
  obtain ⟨zR, hzR, hRmax⟩ := hK.exists_isMaxOn hKne hfx.continuousOn
  let M : ℝ := fy zM
  let B : ℝ := fyinv zB
  let R : ℝ := fx zR
  have hMpos : 0 < M := by
    have hW : Nonempty (InfinitePlace F) := Fintype.card_pos_iff.mp Fintype.card_pos
    obtain ⟨w⟩ := hW
    have hy := eis_height_pos zM w
    have hle : height (zM w) ≤ ‖yvec zM‖ := by
      simpa [yvec, Real.norm_eq_abs, abs_of_pos hy] using (norm_le_pi_norm (yvec zM) w)
    exact lt_of_lt_of_le hy (by simpa [M, fy] using hle)
  have hBpos : 0 < B := by
    have hW : Nonempty (InfinitePlace F) := Fintype.card_pos_iff.mp Fintype.card_pos
    obtain ⟨w⟩ := hW
    have hy := eis_height_pos zB w
    have hyi : 0 < (height (zB w))⁻¹ := inv_pos.mpr hy
    have hle : (height (zB w))⁻¹ ≤ ‖yinv zB‖ := by
      simpa [yinv, Real.norm_eq_abs, abs_of_pos hy] using (norm_le_pi_norm (yinv zB) w)
    exact lt_of_lt_of_le hyi (by simpa [B, fyinv] using hle)
  have hRnonneg : 0 ≤ R := by
    dsimp [R, fx]
    exact norm_nonneg _
  refine ⟨B⁻¹, M, R, inv_pos.mpr hBpos, hMpos, hRnonneg, ?_⟩
  intro z hz w
  have hYmax : ‖yvec z‖ ≤ M := by simpa [M, fy] using hMmax hz
  have hYinvmax : ‖yinv z‖ ≤ B := by simpa [B, fyinv] using hBmax hz
  have hXmax : ‖xvec z‖ ≤ R := by simpa [R, fx] using hRmax hz
  have hy := eis_height_pos z w
  have hYcoord : height (z w) ≤ M := by
    have hle : height (z w) ≤ ‖yvec z‖ := by
      simpa [yvec, Real.norm_eq_abs, abs_of_pos hy] using (norm_le_pi_norm (yvec z) w)
    exact hle.trans hYmax
  have hyInvLe : (height (z w))⁻¹ ≤ B := by
    have hle : (height (z w))⁻¹ ≤ ‖yinv z‖ := by
      have hyi : 0 < (height (z w))⁻¹ := inv_pos.mpr hy
      simpa [yinv, Real.norm_eq_abs, abs_of_pos hy] using (norm_le_pi_norm (yinv z) w)
    exact hle.trans hYinvmax
  have hmY : B⁻¹ ≤ height (z w) := by
    have hmul : 1 ≤ B * height (z w) := by
      calc
        1 = (height (z w))⁻¹ * height (z w) := by field_simp [hy.ne']
        _ ≤ B * height (z w) := mul_le_mul_of_nonneg_right hyInvLe hy.le
    have hdiv : (1 : ℝ) / B ≤ height (z w) :=
      (div_le_iff₀ hBpos).2 (by simpa [mul_comm] using hmul)
    simpa [one_div] using hdiv
  have hXcoord : ‖horiz (z w)‖ ≤ R := by
    exact (norm_le_pi_norm (xvec z) w).trans hXmax
  exact ⟨hmY, hYcoord, hXcoord⟩

private lemma eis_quadratic_form_lower (m M R y : ℝ) (x c d : ℂ)
    (hm : 0 < m) (hM : 0 < M) (hR : 0 ≤ R) (hmy : m ≤ y) (hyM : y ≤ M)
    (hx : ‖x‖ ≤ R) :
    (M * (2 + (1 + 2 * R ^ 2) / m ^ 2))⁻¹ *
        (Complex.normSq c + Complex.normSq d) ≤
      (Complex.normSq (c * x + d) + Complex.normSq c * y ^ 2) / y := by
  let Q : ℝ := Complex.normSq (c * x + d) + Complex.normSq c * y ^ 2
  let C : ℝ := 2 + (1 + 2 * R ^ 2) / m ^ 2
  have hy : 0 < y := lt_of_lt_of_le hm hmy
  have hC : 0 < C := by positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg (Complex.normSq_nonneg _)
      (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))
  have hcQ : Complex.normSq c ≤ Q / m ^ 2 := by
    have hcmsq : ‖c‖ ^ 2 * m ^ 2 ≤ Q := by
      have hmsq : m ^ 2 ≤ y ^ 2 := by nlinarith [hmy, hy]
      calc
        ‖c‖ ^ 2 * m ^ 2 ≤ ‖c‖ ^ 2 * y ^ 2 :=
          mul_le_mul_of_nonneg_left hmsq (sq_nonneg _)
        _ = Complex.normSq c * y ^ 2 := by rw [Complex.normSq_eq_norm_sq]
        _ ≤ Q := by
          dsimp [Q]
          exact le_add_of_nonneg_left (Complex.normSq_nonneg _)
    rw [Complex.normSq_eq_norm_sq]
    exact (le_div_iff₀ (sq_pos_of_pos hm)).2 hcmsq
  have hfirst : ‖c * x + d‖ ^ 2 ≤ Q := by
    calc
      ‖c * x + d‖ ^ 2 = Complex.normSq (c * x + d) :=
        (Complex.normSq_eq_norm_sq _).symm
      _ ≤ Q := by
        dsimp [Q]
        exact le_add_of_nonneg_right (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))
  have hcx : ‖c * x‖ ^ 2 ≤ R ^ 2 * (Q / m ^ 2) := by
    have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [hx, hR, norm_nonneg x]
    have hcSq : ‖c‖ ^ 2 ≤ Q / m ^ 2 := by simpa [Complex.normSq_eq_norm_sq] using hcQ
    calc
      ‖c * x‖ ^ 2 = ‖c‖ ^ 2 * ‖x‖ ^ 2 := by rw [norm_mul]; ring
      _ ≤ ‖c‖ ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hx2 (sq_nonneg _)
      _ ≤ (Q / m ^ 2) * R ^ 2 := mul_le_mul_of_nonneg_right hcSq (sq_nonneg _)
      _ = R ^ 2 * (Q / m ^ 2) := by ring
  have hdTri : ‖d‖ ≤ ‖c * x + d‖ + ‖c * x‖ := by
    calc
      ‖d‖ = ‖(c * x + d) - c * x‖ := by congr 1; ring
      _ ≤ ‖c * x + d‖ + ‖c * x‖ := norm_sub_le _ _
  have hdSq : ‖d‖ ^ 2 ≤ 2 * ‖c * x + d‖ ^ 2 + 2 * ‖c * x‖ ^ 2 := by
    have hleft : 0 ≤ ‖c * x + d‖ + ‖c * x‖ - ‖d‖ := by linarith [hdTri]
    have hright : 0 ≤ ‖c * x + d‖ + ‖c * x‖ + ‖d‖ := by positivity
    have hprod := mul_nonneg hleft hright
    nlinarith [sq_nonneg (‖c * x + d‖ - ‖c * x‖), hprod]
  have hdQ : ‖d‖ ^ 2 ≤ 2 * Q + 2 * R ^ 2 * (Q / m ^ 2) := by
    calc
      ‖d‖ ^ 2 ≤ 2 * ‖c * x + d‖ ^ 2 + 2 * ‖c * x‖ ^ 2 := hdSq
      _ ≤ 2 * Q + 2 * (R ^ 2 * (Q / m ^ 2)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left hcx (by norm_num : (0 : ℝ) ≤ 2))
      _ = 2 * Q + 2 * R ^ 2 * (Q / m ^ 2) := by ring
  have hrow : Complex.normSq c + Complex.normSq d ≤ C * Q := by
    have hdNormSq : Complex.normSq d ≤ 2 * Q + 2 * R ^ 2 * (Q / m ^ 2) := by
      rw [Complex.normSq_eq_norm_sq]
      exact hdQ
    calc
      Complex.normSq c + Complex.normSq d ≤
          Q / m ^ 2 + (2 * Q + 2 * R ^ 2 * (Q / m ^ 2)) := add_le_add hcQ hdNormSq
      _ = C * Q := by
        dsimp [C]
        rw [div_eq_mul_inv]
        ring
  have hscale : (M * C)⁻¹ * C = M⁻¹ := by
    field_simp [ne_of_gt hM, ne_of_gt hC]
  have hbase : (M * C)⁻¹ * (Complex.normSq c + Complex.normSq d) ≤ Q / M := by
    calc
      (M * C)⁻¹ * (Complex.normSq c + Complex.normSq d) ≤ (M * C)⁻¹ * (C * Q) :=
        mul_le_mul_of_nonneg_left hrow (inv_nonneg.mpr (le_of_lt (mul_pos hM hC)))
      _ = Q / M := by
        calc
          (M * C)⁻¹ * (C * Q) = ((M * C)⁻¹ * C) * Q := by rw [← mul_assoc]
          _ = M⁻¹ * Q := by rw [hscale]
          _ = Q / M := by rw [div_eq_mul_inv]; ring
  have hden : Q / M ≤ Q / y := by
    apply (div_le_div_iff₀ hM hy).2
    exact mul_le_mul_of_nonneg_left hyM hQ
  exact hbase.trans hden

private lemma eis_rowNorm_pos (v : F × F) (hv : v ≠ (0, 0)) (w : InfinitePlace F) :
    0 < rowNorm F v w := by
  have hentry : w.embedding v.1 ≠ 0 ∨ w.embedding v.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Prod.ext (w.embedding.injective (by simpa using h.1))
      (w.embedding.injective (by simpa using h.2)))
  unfold rowNorm
  rw [Real.sqrt_pos]
  rcases hentry with hc | hd
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hc) (Complex.normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.mpr hd)

private lemma eis_rowHeightForm_lower (m M R : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hR : 0 ≤ R) {z : X F} {w : InfinitePlace F}
    (hcoord : m ≤ height (z w) ∧ height (z w) ≤ M ∧ ‖horiz (z w)‖ ≤ R)
    (v : F × F) :
    (M * (2 + (1 + 2 * R ^ 2) / m ^ 2))⁻¹ * (rowNorm F v w) ^ 2 ≤
      rowHeightForm F v z w := by
  let p := coordsX F z w
  let c := w.embedding v.1
  let d := w.embedding v.2
  have hquad := eis_quadratic_form_lower m M R p.2 p.1 c d hm hM hR
    hcoord.1 hcoord.2.1 hcoord.2.2
  have hrow : (rowNorm F v w) ^ 2 = Complex.normSq c + Complex.normSq d := by
    unfold rowNorm
    rw [Real.sq_sqrt]
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  calc
    (M * (2 + (1 + 2 * R ^ 2) / m ^ 2))⁻¹ * (rowNorm F v w) ^ 2 =
        (M * (2 + (1 + 2 * R ^ 2) / m ^ 2))⁻¹ *
          (Complex.normSq c + Complex.normSq d) := by rw [hrow]
    _ ≤ rowHeightForm F v z w := by
      simpa [rowHeightForm, p, c, d] using hquad

private lemma eis_normHeight_eq_rowHeightForm_inv (g : SL(2,F)) (z : X F) :
    normHeight F (g • z) =
      ∏ w : InfinitePlace F, (rowHeightForm F (bottomRow F g) z w)⁻¹ := by
  let x : InfinitePlace F → ℂ := fun w => horiz (z w)
  let y : InfinitePlace F → ℝ := fun w => height (z w)
  have hy (w : InfinitePlace F) : 0 < y w := by
    exact eis_height_pos z w
  have hpt : ptX' F x y = z := by
    funext w
    exact pt_horiz_height (z w)
  have hheight (w : InfinitePlace F) :
      height ((g • z) w) = y w /
        (Complex.normSq (w.embedding (g 1 0) * x w + w.embedding (g 1 1)) +
          Complex.normSq (w.embedding (g 1 0)) * y w ^ 2) := by
    rw [← hpt]
    exact height_smul_ptX'_at g x y hy w
  have hlocal (w : InfinitePlace F) :
      height ((g • z) w) = (rowHeightForm F (bottomRow F g) z w)⁻¹ := by
    let c : ℂ := w.embedding (g 1 0)
    let d : ℂ := w.embedding (g 1 1)
    let Q : ℝ := Complex.normSq (c * x w + d) + Complex.normSq c * y w ^ 2
    have hentry : c ≠ 0 ∨ d ≠ 0 := by
      by_contra h
      push_neg at h
      apply eis_bottomRow_ne_zero g
      apply Prod.ext
      · simpa [bottomRow] using w.embedding.injective (by simpa [c] using h.1)
      · simpa [bottomRow] using w.embedding.injective (by simpa [d] using h.2)
    have hQpos : 0 < Q := by
      rcases hentry with hc | hd
      · dsimp [Q]
        exact lt_of_lt_of_le
          (mul_pos (Complex.normSq_pos.mpr hc) (sq_pos_of_pos (hy w)))
          (le_add_of_nonneg_left (Complex.normSq_nonneg _))
      · by_cases hc0 : c = 0
        · have hfirst : 0 < Complex.normSq (c * x w + d) := by
            rw [hc0, zero_mul, zero_add]
            exact Complex.normSq_pos.mpr hd
          dsimp [Q]
          exact lt_of_lt_of_le hfirst
            (le_add_of_nonneg_right (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)))
        · dsimp [Q]
          exact lt_of_lt_of_le
            (mul_pos (Complex.normSq_pos.mpr hc0) (sq_pos_of_pos (hy w)))
            (le_add_of_nonneg_left (Complex.normSq_nonneg _))
    have hheight' : height ((g • z) w) = y w / Q := by
      have hh := hheight w
      dsimp [Q, c, d, x, y] at hh ⊢
      exact hh
    have hform : rowHeightForm F (bottomRow F g) z w = Q / y w := by
      simp [rowHeightForm, Q, c, d, x, y, bottomRow, coordsX]
    calc
      height ((g • z) w) = y w / Q := hheight'
      _ = (Q / y w)⁻¹ := by field_simp [ne_of_gt (hy w), ne_of_gt hQpos]
      _ = (rowHeightForm F (bottomRow F g) z w)⁻¹ := by rw [hform]
  unfold normHeight
  apply Finset.prod_congr rfl
  intro w hw
  exact hlocal w

private lemma eis_cusp_rep_action (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (q : CuspCosets F Γ σ) (z : X F) :
    σ⁻¹ • ((q.out : Γ) • z) =
      (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))) • z := by
  have hq : (q.out : Γ) • z =
      toSLF F ((q.out : Γ) : SL(2,𝓞 F)) • z := rfl
  rw [hq, smul_smul]

private lemma eis_rowPower_summable (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (α : ℝ) (hα : 4 < α) :
    Summable (fun q : CuspCosets F Γ σ =>
      (∏ w : InfinitePlace F,
        rowNorm F (bottomRow F (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)))) w) ^ (-α)) := by
  let v : CuspCosets F Γ σ → F × F := fun q =>
    bottomRow F (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)))
  let P : CuspCosets F Γ σ → ℝ := fun q => ∏ w : InfinitePlace F, rowNorm F (v q) w
  obtain ⟨D, hD, hrows⟩ := E1_eis_def.2 Γ σ (1 : SL(2,F))
  rcases hrows with ⟨hprop, huniq⟩
  have hprops (q : CuspCosets F Γ σ) :
      v q ≠ (0, 0) ∧ HasDenominatorBound F D (v q).1 ∧
        HasDenominatorBound F D (v q).2 := by
    simpa [v] using hprop q
  have huniqV : ∀ q q', (∃ ε : (𝓞 F)ˣ,
      v q = ((algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v q').1,
        (algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v q').2)) → q = q' := by
    intro q q' h
    apply huniq q q'
    simpa [v, unitAssociatedRows] using h
  have hsum := R5_lattice_sums D hD α hα v
    (fun q => ⟨(hprops q).2.1, (hprops q).2.2⟩)
    (fun q => (hprops q).1) huniqV
  have hrowpos (q : CuspCosets F Γ σ) (w : InfinitePlace F) : 0 < rowNorm F (v q) w :=
    eis_rowNorm_pos (v q) (hprops q).1 w
  have hprod (q : CuspCosets F Γ σ) :
      (P q) ^ (-α) = ∏ w : InfinitePlace F, (rowNorm F (v q) w) ^ (-α) := by
    dsimp [P]
    rw [Real.finsetProd_rpow Finset.univ (fun w : InfinitePlace F => rowNorm F (v q) w)
      (fun w hw => (hrowpos q w).le) (-α)]
  have hsumP : Summable (fun q : CuspCosets F Γ σ => (P q) ^ (-α)) := by
    exact hsum.congr fun q => (hprod q).symm
  simpa [P, v] using hsumP

private lemma eis_div_rpow_eq {A P b : ℝ} (hA : 0 < A) (hP : 0 < P) :
    (A / P ^ 2) ^ b = A ^ b * P ^ (-2 * b) := by
  have hPpow : (P ^ 2) ^ (-b) = P ^ (-2 * b) := by
    calc
      (P ^ (2 : ℕ)) ^ (-b) = (P ^ (2 : ℝ)) ^ (-b) := by rw [← Real.rpow_two]
      _ = P ^ (2 * (-b)) := (Real.rpow_mul (le_of_lt hP) 2 (-b)).symm
      _ = P ^ (-2 * b) := by congr 1 <;> ring
  calc
    (A / P ^ 2) ^ b = A ^ b * ((P ^ 2)⁻¹) ^ b := by
      rw [div_eq_mul_inv, Real.mul_rpow (le_of_lt hA) (inv_nonneg.mpr (sq_nonneg P))]
    _ = A ^ b * (P ^ 2) ^ (-b) := by rw [← Real.rpow_neg_eq_inv_rpow]
    _ = A ^ b * P ^ (-2 * b) := by rw [hPpow]

private theorem eisSeries_majorant_aux (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (K : Set (X F)) (hK : IsCompact K) (σ₀ σ₁ : ℝ)
    (h₀ : 1 / 2 < σ₀) :
    ∃ m : CuspCosets F Γ σ → ℝ, Summable m ∧
      ∀ z ∈ K, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ∀ q,
        ‖eisTerm F Γ σ s z q‖ ≤ m q := by
  by_cases hKempty : K = ∅
  · subst K
    refine ⟨fun _ => 0, summable_zero, ?_⟩
    intro z hz
    simpa using hz
  by_cases hstrip : σ₁ < σ₀
  · refine ⟨fun _ => 0, summable_zero, ?_⟩
    intro z hz s hs₀ hs₁ q
    exact False.elim (not_le_of_gt hstrip (le_trans hs₀ hs₁))
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
  obtain ⟨mY, MY, R, hmY, hMY, hR, hcoord⟩ := eis_compact_coordinate_bounds hK hKne
  let C : ℝ := MY * (2 + (1 + 2 * R ^ 2) / mY ^ 2)
  let a : ℝ := C⁻¹
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have ha : 0 < a := by dsimp [a]; exact inv_pos.mpr hC
  let A : ℝ := (a⁻¹) ^ (Fintype.card (InfinitePlace F))
  have hA : 0 < A := by
    dsimp [A]
    exact pow_pos (inv_pos.mpr ha) _
  let v : CuspCosets F Γ σ → F × F := fun q =>
    bottomRow F (σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)))
  let P : CuspCosets F Γ σ → ℝ := fun q => ∏ w : InfinitePlace F, rowNorm F (v q) w
  let g : CuspCosets F Γ σ → SL(2,F) := fun q =>
    σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F))
  obtain ⟨D, hD, hrows⟩ := E1_eis_def.2 Γ σ (1 : SL(2,F))
  rcases hrows with ⟨hprop, huniq⟩
  have hprops (q : CuspCosets F Γ σ) :
      v q ≠ (0, 0) ∧ HasDenominatorBound F D (v q).1 ∧
        HasDenominatorBound F D (v q).2 := by
    simpa [v] using hprop q
  have hPpos (q : CuspCosets F Γ σ) : 0 < P q := by
    dsimp [P]
    exact Finset.prod_pos fun w hw => eis_rowNorm_pos (v q) (hprops q).1 w
  have hrowLow (q : CuspCosets F Γ σ) (z : X F) (hz : z ∈ K)
      (w : InfinitePlace F) :
      a * (rowNorm F (v q) w) ^ 2 ≤ rowHeightForm F (v q) z w := by
    simpa [a, C, v] using
      eis_rowHeightForm_lower mY MY R hmY hMY hR (hcoord z hz w) (v q)
  have hformPos (q : CuspCosets F Γ σ) (z : X F) (hz : z ∈ K)
      (w : InfinitePlace F) : 0 < rowHeightForm F (v q) z w := by
    have hs := eis_rowNorm_pos (v q) (hprops q).1 w
    have hsmall : 0 < a * (rowNorm F (v q) w) ^ 2 := mul_pos ha (sq_pos_of_pos hs)
    exact lt_of_lt_of_le hsmall (hrowLow q z hz w)
  have hprodEq (q : CuspCosets F Γ σ) :
      (∏ w : InfinitePlace F, (a * (rowNorm F (v q) w) ^ 2)⁻¹) =
        A / (P q) ^ 2 := by
    calc
      (∏ w : InfinitePlace F, (a * (rowNorm F (v q) w) ^ 2)⁻¹) =
          ∏ w : InfinitePlace F, a⁻¹ * ((rowNorm F (v q) w)⁻¹) ^ 2 := by
        apply Finset.prod_congr rfl
        intro w hw
        rw [mul_inv, inv_pow]
      _ = (∏ w : InfinitePlace F, a⁻¹) *
          (∏ w : InfinitePlace F, (rowNorm F (v q) w)⁻¹) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow]
      _ = (a⁻¹) ^ Fintype.card (InfinitePlace F) *
          (∏ w : InfinitePlace F, (rowNorm F (v q) w)⁻¹) ^ 2 := by
        rw [Finset.prod_const]
        rw [Finset.card_univ]
      _ = A / (P q) ^ 2 := by
        rw [Finset.prod_inv_distrib]
        dsimp [A, P]
        field_simp [ne_of_gt ha, ne_of_gt (hPpos q)]
  have hNgPos (q : CuspCosets F Γ σ) (z : X F) : 0 < normHeight F (g q • z) := by
    unfold normHeight
    exact Finset.prod_pos fun w hw => eis_height_pos (g q • z) w
  have hNle (q : CuspCosets F Γ σ) (z : X F) (hz : z ∈ K) :
      normHeight F (g q • z) ≤ A / (P q) ^ 2 := by
    have hprodle :
        (∏ w : InfinitePlace F, (rowHeightForm F (v q) z w)⁻¹) ≤
          ∏ w : InfinitePlace F, (a * (rowNorm F (v q) w) ^ 2)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro w hw
        exact inv_nonneg.mpr (le_of_lt (hformPos q z hz w))
      · intro w hw
        have hsmall := mul_pos ha (sq_pos_of_pos (eis_rowNorm_pos (v q) (hprops q).1 w))
        have hrec := one_div_le_one_div_of_le hsmall (hrowLow q z hz w)
        simpa [one_div] using hrec
    calc
      normHeight F (g q • z) =
          ∏ w : InfinitePlace F, (rowHeightForm F (bottomRow F (g q)) z w)⁻¹ :=
        eis_normHeight_eq_rowHeightForm_inv (g q) z
      _ = ∏ w : InfinitePlace F, (rowHeightForm F (v q) z w)⁻¹ := by simp [g, v]
      _ ≤ ∏ w : InfinitePlace F, (a * (rowNorm F (v q) w) ^ 2)⁻¹ := hprodle
      _ = A / (P q) ^ 2 := hprodEq q
  let b₀ : ℝ := 1 + 2 * σ₀
  let b₁ : ℝ := 1 + 2 * σ₁
  have hb₀ : 2 < b₀ := by dsimp [b₀]; linarith
  have hb₁ : b₀ ≤ b₁ := by dsimp [b₀, b₁]; linarith [hstrip]
  have hb₀pos : 0 < b₀ := by linarith
  have hb₁pos : 0 < b₁ := lt_of_lt_of_le hb₀pos hb₁
  have hα₀ : 4 < 2 * b₀ := by linarith
  have hα₁ : 4 < 2 * b₁ := by linarith
  have hsum₀ : Summable (fun q : CuspCosets F Γ σ => A ^ b₀ * (P q) ^ (-2 * b₀)) := by
    have hs := eis_rowPower_summable Γ σ (2 * b₀) hα₀
    simpa [P] using hs.mul_left (A ^ b₀)
  have hsum₁ : Summable (fun q : CuspCosets F Γ σ => A ^ b₁ * (P q) ^ (-2 * b₁)) := by
    have hs := eis_rowPower_summable Γ σ (2 * b₁) hα₁
    simpa [P] using hs.mul_left (A ^ b₁)
  let m : CuspCosets F Γ σ → ℝ := fun q =>
    A ^ b₀ * (P q) ^ (-2 * b₀) + A ^ b₁ * (P q) ^ (-2 * b₁)
  refine ⟨m, ?_, ?_⟩
  · simpa [m] using hsum₀.add hsum₁
  · intro z hz s hs₀ hs₁ q
    let N : ℝ := normHeight F (σ⁻¹ • ((q.out : Γ) • z))
    let t : ℝ := 1 + 2 * s.re
    have hN : 0 < N := by
      dsimp [N]
      rw [eis_cusp_rep_action]
      exact hNgPos q z
    have hNt : b₀ ≤ t ∧ t ≤ b₁ := by
      constructor <;> dsimp [b₀, b₁, t] <;> linarith
    have hNbound : N ≤ A / (P q) ^ 2 := by
      dsimp [N]
      rw [eis_cusp_rep_action]
      exact hNle q z hz
    have hTpos : 0 < A / (P q) ^ 2 := div_pos hA (sq_pos_of_pos (hPpos q))
    have hpow : N ^ t ≤ N ^ b₀ + N ^ b₁ := by
      by_cases hNle1 : N ≤ 1
      · have hsmall := Real.rpow_le_rpow_of_exponent_ge hN hNle1 hNt.1
        exact hsmall.trans (le_add_of_nonneg_right (Real.rpow_nonneg hN.le _))
      · have hNgt : 1 < N := lt_of_not_ge hNle1
        have hlarge := Real.rpow_le_rpow_of_exponent_le (le_of_lt hNgt) hNt.2
        exact hlarge.trans (le_add_of_nonneg_left (Real.rpow_nonneg hN.le _))
    have hpowBound :
        N ^ b₀ + N ^ b₁ ≤ (A / (P q) ^ 2) ^ b₀ + (A / (P q) ^ 2) ^ b₁ := by
      exact add_le_add
        (Real.rpow_le_rpow hN.le hNbound hb₀pos.le)
        (Real.rpow_le_rpow hN.le hNbound hb₁pos.le)
    have hpowFinal :
        (A / (P q) ^ 2) ^ b₀ + (A / (P q) ^ 2) ^ b₁ = m q := by
      simp [m, eis_div_rpow_eq hA (hPpos q)]
    have hnorm : ‖eisTerm F Γ σ s z q‖ = N ^ t := by
      calc
        ‖eisTerm F Γ σ s z q‖ = ‖((N : ℝ) : ℂ) ^ (1 + 2 * s)‖ := by
          unfold eisTerm
          rfl
        _ = N ^ t := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
          simp [t, Complex.add_re, Complex.mul_re]
    rw [hnorm]
    exact hpow.trans (hpowBound.trans_eq hpowFinal)

private lemma eis_rightRel_mul_right (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (δ : Γ)
    {x y : Γ} (h : QuotientGroup.rightRel (cuspStab F Γ σ) x y) :
    QuotientGroup.rightRel (cuspStab F Γ σ) (x * δ) (y * δ) := by
  apply QuotientGroup.rightRel_apply.mpr
  have h' := QuotientGroup.rightRel_apply.mp h
  simpa [_root_.mul_inv_rev, mul_assoc] using h'

private def eis_rightMulEquiv (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (δ : Γ) :
    CuspCosets F Γ σ ≃ CuspCosets F Γ σ where
  toFun := Quotient.map (fun x : Γ => x * δ)
    (fun {_ _} h => eis_rightRel_mul_right Γ σ δ h)
  invFun := Quotient.map (fun x : Γ => x * δ⁻¹)
    (fun {_ _} h => eis_rightRel_mul_right Γ σ δ⁻¹ h)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [mul_assoc]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [mul_assoc]

private lemma eisTerm_differentiable (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (z : X F) (q : CuspCosets F Γ σ) :
    Differentiable ℂ (fun s : ℂ => eisTerm F Γ σ s z q) := by
  have hpos : 0 < normHeight F (σ⁻¹ • ((q.out : Γ) • z)) := by
    unfold normHeight
    exact Finset.prod_pos fun w hw => eis_height_pos (σ⁻¹ • ((q.out : Γ) • z)) w
  have hbase : ((normHeight F (σ⁻¹ • ((q.out : Γ) • z)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hpos.ne'
  unfold eisTerm
  apply Differentiable.const_cpow
  · fun_prop
  · exact Or.inl hbase

/-- E2 `spec:eis-converge` — P-SPEC.md:238, 379–383. The frozen locally uniform majorant and
invariance statements, together with holomorphy in the normalized parameter on `Re s > 1/2`. -/
theorem E2_eis_converge (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    (∀ (K : Set (X F)), IsCompact K → ∀ σ₀ σ₁ : ℝ, 1 / 2 < σ₀ →
      ∃ m : CuspCosets F Γ σ → ℝ, Summable m ∧
        ∀ z ∈ K, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ∀ q,
          ‖eisTerm F Γ σ s z q‖ ≤ m q) ∧
    (∀ (s : ℂ), 1 / 2 < s.re → ∀ (γ : SL(2,𝓞 F)), γ ∈ Γ → ∀ z : X F,
      eisSeries F Γ σ s (γ • z) = eisSeries F Γ σ s z) ∧
    (∀ z : X F,
      AnalyticOnNhd ℂ (fun s => eisSeries F Γ σ s z) {s : ℂ | 1 / 2 < s.re}) := by
  refine ⟨?_, ?_, ?_⟩
  · exact eisSeries_majorant_aux Γ σ
  · intro s hs γ hγ z
    let δ : Γ := ⟨γ, hγ⟩
    let e : CuspCosets F Γ σ ≃ CuspCosets F Γ σ := eis_rightMulEquiv Γ σ δ
    have hmap (q : CuspCosets F Γ σ) :
        e q = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ))
          ((q.out : Γ) * δ) := by
      calc
        e q = e (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out) :=
          congrArg e (Quotient.out_eq q).symm
        _ = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) (q.out * δ) := by
          change Quotient.map (fun x : Γ => x * δ)
            (fun {_ _} h => eis_rightRel_mul_right Γ σ δ h)
            (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out) = _
          rw [Quotient.map_mk]
    have hrepRel (q : CuspCosets F Γ σ) :
        QuotientGroup.rightRel (cuspStab F Γ σ) (e q).out ((q.out : Γ) * δ) := by
      have hout : (e q).out =
          (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) ((q.out : Γ) * δ)).out :=
        congrArg Quotient.out (hmap q)
      rw [hout]
      exact Quotient.mk_out ((q.out : Γ) * δ)
    have hterm (q : CuspCosets F Γ σ) :
        eisTerm F Γ σ s (δ • z) q = eisTerm F Γ σ s z (e q) := by
      have hnorm :
          normHeight F (σ⁻¹ • ((q.out : Γ) • (δ • z))) =
            normHeight F (σ⁻¹ • ((e q).out • z)) := by
        calc
          normHeight F (σ⁻¹ • ((q.out : Γ) • (δ • z))) =
              normHeight F (σ⁻¹ • (((q.out : Γ) * δ) • z)) := by
                congr 2
                exact smul_smul (q.out : Γ) δ z
          _ = normHeight F (σ⁻¹ • ((e q).out • z)) :=
            eis_cusp_height_rightRel Γ σ (e q).out ((q.out : Γ) * δ)
              (hrepRel q) z
      unfold eisTerm
      exact congrArg (fun h : ℝ => (h : ℂ) ^ (1 + 2 * s)) hnorm
    have hinv : eisSeries F Γ σ s (δ • z) = eisSeries F Γ σ s z := by
      unfold eisSeries
      calc
        (∑' q : CuspCosets F Γ σ, eisTerm F Γ σ s (δ • z) q) =
            ∑' q : CuspCosets F Γ σ, eisTerm F Γ σ s z (e q) :=
          tsum_congr hterm
        _ = ∑' q : CuspCosets F Γ σ, eisTerm F Γ σ s z q := by
          exact e.tsum_eq (fun q => eisTerm F Γ σ s z q)
    simpa [δ] using hinv
  · intro z s₀ hs₀
    change 1 / 2 < s₀.re at hs₀
    let r : ℝ := (s₀.re - 1 / 2) / 2
    let σlo : ℝ := 1 / 2 + r
    let σhi : ℝ := s₀.re + r
    have hr : 0 < r := by dsimp [r]; linarith
    have hσlo : 1 / 2 < σlo := by dsimp [σlo]; linarith
    obtain ⟨m, hm, hmajor⟩ :=
      eisSeries_majorant_aux Γ σ ({z} : Set (X F)) isCompact_singleton σlo σhi hσlo
    have hdiff : DifferentiableOn ℂ (fun s : ℂ => eisSeries F Γ σ s z)
        (Metric.ball s₀ r) := by
      unfold eisSeries
      apply Complex.differentiableOn_tsum_of_summable_norm hm
      · intro q s hsball
        exact (eisTerm_differentiable Γ σ z q s).differentiableWithinAt
      · exact Metric.isOpen_ball
      · intro q s hsball
        have hnorm : ‖s - s₀‖ < r := by
          simpa [dist_eq_norm] using (Metric.mem_ball.mp hsball)
        have hre : |s.re - s₀.re| < r := by
          calc
            |s.re - s₀.re| = |(s - s₀).re| := by simp
            _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
            _ < r := hnorm
        have hre' := abs_lt.mp hre
        have hσloeq : σlo = s₀.re - r := by dsimp [σlo, r]; ring
        have hlo : σlo ≤ s.re := by rw [hσloeq]; linarith
        have hhi : s.re ≤ σhi := by dsimp [σhi]; linarith
        exact hmajor z (by simp) s hlo hhi q
    exact hdiff.analyticAt (Metric.ball_mem_nhds s₀ hr)

end ArtinPrimitiveRoots.A1.Spec
