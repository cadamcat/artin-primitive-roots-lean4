import ArtinPrimitiveRoots.Spec.EisensteinExtra

set_option autoImplicit false

open NumberField Matrix
open scoped MatrixGroups

noncomputable section

open ArtinPrimitiveRoots.A1.Spec

namespace ArtinPrimitiveRoots.Proofs.spec_continue_p

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- A diagonal element used to move a cusp cutoff to a large enough height scale. -/
def specVerticalScale (t : F) (ht : t ≠ 0) : SL(2,F) :=
  ⟨!![t⁻¹, 0; 0, t], by
    rw [Matrix.det_fin_two_of]
    simp [ht]⟩

/-- The product-height multiplier of the inverse diagonal action. -/
def specVerticalScaleFactor (t : F) : ℝ :=
  ∏ w : InfinitePlace F, Complex.normSq (w.embedding t)

theorem exists_specVerticalScale_large (A : ℝ) (hA : 0 < A) :
    ∃ t : F, t ≠ 0 ∧ 1 ≤ A * specVerticalScaleFactor t := by
  obtain ⟨n, hn⟩ := exists_nat_gt A⁻¹
  have hnpos : 0 < (n : ℝ) := lt_trans (inv_pos.mpr hA) hn
  have hnNat : 0 < n := by exact_mod_cast hnpos
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hcard : 1 ≤ Fintype.card (InfinitePlace F) := by
    exact Nat.succ_le_iff.mpr Fintype.card_pos
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ (2 * Fintype.card (InfinitePlace F)) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hn1 (show 1 ≤ 2 * Fintype.card (InfinitePlace F) by omega))
  have hfac : specVerticalScaleFactor (n : F) =
      (n : ℝ) ^ (2 * Fintype.card (InfinitePlace F)) := by
    simp [specVerticalScaleFactor, pow_mul]
    ring
  have hAinv : A * A⁻¹ = 1 := mul_inv_cancel₀ hA.ne'
  have hAn : 1 < A * (n : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hn hA
    rw [hAinv] at hmul
    exact hmul
  refine ⟨(n : F), ?_, ?_⟩
  · exact_mod_cast (Nat.ne_of_gt (by exact_mod_cast hnpos))
  · rw [hfac]
    calc
      1 ≤ A * (n : ℝ) := le_of_lt hAn
      _ ≤ A * ((n : ℝ) ^ (2 * Fintype.card (InfinitePlace F))) :=
        mul_le_mul_of_nonneg_left hpow hA.le

/-- Rescale a cusp cutoff while retaining its smooth monotone transition. -/
def specScaledCuspCutoff (c : ℝ) (τ : ℝ → ℝ) : ℝ → ℝ := fun x => τ (x / c)

theorem isCuspCutoff_specScaled (A c : ℝ) (hc : 0 < c) (τ : ℝ → ℝ)
    (hτ : IsCuspCutoff A τ) : IsCuspCutoff (c * A) (specScaledCuspCutoff c τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hτ.1.comp (by fun_prop)
  · intro x y hxy
    exact hτ.2.1 (div_le_div_of_nonneg_right hxy hc.le)
  · intro x hx
    apply hτ.2.2.1
    apply (div_le_iff₀ hc).2
    simpa [specScaledCuspCutoff, mul_comm] using hx
  · intro x hx
    apply hτ.2.2.2
    apply (le_div_iff₀ hc).2
    nlinarith [hx]

theorem specVerticalScale_conj_borel_iff (t : F) (ht : t ≠ 0) (g : SL(2,F)) :
    (specVerticalScale t ht)⁻¹ * g * specVerticalScale t ht ∈ borelSL F ↔
      g ∈ borelSL F := by
  have hentry :
      ((specVerticalScale t ht)⁻¹ * g * specVerticalScale t ht) 1 0 =
        (t⁻¹) ^ 2 * g 1 0 := by
    change ((↑((specVerticalScale t ht)⁻¹ * g * specVerticalScale t ht) :
        Matrix (Fin 2) (Fin 2) F) 1 0) = _
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [specVerticalScale, Matrix.mul_apply, Fin.sum_univ_two]
    change ((!![t, 0; 0, t⁻¹] : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F)) 1 0 * t⁻¹ = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
  change ((specVerticalScale t ht)⁻¹ * g * specVerticalScale t ht) 1 0 = 0 ↔
    g 1 0 = 0
  rw [hentry]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (inv_ne_zero ht))
  · intro h
    simp [h]

theorem cuspStab_specVerticalScale (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (t : F) (ht : t ≠ 0) :
    cuspStab F Γ (σ * specVerticalScale t ht) = cuspStab F Γ σ := by
  ext γ
  simp only [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  change ((σ * specVerticalScale t ht)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) *
      (σ * specVerticalScale t ht) ∈ borelSL F) ↔
    (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ ∈ borelSL F)
  rw [show (σ * specVerticalScale t ht)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) *
      (σ * specVerticalScale t ht) = (specVerticalScale t ht)⁻¹ *
        (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) * specVerticalScale t ht by group]
  exact (specVerticalScale_conj_borel_iff t ht _)

theorem normHeight_specVerticalScale_inv_smul (t : F) (ht : t ≠ 0) (z : X F) :
    normHeight F ((specVerticalScale t ht)⁻¹ • z) =
      specVerticalScaleFactor t * normHeight F z := by
  let x : InfinitePlace F → ℂ := fun w => horiz (z w)
  let y : InfinitePlace F → ℝ := fun w => height (z w)
  have hy : ∀ w, 0 < y w := by
    intro w
    dsimp [y]
    rw [height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : ptX' F x y = z := by
    funext w
    exact pt_horiz_height (z w)
  let g : SL(2,F) :=
    ⟨!![t, 0; 0, t⁻¹], by
      rw [Matrix.det_fin_two_of]
      simp [ht]⟩
  have hmul : specVerticalScale t ht * g = 1 := by
    apply Subtype.ext
    change (!![t⁻¹, 0; 0, t] : Matrix (Fin 2) (Fin 2) F) *
      !![t, 0; 0, t⁻¹] = 1
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht]
  have hginv : (specVerticalScale t ht)⁻¹ = g := by
    calc
      (specVerticalScale t ht)⁻¹ = (specVerticalScale t ht)⁻¹ * 1 := by simp
      _ = (specVerticalScale t ht)⁻¹ * (specVerticalScale t ht * g) := by rw [hmul]
      _ = g := by simp [mul_assoc]
  have hheight (w : InfinitePlace F) :
      height ((g • ptX' F x y) w) = y w / Complex.normSq (w.embedding t⁻¹) := by
    have hg10 : g 1 0 = 0 := rfl
    have hg11 : g 1 1 = t⁻¹ := rfl
    have h := height_smul_ptX'_at g x y hy w
    rw [hg10, hg11] at h
    simpa using h
  have hnormsq (w : InfinitePlace F) :
      Complex.normSq (w.embedding (t⁻¹)) = (Complex.normSq (w.embedding t))⁻¹ := by
    rw [map_inv₀ (w.embedding) t]
    exact Complex.normSq_inv (w.embedding t)
  rw [← hpt, normHeight]
  rw [hginv]
  simp_rw [hheight]
  calc
    (∏ w : InfinitePlace F, y w / Complex.normSq (w.embedding t⁻¹)) =
        ∏ w : InfinitePlace F, Complex.normSq (w.embedding t) * y w := by
      apply Finset.prod_congr rfl
      intro w hw
      rw [hnormsq]
      field_simp
    _ = specVerticalScaleFactor t * normHeight F (ptX' F x y) := by
      rw [Finset.prod_mul_distrib]
      rw [specVerticalScaleFactor]
      rw [hpt]
      rfl

theorem normHeight_specScaled_cusp (σ : SL(2,F)) (t : F) (ht : t ≠ 0)
    (z : X F) :
    normHeight F ((σ * specVerticalScale t ht)⁻¹ • z) =
      specVerticalScaleFactor t * normHeight F (σ⁻¹ • z) := by
  rw [show (σ * specVerticalScale t ht)⁻¹ =
      (specVerticalScale t ht)⁻¹ * σ⁻¹ by group, mul_smul]
  exact normHeight_specVerticalScale_inv_smul t ht (σ⁻¹ • z)

private theorem normHeight_pos_seedScaling (z : X F) : 0 < normHeight F z := by
  rw [normHeight]
  apply Finset.prod_pos
  intro w hw
  rw [height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private theorem cpow_mul_seedScaling {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (a : ℂ) :
    ((x * y : ℝ) : ℂ) ^ a = (x : ℂ) ^ a * (y : ℂ) ^ a := by
  simpa only [Complex.ofReal_mul] using Complex.mul_cpow_ofReal_nonneg hx hy a

set_option maxHeartbeats 1000000 in
theorem eisSeed_specScaled (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (τ : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (t : F) (ht : t ≠ 0) (hcf : c = specVerticalScaleFactor t)
    (s : ℂ) (z : X F) :
    eisSeed F Γ (σ * specVerticalScale t ht) (specScaledCuspCutoff c τ) s z =
      (c : ℂ) ^ (1 + 2 * s) * eisSeed F Γ σ τ s z := by
  classical
  have hstab := cuspStab_specVerticalScale Γ σ t ht
  have hrelMap : ∀ (a b : Γ),
      (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht))).r a b →
        (QuotientGroup.rightRel (cuspStab F Γ σ)).r ((fun x : Γ => x) a) ((fun x : Γ => x) b) := by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    have hm := QuotientGroup.rightRel_apply.mp hab
    rw [hstab] at hm
    exact hm
  have hrelMapInv : ∀ (a b : Γ),
      (QuotientGroup.rightRel (cuspStab F Γ σ)).r a b →
        (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht))).r
          ((fun x : Γ => x) a) ((fun x : Γ => x) b) := by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    have hm := QuotientGroup.rightRel_apply.mp hab
    rw [← hstab] at hm
    exact hm
  let e : CuspCosets F Γ (σ * specVerticalScale t ht) ≃ CuspCosets F Γ σ :=
    { toFun := @Quotient.map Γ Γ
        (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht)))
        (QuotientGroup.rightRel (cuspStab F Γ σ)) (fun x : Γ => x) hrelMap
      invFun := @Quotient.map Γ Γ
        (QuotientGroup.rightRel (cuspStab F Γ σ))
        (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht)))
        (fun x : Γ => x) hrelMapInv
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        change @Quotient.map Γ Γ
          (QuotientGroup.rightRel (cuspStab F Γ σ))
          (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht)))
          (fun x : Γ => x) hrelMapInv
          (@Quotient.map Γ Γ
            (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht)))
            (QuotientGroup.rightRel (cuspStab F Γ σ))
            (fun x : Γ => x) hrelMap
            (Quotient.mk (QuotientGroup.rightRel
              (cuspStab F Γ (σ * specVerticalScale t ht))) x)) = _
        rw [Quotient.map_mk, Quotient.map_mk]
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        change @Quotient.map Γ Γ
          (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht)))
          (QuotientGroup.rightRel (cuspStab F Γ σ))
          (fun x : Γ => x) hrelMap
          (@Quotient.map Γ Γ
            (QuotientGroup.rightRel (cuspStab F Γ σ))
            (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht)))
            (fun x : Γ => x) hrelMapInv
            (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) x)) = _
        rw [Quotient.map_mk, Quotient.map_mk] }
  have hmap (q : CuspCosets F Γ (σ * specVerticalScale t ht)) :
      e q = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out := by
    calc
      e q = e (Quotient.mk (QuotientGroup.rightRel
          (cuspStab F Γ (σ * specVerticalScale t ht))) q.out) :=
        congrArg e (Quotient.out_eq q).symm
      _ = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) q.out := by
        change @Quotient.map Γ Γ
          (QuotientGroup.rightRel (cuspStab F Γ (σ * specVerticalScale t ht)))
          (QuotientGroup.rightRel (cuspStab F Γ σ))
          (fun x : Γ => x) hrelMap
          (Quotient.mk (QuotientGroup.rightRel
            (cuspStab F Γ (σ * specVerticalScale t ht))) q.out) = _
        rw [Quotient.map_mk]
  have heisZero (r : CuspCosets F Γ σ) :
      eisTerm F Γ σ 0 z r =
        ((normHeight F (σ⁻¹ • ((r.out : Γ) • z)) : ℝ) : ℂ) := by
    calc
      eisTerm F Γ σ 0 z r = eisTerm F Γ σ 0 z
          (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) r.out) := by
        exact congrArg (eisTerm F Γ σ 0 z) (Quotient.out_eq r).symm
      _ = ((normHeight F (σ⁻¹ • ((r.out : Γ) • z)) : ℝ) : ℂ) := by
        calc
          eisTerm F Γ σ 0 z
              (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) r.out) =
            ((normHeight F (σ⁻¹ • ((r.out : Γ) • z)) : ℝ) : ℂ) ^ (1 + 2 * (0 : ℂ)) :=
              E1_eis_def.1 Γ σ 0 z r.out
          _ = _ := by simp
  have heisMk (γ : Γ) :
      eisTerm F Γ σ 0 z (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) γ) =
        ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) := by
    calc
      eisTerm F Γ σ 0 z (Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ σ)) γ) =
          ((normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * (0 : ℂ)) :=
        E1_eis_def.1 Γ σ 0 z γ
      _ = _ := by simp
  have hheightRep (q : CuspCosets F Γ (σ * specVerticalScale t ht)) :
      normHeight F (σ⁻¹ • ((((e q).out : Γ) : SL(2,𝓞 F)) • z)) =
        normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z)) := by
    have hterm := congrArg (fun r : CuspCosets F Γ σ => eisTerm F Γ σ 0 z r) (hmap q)
    rw [heisZero (e q), heisMk q.out] at hterm
    exact Complex.ofReal_injective hterm
  unfold eisSeed
  calc
    (∑' q : CuspCosets F Γ (σ * specVerticalScale t ht),
        seedTerm F Γ (σ * specVerticalScale t ht) (specScaledCuspCutoff c τ) s z q) =
      ∑' q : CuspCosets F Γ (σ * specVerticalScale t ht),
        (c : ℂ) ^ (1 + 2 * s) * seedTerm F Γ σ τ s z (e q) := by
          apply tsum_congr
          intro q
          have hh := normHeight_specScaled_cusp σ t ht
            (((q.out : Γ) : SL(2,𝓞 F)) • z)
          rw [← hcf] at hh
          have hrep := hheightRep q
          have hbase : 0 < normHeight F
              (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z)) :=
            normHeight_pos_seedScaling _
          have hcpow := cpow_mul_seedScaling hc.le hbase.le (1 + 2 * s)
          dsimp [seedTerm, specScaledCuspCutoff]
          rw [hh, hrep]
          have hdiv :
              (c * normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))) / c =
                normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z)) := by
            field_simp [hc.ne']
          rw [hdiv, hcpow]
          ring
    _ = (c : ℂ) ^ (1 + 2 * s) *
        ∑' q : CuspCosets F Γ σ, seedTerm F Γ σ τ s z q := by
          rw [tsum_mul_left, e.tsum_eq]

theorem specScaledSeparation (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (A : ℝ) (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (t : F) (ht : t ≠ 0) (hc : 0 < specVerticalScaleFactor t) :
    ∀ γ γ' : Γ, ∀ z : X F,
      specVerticalScaleFactor t * A ≤
          normHeight F ((σ * specVerticalScale t ht)⁻¹ •
            ((γ : SL(2,𝓞 F)) • z)) →
      specVerticalScaleFactor t * A ≤
          normHeight F ((σ * specVerticalScale t ht)⁻¹ •
            ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ (σ * specVerticalScale t ht) := by
  intro γ γ' z hγ hγ'
  rw [normHeight_specScaled_cusp] at hγ hγ'
  have hγ0 : A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) := by
    by_contra hnot
    have hlt : normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) < A := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_left hlt hc
    linarith
  have hγ'0 : A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) := by
    by_contra hnot
    have hlt : normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) < A := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_left hlt hc
    linarith
  rw [cuspStab_specVerticalScale]
  exact hsep γ γ' z hγ0 hγ'0

end ArtinPrimitiveRoots.Proofs.spec_continue_p
