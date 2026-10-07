import ArtinPrimitiveRoots.Spec.Reduction

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
  sorry

end ArtinPrimitiveRoots.A1.Spec
