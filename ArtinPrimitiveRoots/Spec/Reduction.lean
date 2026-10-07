import ArtinPrimitiveRoots.Spec.Geometry
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! Reduction-theory nodes R1--R14. This first stage states the nodes that can start against
the frozen interface. -/

set_option autoImplicit false

open Module NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction nonZeroDivisors NNReal

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- R1 `spec:cusp-lattice` — P-SPEC.md:214, 271–275. Integral multiples lie in the cusp
translation group, all translations have bounded denominators, and the embedded lattice has a
bounded measurable fundamental domain. The signed extension has at most two translation cosets. -/
theorem R1_cusp_lattice (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    (∃ m : ℕ, 0 < m ∧ ∀ a : 𝓞 F,
      algebraMap (𝓞 F) F ((m : 𝓞 F) * a) ∈ cuspLattice F Γ σ) ∧
    (∃ D : ℕ, 0 < D ∧
      (∀ μ ∈ cuspLattice F Γ σ, HasDenominatorBound F D μ) ∧
      (∀ μ ∈ cuspTranslationExtension F Γ σ, HasDenominatorBound F D μ)) ∧
    (∀ μ : F, μ ∈ cuspTranslationExtension F Γ σ ↔ μ ∈ signedCuspTranslations F Γ σ) ∧
    (IsFullZLattice (cuspTranslationsZ F Γ σ) ∧
      cuspLattice F Γ σ ≤ cuspTranslationExtension F Γ σ ∧
      ∃ μ₀ ∈ cuspTranslationExtension F Γ σ,
        ∀ μ ∈ cuspTranslationExtension F Γ σ,
          μ ∈ cuspLattice F Γ σ ∨ μ - μ₀ ∈ cuspLattice F Γ σ) ∧
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P ∧ Bornology.IsBounded P ∧
        MeasurableSet P := by
  sorry

/-- R2 `spec:cusp-units` — P-SPEC.md:215, 277–280. The cusp diagonal units have finite index;
every stabilizer element has a bounded-denominator upper-triangular form; torsion units under a
free action are central; and the stabilizer acts by the stated affine and height maps. -/
theorem R2_cusp_units (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) :
    (cuspUnits F Γ σ).FiniteIndex ∧
    (∀ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ↔ ε ∈ cuspUnitSet F Γ σ) ∧
    ∃ D : ℕ, 0 < D ∧
      (∀ γ : cuspStab F Γ σ, ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
        HasDenominatorBound F D μ ∧
        σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ) ∧
    (∀ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ → IsOfFinOrder ε →
      ε = 1 ∨ ε = -1) ∧
    (∀ γ : cuspStab F Γ σ, ∀ x : InfinitePlace F → ℂ, ∀ y : InfinitePlace F → ℝ,
      (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
        σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ ∧
        (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) =
          σ • ptX' F
            (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
              w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
            (fun w => Complex.normSq (w.embedding
              (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w)) := by
  sorry

/-! ### SPEC-R3 helper lemmas -/

private lemma bottomRow_ne_zero (g : SL(2,F)) : (bottomRow F g) ≠ (0, 0) := by
  intro h
  have h₁ : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := congrArg Prod.fst h
  have h₂ : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := congrArg Prod.snd h
  have hd : Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 := g.2
  rw [Matrix.det_fin_two] at hd
  simp [h₁, h₂] at hd

private lemma bottomRowFractionalIdeal_ne_zero (g : SL(2,F)) :
    bottomRowFractionalIdeal F g ≠ 0 := by
  rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_ne_zero]
  have hrow : (bottomRow F g).1 ≠ 0 ∨ (bottomRow F g).2 ≠ 0 := by
    by_contra hn
    push Not at hn
    exact bottomRow_ne_zero g (Prod.ext hn.1 hn.2)
  rcases hrow with h | h
  · exact ⟨0, Finset.mem_univ _, by simpa [bottomRow] using h⟩
  · exact ⟨1, Finset.mem_univ _, by simpa [bottomRow] using h⟩

private lemma bottomRowFractionalIdeal_coe (g : SL(2,F)) :
    (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F) =
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
  rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_coe]
  have hrange : Set.range (fun i : Fin 2 =>
      if i = 0 then (bottomRow F g).1 else (bottomRow F g).2) = {g 1 0, g 1 1} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [bottomRow]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h
      · exact ⟨0, by simp [bottomRow, h.symm]⟩
      · exact ⟨1, by simp [bottomRow, h.symm]⟩
  simp only [Finset.coe_univ, Set.image_univ, hrange]

private lemma bottomRowClass_eq_mk (g : SL(2,F)) :
    bottomRowClass F g =
      ClassGroup.mk F (Units.mk0 (bottomRowFractionalIdeal F g)
        (bottomRowFractionalIdeal_ne_zero g)) := by
  simp [bottomRowClass, bottomRowFractionalIdeal_ne_zero]

private lemma bottomRowFractionalIdeal_eq_coe_span (a b : 𝓞 F) (g : SL(2,F))
    (h₀ : g 1 0 = algebraMap (𝓞 F) F a)
    (h₁ : g 1 1 = algebraMap (𝓞 F) F b) :
    bottomRowFractionalIdeal F g = (Ideal.span ({a, b} : Set (𝓞 F)) :
      FractionalIdeal (𝓞 F)⁰ F) := by
  apply FractionalIdeal.coeToSubmodule_inj.mp
  rw [bottomRowFractionalIdeal_coe, FractionalIdeal.coe_coeIdeal,
    IsLocalization.coeSubmodule_span, h₀, h₁]
  congr 1
  ext x
  simp

private lemma bottomRowClass_eq_mk0 (I : (Ideal (𝓞 F))⁰)
    (g : SL(2,F)) (hrow : bottomRowFractionalIdeal F g =
      (I.1 : FractionalIdeal (𝓞 F)⁰ F)) :
    bottomRowClass F g = ClassGroup.mk0 I := by
  rw [bottomRowClass_eq_mk]
  have hu : Units.mk0 (bottomRowFractionalIdeal F g)
      (bottomRowFractionalIdeal_ne_zero g) = FractionalIdeal.mk0 F I := by
    apply Units.ext
    exact hrow
  rw [hu, ClassGroup.mk_mk0]

private lemma bottomRowClass_surjective : Function.Surjective (bottomRowClass F) := by
  classical
  intro C
  obtain ⟨I, hC⟩ := ClassGroup.mk0_surjective (R := 𝓞 F) C
  have hIbot : (I : Ideal (𝓞 F)) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIbot
  obtain ⟨b, hpair⟩ := IsDedekindDomain.exists_eq_span_pair haI ha
  let aF : F := algebraMap (𝓞 F) F a
  let bF : F := algebraMap (𝓞 F) F b
  have haF : aF ≠ 0 := by
    intro h
    apply ha
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    simpa [aF] using h
  let g : SL(2,F) := ⟨!![0, -aF⁻¹; aF, bF], by
    rw [Matrix.det_fin_two_of]
    simp [haF]⟩
  have hrow : bottomRowFractionalIdeal F g = (I : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [bottomRowFractionalIdeal_eq_coe_span a b g]
    · rw [← hpair]
    · simp [g, aF]
    · simp [g, bF]
  exact ⟨g, (bottomRowClass_eq_mk0 I g hrow).trans hC⟩

private lemma classGroup_mk_eq_iff_scalar_multiple
    (I J : FractionalIdeal (𝓞 F)⁰ F) (hI : I ≠ 0) (hJ : J ≠ 0) :
    ClassGroup.mk F (Units.mk0 I hI) = ClassGroup.mk F (Units.mk0 J hJ) ↔
      ∃ a : F, a ≠ 0 ∧ I * FractionalIdeal.spanSingleton (𝓞 F)⁰ a = J := by
  constructor
  · intro h
    have hq := congrArg (ClassGroup.equiv (R := 𝓞 F) F) h
    have hmapI : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 I hI) =
          Units.mk0 I hI := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hmapJ : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 J hJ) =
          Units.mk0 J hJ := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range
          (Units.mk0 I hI) =
        QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range
          (Units.mk0 J hJ) := by
      rw [ClassGroup.equiv_mk F, ClassGroup.equiv_mk F] at hq
      rw [hmapI, hmapJ] at hq
      exact hq
    rcases (QuotientGroup.mk'_eq_mk' (toPrincipalIdeal (𝓞 F) F).range).mp hq' with
      ⟨u, hu, hmul⟩
    rcases MonoidHom.mem_range.mp hu with ⟨v, hv⟩
    refine ⟨v, v.ne_zero, ?_⟩
    have hval := congrArg (fun x : (FractionalIdeal (𝓞 F)⁰ F)ˣ =>
      (x : FractionalIdeal (𝓞 F)⁰ F)) hmul
    have hval' : I * FractionalIdeal.spanSingleton (𝓞 F)⁰ (v : F) = J := by
      simpa [← hv, Units.val_mul, coe_toPrincipalIdeal] using hval
    exact hval'
  · rintro ⟨a, ha, hmul⟩
    let u : Fˣ := Units.mk0 a ha
    have hu : toPrincipalIdeal (𝓞 F) F u ∈ (toPrincipalIdeal (𝓞 F) F).range :=
      ⟨u, rfl⟩
    have hmul' : Units.mk0 I hI * toPrincipalIdeal (𝓞 F) F u = Units.mk0 J hJ := by
      apply Units.ext
      simpa [u, Units.val_mul, coe_toPrincipalIdeal] using hmul
    apply (ClassGroup.equiv (R := 𝓞 F) F).injective
    have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range
          (Units.mk0 I hI) =
        QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range
          (Units.mk0 J hJ) :=
      (QuotientGroup.mk'_eq_mk' (toPrincipalIdeal (𝓞 F) F).range).2
        ⟨toPrincipalIdeal (𝓞 F) F u, hu, hmul'⟩
    have hmapI : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 I hI) =
          Units.mk0 I hI := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    have hmapJ : Units.mapEquiv
        (↑(FractionalIdeal.canonicalEquiv (𝓞 F)⁰ F F)) (Units.mk0 J hJ) =
          Units.mk0 J hJ := by
      apply Units.ext
      simp [FractionalIdeal.canonicalEquiv_self]
    rw [ClassGroup.equiv_mk F, ClassGroup.equiv_mk F]
    rw [hmapI, hmapJ]
    exact hq'

private lemma bottomRowClass_eq_iff_scalar_multiple (g h : SL(2,F)) :
    bottomRowClass F g = bottomRowClass F h ↔
      ∃ a : F, a ≠ 0 ∧
        bottomRowFractionalIdeal F g * FractionalIdeal.spanSingleton (𝓞 F)⁰ a =
          bottomRowFractionalIdeal F h := by
  rw [bottomRowClass_eq_mk, bottomRowClass_eq_mk]
  exact classGroup_mk_eq_iff_scalar_multiple _ _
    (bottomRowFractionalIdeal_ne_zero g) (bottomRowFractionalIdeal_ne_zero h)

private lemma exists_inverse_row_coefficients (g : SL(2,F)) :
    ∃ a b : F,
      a ∈ (bottomRowFractionalIdeal F g)⁻¹ ∧
      b ∈ (bottomRowFractionalIdeal F g)⁻¹ ∧
      a * g 1 0 + b * g 1 1 = 1 := by
  let I := bottomRowFractionalIdeal F g
  have hIne : I ≠ 0 := by exact bottomRowFractionalIdeal_ne_zero g
  have hIspan : (I : Submodule (𝓞 F) F) =
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    exact bottomRowFractionalIdeal_coe g
  let K : Submodule (𝓞 F) F := {
    carrier := {x | ∃ a b : F,
      a ∈ (I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) ∧
      b ∈ (I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) ∧ a * g 1 0 + b * g 1 1 = x}
    zero_mem' := by
      exact ⟨0, 0,
        Submodule.zero_mem ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F),
        Submodule.zero_mem ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F), by simp⟩
    add_mem' := by
      rintro x y ⟨a, b, ha, hb, rfl⟩ ⟨a', b', ha', hb', rfl⟩
      refine ⟨a + a', b + b', ?_, ?_, ?_⟩
      · exact Submodule.add_mem
          ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ha ha'
      · exact Submodule.add_mem
          ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) hb hb'
      · ring
    smul_mem' := by
      intro r x hx
      rcases hx with ⟨a, b, ha, hb, hab⟩
      refine ⟨r • a, r • b,
        Submodule.smul_mem ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) r ha,
        Submodule.smul_mem ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) r hb, ?_⟩
      calc
        (r • a) * g 1 0 + (r • b) * g 1 1 =
            (r • (a * g 1 0 + b * g 1 1)) := by
          simp only [Algebra.smul_def]
          ring
        _ = r • x := by rw [hab]
  }
  have hprod_le :
      (I : Submodule (𝓞 F) F) *
        ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ≤ K := by
    rw [Submodule.mul_le]
    intro x hx y hy
    have hx' : x ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
      rw [← hIspan]
      exact hx
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp hx'
    refine ⟨r • y, s • y, Submodule.smul_mem _ r hy,
      Submodule.smul_mem _ s hy, ?_⟩
    calc
      (r • y) * g 1 0 + (s • y) * g 1 1 = (r • g 1 0 + s • g 1 1) * y := by
        simp only [Algebra.smul_def]
        ring
      _ = x * y := by rw [hrs]
  have hone : (1 : F) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hIne]
    simp
  have hone' : (1 : F) ∈ (I : Submodule (𝓞 F) F) *
      ((I⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    simpa only [FractionalIdeal.coe_mul] using (FractionalIdeal.mem_coe).mpr hone
  rcases hprod_le hone' with ⟨a, b, ha, hb, hab⟩
  exact ⟨a, b, ha, hb, hab⟩

private lemma exists_row_completion (g : SL(2,F)) :
    ∃ M : SL(2,F),
      M 1 0 = g 1 0 ∧ M 1 1 = g 1 1 ∧
      M 0 0 ∈ (bottomRowFractionalIdeal F g)⁻¹ ∧
      M 0 1 ∈ (bottomRowFractionalIdeal F g)⁻¹ := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_inverse_row_coefficients g
  let M : SL(2,F) := ⟨!![b, -a; g 1 0, g 1 1], by
    rw [Matrix.det_fin_two_of]
    calc
      b * g 1 1 - (-a) * g 1 0 = a * g 1 0 + b * g 1 1 := by ring
      _ = 1 := hab⟩
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · simp [M]
  · simp [M]
  · simpa [M] using hb
  · change -a ∈ (bottomRowFractionalIdeal F g)⁻¹
    exact Submodule.neg_mem
      (((bottomRowFractionalIdeal F g)⁻¹ : FractionalIdeal (𝓞 F)⁰ F) :
        Submodule (𝓞 F) F) ha

private lemma same_bottomRow_borel (g h : SL(2,F))
    (hh : bottomRow F g = bottomRow F h) : h * g⁻¹ ∈ borelSL F := by
  change (h * g⁻¹ : SL(2,F)) 1 0 = 0
  have hc : g 1 0 = h 1 0 := congrArg Prod.fst hh
  have hd : g 1 1 = h 1 1 := congrArg Prod.snd hh
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]
  rw [hc, hd]
  ring

private lemma quotient_eq_of_bottomRow_eq (g h : SL(2,F))
    (hh : bottomRow F g = bottomRow F h) :
    Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) h := by
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr (same_bottomRow_borel g h hh)

private lemma bottomRow_first_mem (g : SL(2,F)) :
    g 1 0 ∈ bottomRowFractionalIdeal F g := by
  change g 1 0 ∈ (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [bottomRowFractionalIdeal_coe]
  exact Submodule.subset_span (by simp)

private lemma bottomRow_second_mem (g : SL(2,F)) :
    g 1 1 ∈ bottomRowFractionalIdeal F g := by
  change g 1 1 ∈ (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [bottomRowFractionalIdeal_coe]
  exact Submodule.subset_span (by simp)

private lemma exists_integral_transition_of_equal_row_ideal
    (g h : SL(2,F))
    (hI : bottomRowFractionalIdeal F g = bottomRowFractionalIdeal F h) :
    ∃ γ : SL(2,𝓞 F),
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
        Quotient.mk (QuotientGroup.rightRel (borelSL F)) (h * toSLF F γ) := by
  classical
  obtain ⟨M, hMc, hMd, hM₀, hM₁⟩ := exists_row_completion g
  obtain ⟨N, hNc, hNd, hN₀, hN₁⟩ := exists_row_completion h
  let I := bottomRowFractionalIdeal F g
  have hIne : I ≠ 0 := bottomRowFractionalIdeal_ne_zero g
  have hIinv : (bottomRowFractionalIdeal F g)⁻¹ =
      (bottomRowFractionalIdeal F h)⁻¹ := congrArg (fun J : FractionalIdeal (𝓞 F)⁰ F => J⁻¹) hI
  have hM₀' : M 0 0 ∈ I⁻¹ := hM₀
  have hM₁' : M 0 1 ∈ I⁻¹ := hM₁
  have hM₂' : M 1 0 ∈ I := by rw [hMc]; exact bottomRow_first_mem g
  have hM₃' : M 1 1 ∈ I := by rw [hMd]; exact bottomRow_second_mem g
  have hN₀' : N 0 0 ∈ I⁻¹ := hIinv.symm ▸ hN₀
  have hN₁' : N 0 1 ∈ I⁻¹ := hIinv.symm ▸ hN₁
  have hN₂' : N 1 0 ∈ I := by
    change N 1 0 ∈ bottomRowFractionalIdeal F g
    rw [hI, hNc]
    exact bottomRow_first_mem h
  have hN₃' : N 1 1 ∈ I := by
    change N 1 1 ∈ bottomRowFractionalIdeal F g
    rw [hI, hNd]
    exact bottomRow_second_mem h
  have hIprod : I * I⁻¹ = (1 : FractionalIdeal (𝓞 F)⁰ F) :=
    mul_inv_cancel₀ hIne
  have prod01 (x : F) (y : F) (hx : x ∈ I) (hy : y ∈ I⁻¹) :
      x * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := FractionalIdeal.mul_mem_mul hx hy
    simpa [hIprod] using hp
  have prod10 (x : F) (y : F) (hx : x ∈ I⁻¹) (hy : y ∈ I) :
      x * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := FractionalIdeal.mul_mem_mul hy hx
    simpa [mul_comm, hIprod] using hp
  have h00 : M 1 1 * N 0 0 - M 0 1 * N 1 0 ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := prod01 (M 1 1) (N 0 0) hM₃' hN₀'
    have hq := prod10 (M 0 1) (N 1 0) hM₁' hN₂'
    have hp' : M 1 1 * N 0 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hp
    have hq' : M 0 1 * N 1 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hq
    have hs := Submodule.sub_mem _ hp' hq'
    rw [← FractionalIdeal.coe_one] at hs
    exact (FractionalIdeal.mem_coe).mp hs
  have h01 : M 1 1 * N 0 1 - M 0 1 * N 1 1 ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := prod01 (M 1 1) (N 0 1) hM₃' hN₁'
    have hq := prod10 (M 0 1) (N 1 1) hM₁' hN₃'
    have hp' : M 1 1 * N 0 1 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hp
    have hq' : M 0 1 * N 1 1 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hq
    have hs := Submodule.sub_mem _ hp' hq'
    rw [← FractionalIdeal.coe_one] at hs
    exact (FractionalIdeal.mem_coe).mp hs
  have h10 : -(M 1 0 * N 0 0) + M 0 0 * N 1 0 ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := prod01 (M 1 0) (N 0 0) hM₂' hN₀'
    have hq := prod10 (M 0 0) (N 1 0) hM₀' hN₂'
    have hp' : M 1 0 * N 0 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hp
    have hq' : M 0 0 * N 1 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hq
    have hs := Submodule.add_mem _ (Submodule.neg_mem _ hp') hq'
    rw [← FractionalIdeal.coe_one] at hs
    exact (FractionalIdeal.mem_coe).mp hs
  have h11 : -(M 1 0 * N 0 1) + M 0 0 * N 1 1 ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    have hp := prod01 (M 1 0) (N 0 1) hM₂' hN₁'
    have hq := prod10 (M 0 0) (N 1 1) hM₀' hN₃'
    have hp' : M 1 0 * N 0 1 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hp
    have hq' : M 0 0 * N 1 1 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [← FractionalIdeal.coe_one]
      exact (FractionalIdeal.mem_coe).mpr hq
    have hs := Submodule.add_mem _ (Submodule.neg_mem _ hp') hq'
    rw [← FractionalIdeal.coe_one] at hs
    exact (FractionalIdeal.mem_coe).mp hs
  let T : SL(2,F) := M⁻¹ * N
  have hT00formula : T 0 0 = M 1 1 * N 0 0 - M 0 1 * N 1 0 := by
    change ((M⁻¹ * N : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hT01formula : T 0 1 = M 1 1 * N 0 1 - M 0 1 * N 1 1 := by
    change ((M⁻¹ * N : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hT10formula : T 1 0 = -(M 1 0 * N 0 0) + M 0 0 * N 1 0 := by
    change ((M⁻¹ * N : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hT11formula : T 1 1 = -(M 1 0 * N 0 1) + M 0 0 * N 1 1 := by
    change ((M⁻¹ * N : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hT00 : T 0 0 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hT00formula]
    exact h00
  have hT01 : T 0 1 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hT01formula]
    exact h01
  have hT10 : T 1 0 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hT10formula]
    exact h10
  have hT11 : T 1 1 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [hT11formula]
    exact h11
  have hTentries (i j : Fin 2) : T i j ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    fin_cases i <;> fin_cases j
    · exact hT00
    · exact hT01
    · exact hT10
    · exact hT11
  have hLift (i j : Fin 2) : ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = T i j := by
    exact (FractionalIdeal.mem_one_iff (𝓞 F)⁰).mp (hTentries i j)
  let A : Matrix (Fin 2) (Fin 2) (𝓞 F) := fun i j => Classical.choose (hLift i j)
  have hAmap (i j : Fin 2) : algebraMap (𝓞 F) F (A i j) = T i j :=
    Classical.choose_spec (hLift i j)
  have hdetMap : algebraMap (𝓞 F) F (Matrix.det A) = 1 := by
    rw [RingHom.map_det (algebraMap (𝓞 F) F) A]
    calc
      Matrix.det (fun i j => algebraMap (𝓞 F) F (A i j)) =
          Matrix.det (T : Matrix (Fin 2) (Fin 2) F) := by
        congr 1
        ext i j
        exact hAmap i j
      _ = 1 := T.2
  have hdetA : Matrix.det A = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    simpa using hdetMap
  let δ : SL(2,𝓞 F) := ⟨A, hdetA⟩
  have hδ : toSLF F δ = T := by
    apply Subtype.ext
    change (algebraMap (𝓞 F) F).mapMatrix A = (T : Matrix (Fin 2) (Fin 2) F)
    ext i j
    exact hAmap i j
  have hMN : M * toSLF F δ = N := by
    rw [hδ]
    simp [T, mul_assoc]
  have hrowM : bottomRow F (g * toSLF F δ) = bottomRow F (M * toSLF F δ) := by
    simp [bottomRow, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hMc, hMd]
  have hrowN : bottomRow F (M * toSLF F δ) = bottomRow F N := congrArg (bottomRow F) hMN
  have hrowH : bottomRow F N = bottomRow F h := by simp [bottomRow, hNc, hNd]
  have hrow : bottomRow F (g * toSLF F δ) = bottomRow F h := hrowM.trans (hrowN.trans hrowH)
  have hrel : (h * toSLF F δ⁻¹) * g⁻¹ ∈ borelSL F := by
    simpa [_root_.mul_inv_rev, mul_assoc] using
      (same_bottomRow_borel (g * toSLF F δ) h hrow)
  refine ⟨δ⁻¹, ?_⟩
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr hrel

private lemma bottomRowFractionalIdeal_left_borel
    (b : SL(2,F)) (hb : b ∈ borelSL F) (g : SL(2,F)) :
    b 1 1 ≠ 0 ∧ bottomRowFractionalIdeal F (b * g) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1) * bottomRowFractionalIdeal F g := by
  have hb₀ : b 1 0 = 0 := hb
  let u : F := b 1 1
  have hu : u ≠ 0 := by
    intro hu0
    have hdet : Matrix.det (b : Matrix (Fin 2) (Fin 2) F) = 1 := b.2
    rw [Matrix.det_fin_two] at hdet
    simp [hb₀, u, hu0] at hdet
  have hrow₀ : (b * g) 1 0 = u * g 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [u, hb₀]
  have hrow₁ : (b * g) 1 1 = u * g 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [u, hb₀]
  refine ⟨hu, ?_⟩
  have hrow : bottomRowFractionalIdeal F (b * g) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ u * bottomRowFractionalIdeal F g := by
    apply FractionalIdeal.coeToSubmodule_inj.mp
    rw [bottomRowFractionalIdeal_coe, FractionalIdeal.coe_mul,
      FractionalIdeal.coe_spanSingleton, bottomRowFractionalIdeal_coe,
      hrow₀, hrow₁, Submodule.span_mul_span]
    apply congrArg (Submodule.span (𝓞 F))
    ext x
    simp
  simpa [u] using hrow

private lemma bottomRowFractionalIdeal_right_early_le (g : SL(2,F))
    (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) ≤ bottomRowFractionalIdeal F g := by
  change (bottomRowFractionalIdeal F (g * toSLF F γ) : Submodule (𝓞 F) F) ≤
    (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [bottomRowFractionalIdeal_coe, bottomRowFractionalIdeal_coe]
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hrow₀ : (g * toSLF F γ) 1 0 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 0) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 0) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hrow₁ : (g * toSLF F γ) 1 1 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 1) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hc : g 1 0 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hd : g 1 1 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hca : g 1 0 * algebraMap (𝓞 F) F (γ 0 0) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 0 0) hc)
  have hdb : g 1 1 * algebraMap (𝓞 F) F (γ 1 0) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 1 0) hd)
  have hca' : g 1 0 * algebraMap (𝓞 F) F (γ 0 1) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 0 1) hc)
  have hdb' : g 1 1 * algebraMap (𝓞 F) F (γ 1 1) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 1 1) hd)
  rcases hx with hx | hx
  · rw [hx, hrow₀]
    exact Submodule.add_mem _ hca hdb
  · rw [hx, hrow₁]
    exact Submodule.add_mem _ hca' hdb'

private lemma bottomRowFractionalIdeal_right_early (g : SL(2,F))
    (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) = bottomRowFractionalIdeal F g := by
  apply le_antisymm (bottomRowFractionalIdeal_right_early_le g γ)
  have hmul : (g * toSLF F γ) * toSLF F γ⁻¹ = g := by simp [mul_assoc]
  have h := bottomRowFractionalIdeal_right_early_le (g * toSLF F γ) γ⁻¹
  rw [hmul] at h
  exact h

private lemma bottomRowClass_left_borel
    (b : SL(2,F)) (hb : b ∈ borelSL F) (g : SL(2,F)) :
    bottomRowClass F (b * g) = bottomRowClass F g := by
  obtain ⟨hu, hrow⟩ := bottomRowFractionalIdeal_left_borel b hb g
  apply (bottomRowClass_eq_iff_scalar_multiple (b * g) g).2
  refine ⟨(b 1 1)⁻¹, inv_ne_zero hu, ?_⟩
  calc
    bottomRowFractionalIdeal F (b * g) *
        FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1)⁻¹ =
      (FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1) *
        bottomRowFractionalIdeal F g) *
          FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1)⁻¹ := by rw [hrow]
    _ = bottomRowFractionalIdeal F g := by
      calc
        _ = bottomRowFractionalIdeal F g *
            (FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1) *
              FractionalIdeal.spanSingleton (𝓞 F)⁰ (b 1 1)⁻¹) := by ac_rfl
        _ = bottomRowFractionalIdeal F g := by
          rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
          simp [hu]

private lemma bottomRowClass_right_integral (g : SL(2,F)) (γ : SL(2,𝓞 F)) :
    bottomRowClass F (g * toSLF F γ) = bottomRowClass F g := by
  rw [bottomRowClass_eq_mk, bottomRowClass_eq_mk]
  apply congrArg (ClassGroup.mk F)
  apply Units.ext
  exact bottomRowFractionalIdeal_right_early g γ

private lemma quotient_eq_left_borel
    (b : SL(2,F)) (hb : b ∈ borelSL F) (g : SL(2,F)) :
    Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) (b * g) := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa [mul_assoc] using hb

private lemma bottomRowClass_eq_iff_integral_orbit (g h : SL(2,F)) :
    bottomRowClass F g = bottomRowClass F h ↔
      ∃ γ : SL(2,𝓞 F),
        Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
          Quotient.mk (QuotientGroup.rightRel (borelSL F)) (h * toSLF F γ) := by
  constructor
  · intro hclass
    obtain ⟨a, ha, hscale⟩ :=
      (bottomRowClass_eq_iff_scalar_multiple g h).mp hclass
    let b : SL(2,F) := ⟨!![a⁻¹, 0; 0, a], by
      rw [Matrix.det_fin_two_of]
      simp [ha]⟩
    have hb : b ∈ borelSL F := by
      change (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      simp [b]
    have hscale' : bottomRowFractionalIdeal F (b * g) =
        bottomRowFractionalIdeal F h := by
      calc
        bottomRowFractionalIdeal F (b * g) =
            FractionalIdeal.spanSingleton (𝓞 F)⁰ a * bottomRowFractionalIdeal F g := by
          simpa [b] using (bottomRowFractionalIdeal_left_borel b hb g).2
        _ = bottomRowFractionalIdeal F g * FractionalIdeal.spanSingleton (𝓞 F)⁰ a := by
          rw [mul_comm]
        _ = bottomRowFractionalIdeal F h := hscale
    obtain ⟨γ, htrans⟩ := exists_integral_transition_of_equal_row_ideal (b * g) h hscale'
    exact ⟨γ, (quotient_eq_left_borel b hb g).trans htrans⟩
  · rintro ⟨γ, hq⟩
    have hrel : (h * toSLF F γ) * g⁻¹ ∈ borelSL F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    let b : SL(2,F) := (h * toSLF F γ) * g⁻¹
    have hb : b ∈ borelSL F := hrel
    have hbg : b * g = h * toSLF F γ := by simp [b, mul_assoc]
    calc
      bottomRowClass F g = bottomRowClass F (b * g) :=
        (bottomRowClass_left_borel b hb g).symm
      _ = bottomRowClass F (h * toSLF F γ) := congrArg (bottomRowClass F) hbg
      _ = bottomRowClass F h := bottomRowClass_right_integral h γ

private lemma quotient_right_mul_congr (x y δ : SL(2,F))
    (h : Quotient.mk (QuotientGroup.rightRel (borelSL F)) x =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) y) :
    Quotient.mk (QuotientGroup.rightRel (borelSL F)) (x * δ) =
      Quotient.mk (QuotientGroup.rightRel (borelSL F)) (y * δ) := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have hrel : y * x⁻¹ ∈ borelSL F := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
  simpa [_root_.mul_inv_rev, mul_assoc] using hrel

private def cuspOrbitSetoid (Γ : Subgroup SL(2,𝓞 F)) (A : SL(2,F))
    (rep : (SL(2,𝓞 F) ⧸ Γ) → SL(2,𝓞 F)) : Setoid (SL(2,𝓞 F) ⧸ Γ) where
  r p q := ∃ γ : Γ,
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
      (A * toSLF F (rep p)) =
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
      (A * toSLF F (rep q) * toSLF F (γ : SL(2,𝓞 F)))
  iseqv := by
    constructor
    · intro p
      exact ⟨1, by simp⟩
    · intro p q hpq
      rcases hpq with ⟨γ, hγ⟩
      refine ⟨γ⁻¹, ?_⟩
      have hmul := quotient_right_mul_congr
        (A * toSLF F (rep p))
        (A * toSLF F (rep q) * toSLF F (γ : SL(2,𝓞 F)))
        (toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F))) hγ
      simpa [mul_assoc] using hmul.symm
    · intro p q r hpq hqr
      rcases hpq with ⟨γ, hγ⟩
      rcases hqr with ⟨δ, hδ⟩
      refine ⟨δ * γ, ?_⟩
      have hmul := quotient_right_mul_congr
        (A * toSLF F (rep q))
        (A * toSLF F (rep r) * toSLF F (δ : SL(2,𝓞 F)))
        (toSLF F (γ : SL(2,𝓞 F))) hδ
      calc
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (A * toSLF F (rep p)) =
          Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (A * toSLF F (rep q) * toSLF F (γ : SL(2,𝓞 F))) := hγ
        _ = Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (A * toSLF F (rep r) * toSLF F (δ : SL(2,𝓞 F)) *
              toSLF F (γ : SL(2,𝓞 F))) := hmul
        _ = Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (A * toSLF F (rep r) * toSLF F ((δ * γ : Γ) : SL(2,𝓞 F))) := by
          simp [map_mul, mul_assoc]

private lemma mem_cuspStab_iff (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) :
    γ ∈ cuspStab F Γ σ ↔
      σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ ∈ borelSL F := by
  simp only [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

private lemma cuspStab_transition_image (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ γ' : Γ) (h : γ' * γ⁻¹ ∈ cuspStab F Γ σ) :
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
        (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F))) =
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
        (σ⁻¹ * toSLF F (γ' : SL(2,𝓞 F))) := by
  have hconj := (mem_cuspStab_iff Γ σ (γ' * γ⁻¹)).mp h
  have hrel : (σ⁻¹ * toSLF F (γ' : SL(2,𝓞 F))) *
      (σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)))⁻¹ ∈ borelSL F := by
    simpa [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc] using hconj
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr hrel

private def cuspIndexSetoid (Γ : Subgroup SL(2,𝓞 F))
    (a : ClassGroup (𝓞 F) → SL(2,F))
    (rep : (SL(2,𝓞 F) ⧸ Γ) → SL(2,𝓞 F)) :
    Setoid (ClassGroup (𝓞 F) × (SL(2,𝓞 F) ⧸ Γ)) where
  r x y := x.1 = y.1 ∧
    cuspOrbitSetoid Γ (a x.1) rep x.2 y.2
  iseqv := by
    constructor
    · intro x
      exact ⟨rfl, (cuspOrbitSetoid Γ (a x.1) rep).iseqv.refl x.2⟩
    · rintro ⟨C, p⟩ ⟨C', q⟩ h
      rcases h with ⟨hC, hq⟩
      cases hC
      exact ⟨rfl, (cuspOrbitSetoid Γ (a C) rep).iseqv.symm hq⟩
    · rintro ⟨C, p⟩ ⟨C', q⟩ ⟨C'', r⟩ hxy hyz
      rcases hxy with ⟨hxyC, hxy⟩
      rcases hyz with ⟨hyzC, hyz⟩
      cases hxyC
      cases hyzC
      exact ⟨rfl, (cuspOrbitSetoid Γ (a C) rep).iseqv.trans hxy hyz⟩

set_option maxHeartbeats 500000 in
private theorem exists_cusp_reps_bijective (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    ∃ (ι : Type) (_ : Fintype ι) (σ : ι → SL(2,F)),
      Function.Bijective (fun p : (Σ i, CuspCosets F Γ (σ i)) =>
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F)))) := by
  classical
  letI : Fintype (ClassGroup (𝓞 F)) := inferInstance
  let P := SL(2,𝓞 F) ⧸ Γ
  letI : Fintype P := Subgroup.fintypeQuotientOfFiniteIndex
  have hmkSurj : Function.Surjective
      (Quotient.mk (QuotientGroup.leftRel Γ) : SL(2,𝓞 F) → P) := Quotient.mk_surjective
  let rep : P → SL(2,𝓞 F) := fun p => Classical.choose (hmkSurj p)
  have hrep (p : P) : Quotient.mk (QuotientGroup.leftRel Γ) (rep p) = p :=
    Classical.choose_spec (hmkSurj p)
  let a : ClassGroup (𝓞 F) → SL(2,F) := fun C => Classical.choose (bottomRowClass_surjective C)
  have ha (C : ClassGroup (𝓞 F)) : bottomRowClass F (a C) = C :=
    Classical.choose_spec (bottomRowClass_surjective C)
  let ι := Quotient (cuspIndexSetoid Γ a rep)
  letI : Fintype ι := by
    dsimp [ι]
    infer_instance
  let indexRep : ι → ClassGroup (𝓞 F) × P := Quotient.out
  have hindexRep (i : ι) :
      Quotient.mk (cuspIndexSetoid Γ a rep) (indexRep i) = i := Quotient.out_eq' i
  let σ : ι → SL(2,F) := fun i =>
    (a (indexRep i).1 * toSLF F (rep (indexRep i).2))⁻¹
  have hσ (i : ι) : (σ i)⁻¹ = a (indexRep i).1 * toSLF F (rep (indexRep i).2) := by
    simp [σ]
  let Q := Quotient (QuotientGroup.rightRel (borelSL F))
  let f : (Σ i, CuspCosets F Γ (σ i)) → Q := fun p =>
    Quotient.mk (QuotientGroup.rightRel (borelSL F))
      ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F)))
  refine ⟨ι, inferInstance, σ, ?_⟩
  change Function.Bijective f
  have hsurj : Function.Surjective f := by
    intro z
    let g : SL(2,F) := Quotient.out z
    have hg : Quotient.mk (QuotientGroup.rightRel (borelSL F)) g = z :=
      Quotient.out_eq' z
    let C : ClassGroup (𝓞 F) := bottomRowClass F g
    let C0 := C
    have hclass : bottomRowClass F g = bottomRowClass F (a C0) := by
      simpa [C0, C] using (ha C0).symm
    obtain ⟨δ, hδorbit⟩ :=
      (bottomRowClass_eq_iff_integral_orbit g (a C0)).mp hclass
    let pG : P := Quotient.mk (QuotientGroup.leftRel Γ) δ
    have hmk : Quotient.mk (QuotientGroup.leftRel Γ) (rep pG) =
        Quotient.mk (QuotientGroup.leftRel Γ) δ := by
      simpa [pG] using hrep pG
    have hleft : (rep pG)⁻¹ * δ ∈ Γ :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact hmk)
    let β : Γ := ⟨(rep pG)⁻¹ * δ, hleft⟩
    have hδ : δ = rep pG * (β : SL(2,𝓞 F)) := by
      change δ = rep pG * ((rep pG)⁻¹ * δ)
      group
    have hgbase :
        Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
          Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (a C0 * toSLF F (rep pG) * toSLF F (β : SL(2,𝓞 F))) := by
      simpa [hδ, map_mul, mul_assoc] using hδorbit
    let i : ι := Quotient.mk (cuspIndexSetoid Γ a rep) (C0, pG)
    have hidx : Quotient.mk (cuspIndexSetoid Γ a rep) (indexRep i) =
        Quotient.mk (cuspIndexSetoid Γ a rep) (C0, pG) := by
      simpa [i] using hindexRep i
    rcases Quotient.exact hidx with ⟨hC, hOrbit⟩
    let C1 := (indexRep i).1
    let p1 := (indexRep i).2
    have hclass1 : bottomRowClass F (a C1) = bottomRowClass F (a C0) := by
      calc
        _ = C1 := ha C1
        _ = C0 := hC
        _ = bottomRowClass F (a C0) := (ha C0).symm
    obtain ⟨ε, hε⟩ := hOrbit
    let α : Γ := ε⁻¹ * β
    have hmove :
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((a (indexRep i).1 * toSLF F (rep (indexRep i).2)) *
            toSLF F (α : SL(2,𝓞 F))) =
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((a C0 * toSLF F (rep pG)) * toSLF F (β : SL(2,𝓞 F))) := by
      have hm := quotient_right_mul_congr
        (a (indexRep i).1 * toSLF F (rep (indexRep i).2))
        (a (indexRep i).1 * toSLF F (rep pG) * toSLF F (ε : SL(2,𝓞 F)))
        (toSLF F (α : SL(2,𝓞 F))) hε
      simpa [α, hC, map_mul, mul_assoc] using hm
    have hfinal : Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ i)⁻¹ * toSLF F (α : SL(2,𝓞 F))) := by
      rw [hσ i]
      exact hgbase.trans hmove.symm
    let c : CuspCosets F Γ (σ i) :=
      Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (σ i))) α
    have hcEq : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (σ i))) c.out =
        Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (σ i))) α := by
      simpa [c] using (Quotient.out_eq' c)
    have hstab : α * c.out⁻¹ ∈ cuspStab F Γ (σ i) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hcEq)
    have hcout := cuspStab_transition_image Γ (σ i) c.out α hstab
    refine ⟨⟨i, c⟩, ?_⟩
    dsimp [f]
    exact hcout.trans (hfinal.symm.trans hg)
  have hinj : Function.Injective f := by
    intro p p' hp
    rcases p with ⟨i, c⟩
    rcases p' with ⟨j, d⟩
    let γ : Γ := c.out
    let δ : Γ := d.out
    let x : ClassGroup (𝓞 F) × P := indexRep i
    let y : ClassGroup (𝓞 F) × P := indexRep j
    have hq : Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((a x.1 * toSLF F (rep x.2)) * toSLF F (γ : SL(2,𝓞 F))) =
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ : SL(2,𝓞 F))) := by
      simpa [f, hσ, γ, δ, x, y] using hp
    have hxi : bottomRowClass F
        ((a x.1 * toSLF F (rep x.2)) * toSLF F (γ : SL(2,𝓞 F))) = x.1 := by
      calc
        _ = bottomRowClass F (a x.1 * toSLF F (rep x.2)) :=
          bottomRowClass_right_integral _ γ
        _ = bottomRowClass F (a x.1) := bottomRowClass_right_integral _ _
        _ = x.1 := ha x.1
    have hyi : bottomRowClass F
        ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ : SL(2,𝓞 F))) = y.1 := by
      calc
        _ = bottomRowClass F (a y.1 * toSLF F (rep y.2)) :=
          bottomRowClass_right_integral _ δ
        _ = bottomRowClass F (a y.1) := bottomRowClass_right_integral _ _
        _ = y.1 := ha y.1
    have hclassOut := (bottomRowClass_eq_iff_integral_orbit _ _).2 ⟨1, by simpa using hq⟩
    have hC : x.1 = y.1 := by
      calc
        x.1 = bottomRowClass F
            ((a x.1 * toSLF F (rep x.2)) * toSLF F (γ : SL(2,𝓞 F))) := hxi.symm
        _ = bottomRowClass F
            ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ : SL(2,𝓞 F))) := hclassOut
        _ = y.1 := hyi
    have hmove :
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
            (a x.1 * toSLF F (rep x.2)) =
          Quotient.mk (QuotientGroup.rightRel (borelSL F))
            ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ * γ⁻¹ : SL(2,𝓞 F))) := by
      have hm := quotient_right_mul_congr
        ((a x.1 * toSLF F (rep x.2)) * toSLF F (γ : SL(2,𝓞 F)))
        ((a y.1 * toSLF F (rep y.2)) * toSLF F (δ : SL(2,𝓞 F)))
        (toSLF F ((γ⁻¹ : Γ) : SL(2,𝓞 F))) hq
      simpa [map_mul, mul_assoc] using hm
    have hOrbit : cuspOrbitSetoid Γ (a x.1) rep x.2 y.2 := by
      refine ⟨δ * γ⁻¹, ?_⟩
      simpa [hC, map_mul, mul_assoc] using hmove
    have hidxRel : (cuspIndexSetoid Γ a rep).r x y := ⟨hC, hOrbit⟩
    have hidx : Quotient.mk (cuspIndexSetoid Γ a rep) x =
        Quotient.mk (cuspIndexSetoid Γ a rep) y := Quotient.sound hidxRel
    have hij : i = j := by
      dsimp [x, y] at hidx
      rw [← hindexRep i, ← hindexRep j]
      exact hidx
    cases hij
    have hq' : Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F))) =
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((σ i)⁻¹ * toSLF F (δ : SL(2,𝓞 F))) := by
      simpa [f] using hp
    have hrelB : (σ i)⁻¹ * toSLF F (δ : SL(2,𝓞 F)) *
        ((σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)))⁻¹ ∈ borelSL F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hq')
    have hconj : (σ i)⁻¹ * toSLF F (δ * γ⁻¹ : SL(2,𝓞 F)) * (σ i) ∈ borelSL F := by
      simpa [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc] using hrelB
    have hstab : δ * γ⁻¹ ∈ cuspStab F Γ (σ i) :=
      (mem_cuspStab_iff Γ (σ i) (δ * γ⁻¹)).mpr hconj
    have hcd : c = d := by
      rw [← Quotient.out_eq' c, ← Quotient.out_eq' d]
      apply Quotient.sound
      exact QuotientGroup.rightRel_apply.mpr hstab
    exact congrArg (Sigma.mk i) hcd
  exact ⟨hinj, hsurj⟩

private lemma bottomRowFractionalIdeal_right_le (g : SL(2,F))
    (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) ≤ bottomRowFractionalIdeal F g := by
  change (bottomRowFractionalIdeal F (g * toSLF F γ) : Submodule (𝓞 F) F) ≤
    (bottomRowFractionalIdeal F g : Submodule (𝓞 F) F)
  rw [bottomRowFractionalIdeal_coe, bottomRowFractionalIdeal_coe]
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hrow₀ : (g * toSLF F γ) 1 0 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 0) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 0) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hrow₁ : (g * toSLF F γ) 1 1 =
      g 1 0 * algebraMap (𝓞 F) F (γ 0 1) +
        g 1 1 * algebraMap (𝓞 F) F (γ 1 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, toSLF]
  have hc : g 1 0 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hd : g 1 1 ∈ Submodule.span (𝓞 F) {g 1 0, g 1 1} :=
    Submodule.subset_span (by simp)
  have hca : g 1 0 * algebraMap (𝓞 F) F (γ 0 0) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 0 0) hc)
  have hdb : g 1 1 * algebraMap (𝓞 F) F (γ 1 0) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 1 0) hd)
  have hca' : g 1 0 * algebraMap (𝓞 F) F (γ 0 1) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 0 1) hc)
  have hdb' : g 1 1 * algebraMap (𝓞 F) F (γ 1 1) ∈
      Submodule.span (𝓞 F) {g 1 0, g 1 1} := by
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.smul_mem (Submodule.span (𝓞 F) {g 1 0, g 1 1}) (γ 1 1) hd)
  rcases hx with hx | hx
  · rw [hx, hrow₀]
    exact Submodule.add_mem _ hca hdb
  · rw [hx, hrow₁]
    exact Submodule.add_mem _ hca' hdb'

private lemma bottomRowFractionalIdeal_right (g : SL(2,F))
    (γ : SL(2,𝓞 F)) :
    bottomRowFractionalIdeal F (g * toSLF F γ) = bottomRowFractionalIdeal F g := by
  apply le_antisymm (bottomRowFractionalIdeal_right_le g γ)
  have hmul : (g * toSLF F γ) * toSLF F γ⁻¹ = g := by simp [mul_assoc]
  have h := bottomRowFractionalIdeal_right_le (g * toSLF F γ) γ⁻¹
  rw [hmul] at h
  exact h

/-- R3 `spec:cusps-finite` — P-SPEC.md:216, 282–289. The finite cusp representatives give the
bijective decomposition of `B(F) \ SL(2,F)` consumed by P-EIS and P-REDUCTION; bottom-row ideal
classes have precisely the `SL(2,O_F)` orbits as fibres. -/
theorem R3_cusps_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∃ (ι : Type) (_ : Fintype ι) (σ : ι → SL(2,F)),
      Function.Bijective (fun p : (Σ i, CuspCosets F Γ (σ i)) =>
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F))))) ∧
    (∀ g : SL(2,F), bottomRowFractionalIdeal F g ≠ 0) ∧
    Function.Surjective (bottomRowClass F) ∧
    ∀ g h : SL(2,F),
      bottomRowClass F g = bottomRowClass F h ↔
        ∃ γ : SL(2,𝓞 F),
          Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
            Quotient.mk (QuotientGroup.rightRel (borelSL F)) (h * toSLF F γ) := by
  exact ⟨exists_cusp_reps_bijective Γ,
    bottomRowFractionalIdeal_ne_zero,
    bottomRowClass_surjective,
    bottomRowClass_eq_iff_integral_orbit⟩

/-- A finite-index unit subgroup still translates every positive height vector into a bounded
logarithmic balance region. The bound depends only on the subgroup and the field. -/
theorem spec_unit_balance (E : Subgroup ((𝓞 F)ˣ)) [E.FiniteIndex] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ E ∧ ∀ w,
        |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
  classical
  let w₀ : InfinitePlace F := dirichletUnitTheorem.w₀
  let b : Basis (Fin (Units.rank F)) ℝ (dirichletUnitTheorem.logSpace F) :=
    (Units.basisUnitLattice F).ofZLatticeBasis ℝ (Units.unitLattice F)
  let C : ℝ := ∑ i, ‖b i‖
  let n : ℕ := E.index
  let r : ℝ := placeCount F
  have hr : 0 < r := by
    dsimp [r, placeCount]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace F))
  have hn0 : n ≠ 0 := by
    dsimp [n]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨r * n * C, mul_nonneg (mul_nonneg hr.le (Nat.cast_nonneg _)) hC, ?_⟩
  intro t ht
  let m : ℝ := r⁻¹ * ∑ w : InfinitePlace F, Real.log (t w)
  let x : dirichletUnitTheorem.logSpace F := fun w => -2 * (Real.log (t w.val) - m)
  let q : dirichletUnitTheorem.logSpace F := (n : ℝ)⁻¹ • x
  let l : dirichletUnitTheorem.logSpace F := (ZSpan.floor b q : dirichletUnitTheorem.logSpace F)
  let p : dirichletUnitTheorem.logSpace F := ZSpan.fract b q
  have hp : ‖p‖ ≤ C := by
    dsimp [p, C]
    exact ZSpan.norm_fract_le b q
  have hcoord (w : {w : InfinitePlace F // w ≠ w₀}) : |p w| ≤ C := by
    have hc : ‖p w‖ ≤ ‖p‖ := by
      rw [Pi.norm_def]
      have hs : ‖p w‖₊ ≤ Finset.univ.sup (fun b : {w : InfinitePlace F // w ≠ w₀} => ‖p b‖₊) :=
        Finset.le_sup (f := fun b : {w : InfinitePlace F // w ≠ w₀} => ‖p b‖₊)
          (Finset.mem_univ w)
      exact NNReal.coe_le_coe.mpr hs
    rw [← Real.norm_eq_abs]
    exact hc.trans hp
  have hlattice : (l : dirichletUnitTheorem.logSpace F) ∈ Units.unitLattice F := by
    have hspan : l ∈ Submodule.span ℤ (Set.range b) := by
      dsimp [l]
      exact (ZSpan.floor b q).property
    have heq : Submodule.span ℤ (Set.range b) = Units.unitLattice F :=
      Module.Basis.ofZLatticeBasis_span ℝ (Units.unitLattice F)
        (Units.basisUnitLattice F)
    exact heq ▸ hspan
  change l ∈
      Submodule.map (logEmbedding F).toIntLinearMap ⊤ at hlattice
  obtain ⟨z, hz, hzl⟩ := Submodule.mem_map.mp hlattice
  let η : (𝓞 F)ˣ := z.toMul
  have hη : logEmbedding F (Additive.ofMul η) = l := by
    simpa [η] using hzl
  let ε : (𝓞 F)ˣ := η ^ n
  have hεE : ε ∈ E := by
    dsimp [ε, η]
    exact E.pow_index_mem z.toMul
  have hεlog : logEmbedding F (Additive.ofMul ε) =
      n • l := by
    rw [show ε = η ^ n by rfl, ofMul_pow, map_nsmul, hη]
  have hcenter : ∑ w : InfinitePlace F, (Real.log (t w) - m) = 0 := by
    dsimp [m, r, placeCount]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr (Fintype.card_pos.ne' :
      Fintype.card (InfinitePlace F) ≠ 0)]
    ring
  have hunit : ∑ w : InfinitePlace F,
      Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 0 := by
    have hu := Units.sum_mult_mul_log ε
    have hu' : ∑ w : InfinitePlace F,
        2 * Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ = 0 := by
      simpa [IsTotallyComplex.mult_eq, ← InfinitePlace.norm_embedding_eq] using hu
    have hsum := hu'
    rw [← Finset.mul_sum] at hsum
    nlinarith
  let d : InfinitePlace F → ℝ := fun w =>
      Real.log ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ + Real.log (t w) - m
  have hdsum : ∑ w : InfinitePlace F, d w = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hunit]
    have hc : (∑ w : InfinitePlace F, Real.log (t w)) -
        (∑ w : InfinitePlace F, m) = 0 := by
      simpa only [Finset.sum_sub_distrib] using hcenter
    linarith [hc]
  have hretained (w : {w : InfinitePlace F // w ≠ w₀}) : |d w.val| ≤ (n : ℝ) * C := by
    have hlog : 2 * Real.log
        ‖w.val.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ =
          (n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w := by
      simpa [logEmbedding_component, IsTotallyComplex.mult_eq,
        InfinitePlace.norm_embedding_eq, Pi.smul_apply, smul_eq_mul, l]
        using congrFun hεlog w
    have hqcoord : q w = (n : ℝ)⁻¹ * x w := by simp [q, Pi.smul_apply]
    have hfract : p w = q w - (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w := by
      simp [p, ZSpan.fract_apply]
    have hxmul : (n : ℝ) * q w = x w := by
      rw [hqcoord]
      field_simp [hn.ne']
    have hldiff : (n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w - x w =
        -(n : ℝ) * p w := by
      rw [← hxmul, hfract]
      ring
    have hvalue : d w.val =
        ((n : ℝ) * (ZSpan.floor b q : dirichletUnitTheorem.logSpace F) w - x w) / 2 := by
      dsimp [d, x]
      rw [← hlog]
      ring
    calc
      |d w.val| = |-(n : ℝ) * p w / 2| := by rw [hvalue, hldiff]
      _ = (n : ℝ) * |p w| / 2 := by
        rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
        norm_num
      _ ≤ (n : ℝ) * C / 2 := by
        gcongr
        exact hcoord w
      _ ≤ (n : ℝ) * C := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hC]
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne d w₀
  have hw₀ : d w₀ = -∑ w : {w : InfinitePlace F // w ≠ w₀}, d w.val := by
    have h := hdsum
    rw [hsplit] at h
    linarith
  have hdrop : |d w₀| ≤ r * (n : ℝ) * C := by
    rw [hw₀, abs_neg]
    calc
      |∑ w : {w : InfinitePlace F // w ≠ w₀}, d w.val| ≤
          ∑ w : {w : InfinitePlace F // w ≠ w₀}, |d w.val| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w : {w : InfinitePlace F // w ≠ w₀}, (n : ℝ) * C :=
          Finset.sum_le_sum fun w hw => hretained w
      _ = (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) * ((n : ℝ) * C) := by simp
      _ ≤ r * (n : ℝ) * C := by
          have hcard : Fintype.card {w : InfinitePlace F // w ≠ w₀} ≤
              Fintype.card (InfinitePlace F) := Fintype.card_subtype_le _
          have hreal : (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) ≤ r := by
            dsimp [r, placeCount]
            exact_mod_cast hcard
          calc
            (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) * ((n : ℝ) * C) ≤
                r * ((n : ℝ) * C) := mul_le_mul_of_nonneg_right hreal
                  (mul_nonneg (Nat.cast_nonneg n) hC)
            _ = r * (n : ℝ) * C := by ring
  have hr1 : 1 ≤ r := by
    dsimp [r, placeCount]
    have hc : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    exact_mod_cast (show 1 ≤ Fintype.card (InfinitePlace F) by omega)
  have hnormpos (w : InfinitePlace F) :
      0 < ‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ := by
    apply norm_pos_iff.mpr
    have hO : (ε : 𝓞 F) ≠ 0 := Units.ne_zero ε
    have hF : algebraMap (𝓞 F) F (ε : 𝓞 F) ≠ 0 :=
      (map_ne_zero_iff (algebraMap (𝓞 F) F)
        (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hO
    exact (map_ne_zero_iff w.embedding w.embedding.injective).mpr hF
  have htarget (w : InfinitePlace F) :
      Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
        (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w') = d w := by
    rw [Real.log_mul (hnormpos w).ne' (ht w).ne']
  refine ⟨ε, hεE, ?_⟩
  intro w
  by_cases hw : w = w₀
  · subst w
    rw [htarget]
    exact hdrop
  · have hd := hretained ⟨w, hw⟩
    have hbound : (n : ℝ) * C ≤ r * (n : ℝ) * C := by
      have hnc : 0 ≤ (n : ℝ) * C := mul_nonneg (Nat.cast_nonneg n) hC
      nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hnc]
    rw [htarget]
    exact hd.trans hbound


/-- R4 `spec:unit-balance` — P-SPEC.md:217, 290–293. Every positive height vector can be moved
by a finite-index unit subgroup into a uniformly bounded logarithmic balance region. -/
theorem R4_unit_balance (E : Subgroup ((𝓞 F)ˣ)) [E.FiniteIndex] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ E ∧ ∀ w,
        |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
  exact spec_unit_balance E

private abbrev specMixedSpace (F : Type) [Field F] [NumberField F] :=
  NumberField.mixedEmbedding.mixedSpace F

private abbrev specIntegerLattice (F : Type) [Field F] [NumberField F] :=
  NumberField.mixedEmbedding.integerLattice F

private noncomputable def specIntegerBasis (F : Type) [Field F] [NumberField F] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ (specMixedSpace F) :=
  NumberField.mixedEmbedding.latticeBasis F

private noncomputable def specRowLatticeBasis (F : Type) [Field F] [NumberField F] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 F) ⊕ Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ
      (specMixedSpace F × specMixedSpace F) :=
  (specIntegerBasis F).prod (specIntegerBasis F)

private noncomputable def specRowLattice (F : Type) [Field F] [NumberField F] :
    Submodule ℤ (specMixedSpace F × specMixedSpace F) :=
  Submodule.span ℤ (Set.range (specRowLatticeBasis F))

private theorem spec_mixed_integer_mem (a : 𝓞 F) :
    NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) ∈ specIntegerLattice F := by
  change NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) ∈
    LinearMap.range ((NumberField.mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  exact LinearMap.mem_range.mpr ⟨a, rfl⟩

private theorem spec_rowLattice_mem (x y : specMixedSpace F)
    (hx : x ∈ specIntegerLattice F) (hy : y ∈ specIntegerLattice F) :
    (x, y) ∈ specRowLattice F := by
  classical
  let b := specIntegerBasis F
  have hbspan : Submodule.span ℤ (Set.range b) = specIntegerLattice F :=
    NumberField.mixedEmbedding.span_latticeBasis F
  have hxspan : x ∈ Submodule.span ℤ (Set.range b) := by
    rw [hbspan]
    exact hx
  have hyspan : y ∈ Submodule.span ℤ (Set.range b) := by
    rw [hbspan]
    exact hy
  change (x, y) ∈ Submodule.span ℤ (Set.range (b.prod b))
  rw [(b.prod b).mem_span_iff_repr_mem ℤ]
  intro i
  cases i with
  | inl i =>
      simpa only [Module.Basis.prod_repr_inl] using
        (b.mem_span_iff_repr_mem ℤ x).mp hxspan i
  | inr i =>
      simpa only [Module.Basis.prod_repr_inr] using
        (b.mem_span_iff_repr_mem ℤ y).mp hyspan i

private theorem spec_mixed_norm_le
    [Fintype {w : InfinitePlace F // NumberField.InfinitePlace.IsReal w}]
    [Fintype {w : InfinitePlace F // NumberField.InfinitePlace.IsComplex w}]
    (a : F) (S : ℝ) (hS : 0 ≤ S)
    (hcoord : ∀ w : InfinitePlace F, ‖w.embedding a‖ ≤ S) :
    ‖NumberField.mixedEmbedding F a‖ ≤ S := by
  classical
  letI : IsEmpty {w : InfinitePlace F // NumberField.InfinitePlace.IsReal w} :=
    ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex).2
      (IsTotallyComplex.isComplex w.1) w.2⟩
  have hreal : (NumberField.mixedEmbedding F a).1 = 0 := by
    funext w
    exact isEmptyElim w
  have hcomplex : ‖(NumberField.mixedEmbedding F a).2‖ ≤ S := by
    rw [Pi.norm_def]
    have hsup : Finset.univ.sup (fun w : {w : InfinitePlace F // NumberField.InfinitePlace.IsComplex w} =>
        ‖(NumberField.mixedEmbedding F a).2 w‖₊) ≤ ⟨S, hS⟩ := by
      apply Finset.sup_le
      intro w hw
      exact_mod_cast hcoord w.1
    exact NNReal.coe_le_coe.mpr hsup
  rw [Prod.norm_def, hreal, norm_zero]
  exact max_le_iff.mpr ⟨hS, hcomplex⟩

private theorem spec_rowNorm_pos (v : F × F) (hv : v ≠ (0, 0))
    (w : InfinitePlace F) : 0 < rowNorm F v w := by
  have hentry : w.embedding v.1 ≠ 0 ∨ w.embedding v.2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    exact Prod.ext (w.embedding.injective (by simpa using h.1))
      (w.embedding.injective (by simpa using h.2))
  unfold rowNorm
  rw [Real.sqrt_pos]
  rcases hentry with h | h
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr h) (Complex.normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.mpr h)

private theorem spec_rowEntry_le_rowNorm (v : F × F) (w : InfinitePlace F) :
    ‖w.embedding v.1‖ ≤ rowNorm F v w := by
  unfold rowNorm
  calc
    ‖w.embedding v.1‖ = Real.sqrt (Complex.normSq (w.embedding v.1)) := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (Complex.normSq (w.embedding v.1) + Complex.normSq (w.embedding v.2)) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (Complex.normSq_nonneg _))

private theorem spec_rowEntry2_le_rowNorm (v : F × F) (w : InfinitePlace F) :
    ‖w.embedding v.2‖ ≤ rowNorm F v w := by
  unfold rowNorm
  calc
    ‖w.embedding v.2‖ = Real.sqrt (Complex.normSq (w.embedding v.2)) := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (Complex.normSq (w.embedding v.1) + Complex.normSq (w.embedding v.2)) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_left (Complex.normSq_nonneg _))

private theorem spec_rpow_compare (r α K P N : ℝ) (hr : 0 < r) (hα : 0 < α)
    (hK : 0 < K) (hP : 0 < P) (hN : 0 < N)
    (hNbound : N ≤ K * P ^ r⁻¹) :
    P ^ (-α) ≤ K ^ (r * α) * N ^ (-(r * α)) := by
  have hq : 0 < r * α := mul_pos hr hα
  have hexp : r⁻¹ * (r * α) = α := by field_simp [hr.ne']
  have hpow : N ^ (r * α) ≤ K ^ (r * α) * P ^ α := by
    calc
      N ^ (r * α) ≤ (K * P ^ r⁻¹) ^ (r * α) :=
        Real.rpow_le_rpow (le_of_lt hN) hNbound hq.le
      _ = K ^ (r * α) * (P ^ r⁻¹) ^ (r * α) := by
        rw [Real.mul_rpow (le_of_lt hK) (Real.rpow_nonneg (le_of_lt hP) _)]
      _ = K ^ (r * α) * P ^ α := by
        rw [← Real.rpow_mul (le_of_lt hP) (r⁻¹) (r * α), hexp]
  have hdiv : 1 / P ^ α ≤ K ^ (r * α) / N ^ (r * α) :=
    (div_le_div_iff₀ (Real.rpow_pos_of_pos hP α) (Real.rpow_pos_of_pos hN (r * α))).2
      (by simpa using hpow)
  calc
    P ^ (-α) = 1 / P ^ α := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.inv_rpow hP.le]
      simp
    _ ≤ K ^ (r * α) / N ^ (r * α) := hdiv
    _ = K ^ (r * α) * N ^ (-(r * α)) := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.inv_rpow hN.le]
      simp [div_eq_mul_inv]

private theorem spec_denominator_bound_unit (D : ℕ) {a : F}
    (ha : HasDenominatorBound F D a) (ε : (𝓞 F)ˣ) :
    HasDenominatorBound F D (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) := by
  rcases ha with ⟨b, hb⟩
  refine ⟨(ε : 𝓞 F) * b, ?_⟩
  change (D : F) * (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) =
    algebraMap (𝓞 F) F ((ε : 𝓞 F) * b)
  calc
    (D : F) * (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) =
        algebraMap (𝓞 F) F (ε : 𝓞 F) * ((D : F) * a) := by ring
    _ = algebraMap (𝓞 F) F (ε : 𝓞 F) * algebraMap (𝓞 F) F b := by rw [hb]
    _ = algebraMap (𝓞 F) F ((ε : 𝓞 F) * b) := by rw [map_mul]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- R5 `spec:lattice-sums` — P-SPEC.md:218, 295–298. Rows in a fixed denominator multiple of
`O_F²`, with no two representatives in the same unit orbit, have the stated summable norm weight. -/
theorem R5_lattice_sums (D : ℕ) (hD : 0 < D) (α : ℝ) (hα : 4 < α)
    {ι : Type*} (v : ι → F × F)
    (hvD : ∀ i, HasDenominatorBound F D (v i).1 ∧ HasDenominatorBound F D (v i).2)
    (hv0 : ∀ i, v i ≠ (0, 0))
    (huniq : ∀ i j, (∃ ε : (𝓞 F)ˣ,
      v i = ((algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v j).1,
        (algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v j).2)) → i = j) :
    Summable (fun i => ∏ w : InfinitePlace F, (rowNorm F (v i) w) ^ (-α)) := by
  classical
  let r : ℝ := placeCount F
  have hr : 0 < r := by
    dsimp [r, placeCount]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace F))
  have hαpos : 0 < α := by linarith
  let Etop : Subgroup ((𝓞 F)ˣ) := ⊤
  letI : Etop.FiniteIndex := ⟨by dsimp [Etop]; simp⟩
  obtain ⟨B, hB, hbal⟩ := R4_unit_balance Etop
  let t : ι → InfinitePlace F → ℝ := fun i w => rowNorm F (v i) w
  have ht (i : ι) (w : InfinitePlace F) : 0 < t i w := by
    exact spec_rowNorm_pos (v i) (hv0 i) w
  let ε : ι → (𝓞 F)ˣ := fun i => Classical.choose (hbal (t i) (ht i))
  have hεbal (i : ι) (w : InfinitePlace F) :=
    (Classical.choose_spec (hbal (t i) (ht i))).2 w
  let e : ι → F := fun i => algebraMap (𝓞 F) F (ε i : 𝓞 F)
  let u : ι → F × F := fun i => (e i * (v i).1, e i * (v i).2)
  let P : ι → ℝ := fun i => ∏ w : InfinitePlace F, t i w
  have hPpos (i : ι) : 0 < P i := by
    dsimp [P]
    exact Finset.prod_pos fun w hw => ht i w
  have hPlog (i : ι) : Real.log (P i) = ∑ w : InfinitePlace F, Real.log (t i w) := by
    simpa [P] using
      (Real.log_prod (s := Finset.univ) (f := fun w : InfinitePlace F => t i w)
        (fun w hw => (ht i w).ne'))
  have hmean (i : ι) : Real.exp (r⁻¹ * Real.log (P i)) = P i ^ r⁻¹ := by
    rw [mul_comm]
    exact (Real.rpow_def_of_pos (hPpos i) r⁻¹).symm
  have heNZ (i : ι) : e i ≠ 0 := by
    dsimp [e]
    exact (map_ne_zero_iff (algebraMap (𝓞 F) F)
      (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (Units.ne_zero (ε i))
  have hnormε (i : ι) (w : InfinitePlace F) : 0 < ‖w.embedding (e i)‖ := by
    apply norm_pos_iff.mpr
    exact (map_ne_zero_iff w.embedding w.embedding.injective).mpr (heNZ i)
  have hbalancedUpper (i : ι) (w : InfinitePlace F) :
      ‖w.embedding (e i)‖ * t i w ≤ Real.exp B * P i ^ r⁻¹ := by
    have hlog := (abs_le.mp (hεbal i w)).2
    change Real.log (‖w.embedding (e i)‖ * t i w) - r⁻¹ *
      (∑ w' : InfinitePlace F, Real.log (t i w')) ≤ B at hlog
    rw [← hPlog i] at hlog
    have hlog' : Real.log (‖w.embedding (e i)‖ * t i w) ≤
        r⁻¹ * Real.log (P i) + B := by linarith
    calc
      ‖w.embedding (e i)‖ * t i w ≤
          Real.exp (r⁻¹ * Real.log (P i) + B) :=
        (Real.log_le_iff_le_exp (mul_pos (hnormε i w) (ht i w))).mp hlog'
      _ = Real.exp B * P i ^ r⁻¹ := by
        rw [Real.exp_add, hmean i]
        ring
  have hentry1 (i : ι) (w : InfinitePlace F) :
      ‖w.embedding (u i).1‖ ≤ Real.exp B * P i ^ r⁻¹ := by
    dsimp [u]
    rw [map_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_left (spec_rowEntry_le_rowNorm (v i) w)
      (norm_nonneg _)).trans (hbalancedUpper i w)
  have hentry2 (i : ι) (w : InfinitePlace F) :
      ‖w.embedding (u i).2‖ ≤ Real.exp B * P i ^ r⁻¹ := by
    dsimp [u]
    rw [map_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_left (spec_rowEntry2_le_rowNorm (v i) w)
      (norm_nonneg _)).trans (hbalancedUpper i w)
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDfield : (D : F) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hnormD (w : InfinitePlace F) : ‖w.embedding (D : F)‖ = (D : ℝ) := by
    simp
  have hDentry1 (i : ι) (w : InfinitePlace F) :
      ‖w.embedding ((D : F) * (u i).1)‖ ≤ (D : ℝ) * (Real.exp B * P i ^ r⁻¹) := by
    rw [map_mul, norm_mul, hnormD]
    exact mul_le_mul_of_nonneg_left (hentry1 i w) hDreal.le
  have hDentry2 (i : ι) (w : InfinitePlace F) :
      ‖w.embedding ((D : F) * (u i).2)‖ ≤ (D : ℝ) * (Real.exp B * P i ^ r⁻¹) := by
    rw [map_mul, norm_mul, hnormD]
    exact mul_le_mul_of_nonneg_left (hentry2 i w) hDreal.le
  let K : ℝ := (D : ℝ) * Real.exp B
  have hK : 0 < K := mul_pos hDreal (Real.exp_pos B)
  let point : ι → specMixedSpace F × specMixedSpace F := fun i =>
    (NumberField.mixedEmbedding F ((D : F) * (u i).1),
      NumberField.mixedEmbedding F ((D : F) * (u i).2))
  have hpointNorm (i : ι) : ‖point i‖ ≤ K * P i ^ r⁻¹ := by
    dsimp [point]
    change max (‖NumberField.mixedEmbedding F ((D : F) * (u i).1)‖)
      (‖NumberField.mixedEmbedding F ((D : F) * (u i).2)‖) ≤ K * P i ^ r⁻¹
    have hS : 0 ≤ (D : ℝ) * (Real.exp B * P i ^ r⁻¹) :=
      mul_nonneg hDreal.le (mul_nonneg (Real.exp_nonneg B)
        (Real.rpow_nonneg (hPpos i).le _))
    have h1 := spec_mixed_norm_le ((D : F) * (u i).1)
      ((D : ℝ) * (Real.exp B * P i ^ r⁻¹)) hS (hDentry1 i)
    have h2 := spec_mixed_norm_le ((D : F) * (u i).2)
      ((D : ℝ) * (Real.exp B * P i ^ r⁻¹)) hS (hDentry2 i)
    apply max_le_iff.mpr
    constructor
    · simpa [K, mul_assoc, mul_left_comm, mul_comm] using h1
    · simpa [K, mul_assoc, mul_left_comm, mul_comm] using h2
  have hden1 (i : ι) : HasDenominatorBound F D (u i).1 := by
    simpa [u, e] using spec_denominator_bound_unit D (hvD i).1 (ε i)
  have hden2 (i : ι) : HasDenominatorBound F D (u i).2 := by
    simpa [u, e] using spec_denominator_bound_unit D (hvD i).2 (ε i)
  have hpointMem (i : ι) : point i ∈ specRowLattice F := by
    apply spec_rowLattice_mem
    · obtain ⟨a, ha⟩ := hden1 i
      change NumberField.mixedEmbedding F ((D : F) * (u i).1) ∈ specIntegerLattice F
      rw [ha]
      exact spec_mixed_integer_mem a
    · obtain ⟨a, ha⟩ := hden2 i
      change NumberField.mixedEmbedding F ((D : F) * (u i).2) ∈ specIntegerLattice F
      rw [ha]
      exact spec_mixed_integer_mem a
  let latticePoint : ι → specRowLattice F := fun i => ⟨point i, hpointMem i⟩
  have hεmap (i j : ι) :
      algebraMap (𝓞 F) F (((ε i)⁻¹ * ε j : (𝓞 F)ˣ) : 𝓞 F) = (e i)⁻¹ * e j := by
    simp [e, map_mul, map_inv₀]
  have horbit (i j : ι) (hpoint : point i = point j) : ∃ η : (𝓞 F)ˣ,
      v i = (algebraMap (𝓞 F) F (η : 𝓞 F) * (v j).1,
        algebraMap (𝓞 F) F (η : 𝓞 F) * (v j).2) := by
    have hu1scaled : (D : F) * (u i).1 = (D : F) * (u j).1 :=
      NumberField.mixedEmbedding_injective F (congrArg Prod.fst hpoint)
    have hu2scaled : (D : F) * (u i).2 = (D : F) * (u j).2 :=
      NumberField.mixedEmbedding_injective F (congrArg Prod.snd hpoint)
    have hu1 : (u i).1 = (u j).1 := mul_left_cancel₀ hDfield hu1scaled
    have hu2 : (u i).2 = (u j).2 := mul_left_cancel₀ hDfield hu2scaled
    refine ⟨(ε i)⁻¹ * ε j, ?_⟩
    apply Prod.ext
    · calc
        (v i).1 = (e i)⁻¹ * (e i * (v i).1) := by simp [heNZ i]
        _ = (e i)⁻¹ * (u i).1 := rfl
        _ = (e i)⁻¹ * (u j).1 := by rw [hu1]
        _ = ((e i)⁻¹ * e j) * (v j).1 := by ring
        _ = algebraMap (𝓞 F) F (((ε i)⁻¹ * ε j : (𝓞 F)ˣ) : 𝓞 F) * (v j).1 := by
          rw [← hεmap i j]
    · calc
        (v i).2 = (e i)⁻¹ * (e i * (v i).2) := by simp [heNZ i]
        _ = (e i)⁻¹ * (u i).2 := rfl
        _ = (e i)⁻¹ * (u j).2 := by rw [hu2]
        _ = ((e i)⁻¹ * e j) * (v j).2 := by ring
        _ = algebraMap (𝓞 F) F (((ε i)⁻¹ * ε j : (𝓞 F)ˣ) : 𝓞 F) * (v j).2 := by
          rw [← hεmap i j]
  have hinj : Function.Injective latticePoint := by
    intro i j hij
    apply huniq i j
    exact horbit i j (congrArg Subtype.val hij)
  have hpointNZ (i : ι) : point i ≠ (0, 0) := by
    intro h
    have h1 : NumberField.mixedEmbedding F ((D : F) * (u i).1) = 0 := by
      simpa [point] using congrArg Prod.fst h
    have h2 : NumberField.mixedEmbedding F ((D : F) * (u i).2) = 0 := by
      simpa [point] using congrArg Prod.snd h
    have h1' : NumberField.mixedEmbedding F ((D : F) * (u i).1) =
        NumberField.mixedEmbedding F (0 : F) := by simpa using h1
    have h2' : NumberField.mixedEmbedding F ((D : F) * (u i).2) =
        NumberField.mixedEmbedding F (0 : F) := by simpa using h2
    have hu1 : (u i).1 = 0 :=
      (mul_eq_zero.mp ((NumberField.mixedEmbedding_injective F) h1')).resolve_left hDfield
    have hu2 : (u i).2 = 0 :=
      (mul_eq_zero.mp ((NumberField.mixedEmbedding_injective F) h2')).resolve_left hDfield
    have hv1 : (v i).1 = 0 := (mul_eq_zero.mp (by simpa [u, e] using hu1)).resolve_left (heNZ i)
    have hv2 : (v i).2 = 0 := (mul_eq_zero.mp (by simpa [u, e] using hu2)).resolve_left (heNZ i)
    exact hv0 i (Prod.ext hv1 hv2)
  have hpointNormPos (i : ι) : 0 < ‖point i‖ := by
    apply norm_pos_iff.mpr
    exact hpointNZ i
  have hnormpos (i : ι) : 0 < ‖(latticePoint i : specMixedSpace F × specMixedSpace F)‖ := by
    simpa [latticePoint] using hpointNormPos i
  have hnormbound (i : ι) :
      ‖(latticePoint i : specMixedSpace F × specMixedSpace F)‖ ≤ K * P i ^ r⁻¹ := by
    simpa [latticePoint] using hpointNorm i
  letI : Finite (Free.ChooseBasisIndex ℤ (𝓞 F)) :=
    Module.Finite.finite_basis (Module.Free.chooseBasis ℤ (𝓞 F))
  letI : Finite (Free.ChooseBasisIndex ℤ (𝓞 F) ⊕ Free.ChooseBasisIndex ℤ (𝓞 F)) := inferInstance
  letI : DiscreteTopology (specRowLattice F) := by
    change DiscreteTopology (Submodule.span ℤ (Set.range (specRowLatticeBasis F)))
    infer_instance
  letI : IsZLattice ℝ (specRowLattice F) := ⟨by
      change Submodule.span ℝ
        (Submodule.span ℤ (Set.range (specRowLatticeBasis F)) :
          Set (specMixedSpace F × specMixedSpace F)) = ⊤
      exact ZSpan.span_top (specRowLatticeBasis F)⟩
  have hrowLatticeRank :
      Module.finrank ℤ (specRowLattice F) = 4 * Fintype.card (InfinitePlace F) := by
    rw [ZLattice.rank ℝ (specRowLattice F), finrank_prod,
      NumberField.mixedEmbedding.finrank,
      NumberField.IsTotallyComplex.finrank,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  have hrank :
      - (r * α) < -(Module.finrank ℤ (specRowLattice F) : ℝ) := by
    have hrankR : (Module.finrank ℤ (specRowLattice F) : ℝ) = 4 * r := by
      rw [hrowLatticeRank]
      dsimp [r, placeCount]
      norm_num
    rw [hrankR]
    nlinarith
  have hlat : Summable (fun z : specRowLattice F => ‖z‖ ^ (-(r * α))) :=
    ZLattice.summable_norm_rpow (specRowLattice F) (-(r * α)) hrank
  let fLat : specRowLattice F → ℝ≥0 := fun z => ‖z‖₊ ^ (-(r * α))
  have hlatNN : Summable fLat := by
    apply NNReal.summable_coe.mp
    simpa [fLat, NNReal.coe_rpow, coe_nnnorm] using hlat
  have hcompNN := NNReal.summable_comp_injective hlatNN hinj
  let kLat : ℝ≥0 := ⟨K ^ (r * α), by positivity⟩
  have hmajorNN : Summable (fun i => kLat * fLat (latticePoint i)) :=
    hcompNN.mul_left kLat
  have hweight (i : ι) :
      ∏ w : InfinitePlace F, (rowNorm F (v i) w) ^ (-α) = P i ^ (-α) := by
    simpa [P, t] using
      (Real.finsetProd_rpow Finset.univ (fun w : InfinitePlace F => rowNorm F (v i) w)
        (fun w hw => (spec_rowNorm_pos (v i) (hv0 i) w).le) (-α))
  have hcompare (i : ι) :
      ∏ w : InfinitePlace F, (rowNorm F (v i) w) ^ (-α) ≤
        K ^ (r * α) * ‖(latticePoint i : specMixedSpace F × specMixedSpace F)‖ ^ (-(r * α)) := by
    rw [hweight i]
    exact spec_rpow_compare r α K (P i)
      ‖(latticePoint i : specMixedSpace F × specMixedSpace F)‖ hr hαpos hK
      (hPpos i) (hnormpos i) (hnormbound i)
  let targetReal : ι → ℝ := fun i =>
    ∏ w : InfinitePlace F, (rowNorm F (v i) w) ^ (-α)
  have targetNonneg (i : ι) : 0 ≤ targetReal i := by
    dsimp [targetReal]
    exact Finset.prod_nonneg fun w hw =>
      Real.rpow_nonneg (spec_rowNorm_pos (v i) (hv0 i) w).le _
  let targetNN : ι → ℝ≥0 := fun i => ⟨targetReal i, targetNonneg i⟩
  have hcompareNN (i : ι) : targetNN i ≤ kLat * fLat (latticePoint i) := by
    have htargetCoe : (targetNN i : ℝ) = targetReal i := rfl
    have hkLat : (kLat : ℝ) = K ^ (r * α) := rfl
    have hfLat : (fLat (latticePoint i) : ℝ) =
        ‖(latticePoint i : specMixedSpace F × specMixedSpace F)‖ ^ (-(r * α)) := by
      simp [fLat, NNReal.coe_rpow, coe_nnnorm, Submodule.coe_norm]
    have hmajorCoe : ((kLat * fLat (latticePoint i) : ℝ≥0) : ℝ) =
        K ^ (r * α) * ‖(latticePoint i : specMixedSpace F × specMixedSpace F)‖ ^
          (-(r * α)) := by
      rw [NNReal.coe_mul, hkLat, hfLat]
    apply NNReal.coe_le_coe.mp
    rw [htargetCoe, hmajorCoe]
    exact hcompare i
  have htargetNN : Summable targetNN := NNReal.summable_of_le hcompareNN hmajorNN
  have htargetReal : Summable targetReal :=
    (NNReal.summable_mk (f := targetReal) targetNonneg).mp htargetNN
  simpa [targetReal] using htargetReal

/-- R6 `spec:two-heights` — P-SPEC.md:219, 300. A nonzero lower-left entry bounds the product
of the two heights, and denominator bounds make this uniform over the arithmetic subgroup. -/
theorem R6_two_heights (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∀ g : SL(2,F), ∀ z : X F, g 1 0 ≠ 0 →
      normHeight F z * normHeight F (g • z) ≤ (absFieldNorm F (g 1 0))⁻¹) ∧
    (∀ σ σ' : SL(2,F),
      ∃ C : ℝ, 0 < C ∧ ∀ γ : Γ, ∀ z : X F,
        (σ'⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) 1 0 ≠ 0 →
          normHeight F (σ⁻¹ • z) *
            normHeight F (σ'⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ C) := by
  sorry

/-- R7 `spec:minkowski` — P-SPEC.md:220, 302–306. A uniform Minkowski bound for a nonzero
integral row in the height-dependent positive Hermitian forms. -/
theorem R7_minkowski :
    ∃ C_M : ℝ, 0 < C_M ∧ ∀ z : X F, ∃ v : 𝓞 F × 𝓞 F,
      v ≠ (0, 0) ∧
        ∏ w : InfinitePlace F,
          rowHeightForm F
            (algebraMap (𝓞 F) F v.1, algebraMap (𝓞 F) F v.2) z w ≤ C_M := by
  sorry

/-- R11 `spec:free-level` — P-SPEC.md:224, 330–336. A nonzero principal congruence subgroup
acts freely on the product hyperbolic space. -/
theorem R11_free_level :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ FreeAction F (congrSubgroup F N) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
