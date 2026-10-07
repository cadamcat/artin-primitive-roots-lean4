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
open scoped MatrixGroups ContDiff BoundedContinuousFunction NNReal

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
  sorry

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
