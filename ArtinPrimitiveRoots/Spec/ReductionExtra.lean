import ArtinPrimitiveRoots.Spec.Stage1
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_CALIBRATE.R8
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.siegel_low_height_overlap_finite
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.siegel_high_height_overlap_finite
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.free_action_wandering_nbhd
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.local_finite_overlap

/-! Remaining reduction-theory nodes R8--R10 and R12--R14. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- R8 `spec:siegel-cover` — P-SPEC.md:221, 308–313. The Siegel sets with the R1 translation
domains, R4 balance constants, and R7 Minkowski scale cover every point modulo `Γ`. Correction
from review lane `rev-spec`: use the Siegel sets with the doubled balance bound. Correction from
`sol-gate-spec`: calibrate the Minkowski scale and require pointwise translation coverage. -/
theorem R8_siegel_cover (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    ∀ z : X F, ∃ i : d.ι, ∃ γ : Γ,
      (d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z) ∈ SiegelData.setAt F d i := by
  exact r8_siegel_cover_helper Γ d

/-- R9 `spec:proper` — P-SPEC.md:222, 315–324. Arithmetic compact intersections and Siegel-set
intersections are finite; freeness gives disjoint neighborhoods for nonidentity elements. -/
theorem R9_proper (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    (∀ K K' : Set (X F), IsCompact K → IsCompact K' →
      {γ : SL(2,𝓞 F) | ∃ z ∈ K, γ • z ∈ K'}.Finite) ∧
    {γ : Γ | ∃ z ∈ SiegelData.unionSet F d,
      (γ : SL(2,𝓞 F)) • z ∈ SiegelData.unionSet F d}.Finite ∧
    (∀ (hfree : FreeAction F Γ) (z : X F),
      ∃ U : Set (X F), IsOpen U ∧ z ∈ U ∧
        ∀ γ : Γ, γ ≠ 1 → Disjoint ((fun x => (γ : SL(2,𝓞 F)) • x) '' U) U) := by
  classical
  obtain ⟨A, hA, hhigh⟩ := siegel_high_height_overlap_finite Γ d
  have hlow := siegel_low_height_overlap_finite Γ d A hA
  refine ⟨fun K K' hK hK' => compact_overlap_finite_SL2O K K' hK hK', ?_,
    fun hfree z => free_action_wandering_nbhd Γ hfree z⟩
  apply (hlow.union hhigh).subset
  rintro γ ⟨z, ⟨i, x, hx, hix⟩, j, y, hy, hjy⟩
  have htransition : siegelOverlapTransition Γ d i j γ x = y := by
    unfold siegelOverlapTransition
    rw [hix, ← hjy]
    exact inv_smul_smul (d.σ j) y
  by_cases hsmall : normHeight F x ≤ A ∧
      normHeight F (siegelOverlapTransition Γ d i j γ x) ≤ A
  · exact Or.inl ⟨i, j, x, hx, htransition.symm ▸ hy, hsmall⟩
  · apply Or.inr
    refine ⟨i, j, x, hx, htransition.symm ▸ hy, ?_⟩
    exact (not_and_or.mp hsmall).imp lt_of_not_ge lt_of_not_ge

private lemma cuspStab_iff_borel_local (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F))
    (γ : Γ) :
    γ ∈ cuspStab F Γ σ ↔
      σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ ∈ borelSL F := by
  simp only [cuspStab, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

private lemma reps_map_cuspCoset_mk (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (i : d.ι) (γ : Γ) :
    (fun p : (Σ i, CuspCosets F Γ (d.σ i)) =>
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((d.σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F))))
        ⟨i, Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) γ⟩ =
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
        ((d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F))) := by
  let c : CuspCosets F Γ (d.σ i) :=
    Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) γ
  have hc : Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) c.out =
      Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) γ := by
    calc
      _ = c := Quotient.out_eq' c
      _ = Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) γ := rfl
  have hstab : γ * c.out⁻¹ ∈ cuspStab F Γ (d.σ i) :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hc)
  have hB : ((d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F))) *
      ((d.σ i)⁻¹ * toSLF F (c.out : SL(2,𝓞 F)))⁻¹ ∈ borelSL F := by
    have hconj := (cuspStab_iff_borel_local Γ (d.σ i) (γ * c.out⁻¹)).mp hstab
    simpa [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc] using hconj
  have hquot :
      Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ i)⁻¹ * toSLF F (c.out : SL(2,𝓞 F))) =
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) ) := by
    apply Quotient.sound
    exact QuotientGroup.rightRel_apply.mpr hB
  simpa [c] using hquot

/-- R10 `spec:cusp-separation` — P-SPEC.md:223, 326–328. Above a uniform height threshold,
large representatives at one cusp differ by its stabilizer; compact sets meet only finitely many
high-height cusp cosets. Correction from review lane `rev-spec`: require a common sufficiently
large threshold for each representative set. -/
theorem R10_cusp_separation (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∀ σ : SL(2,F), ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ γ γ' : Γ, ∀ z : X F,
        A ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
        A ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        γ' * γ⁻¹ ∈ cuspStab F Γ σ) ∧
    (∀ (d : SiegelData F Γ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
        A ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
        A ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
        i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i)) ∧
    (∀ σ : SL(2,F), ∀ K : Set (X F), IsCompact K → ∀ A : ℝ, 0 < A →
      {q : CuspCosets F Γ σ | ∃ z ∈ K,
        A ≤ normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))}.Finite) := by
  classical
  rcases R6_two_heights (F := F) Γ with ⟨_, hpair⟩
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    obtain ⟨C, hC, hbound⟩ := hpair σ σ
    let A₀ : ℝ := max 1 (Real.sqrt C + 1)
    refine ⟨A₀, le_max_left _ _, ?_⟩
    intro A hA γ γ' z hγ hγ'
    have hAroot : Real.sqrt C + 1 ≤ A := le_trans (le_max_right _ _) hA
    have hC_lt_A2 : C < A ^ 2 := by
      have hsqrt := Real.sq_sqrt hC.le
      nlinarith [Real.sqrt_nonneg C, sq_nonneg (Real.sqrt C)]
    have hzero :
        (σ⁻¹ * toSLF F ((γ' * γ⁻¹ : Γ) : SL(2,𝓞 F)) * σ) 1 0 = 0 := by
      by_contra hne
      have hb := hbound (γ' * γ⁻¹) ((γ : SL(2,𝓞 F)) • z) hne
      have hb' :
          normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) *
            normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) ≤ C := by
        simpa [map_mul, smul_smul, mul_assoc] using hb
      have hApos : 0 ≤ A := by linarith [Real.sqrt_nonneg C]
      have hfirstpos : 0 ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) :=
        le_trans hApos hγ
      have hsecondpos : 0 ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) :=
        le_trans hApos hγ'
      have hprod : A ^ 2 ≤
          normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) *
            normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) := by
        nlinarith [add_nonneg
          (mul_nonneg (sub_nonneg.mpr hγ) hsecondpos)
          (mul_nonneg hApos (sub_nonneg.mpr hγ'))]
      exact (not_lt_of_ge (le_trans hprod hb')) hC_lt_A2
    apply (cuspStab_iff_borel_local Γ σ (γ' * γ⁻¹)).mpr
    change σ⁻¹ * toSLF F ((γ' * γ⁻¹ : Γ) : SL(2,𝓞 F)) * σ ∈ borelSL F
    change (σ⁻¹ * toSLF F ((γ' * γ⁻¹ : Γ) : SL(2,𝓞 F)) * σ) 1 0 = 0
    exact hzero
  · intro d
    letI : Fintype d.ι := d.fintype
    let cfun : d.ι × d.ι → ℝ := fun ij => Classical.choose (hpair (d.σ ij.1) (d.σ ij.2))
    have hcpos (ij : d.ι × d.ι) : 0 < cfun ij :=
      (Classical.choose_spec (hpair (d.σ ij.1) (d.σ ij.2))).1
    have hcbound (ij : d.ι × d.ι) : ∀ γ : Γ, ∀ z : X F,
        ((d.σ ij.2)⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * (d.σ ij.1)) 1 0 ≠ 0 →
        normHeight F ((d.σ ij.1)⁻¹ • z) *
          normHeight F ((d.σ ij.2)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ cfun ij :=
      (Classical.choose_spec (hpair (d.σ ij.1) (d.σ ij.2))).2
    let S : ℝ := ∑ ij : d.ι × d.ι, cfun ij
    have hSnonneg : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun ij _ => (hcpos ij).le
    let A₀ : ℝ := max 1 (S + 1)
    refine ⟨A₀, le_max_left _ _, ?_⟩
    intro A hA i j γ γ' z hγ hγ'
    have hAlarge : S + 1 ≤ A := le_trans (le_max_right _ _) hA
    have hc_le_sum : cfun (i, j) ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum (fun ij _ => (hcpos ij).le) (Finset.mem_univ _)
    have hC_lt_A2 : cfun (i, j) < A ^ 2 := by
      have hAone : 1 ≤ A := le_trans (le_max_left _ _) hA
      have hCA : cfun (i, j) < A := by linarith
      nlinarith [sq_nonneg (A - 1)]
    have hzero :
        ((d.σ j)⁻¹ * toSLF F ((γ' * γ⁻¹ : Γ) : SL(2,𝓞 F)) * d.σ i) 1 0 = 0 := by
      by_contra hne
      have hb := hcbound (i, j) (γ' * γ⁻¹) ((γ : SL(2,𝓞 F)) • z) hne
      have hb' :
          normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) *
            normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) ≤ cfun (i, j) := by
        simpa [map_mul, smul_smul, mul_assoc] using hb
      have hApos : 0 ≤ A := by linarith [le_max_left (1 : ℝ) (S + 1), hA]
      have hfirstpos : 0 ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) :=
        le_trans hApos hγ
      have hsecondpos : 0 ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) :=
        le_trans hApos hγ'
      have hprod : A ^ 2 ≤
          normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) *
            normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) := by
        nlinarith [add_nonneg
          (mul_nonneg (sub_nonneg.mpr hγ) hsecondpos)
          (mul_nonneg hApos (sub_nonneg.mpr hγ'))]
      exact (not_lt_of_ge (le_trans hprod hb')) hC_lt_A2
    have htransition : (d.σ j)⁻¹ * toSLF F ((γ' * γ⁻¹ : Γ) : SL(2,𝓞 F)) * d.σ i ∈
        borelSL F := by
      change ((d.σ j)⁻¹ * toSLF F ((γ' * γ⁻¹ : Γ) : SL(2,𝓞 F)) * d.σ i) 1 0 = 0
      exact hzero
    have hquot :
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F))) =
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ j)⁻¹ * toSLF F (γ' : SL(2,𝓞 F))) := by
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      simpa [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc] using htransition
    let p : Σ k, CuspCosets F Γ (d.σ k) :=
      ⟨i, Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ i))) γ⟩
    let q : Σ k, CuspCosets F Γ (d.σ k) :=
      ⟨j, Quotient.mk (QuotientGroup.rightRel (cuspStab F Γ (d.σ j))) γ'⟩
    have hpeq : p = q := by
      apply d.reps_bijective.injective
      change Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((d.σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F))) = _
      calc
        _ = Quotient.mk (QuotientGroup.rightRel (borelSL F))
            ((d.σ i)⁻¹ * toSLF F (γ : SL(2,𝓞 F))) := by
          simpa [p] using reps_map_cuspCoset_mk Γ d i γ
        _ = Quotient.mk (QuotientGroup.rightRel (borelSL F))
            ((d.σ j)⁻¹ * toSLF F (γ' : SL(2,𝓞 F))) := hquot
        _ = Quotient.mk (QuotientGroup.rightRel (borelSL F))
            ((d.σ q.1)⁻¹ * toSLF F ((q.2.out : Γ) : SL(2,𝓞 F))) := by
          symm
          simpa [q] using reps_map_cuspCoset_mk Γ d j γ'
    have hij : i = j := congrArg Sigma.fst hpeq
    subst j
    refine ⟨rfl, ?_⟩
    apply (cuspStab_iff_borel_local Γ (d.σ i) (γ' * γ⁻¹)).mpr
    exact htransition
  · intro σ K hK A hA
    by_cases hKne : K.Nonempty
    · obtain ⟨z₀, hz₀⟩ := hKne
      obtain ⟨m, hmSummable, hmBound⟩ :=
        (E2_eis_converge (F := F) Γ σ).1 K hK 1 1 (by norm_num)
      have hmnonneg (q : CuspCosets F Γ σ) : 0 ≤ m q :=
        le_trans (norm_nonneg _) (hmBound z₀ hz₀ (1 : ℂ) (by norm_num) (by norm_num) q)
      have hsmall : ∀ᶠ q : CuspCosets F Γ σ in Filter.cofinite, ‖m q‖ < A ^ 3 :=
        hmSummable.norm.tendsto_cofinite_zero.eventually
          (Iio_mem_nhds (by positivity : 0 < A ^ 3))
      have htail : ({q : CuspCosets F Γ σ | ‖m q‖ < A ^ 3}ᶜ).Finite := by
        convert (Filter.eventually_cofinite.mp hsmall) using 1
        ext q
        simp
      apply htail.subset
      intro q hq
      change ¬ ‖m q‖ < A ^ 3
      intro hmq
      rcases hq with ⟨z, hzK, hzA⟩
      let h := normHeight F (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))
      have hpos : 0 < h := lt_of_lt_of_le hA hzA
      have hterm : eisTerm F Γ σ (1 : ℂ) z q = ((h : ℂ) ^ 3) := by
        norm_num [eisTerm, h]
      have hnorm : ‖eisTerm F Γ σ (1 : ℂ) z q‖ = h ^ 3 := by
        rw [hterm]
        simp [abs_of_pos hpos]
      have hcube : A ^ 3 ≤ h ^ 3 := by
        have hfac : 0 ≤ (h - A) * (h ^ 2 + h * A + A ^ 2) :=
          mul_nonneg (sub_nonneg.mpr hzA)
            (by positivity : 0 ≤ h ^ 2 + h * A + A ^ 2)
        nlinarith [hfac]
      have hmA : A ^ 3 ≤ m q := by
        calc
          A ^ 3 ≤ h ^ 3 := hcube
          _ = ‖eisTerm F Γ σ (1 : ℂ) z q‖ := hnorm.symm
          _ ≤ m q := hmBound z hzK (1 : ℂ) (by norm_num) (by norm_num) q
      exact (not_lt_of_ge (le_trans hmA (le_abs_self (m q)))) hmq
    · apply Set.finite_empty.subset
      intro q hq
      rcases hq with ⟨z, hz, _⟩
      exact hKne ⟨z, hz⟩

/-- R12 `spec:fund-domain` — P-SPEC.md:225, 338–342. The lexicographically least point in each
Siegel-covered orbit is a measurable finite-volume fundamental domain when the action is free.
Correction from `sol-gate-spec`: require calibrated Siegel data so the covering premise holds. -/
theorem R12_fund_domain (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (d : SiegelData F Γ) :
    let D := fundamentalDomainCandidate F Γ (SiegelData.unionSet F d)
    MeasurableSet D ∧ IsFundamentalDomain Γ D (volX F) ∧ volX F D < ⊤ := by
  sorry

/-- R13 `spec:compact-part` — P-SPEC.md:226. Bounded cusp heights reduce to the union of the
compact balanced boxes from the R8 Siegel sets. Correction from `sol-gate-spec`: require calibrated
Siegel data so the lower height floor comes from R7. -/
theorem R13_compact_part (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) :
    (∀ A : ℝ, 0 ≤ A → ∀ i : d.ι, IsCompact (SiegelData.compactBox F d i A)) ∧
    (∀ A : ℝ, 0 ≤ A → ∀ z : X F,
      (∀ i : d.ι, ∀ γ : Γ,
        normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ A) →
      z ∈ SiegelData.compactOrbit F d A) := by
  sorry

/-- R14 `spec:cusp-fubini` — P-SPEC.md:227, 344–347. The invariant integral over a high cusp
tail is the integral over a unit-height domain and a signed-translation domain. Correction from
`sol-gate-spec`: assume integrability on the quotient tail used by the change of fundamental domain. -/
theorem R14_cusp_fubini (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : X F,
      A₀ ≤ normHeight F (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ normHeight F (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ cuspStab F Γ σ)
    (Y : Set (InfinitePlace F → ℝ))
    (hYmeas : MeasurableSet Y)
    (hYpos : ∀ y ∈ Y, ∀ w, 0 < y w)
    (hYfd : ∀ y, (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ unitHeightAction F ε y ∈ Y ∧
        ∀ ε' : (𝓞 F)ˣ, ε' ∈ cuspUnits F Γ σ → unitHeightAction F ε' y ∈ Y →
          ε' = ε ∨ ε' = -ε)
    (P' : Set (InfinitePlace F → ℂ))
    (hP' : IsAddFundamentalDomain (cuspTranslationExtensionComplex F Γ σ) P')
    (hP'meas : MeasurableSet P')
    (G : X F → ℂ) (hGinv : IsGammaInvariant F Γ G)
    (hGint : IntegrableOn G (D ∩ cuspTail F Γ σ A) (volX F)) :
    ∫ z in D ∩ cuspTail F Γ σ A, G z ∂(volX F) =
      ∫ y in {y ∈ Y | A < ∏ w : InfinitePlace F, y w},
        (∫ x in P', G (σ • ptX' F x y) ∂volume) *
          (∏ w : InfinitePlace F, (y w ^ 3)⁻¹) ∂volume := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
