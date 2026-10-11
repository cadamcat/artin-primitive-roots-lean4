import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_bigCell_rtr

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- Every local section at s0 is a finite linear combination of s0 values of analytic global
families with that place inserted and the exterior sections held fixed. Translated big-cell
families first match the value at 1; section_eq_bigCell supplies the remaining section.
Uses: analyticFamily_bigCell_rtr, section_eq_bigCell, bigCell_apply and compact open local balls.
Feeds: theta_lambda_descent, theta_lambda_whittaker, thetaWhit_section_multilinear. -/
theorem sectionSpace_family_spanning (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (f : (P.loc v0).L → (G.T v0).V)
    (hf : f ∈ sectionSpace (P.loc v0) (G.T v0) (1 / 6)) :
    ∃ n : ℕ, ∃ c : Fin n → ℂ, ∃ fams : Fin n → AnalyticFamily P G μ,
      (∀ i, ExteriorFamily Fam v0 (fams i)) ∧
      f = ∑ i, c i • (((fams i).sec (1 / 6)).f v0) := by
  classical
  let K := v0.adicCompletion F
  letI : Finite (IsLocalRing.ResidueField (v0.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v0.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v0.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v0.adicCompletionIntegers F)))⟩
  let U : Set K := v0.adicCompletionIntegers F
  have hset : U = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) =
      Metric.closedBall (0 : K) 1
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  have hcompact : IsCompact U := by
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  have hopen : IsOpen U := Valued.isOpen_valuationSubring K
  have hclopen : IsClopen U := ⟨hcompact.isClosed, hopen⟩
  let φ : K → (G.T v0).V := U.indicator (fun _ => f 1)
  have hφ : IsLocallyConstant φ :=
    ((LocallyConstant.const K (f 1)).indicator hclopen).isLocallyConstant
  have hcφ : HasCompactSupport φ := by
    apply HasCompactSupport.of_support_subset_isCompact hcompact
    exact Set.support_indicator_subset
  have hφ0 : φ 0 = f 1 := by
    apply Set.indicator_of_mem
    simp [U, HeightOneSpectrum.mem_adicCompletionIntegers]
  obtain ⟨Fam₁, hExt₁, hval₁⟩ :=
    analyticFamily_bigCell_rtr Fam v0 φ hφ hcφ (P.loc v0).w
  let f₁ := (Fam₁.sec (1 / 6)).f v0
  have hf₁ : f₁ ∈ sectionSpace (P.loc v0) (G.T v0) (1 / 6) :=
    (Fam₁.sec (1 / 6)).f_sec v0
  have heval : f₁ 1 = f 1 := by
    change ((Fam₁.sec (1 / 6)).f v0) 1 = f 1
    rw [hval₁ (1 / 6)]
    simp only [rtr, one_mul]
    simpa [absFin_eq_norm, (P.loc v0).a_one, (G.T v0).σa_one, hφ0] using
      bigCell_apply (P.loc v0) (G.T v0) (1 / 6) φ 0 1 1 0
  have hrem : IsSection (P.loc v0) (G.T v0) (1 / 6) (f - f₁) :=
    (sectionSpace (P.loc v0) (G.T v0) (1 / 6)).sub_mem hf hf₁
  have hzero : (f - f₁) 1 = 0 := by
    change f 1 - f₁ 1 = 0
    rw [heval]
    simp
  obtain ⟨φ₂, hφ₂, hcφ₂, hbig⟩ :=
    section_eq_bigCell (P.loc v0) (G.T v0) (1 / 6) (f - f₁) hrem hzero
  obtain ⟨Fam₂, hExt₂, hval₂⟩ := analyticFamily_bigCell_rtr Fam v0 φ₂ hφ₂ hcφ₂ 1
  have hf₂ : (Fam₂.sec (1 / 6)).f v0 = f - f₁ := by
    rw [hval₂ (1 / 6)]
    funext h
    change bigCell (P.loc v0) (G.T v0) (1 / 6) φ₂ (h * 1) = (f - f₁) h
    rw [mul_one]
    exact congrFun hbig.symm h
  refine ⟨2, (fun _ => 1), ![Fam₁, Fam₂], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hExt₁
    · exact hExt₂
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]
    change f = f₁ + (Fam₂.sec (1 / 6)).f v0
    rw [hf₂]
    abel

end ArtinPrimitiveRoots.A1.Theta
