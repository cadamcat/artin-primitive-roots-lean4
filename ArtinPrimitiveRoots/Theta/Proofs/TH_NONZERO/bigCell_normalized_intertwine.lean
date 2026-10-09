import ArtinPrimitiveRoots.Theta.LocalInt

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- A compactly supported big-cell section can prescribe its intertwined
value at the identity, uniformly in the complex parameter. -/
theorem bigCell_normalized_intertwine (L : FinLocalCover D H v)
    (T : TorusRep D H v) (μ : LocHaar v) (x : T.V) :
    ∃ φ : v.adicCompletion F → T.V,
      IsLocallyConstant φ ∧ HasCompactSupport φ ∧
      ∀ s : ℂ, intertwine L μ (bigCell L T s φ) 1 = x := by
  classical
  let K := v.adicCompletion F
  let : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  let U : Set K := v.adicCompletionIntegers F
  have hset : U = Metric.closedBall (0 : K) 1 :=
    Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  have hcompact : IsCompact U := by
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  have hopen : IsOpen U := Valued.isOpen_valuationSubring K
  have hclopen : IsClopen U := ⟨hcompact.isClosed, hopen⟩
  let φ : K → T.V := U.indicator (fun _ => x)
  have hφ : IsLocallyConstant φ :=
    ((LocallyConstant.const K x).indicator hclopen).isLocallyConstant
  have hcφ : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact hcompact Set.support_indicator_subset
  refine ⟨φ, hφ, hcφ, ?_⟩
  intro s
  have heval (t : K) :
      bigCell L T s φ (L.w * L.n (Multiplicative.ofAdd t)) = φ t := by
    simpa [absFin_eq_norm, L.a_one, T.σa_one] using
      bigCell_apply L T s φ 0 1 1 t
  change (∫ t : K, bigCell L T s φ (L.w * L.n (Multiplicative.ofAdd t) * 1) ∂μ.μ) = x
  simp only [mul_one, heval]
  change (∫ t : K, U.indicator (fun _ => x) t ∂μ.μ) = x
  rw [integral_indicator_const x hopen.measurableSet]
  simp [MeasureTheory.measureReal_def, U, μ.norm_O]

end ArtinPrimitiveRoots.A1.Theta
