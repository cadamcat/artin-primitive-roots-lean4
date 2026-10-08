import ArtinPrimitiveRoots.Spec.EisensteinExtra

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem probe_T7_estimate
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (E : FAEnergySpace (L2Space F D) (GradientL2Space F D))
    (e : EnergyContext F Γ D E) :
    ∃ R : E.V →L[ℂ] L2Space F D, IsCompactOperator R ∧
      ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
        ∀ x : E.V, ‖E.M x‖ ^ 2 ≤ c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := by
  classical
  let d : SiegelData F Γ := Classical.choice (spec_exists_siegelData Γ)
  obtain ⟨A₀, hA₀, hsep⟩ := (R10_cusp_separation (F := F) Γ).2.1 d
  let A : d.ι → ℝ := fun _ => A₀
  have hApos : ∀ i, 0 < A i := fun _ => lt_of_lt_of_le zero_lt_one hA₀
  have hAsep : ∀ i j : d.ι, ∀ γ γ' : Γ, ∀ z : X F,
      A i ≤ normHeight F ((d.σ i)⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A j ≤ normHeight F ((d.σ j)⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      i = j ∧ γ' * γ⁻¹ ∈ cuspStab F Γ (d.σ i) := by
    intro i j γ γ' z hi hj
    exact hsep A₀ le_rfl i j γ γ' z hi hj
  obtain ⟨K, hK, C₀, hC₀, R, hR, hT7, _⟩ :=
    T7_ground_state Γ D hD d A hApos hAsep E e A₀ (fun _ => le_rfl)
  let k : ℝ := placeCount F * (1 - 1 / (2 * A₀))
  have hr : 0 < placeCount F := by
    unfold placeCount
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (InfinitePlace F)))
  have hk : 0 < k := by
    dsimp [k]
    have hA₀pos : 0 < A₀ := lt_of_lt_of_le zero_lt_one hA₀
    have hfactor : 0 < 1 - 1 / (2 * A₀) := by
      have hden : 1 / (2 * A₀) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * A₀)).2
        nlinarith [hA₀]
      linarith
    exact mul_pos hr hfactor
  let c : ℝ := k⁻¹
  let C : ℝ := C₀ * k⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨R, hR, c, C, hc, hC, ?_⟩
  intro x
  have hmul := mul_le_mul_of_nonneg_right (hT7 x) (inv_nonneg.mpr hk.le)
  have hleft : (k * ‖E.M x‖ ^ 2) * k⁻¹ = ‖E.M x‖ ^ 2 := by
    field_simp [hk.ne']
  rw [hleft] at hmul
  calc
    ‖E.M x‖ ^ 2 ≤ (‖E.Gr x‖ ^ 2 + C₀ * ‖R x‖ ^ 2) * k⁻¹ := hmul
    _ = c * ‖E.Gr x‖ ^ 2 + C * ‖R x‖ ^ 2 := by
      dsimp [c, C]
      ring

end ArtinPrimitiveRoots.A1.Spec
