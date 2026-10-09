import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.A1.SLattice
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped Classical Valued

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1

/-- Multiplication by an inverse unit scales finite additive Haar measure by
the absolute value of the original unit. -/
theorem finiteHaar_map_unit_inverse
    {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : (v.adicCompletion F)ˣ) :
    Measure.map (fun x : v.adicCompletion F => x * (k⁻¹ : (v.adicCompletion F)ˣ).val)
        μ.μ =
      ENNReal.ofReal (absFin v (k : v.adicCompletion F)) • μ.μ := by
  let K := v.adicCompletion F
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  letI : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  letI : Measure.IsAddHaarMeasure μ.μ := μ.isHaar
  letI : Measure.Regular μ.μ := inferInstance
  let e : K ≃ₜ K := Homeomorph.mulRight₀ (k⁻¹ : Kˣ).val (Units.ne_zero _)
  letI : Measure.Regular (Measure.map e μ.μ) := Measure.Regular.map e
  letI : Measure.Regular (ENNReal.ofReal (absFin v (k : K)) • μ.μ) :=
    Measure.Regular.smul ENNReal.ofReal_ne_top
  change Measure.map e μ.μ = ENNReal.ofReal (absFin v (k : K)) • μ.μ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  calc
    ∫ x, f x ∂Measure.map e μ.μ = ∫ x, f (e x) ∂μ.μ :=
      integral_map_equiv e.toMeasurableEquiv f
    _ = (absFin v (k : K)) • ∫ x, f x ∂μ.μ := by
      have h := μ.integral_comp_mul (k⁻¹) (fun x : K => f x)
      simpa [e, mul_comm, Theta.absFin_eq_norm] using h
    _ = ∫ x, f x ∂(ENNReal.ofReal (absFin v (k : K)) • μ.μ) := by
      rw [integral_smul_measure,
        ENNReal.toReal_ofReal (by rw [Theta.absFin_eq_norm]; positivity)]

/-- Multiplication by an inverse complex unit scales volume by its norm square. -/
theorem complex_volume_map_unit_inverse (k : ℂˣ) :
    Measure.map (fun x : ℂ => x * (k⁻¹ : ℂˣ).val) (volume : Measure ℂ) =
      ENNReal.ofReal (Complex.normSq (k : ℂ)) • (volume : Measure ℂ) := by
  let a : ℂ := (k⁻¹ : ℂˣ).val
  let f : ℂ →ₗ[ℝ] ℂ := LinearMap.mul ℝ ℂ a
  have hmatrix : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI f =
      !![a.re, -a.im; a.im, a.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [f, LinearMap.toMatrix_apply, Complex.mul_re, Complex.mul_im]
  have hdet : LinearMap.det f = Complex.normSq a := by
    rw [← LinearMap.det_toMatrix Complex.basisOneI, hmatrix,
      Matrix.det_fin_two_of, Complex.normSq_apply]
    ring
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact ne_of_gt (Complex.normSq_pos.mpr (Units.ne_zero (k⁻¹)))
  have hcoef : |(LinearMap.det f)⁻¹| = Complex.normSq (k : ℂ) := by
    simp [hdet, a, Complex.normSq_inv,
      abs_of_nonneg (Complex.normSq_nonneg (k : ℂ))]
  have hfun : (fun x : ℂ => x * (k⁻¹ : ℂˣ).val) = (f : ℂ → ℂ) := by
    funext x
    exact mul_comm x a
  rw [hfun, Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne,
    hcoef]

/-- The additive Haar Jacobian of inverse-unit dilation on the full S-adic space. -/
theorem selfDual_map_unit_inverse
    {F : Type} [Field F] [NumberField F] {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (A : AddCharData F) (sd : S.SelfDualMeasure A)
    (μ : ∀ v : FinPlace F, Theta.LocHaar v) (k : S.FSˣ) :
    @Measure.map S.FS S.FS (borel S.FS) (borel S.FS)
        (fun x : S.FS => x * (k⁻¹ : S.FSˣ).val) sd.measure =
      ENNReal.ofReal (S.absS (k : S.FS)) • sd.measure := by
  letI : ∀ v : S.Sf, ProperSpace (v.1.adicCompletion F) := fun v => by
    let K := v.1.adicCompletion F
    letI : Finite (IsLocalRing.ResidueField (v.1.adicCompletionIntegers F)) :=
      Finite.of_equiv _ (v.1.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
    exact
      (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
        (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
        ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.1.adicCompletionIntegers F)),
          inferInstanceAs (Finite (IsLocalRing.ResidueField (v.1.adicCompletionIntegers F)))⟩
  letI : ∀ v : S.Sf, Measure.IsAddHaarMeasure (μ v.1).μ := fun v => (μ v.1).isHaar
  letI : ∀ v : S.Sf, SigmaFinite (μ v.1).μ := fun v => inferInstance
  let kf (v : S.Sf) : (v.1.adicCompletion F)ˣ :=
    ⟨k.val.1 v, k.inv.1 v,
      congrArg (fun x : S.FS => x.1 v) k.val_inv,
      congrArg (fun x : S.FS => x.1 v) k.inv_val⟩
  let kc (w : InfinitePlace F) : ℂˣ :=
    ⟨k.val.2 w, k.inv.2 w,
      congrArg (fun x : S.FS => x.2 w) k.val_inv,
      congrArg (fun x : S.FS => x.2 w) k.inv_val⟩
  let cf (v : S.Sf) : NNReal :=
    ⟨absFin v.1 (k.val.1 v), by rw [Theta.absFin_eq_norm]; positivity⟩
  let cc (w : InfinitePlace F) : NNReal :=
    ⟨Complex.normSq (k.val.2 w), Complex.normSq_nonneg _⟩
  let C : NNReal := (∏ v : S.Sf, cf v) * ∏ w : InfinitePlace F, cc w
  have hCReal : (C : ℝ) = S.absS (k : S.FS) := by
    exact (NNReal.coe_mul (∏ v : S.Sf, cf v) (∏ w : InfinitePlace F, cc w)).trans
      (congrArg₂ (fun x y : ℝ => x * y)
        (NNReal.coe_prod Finset.univ cf) (NNReal.coe_prod Finset.univ cc))
  have hC : (C : ENNReal) = ENNReal.ofReal (S.absS (k : S.FS)) := by
    rw [← hCReal]
    simp
  have hpi {ι : Type} [Fintype ι] {X : ι → Type}
      [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i))
      [∀ i, SigmaFinite (ν i)] (c : ι → NNReal) :
      Measure.pi (fun i => c i • ν i) = (∏ i, c i) • Measure.pi ν := by
    apply Measure.pi_eq
    intro s hs
    rw [Measure.smul_apply, Measure.pi_pi]
    simp only [Measure.smul_apply]
    change ((∏ i, c i : NNReal) : ENNReal) * (∏ i, ν i (s i)) =
      ∏ i, (c i : ENNReal) * ν i (s i)
    rw [ENNReal.ofNNReal_finsetProd, Finset.prod_mul_distrib]
  have hscale {X : Type} [MeasurableSpace X] (c : NNReal) (ν : Measure X) :
      (c : ENNReal) • ν = c • ν := by
    ext s hs
    simp only [Measure.smul_apply, ENNReal.smul_def]
  have hf (v : S.Sf) :
      Measure.map (fun x : v.1.adicCompletion F => x * (k⁻¹ : S.FSˣ).val.1 v)
        (μ v.1).μ = cf v • (μ v.1).μ := by
    have h := finiteHaar_map_unit_inverse v.1 (μ v.1) (kf v)
    change Measure.map
      (fun x : v.1.adicCompletion F => x * (k⁻¹ : S.FSˣ).val.1 v) (μ v.1).μ =
        ENNReal.ofReal (cf v : ℝ) • (μ v.1).μ at h
    simpa only [ENNReal.ofReal_coe_nnreal, hscale] using h
  have hc (w : InfinitePlace F) :
      Measure.map (fun x : ℂ => x * (k⁻¹ : S.FSˣ).val.2 w) (volume : Measure ℂ) =
        cc w • (volume : Measure ℂ) := by
    have h := complex_volume_map_unit_inverse (kc w)
    change Measure.map (fun x : ℂ => x * (k⁻¹ : S.FSˣ).val.2 w)
      (volume : Measure ℂ) = ENNReal.ofReal (cc w : ℝ) • (volume : Measure ℂ) at h
    simpa only [ENNReal.ofReal_coe_nnreal, hscale] using h
  haveI (v : S.Sf) : SigmaFinite
      (Measure.map (fun x : v.1.adicCompletion F => x * (k⁻¹ : S.FSˣ).val.1 v)
        (μ v.1).μ) := by rw [hf]; infer_instance
  haveI (w : InfinitePlace F) : SigmaFinite
      (Measure.map (fun x : ℂ => x * (k⁻¹ : S.FSˣ).val.2 w) (volume : Measure ℂ)) := by
    rw [hc]; infer_instance
  let ff (x : ∀ v : S.Sf, v.1.adicCompletion F) : ∀ v : S.Sf, v.1.adicCompletion F :=
    fun v => x v * (k⁻¹ : S.FSˣ).val.1 v
  let fc (x : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
    fun w => x w * (k⁻¹ : S.FSˣ).val.2 w
  let νf := Measure.pi fun v : S.Sf => (μ v.1).μ
  let νc := Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ)
  haveI hνf : Measure.IsAddHaarMeasure νf := by dsimp [νf]; infer_instance
  haveI hνc : Measure.IsAddHaarMeasure νc := by dsimp [νc]; infer_instance
  have hmf : Measure.map ff νf = (∏ v : S.Sf, cf v) • νf := by
    change Measure.map (fun x v => x v * (k⁻¹ : S.FSˣ).val.1 v)
      (Measure.pi fun v : S.Sf => (μ v.1).μ) = _
    rw [Measure.pi_map_pi (fun v => (by fun_prop :
      Measurable (fun x : v.1.adicCompletion F => x * (k⁻¹ : S.FSˣ).val.1 v)).aemeasurable)]
    simp_rw [hf]
    exact hpi (fun v : S.Sf => (μ v.1).μ) cf
  have hmc : Measure.map fc νc = (∏ w : InfinitePlace F, cc w) • νc := by
    change Measure.map (fun x w => x w * (k⁻¹ : S.FSˣ).val.2 w)
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ)) = _
    rw [Measure.pi_map_pi (fun w => (by fun_prop :
      Measurable (fun x : ℂ => x * (k⁻¹ : S.FSˣ).val.2 w)).aemeasurable)]
    simp_rw [hc]
    exact hpi (fun _ : InfinitePlace F => (volume : Measure ℂ)) cc
  let m0 : MeasurableSpace S.FS := inferInstance
  let ν0 : @Measure S.FS m0 := νf.prod νc
  let δ (x : S.FS) : S.FS := x * (k⁻¹ : S.FSˣ).val
  have hδ0 : @Measurable S.FS S.FS m0 m0 δ := by fun_prop
  have hnatural : @Measure.map S.FS S.FS m0 m0 δ ν0 = C • ν0 := by
    change Measure.map (Prod.map ff fc) (νf.prod νc) = C • (νf.prod νc)
    rw [← Measure.map_prod_map νf νc (by fun_prop) (by fun_prop), hmf, hmc,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  haveI hν0 : Measure.IsAddHaarMeasure ν0 := by dsimp [ν0, m0]; infer_instance
  haveI hBorel0 : @BorelSpace S.FS _ m0 := by infer_instance
  letI : MeasurableSpace S.FS := borel S.FS
  letI : BorelSpace S.FS := ⟨rfl⟩
  let e : @MeasurableEquiv S.FS S.FS m0 (borel S.FS) :=
    @MeasurableEquiv.mk S.FS S.FS m0 (borel S.FS) (Equiv.refl S.FS)
      (@Continuous.measurable S.FS S.FS _ m0 _ _ (borel S.FS) _ id continuous_id)
      (@Continuous.measurable S.FS S.FS _ (borel S.FS) _ _ m0 hBorel0 id continuous_id)
  let ν : Measure S.FS := @Measure.map S.FS S.FS m0 (borel S.FS) id ν0
  have hId : @Measurable S.FS S.FS m0 (borel S.FS) id :=
    @MeasurableEquiv.measurable S.FS S.FS m0 (borel S.FS) e
  letI : Measure.IsAddHaarMeasure ν := by
    exact @AddEquiv.isAddHaarMeasure_map S.FS m0 _ _ ν0 hν0 hBorel0 _
      S.FS _ _ (borel S.FS) _ _ (AddEquiv.refl S.FS) continuous_id continuous_id
  letI : Measure.IsAddHaarMeasure sd.measure := sd.isHaar
  let q : NNReal := Measure.addHaarScalarFactor sd.measure ν
  have hμ : sd.measure = q • ν := Measure.isAddLeftInvariant_eq_smul sd.measure ν
  have hδ : Measurable δ := by fun_prop
  have hνmap : Measure.map δ ν = C • ν := by
    calc
      Measure.map δ ν = @Measure.map S.FS S.FS m0 (borel S.FS) δ ν0 :=
        @Measure.map_map S.FS S.FS S.FS m0 (borel S.FS) (borel S.FS) ν0 δ id hδ hId
      _ = @Measure.map S.FS S.FS m0 (borel S.FS) id
          (@Measure.map S.FS S.FS m0 m0 δ ν0) :=
        (@Measure.map_map S.FS S.FS S.FS m0 m0 (borel S.FS) ν0 id δ hId hδ0).symm
      _ = C • ν := by
        rw [hnatural]
        exact @Measure.map_smul S.FS S.FS m0 (borel S.FS) NNReal _ _ C ν0 id
          (@Measurable.aemeasurable S.FS S.FS m0 (borel S.FS) id ν0 hId)
  have hresult : Measure.map δ sd.measure = C • sd.measure := by
    rw [hμ, Measure.map_smul q hδ.aemeasurable, hνmap, smul_comm]
  change Measure.map δ sd.measure = _
  calc
    _ = C • sd.measure := hresult
    _ = (C : ENNReal) • sd.measure := (hscale C sd.measure).symm
    _ = ENNReal.ofReal (S.absS (k : S.FS)) • sd.measure := by rw [hC]

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
