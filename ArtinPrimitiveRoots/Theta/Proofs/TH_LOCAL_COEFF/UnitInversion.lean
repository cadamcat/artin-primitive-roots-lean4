import ArtinPrimitiveRoots.Theta.LocalInt

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_lcoeff_sol

open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F] {v : FinPlace F}

/-- Inversion preserves additive Haar measure on the local unit shell. -/
theorem unit_integral_inv (μ : LocHaar v) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : v.adicCompletion F → E) :
    (∫ x in {x : v.adicCompletion F | Valued.v x = 1}, f x⁻¹ ∂μ.μ) =
      ∫ x in {x : v.adicCompletion F | Valued.v x = 1}, f x ∂μ.μ := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let G := Oˣ
  let U : Set K := {x | Valued.v x = 1}
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hOcompact : IsCompact (O : Set K) := by
    have hset : (O : Set K) = Metric.closedBall (0 : K) 1 :=
      Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  letI : CompactSpace O := isCompact_iff_compactSpace.mp hOcompact
  letI : MeasurableSpace O := borel O
  letI : BorelSpace O := ⟨rfl⟩
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  let r : O →+ K :=
    { toFun := fun a => (a : K)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hOopen : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  have hrOpen : Topology.IsOpenEmbedding r := hOopen.isOpenEmbedding_subtypeVal
  have hr : MeasurableEmbedding r := hrOpen.measurableEmbedding
  let μO : Measure O := μ.μ.comap r
  letI : μO.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ.μ hrOpen
  have hμO : μO Set.univ = 1 := by
    rw [hr.comap_apply]
    simpa [r, Set.image_univ, Subtype.range_coe, O] using μ.norm_O
  let g : G → O := fun u => (u : O)
  have hgClosed : Topology.IsClosedEmbedding g :=
    Units.continuous_val.isClosedEmbedding Units.val_injective
  have hg : MeasurableEmbedding g := hgClosed.measurableEmbedding
  let ν : Measure G := μO.comap g
  letI : IsFiniteMeasureOnCompacts ν :=
    IsFiniteMeasureOnCompacts.comap' μO hgClosed.continuous hg
  have hMul (u : G) : Measure.map (fun b : G => u * b) ν = ν := by
    let e : O ≃ₜ+ O := (ContinuousLinearEquiv.smulLeft (R₁ := O) u).toContinuousAddEquiv
    have he (a : O) : e a = (u : O) * a := rfl
    have hfactor : addEquivAddHaarChar e = 1 := by
      have h := addEquivAddHaarChar_smul_preimage μO e (X := Set.univ)
      have h' : (addEquivAddHaarChar e : ENNReal) = 1 := by
        simpa [hμO] using h
      exact_mod_cast h'
    have hpres (s : Set O) : μO (e ⁻¹' s) = μO s := by
      simpa [hfactor] using addEquivAddHaarChar_smul_preimage μO e (X := s)
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs, hg.comap_apply, hg.comap_apply]
    have himage : g '' ((fun b : G => u * b) ⁻¹' s) = e ⁻¹' (g '' s) := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨u * b, hb, rfl⟩
      · rintro ⟨b, hb, heq⟩
        refine ⟨u⁻¹ * b, ?_, ?_⟩
        · change u * (u⁻¹ * b) ∈ s
          have hcancel : u * u⁻¹ = (1 : G) := by
            apply Units.ext
            exact u.mul_inv
          rw [← mul_assoc, hcancel, one_mul]
          exact hb
        · change ((u⁻¹ : G) : O) * (b : O) = a
          change (b : O) = e a at heq
          rw [heq, he]
          rw [← mul_assoc]
          have hcancel : ((u⁻¹ : G) : O) * (u : O) = 1 := u.inv_mul
          rw [hcancel, one_mul]
    rw [himage, hpres]
  letI : ν.IsMulLeftInvariant := ⟨hMul⟩
  let η : Measure G := Measure.haar
  have hscale : ν = Measure.haarScalarFactor ν η • η :=
    Measure.isMulInvariant_eq_smul_of_compactSpace ν η
  letI : ν.IsInvInvariant := ⟨by
    change Measure.map Inv.inv ν = ν
    rw [hscale, Measure.map_smul _ measurable_inv.aemeasurable, Measure.map_inv_eq_self]
  ⟩
  let j : G → K := r ∘ g
  have hj : MeasurableEmbedding j := hr.comp hg
  have hjmul (a b : G) : j (a * b) = j a * j b := rfl
  have hjone : j (1 : G) = 1 := rfl
  have hjinv (b : G) : j b⁻¹ = (j b)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← hjmul, mul_inv_cancel, hjone]
  have hrange : Set.range j = U := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      have hb : j b ∈ O := (b : O).property
      have hbi : j b⁻¹ ∈ O := ((b⁻¹ : G) : O).property
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hb hbi
      have hprod : Valued.v (j b) * Valued.v (j b⁻¹) = 1 := by
        rw [← map_mul, ← hjmul, mul_inv_cancel, hjone, map_one]
      have hge : 1 ≤ Valued.v (j b) := by
        calc
          1 = Valued.v (j b) * Valued.v (j b⁻¹) := hprod.symm
          _ ≤ Valued.v (j b) * 1 := by
            simpa only [mul_comm] using mul_le_mul_left hbi (Valued.v (j b))
          _ = Valued.v (j b) := mul_one _
      exact le_antisymm hb hge
    · intro hx
      change Valued.v x = 1 at hx
      have hx0 : x ≠ 0 := by
        intro hzero
        rw [hzero, map_zero] at hx
        exact zero_ne_one hx
      have hxO : x ∈ O := by
        change x ∈ v.adicCompletionIntegers F
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hx.le
      have hxiO : x⁻¹ ∈ O := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hx]
        simp
      refine ⟨⟨⟨x, hxO⟩, ⟨x⁻¹, hxiO⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        exact mul_inv_cancel₀ hx0
      · apply Subtype.ext
        exact inv_mul_cancel₀ hx0
  have hν : ν = μ.μ.comap j :=
    Measure.comap_comap hg.measurableSet_image' hr.injective hr.measurableSet_image' μ.μ
  have hmap : Measure.map j ν = μ.μ.restrict U := by
    rw [hν, hj.map_comap, hrange]
  have hInt (p : K → E) : (∫ b : G, p (j b) ∂ν) = ∫ x in U, p x ∂μ.μ := by
    rw [← hmap]
    exact (hj.integral_map p).symm
  calc
    (∫ x in U, f x⁻¹ ∂μ.μ) = ∫ b : G, f ((j b)⁻¹) ∂ν :=
      (hInt (fun x => f x⁻¹)).symm
    _ = ∫ b : G, (fun c : G => f (j c)) b⁻¹ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with b
      rw [hjinv]
    _ = ∫ b : G, f (j b) ∂ν := integral_inv_eq_self (fun b : G => f (j b)) ν
    _ = ∫ x in U, f x ∂μ.μ := hInt f

end ArtinPrimitiveRoots.Proofs.th_lcoeff_sol
