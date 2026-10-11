import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.scalar_unit_orbit_section
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.scalar_unit_orbit_summable
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.balanced_first_coordinate_fiber_bound

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private lemma absFieldNorm_nonneg_local (a : F) : 0 ≤ absFieldNorm F a := by
  unfold absFieldNorm
  exact Finset.prod_nonneg (fun w hw => sq_nonneg ‖w.embedding a‖)

private lemma hasDenominatorBound_mul_unit {D : ℕ} {a : F}
    (ha : HasDenominatorBound F D a) (ε : (𝓞 F)ˣ) :
    HasDenominatorBound F D (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨(ε : 𝓞 F) * b, ?_⟩
  change (D : F) * (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) =
    algebraMap (𝓞 F) F ((ε : 𝓞 F) * b)
  calc
    (D : F) * (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) =
        algebraMap (𝓞 F) F (ε : 𝓞 F) * ((D : F) * a) := by ring
    _ = algebraMap (𝓞 F) F (ε : 𝓞 F) * algebraMap (𝓞 F) F b := by rw [hb]
    _ = algebraMap (𝓞 F) F ((ε : 𝓞 F) * b) := by rw [map_mul]

private lemma siegelRowKernel_unit_smul (ε : (𝓞 F)ˣ) (a b : F)
    (ha : a ≠ 0) (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (α : ℝ) :
    siegelRowKernel
      (algebraMap (𝓞 F) F (ε : 𝓞 F) * a,
        algebraMap (𝓞 F) F (ε : 𝓞 F) * b) x y α =
      siegelRowKernel (a, b) x y α := by
  let e : F := algebraMap (𝓞 F) F (ε : 𝓞 F)
  have he : e ≠ 0 := by
    dsimp [e]
    exact (map_ne_zero_iff (algebraMap (𝓞 F) F)
      (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (Units.ne_zero ε)
  have hnorm : absFieldNorm F e = 1 := by
    dsimp [e]
    simpa [absFieldNorm_eq_abs_norm] using (NumberField.Units.norm F ε)
  let q : InfinitePlace F → ℝ := fun w => Complex.normSq (w.embedding e)
  have hqpos (w : InfinitePlace F) : 0 < q w := by
    dsimp [q]
    rw [Complex.normSq_eq_norm_sq]
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact (map_ne_zero_iff _ w.embedding.injective).mpr he
  have hqprod : ∏ w : InfinitePlace F, q w = 1 := by
    calc
      ∏ w : InfinitePlace F, q w = absFieldNorm F e := by
        simp [q, absFieldNorm, Complex.normSq_eq_norm_sq]
      _ = 1 := hnorm
  have hqpow : (∏ w : InfinitePlace F, Real.rpow (q w) (-α)) = 1 := by
    calc
      (∏ w : InfinitePlace F, Real.rpow (q w) (-α)) =
          Real.rpow (∏ w : InfinitePlace F, q w) (-α) :=
        Real.finsetProd_rpow Finset.univ q (by intro w hw; exact (hqpos w).le) _
      _ = 1 := by rw [hqprod]; simp
  have hbasePos (w : InfinitePlace F) : 0 < Complex.normSq (w.embedding a * x w +
      w.embedding b) + Complex.normSq (w.embedding a) * y w ^ 2 := by
    have haw : w.embedding a ≠ 0 :=
      (map_ne_zero_iff _ w.embedding.injective).mpr ha
    have hnormA : 0 < Complex.normSq (w.embedding a) := by
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr haw)
    exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (mul_pos hnormA (sq_pos_of_pos (hy w)))
  have hscaledDen (w : InfinitePlace F) :
      Complex.normSq (w.embedding (e * a) * x w + w.embedding (e * b)) +
        Complex.normSq (w.embedding (e * a)) * y w ^ 2 =
      q w * (Complex.normSq (w.embedding a * x w + w.embedding b) +
        Complex.normSq (w.embedding a) * y w ^ 2) := by
    have hlin : w.embedding (e * a) * x w + w.embedding (e * b) =
        w.embedding e * (w.embedding a * x w + w.embedding b) := by
      simp only [map_mul]
      ring
    rw [hlin]
    simp only [map_mul, Complex.normSq_mul, q]
    ring
  have hfactor (w : InfinitePlace F) :
      Real.rpow (y w /
        (q w * (Complex.normSq (w.embedding a * x w + w.embedding b) +
          Complex.normSq (w.embedding a) * y w ^ 2))) α =
        Real.rpow (q w) (-α) * Real.rpow (y w /
          (Complex.normSq (w.embedding a * x w + w.embedding b) +
            Complex.normSq (w.embedding a) * y w ^ 2)) α := by
    have hq := (hqpos w).le
    have hb := (hbasePos w).le
    have hmul : Real.rpow (q w *
        (Complex.normSq (w.embedding a * x w + w.embedding b) +
          Complex.normSq (w.embedding a) * y w ^ 2)) α =
        Real.rpow (q w) α * Real.rpow
          (Complex.normSq (w.embedding a * x w + w.embedding b) +
            Complex.normSq (w.embedding a) * y w ^ 2) α := Real.mul_rpow hq hb
    have hqneg : Real.rpow (q w) (-α) = (Real.rpow (q w) α)⁻¹ :=
      Real.rpow_neg (hqpos w).le α
    have hdiv : Real.rpow (y w /
        (Complex.normSq (w.embedding a * x w + w.embedding b) +
          Complex.normSq (w.embedding a) * y w ^ 2)) α =
        Real.rpow (y w) α /
          Real.rpow (Complex.normSq (w.embedding a * x w + w.embedding b) +
            Complex.normSq (w.embedding a) * y w ^ 2) α :=
      Real.div_rpow (hy w).le hb α
    calc
      _ = Real.rpow (y w) α /
          Real.rpow (q w * (Complex.normSq (w.embedding a * x w + w.embedding b) +
            Complex.normSq (w.embedding a) * y w ^ 2)) α :=
          Real.div_rpow (hy w).le (mul_nonneg hq hb) α
      _ = Real.rpow (y w) α /
          (Real.rpow (q w) α * Real.rpow
            (Complex.normSq (w.embedding a * x w + w.embedding b) +
              Complex.normSq (w.embedding a) * y w ^ 2) α) := by
          exact congrArg (fun z : ℝ => Real.rpow (y w) α / z) hmul
      _ = Real.rpow (q w) (-α) * Real.rpow (y w /
          (Complex.normSq (w.embedding a * x w + w.embedding b) +
            Complex.normSq (w.embedding a) * y w ^ 2)) α := by
          calc
            _ = (Real.rpow (q w) α)⁻¹ *
                (Real.rpow (y w) α /
                  Real.rpow (Complex.normSq (w.embedding a * x w + w.embedding b) +
                    Complex.normSq (w.embedding a) * y w ^ 2) α) := by ring
            _ = _ := congrArg₂ (fun s t : ℝ => s * t) hqneg.symm hdiv.symm
  unfold siegelRowKernel
  calc
    (∏ w : InfinitePlace F,
      Real.rpow (y w /
        (Complex.normSq (w.embedding (e * a) * x w + w.embedding (e * b)) +
          Complex.normSq (w.embedding (e * a)) * y w ^ 2)) α) =
        ∏ w : InfinitePlace F,
          (Real.rpow (q w) (-α) * Real.rpow (y w /
            (Complex.normSq (w.embedding a * x w + w.embedding b) +
              Complex.normSq (w.embedding a) * y w ^ 2)) α) := by
      apply Finset.prod_congr rfl
      intro w hw
      rw [hscaledDen w]
      exact hfactor w
    _ = (∏ w : InfinitePlace F, Real.rpow (q w) (-α)) *
        ∏ w : InfinitePlace F,
          Real.rpow (y w /
            (Complex.normSq (w.embedding a * x w + w.embedding b) +
              Complex.normSq (w.embedding a) * y w ^ 2)) α := Finset.prod_mul_distrib
    _ = siegelRowKernel (a, b) x y α := by
      rw [hqpow]
      simp [siegelRowKernel]

/-- The row-kernel sum is uniformly bounded on balanced positive heights with a
product floor, for any denominator-bounded row family with distinct unit orbits and
nonzero first coordinates.
Uses `scalar_unit_orbit_section`, `scalar_unit_orbit_summable`, and
`balanced_first_coordinate_fiber_bound`; feeds `nontriangular_siegel_summable`.
Rescale each whole row to its chosen c representative, inject into the (c,d) family,
then split the c norm at one to use the two endpoint summable weights. -/
theorem balanced_denominator_rows_bound (D : ℕ) (hD : 0 < D)
    (By H αmin αmax : ℝ) (hBy : 0 ≤ By) (hH : 0 < H)
    (hαmin : 2 < αmin) (hαrange : αmin ≤ αmax) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, αmin ≤ α → α ≤ αmax →
      ∀ {ι : Type*} (v : ι → F × F),
        (∀ i, HasDenominatorBound F D (v i).1 ∧ HasDenominatorBound F D (v i).2) →
        (∀ i, (v i).1 ≠ 0) →
        (∀ i j, unitAssociatedRows F (v i) (v j) → i = j) →
      ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
        IsBalancedHeights F By y → H ≤ ∏ w, y w →
        Summable (fun i => siegelRowKernel (v i) x y α) ∧
          (∑' i, siegelRowKernel (v i) x y α) ≤ C := by
  classical
  obtain ⟨Bc, S, hBc, hS, hSuniq, hCover⟩ :=
    scalar_unit_orbit_section (F := F) D hD
  have hαfiber : 1 < αmin := by linarith
  obtain ⟨CF, hCF, hFiber⟩ :=
    balanced_first_coordinate_fiber_bound (F := F) D hD Bc By H αmin αmax
      hBc hBy hH hαfiber hαrange
  let lowWeight : S → ℝ := fun c => Real.rpow (absFieldNorm F c.1) (1 - αmin)
  let highWeight : S → ℝ := fun c => Real.rpow (absFieldNorm F c.1) (1 - αmax)
  have hLow : Summable lowWeight := by
    have h := scalar_unit_orbit_summable (F := F) D hD (αmin - 1)
      (by linarith) (fun c : S => c.1)
      (fun c => (hS c.1 c.2).2.1) (fun c => (hS c.1 c.2).1)
      (by
        intro c c' hcc
        apply Subtype.ext
        exact hSuniq c.1 c'.1 c.2 c'.2 hcc)
    simpa only [lowWeight, show -(αmin - 1) = 1 - αmin by ring] using h
  have hHigh : Summable highWeight := by
    have h := scalar_unit_orbit_summable (F := F) D hD (αmax - 1)
      (by linarith [hαmin, hαrange]) (fun c : S => c.1)
      (fun c => (hS c.1 c.2).2.1) (fun c => (hS c.1 c.2).1)
      (by
        intro c c' hcc
        apply Subtype.ext
        exact hSuniq c.1 c'.1 c.2 c'.2 hcc)
    simpa only [highWeight, show -(αmax - 1) = 1 - αmax by ring] using h
  let T : ℝ := max 1 (Real.rpow H (2 - αmax))
  have hT : 0 ≤ T := by
    dsimp [T]
    exact le_max_of_le_left (by norm_num)
  let C : ℝ := CF * T * ((∑' c : S, lowWeight c) + ∑' c : S, highWeight c)
  have hC : 0 ≤ C := by
    dsimp [C]
    apply mul_nonneg
    · exact mul_nonneg hCF hT
    · exact add_nonneg
        (tsum_nonneg (fun c => Real.rpow_nonneg (absFieldNorm_nonneg_local c.1) _))
        (tsum_nonneg (fun c => Real.rpow_nonneg (absFieldNorm_nonneg_local c.1) _))
  refine ⟨C, hC, ?_⟩
  intro α hαlo hαhi ι v hvD hv0 huniq x y hy hHY
  let Y : ℝ := ∏ w : InfinitePlace F, y w
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact Finset.prod_pos (fun w hw => hy.1 w)
  have hYbound : Real.rpow Y (2 - α) ≤ T := by
    by_cases hYone : 1 ≤ Y
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hYone (by linarith)).trans
        (le_max_left 1 (Real.rpow H (2 - αmax)))
    · have hYle : Y ≤ 1 := le_of_not_ge hYone
      calc
        Real.rpow Y (2 - α) ≤ Real.rpow Y (2 - αmax) :=
          Real.rpow_le_rpow_of_exponent_ge hYpos hYle (by linarith)
        _ ≤ Real.rpow H (2 - αmax) :=
          Real.rpow_le_rpow_of_nonpos hH hHY (by linarith [hαmin, hαrange])
        _ ≤ T := le_max_right 1 (Real.rpow H (2 - αmax))
  have hweight (c : S) :
      Real.rpow (absFieldNorm F c.1) (1 - α) ≤ lowWeight c + highWeight c := by
    have hcpos : 0 < absFieldNorm F c.1 := absFieldNorm_pos_of_ne_zero (hS c.1 c.2).1
    by_cases hcnorm : absFieldNorm F c.1 ≤ 1
    · have hpow := Real.rpow_le_rpow_of_exponent_ge
        (x := absFieldNorm F c.1) (y := 1 - α) (z := 1 - αmax)
        hcpos hcnorm (by linarith)
      exact hpow.trans (le_add_of_nonneg_left
        (Real.rpow_nonneg (absFieldNorm_nonneg_local c.1) _))
    · have hcnorm' : 1 ≤ absFieldNorm F c.1 := le_of_not_ge hcnorm
      have hpow := Real.rpow_le_rpow_of_exponent_le
        (x := absFieldNorm F c.1) (y := 1 - α) (z := 1 - αmin)
        hcnorm' (by linarith)
      exact hpow.trans (le_add_of_nonneg_right
        (Real.rpow_nonneg (absFieldNorm_nonneg_local c.1) _))
  let ε : ι → (𝓞 F)ˣ := fun i => Classical.choose
    (hCover (v i).1 (hv0 i) (hvD i).1)
  let e : ι → F := fun i => algebraMap (𝓞 F) F (ε i : 𝓞 F)
  let cRep : ι → S := fun i => ⟨e i * (v i).1,
    Classical.choose_spec (hCover (v i).1 (hv0 i) (hvD i).1)
      ⟩
  let dRep : ι → DenominatorScalars (F := F) D := fun i =>
    ⟨e i * (v i).2, hasDenominatorBound_mul_unit (hvD i).2 (ε i)⟩
  let pair : ι → S × DenominatorScalars (F := F) D := fun i => (cRep i, dRep i)
  have heNZ (i : ι) : e i ≠ 0 := by
    dsimp [e]
    exact (map_ne_zero_iff (algebraMap (𝓞 F) F)
      (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (Units.ne_zero (ε i))
  have hpairInj : Function.Injective pair := by
    intro i j hij
    have hu1 : e i * (v i).1 = e j * (v j).1 := by
      exact congrArg Subtype.val (congrArg Prod.fst hij)
    have hu2 : e i * (v i).2 = e j * (v j).2 := by
      exact congrArg Subtype.val (congrArg Prod.snd hij)
    apply huniq i j
    change ∃ η : (𝓞 F)ˣ,
      v i = (algebraMap (𝓞 F) F (η : 𝓞 F) * (v j).1,
        algebraMap (𝓞 F) F (η : 𝓞 F) * (v j).2)
    refine ⟨(ε i)⁻¹ * ε j, ?_⟩
    apply Prod.ext
    · calc
        (v i).1 = (e i)⁻¹ * (e i * (v i).1) := by field_simp [heNZ i]
        _ = (e i)⁻¹ * (e j * (v j).1) := by rw [hu1]
        _ = ((e i)⁻¹ * e j) * (v j).1 := by ring
        _ = algebraMap (𝓞 F) F ((((ε i)⁻¹ * ε j : (𝓞 F)ˣ) : 𝓞 F)) *
            (v j).1 := by simp [e, map_mul, map_inv₀]
    · calc
        (v i).2 = (e i)⁻¹ * (e i * (v i).2) := by field_simp [heNZ i]
        _ = (e i)⁻¹ * (e j * (v j).2) := by rw [hu2]
        _ = ((e i)⁻¹ * e j) * (v j).2 := by ring
        _ = algebraMap (𝓞 F) F ((((ε i)⁻¹ * ε j : (𝓞 F)ˣ) : 𝓞 F)) *
            (v j).2 := by simp [e, map_mul, map_inv₀]
  let G : (S × DenominatorScalars (F := F) D) → ℝ := fun p =>
    siegelRowKernel (p.1.1, p.2.1) x y α
  have hGnonneg (p : S × DenominatorScalars (F := F) D) : 0 ≤ G p := by
    unfold G siegelRowKernel
    apply Finset.prod_nonneg
    intro w hw
    apply Real.rpow_nonneg
    apply div_nonneg (hy.1 w).le
    exact add_nonneg (Complex.normSq_nonneg _)
      (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))
  have hFiberAt (c : S) :
      Summable (fun d : DenominatorScalars (F := F) D => G (c, d)) ∧
        (∑' d : DenominatorScalars (F := F) D, G (c, d)) ≤
          CF * Real.rpow Y (2 - α) * Real.rpow (absFieldNorm F c.1) (1 - α) := by
    have hcprops := hS c.1 c.2
    have h := hFiber α hαlo hαhi c.1 hcprops.1 hcprops.2.1 hcprops.2.2
      x y hy hHY
    simpa [G, Y] using h
  have hInnerBound (c : S) :
      (∑' d : DenominatorScalars (F := F) D, G (c, d)) ≤
        (CF * T) * (lowWeight c + highWeight c) := by
    calc
      _ ≤ CF * Real.rpow Y (2 - α) * Real.rpow (absFieldNorm F c.1) (1 - α) :=
        (hFiberAt c).2
      _ ≤ CF * T * Real.rpow (absFieldNorm F c.1) (1 - α) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hYbound hCF)
          (Real.rpow_nonneg (absFieldNorm_nonneg_local c.1) _)
      _ ≤ (CF * T) * (lowWeight c + highWeight c) :=
        mul_le_mul_of_nonneg_left (hweight c) (mul_nonneg hCF hT)
  have hMajor : Summable (fun c : S => (CF * T) * (lowWeight c + highWeight c)) :=
    (hLow.add hHigh).mul_left (CF * T)
  have hInnerNonneg (c : S) : 0 ≤ ∑' d : DenominatorScalars (F := F) D, G (c, d) :=
    tsum_nonneg (fun d => hGnonneg (c, d))
  have hOuter : Summable (fun c : S => ∑' d : DenominatorScalars (F := F) D,
      G (c, d)) :=
    Summable.of_nonneg_of_le hInnerNonneg hInnerBound hMajor
  have hPairSummable : Summable G :=
    (summable_prod_of_nonneg hGnonneg).2 ⟨fun c => (hFiberAt c).1, hOuter⟩
  have hPairTsumBound : (∑' p : S × DenominatorScalars (F := F) D, G p) ≤ C := by
    rw [hPairSummable.tsum_prod]
    calc
      (∑' c : S, ∑' d : DenominatorScalars (F := F) D, G (c, d)) ≤
          ∑' c : S, (CF * T) * (lowWeight c + highWeight c) :=
        hOuter.tsum_le_tsum hInnerBound hMajor
      _ = C := by
        dsimp [C]
        rw [(hLow.add hHigh).tsum_mul_left, hLow.tsum_add hHigh]
  have hkernelEq (i : ι) : siegelRowKernel (v i) x y α = G (pair i) := by
    change siegelRowKernel (v i) x y α =
      siegelRowKernel (e i * (v i).1, e i * (v i).2) x y α
    exact (siegelRowKernel_unit_smul (ε i) (v i).1 (v i).2 (hv0 i) x y hy.1 α).symm
  have hcompSummable : Summable (fun i => G (pair i)) :=
    hPairSummable.comp_injective hpairInj
  have hcompBound : (∑' i, G (pair i)) ≤ C :=
    (tsum_comp_le_tsum_of_inj hPairSummable hGnonneg hpairInj).trans hPairTsumBound
  refine ⟨hcompSummable.congr (fun i => (hkernelEq i).symm), ?_⟩
  calc
    (∑' i, siegelRowKernel (v i) x y α) = ∑' i, G (pair i) := tsum_congr hkernelEq
    _ ≤ C := hcompBound

end ArtinPrimitiveRoots.A1.Spec
