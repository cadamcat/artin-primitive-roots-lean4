import ArtinPrimitiveRoots.Hecke.Theta.RayTheta

/-!
Small-parameter estimates for the ray theta Poisson expansion.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open NumberField.mixedEmbedding
open NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open DedekindResidue
open ArtinPrimitiveRoots.Hecke.Theta
open MeasureTheory
open scoped NumberField nonZeroDivisors Real Classical FourierTransform RealInnerProductSpace

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

local instance raySmallModulusQuotientFinite (m : RayClassModulus K) :
    Finite ((𝓞 K) ⧸ modulusIdeal m) := by
  letI : NeZero (modulusIdeal m) := ⟨modulusIdeal_ne_bot m⟩
  infer_instance

local instance raySmallAcceptedFinite (m : RayClassModulus K) :
    Finite (acceptedResidues m) :=
  Finite.of_injective (fun r : acceptedResidues m => r.1) Subtype.val_injective

local instance raySmallAcceptedFintype (m : RayClassModulus K) :
    Fintype (acceptedResidues m) := Fintype.ofFinite _

private theorem heckeWeights_upper_of_bounded {R T : ℝ} (hR : 0 ≤ R)
    (u : logSpace K) (hu : ∀ i, |u i| ≤ R) (hT : 0 < T) (w : InfinitePlace K) :
    heckeWeights K T u w ≤
      Real.exp (2 * (Fintype.card (InfinitePlace K) : ℝ) * R) *
        T ^ ((1 : ℝ) / (Module.finrank ℚ K)) := by
  have hlog := DedekindResidue.abs_fullLog_le K hR hu w
  have hfull : fullLog K u w ≤ (Fintype.card (InfinitePlace K) : ℝ) * R :=
    le_trans (le_abs_self (fullLog K u w)) hlog
  have hmult : (1 : ℝ) ≤ mult w := NumberField.InfinitePlace.one_le_mult
  have hmpos : 0 < (mult w : ℝ) := by positivity
  have hC : 0 ≤ (Fintype.card (InfinitePlace K) : ℝ) * R :=
    mul_nonneg (Nat.cast_nonneg _) hR
  have hmult' : 0 ≤ (mult w : ℝ) - 1 := sub_nonneg.mpr hmult
  have hdiv : fullLog K u w / mult w ≤
      (Fintype.card (InfinitePlace K) : ℝ) * R := by
    rw [div_le_iff₀ hmpos]
    nlinarith [mul_nonneg hC hmult']
  have harg : 2 * fullLog K u w / mult w ≤
      2 * (Fintype.card (InfinitePlace K) : ℝ) * R := by
    calc
      2 * fullLog K u w / mult w =
          2 * (fullLog K u w / mult w) := by ring
      _ ≤ 2 * ((Fintype.card (InfinitePlace K) : ℝ) * R) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 2 * (Fintype.card (InfinitePlace K) : ℝ) * R := by ring
  rw [heckeWeights]
  calc
    T ^ ((1 : ℝ) / (Module.finrank ℚ K)) *
        Real.exp (2 * fullLog K u w / mult w)
      ≤ T ^ ((1 : ℝ) / (Module.finrank ℚ K)) *
        Real.exp (2 * (Fintype.card (InfinitePlace K) : ℝ) * R) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
            (Real.rpow_nonneg hT.le _)
    _ = _ := by ring

/-- Splitting a single shifted dual Gaussian theta at its zero frequency. -/
theorem rayResidueDualGaussian_split_zero [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥) (c : index K → ℝ)
    (r : acceptedResidues m) {a : ℝ} (ha : 0 < a)
    (hca : ∀ i, a ≤ (c i)⁻¹) :
    ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
        (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)),
      Real.fourierChar (⟪embeddingCoords K
          (algebraMap (𝓞 K) K
            (acceptedResidueLift m J
              ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1),
          (w : EuclideanSpace ℝ (index K))⟫) •
        ((Real.sqrt (∏ i, c i))⁻¹ •
          weightedGaussianCM (fun i => (c i)⁻¹) (w : EuclideanSpace ℝ (index K))) =
      ((Real.sqrt (∏ i, c i))⁻¹ : ℂ) +
        ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
          (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)),
          if w = 0 then 0 else
            Real.fourierChar (⟪embeddingCoords K
                (algebraMap (𝓞 K) K
                  (acceptedResidueLift m J
                    ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1),
                (w : EuclideanSpace ℝ (index K))⟫) •
              ((Real.sqrt (∏ i, c i))⁻¹ •
                weightedGaussianCM (fun i => (c i)⁻¹)
                  (w : EuclideanSpace ℝ (index K))) := by
  classical
  let L := ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
    (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ))
  let shift := embeddingCoords K (algebraMap (𝓞 K) K
    (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1)
  let S : ℝ := (Real.sqrt (∏ i, c i))⁻¹
  let g : L → ℂ := fun w => Real.fourierChar (⟪shift, (w : EuclideanSpace ℝ (index K))⟫) •
    (S • weightedGaussianCM (fun i => (c i)⁻¹) (w : EuclideanSpace ℝ (index K)))
  have hreal : Summable (fun w : L =>
      Real.exp (-Real.pi * ∑ i : index K,
        (c i)⁻¹ * ((w : EuclideanSpace ℝ (index K)) i) ^ 2)) :=
    DedekindResidue.summable_real_weightedGaussian L ha hca
  have hsum : Summable g := by
    apply Summable.of_norm
    have hmajor := hreal.mul_left |S|
    exact hmajor.congr (fun w => by
      simp [g, S, norm_weightedGaussianCM_apply])
  have hsplit := hsum.tsum_eq_add_tsum_ite (0 : L)
  have hzero : g 0 = (S : ℂ) := by
    simp [g, S, shift, weightedGaussianCM]
  rw [hzero] at hsplit
  unfold g at hsplit
  simpa [S, L] using hsplit

/-- The nonzero-frequency part of one residue transform is bounded by the zero-removed
Gaussian tail on the dual lattice. -/
theorem rayResidueDualGaussian_tail_bound [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥) (c : index K → ℝ)
    (r : acceptedResidues m) {a a₀ δ : ℝ}
    (ha₀ : 0 < a₀) (ha₀a : a₀ ≤ a) (hδ : 0 < δ)
    (hca : ∀ i, a ≤ (c i)⁻¹)
    (hδL : ∀ w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
      (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)),
        w ≠ 0 → δ ≤ ‖(w : EuclideanSpace ℝ (index K))‖) :
    ‖∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
        (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)),
        if w = 0 then 0 else
          Real.fourierChar (⟪embeddingCoords K
              (algebraMap (𝓞 K) K
                (acceptedResidueLift m J
                  ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1),
              (w : EuclideanSpace ℝ (index K))⟫) •
            ((Real.sqrt (∏ i, c i))⁻¹ •
              weightedGaussianCM (fun i => (c i)⁻¹)
                (w : EuclideanSpace ℝ (index K)))‖ ≤
      |(Real.sqrt (∏ i, c i))⁻¹| *
        (Real.exp (-Real.pi * (a - a₀) * δ ^ 2) *
          ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
            (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)),
            Real.exp (-Real.pi * ∑ i : index K, a₀ *
              ((w : EuclideanSpace ℝ (index K)) i) ^ 2)) := by
  classical
  let L := ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
    (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ))
  let shift := embeddingCoords K (algebraMap (𝓞 K) K
    (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1)
  let S : ℝ := (Real.sqrt (∏ i, c i))⁻¹
  let g : L → ℝ := fun w =>
    Real.exp (-Real.pi * ∑ i : index K, (c i)⁻¹ *
      ((w : EuclideanSpace ℝ (index K)) i) ^ 2)
  let phase : L → ℂ := fun w =>
    Real.fourierChar (⟪shift, (w : EuclideanSpace ℝ (index K))⟫)
  let tail : L → ℂ := fun w =>
    if w = 0 then 0 else phase w • (S • weightedGaussianCM (fun i => (c i)⁻¹)
      (w : EuclideanSpace ℝ (index K)))
  have hreal : Summable g := by
    exact DedekindResidue.summable_real_weightedGaussian L ha₀
      (fun i => le_trans ha₀a (hca i))
  have hnorm : Summable (fun w : L => ‖tail w‖) := by
    apply (hreal.mul_left |S|).of_nonneg_of_le
    · intro w
      exact norm_nonneg _
    · intro w
      by_cases hw : w = 0
      · simp [tail, hw]
        positivity
      · simp [tail, hw, phase, S, g, _root_.norm_smul,
          norm_weightedGaussianCM_apply, Real.norm_eq_abs]
  have hnorm_eq : (∑' w : L, ‖tail w‖) =
      |S| * ∑' w : L, if w = 0 then 0 else g w := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro w
    by_cases hw : w = 0
    · simp [tail, hw]
    · simp [tail, hw, phase, S, g, _root_.norm_smul,
        norm_weightedGaussianCM_apply, Real.norm_eq_abs]
  have htail := DedekindResidue.tsum_ite_gaussian_tail L ha₀ ha₀a hδ hδL
    (fun i => hca i)
  calc
    ‖∑' w : L, tail w‖ ≤ ∑' w : L, ‖tail w‖ := norm_tsum_le_tsum_norm hnorm
    _ = |S| * ∑' w : L, if w = 0 then 0 else g w := hnorm_eq
    _ ≤ |S| * (Real.exp (-Real.pi * (a - a₀) * δ ^ 2) *
        ∑' w : L, Real.exp (-Real.pi * ∑ i : index K, a₀ *
          ((w : EuclideanSpace ℝ (index K)) i) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left htail (abs_nonneg _)

/-- Summing over the accepted residues leaves the common zero-frequency coefficient and an
exponentially bounded dual tail. -/
theorem rayTheta_poisson_error_bound [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J)
    (hMJ : modulusIdeal m * J ≠ ⊥) (c : InfinitePlace K → ℝ)
    {aC B a a₀ δ : ℝ} (haC : 0 < aC) (hcaC : ∀ i, aC ≤ placeWeights K c i)
    (hB : 0 < B) (hcB : ∀ i, placeWeights K c i ≤ B)
    (ha₀ : 0 < a₀) (ha₀a : a₀ ≤ a) (hδ : 0 < δ)
    (hca : ∀ i, a ≤ (placeWeights K c i)⁻¹)
    (hδL : ∀ w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
      (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)),
        w ≠ 0 → δ ≤ ‖(w : EuclideanSpace ℝ (index K))‖) :
    ‖((rayTheta m J hcop c : ℝ) : ℂ) -
        (((residueCount m : ℝ) *
          (ZLattice.covolume
            (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)) volume)⁻¹ *
          (Real.sqrt (∏ i, placeWeights K c i))⁻¹ : ℝ) : ℂ)‖ ≤
      (residueCount m : ℝ) *
        |(ZLattice.covolume
          (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)) volume)⁻¹| *
        |(Real.sqrt (∏ i, placeWeights K c i))⁻¹| *
        (Real.exp (-Real.pi * (a - a₀) * δ ^ 2) *
          ∑' w : ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
            (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)),
            Real.exp (-Real.pi * ∑ i : index K, a₀ *
              ((w : EuclideanSpace ℝ (index K)) i) ^ 2)) := by
  classical
  have ha : 0 < a := lt_of_lt_of_le ha₀ ha₀a
  let D := ArtinPrimitiveRoots.Hecke.Theta.dualZLattice
    (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ))
  let P : ℝ := (ZLattice.covolume
    (idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)) volume)⁻¹
  let S : ℝ := (Real.sqrt (∏ i, placeWeights K c i))⁻¹
  let T : ℝ := Real.exp (-Real.pi * (a - a₀) * δ ^ 2)
  let V : ℝ := ∑' w : D, Real.exp (-Real.pi * ∑ i : index K,
    a₀ * ((w : EuclideanSpace ℝ (index K)) i) ^ 2)
  let tail (r : acceptedResidues m) : ℂ :=
    ∑' w : D, if w = 0 then 0 else
      Real.fourierChar (⟪embeddingCoords K
        (algebraMap (𝓞 K) K
          (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1),
        (w : EuclideanSpace ℝ (index K))⟫) •
        (S • weightedGaussianCM (fun i => (placeWeights K c i)⁻¹)
          (w : EuclideanSpace ℝ (index K)))
  have htail (r : acceptedResidues m) : ‖tail r‖ ≤ |S| * (T * V) := by
    simpa [tail, S, T, V, D] using
      rayResidueDualGaussian_tail_bound m J hcop hMJ (placeWeights K c) r
        ha₀ ha₀a hδ hca hδL
  have hpoisson : ((rayTheta m J hcop c : ℝ) : ℂ) =
      ∑ r : acceptedResidues m, P •
        ∑' w : D, Real.fourierChar (⟪embeddingCoords K
            (algebraMap (𝓞 K) K
              (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1),
            (w : EuclideanSpace ℝ (index K))⟫) •
          (S • weightedGaussianCM (fun i => (placeWeights K c i)⁻¹)
            (w : EuclideanSpace ℝ (index K))) := by
    simpa [P, S, D] using
      rayTheta_poisson m J hcop hMJ c haC hcaC hB hcB
  have hsplit : ∀ r : acceptedResidues m,
      (∑' w : D, Real.fourierChar (⟪embeddingCoords K
          (algebraMap (𝓞 K) K
            (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1),
          (w : EuclideanSpace ℝ (index K))⟫) •
        (S • weightedGaussianCM (fun i => (placeWeights K c i)⁻¹)
          (w : EuclideanSpace ℝ (index K)))) = (S : ℂ) + tail r := by
    intro r
    simpa [tail, S, D] using
      rayResidueDualGaussian_split_zero m J hcop hMJ (placeWeights K c) r ha hca
  have hconst : ∑ r : acceptedResidues m, P • (S : ℂ) =
      (((residueCount m : ℝ) * P * S : ℝ) : ℂ) := by
    simp [residueCount, Nat.card_eq_fintype_card, P, S,
      Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
    ring
  have hsum : ∑ r : acceptedResidues m, P • ((S : ℂ) + tail r) =
      (((residueCount m : ℝ) * P * S : ℝ) : ℂ) + P • ∑ r : acceptedResidues m, tail r := by
    calc
      ∑ r : acceptedResidues m, P • ((S : ℂ) + tail r) =
          ∑ r : acceptedResidues m, (P • (S : ℂ) + P • tail r) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [smul_add]
      _ = (∑ r : acceptedResidues m, P • (S : ℂ)) +
          ∑ r : acceptedResidues m, P • tail r := by rw [Finset.sum_add_distrib]
      _ = (((residueCount m : ℝ) * P * S : ℝ) : ℂ) +
          P • ∑ r : acceptedResidues m, tail r := by
            rw [hconst, ← Finset.smul_sum]
  have herror : ((rayTheta m J hcop c : ℝ) : ℂ) -
      (((residueCount m : ℝ) * P * S : ℝ) : ℂ) =
        P • ∑ r : acceptedResidues m, tail r := by
    rw [hpoisson]
    have htailExpr : ∑ r : acceptedResidues m, P •
        ∑' w : D, Real.fourierChar (⟪embeddingCoords K
            (algebraMap (𝓞 K) K
              (acceptedResidueLift m J ((isCoprimeTo_iff_sup m J).mp hcop |>.2) r).1),
            (w : EuclideanSpace ℝ (index K))⟫) •
          (S • weightedGaussianCM (fun i => (placeWeights K c i)⁻¹)
            (w : EuclideanSpace ℝ (index K))) =
          ∑ r : acceptedResidues m, P • ((S : ℂ) + tail r) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [hsplit]
    rw [htailExpr, hsum]
    exact add_sub_cancel_left _ _
  have hsumTail : ‖∑ r : acceptedResidues m, tail r‖ ≤
      (residueCount m : ℝ) * (|S| * (T * V)) := by
    calc
      ‖∑ r : acceptedResidues m, tail r‖ ≤
          ∑ r : acceptedResidues m, ‖tail r‖ := norm_sum_le _ _
      _ ≤ ∑ r : acceptedResidues m, |S| * (T * V) :=
          Finset.sum_le_sum (fun r _ => htail r)
      _ = (residueCount m : ℝ) * (|S| * (T * V)) := by
          simp [residueCount, Nat.card_eq_fintype_card, Finset.sum_const, nsmul_eq_mul]
  rw [herror, _root_.norm_smul, Real.norm_eq_abs]
  calc
    |P| * ‖∑ r : acceptedResidues m, tail r‖ ≤
        |P| * ((residueCount m : ℝ) * (|S| * (T * V))) :=
          mul_le_mul_of_nonneg_left hsumTail (abs_nonneg _)
    _ = (residueCount m : ℝ) * |P| * |S| * (T * V) := by ring

set_option maxHeartbeats 5000000 in
private theorem exists_rayTheta_small_bound [IsTotallyComplex K]
    (m : RayClassModulus K) (J : Ideal (𝓞 K)) (hcop : IsCoprimeTo m J) :
    ∃ C c' t₀ : ℝ, 0 < C ∧ 0 < c' ∧ 0 < t₀ ∧
      ∀ {t : ℝ}, 0 < t → t ≤ t₀ →
        ∀ u ∈ ZSpan.fundamentalDomain
          ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
          |rayTheta m J hcop (heckeWeights K
              ((idealNormR K (idealUnit J hcop.1))⁻¹ ^ 2 * heckeBeta K * t) u) -
            ((residueCount m : ℝ) / (modulusNorm m : ℝ) * t ^ (-(1 : ℝ) / 2))| ≤
            C * t ^ (-(1 : ℝ) / 2) *
              Real.exp (-c' * t ^ (-(1 : ℝ) / (Module.finrank ℚ K))) := by
  classical
  let I : NumberFieldFractionalIdealGroup K := idealUnit J hcop.1
  let scale : ℝ := (idealNormR K I)⁻¹ ^ 2 * heckeBeta K
  let q : ℝ := (1 : ℝ) / (Module.finrank ℚ K)
  have hN : 0 < idealNormR K I := DedekindResidue.idealNormR_pos K I
  have hβ : 0 < heckeBeta K := DedekindResidue.heckeBeta_pos K
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos one_pos (finrank_pos_real K)
  have hMJ : modulusIdeal m * J ≠ ⊥ := by
    intro h
    exact (Ideal.mul_eq_bot.mp h).elim (modulusIdeal_ne_bot m) hcop.1
  let L := idealZLattice K (idealUnit (modulusIdeal m * J) hMJ)
  let D := ArtinPrimitiveRoots.Hecke.Theta.dualZLattice L
  obtain ⟨δ, hδ, hδL⟩ := DedekindResidue.exists_pos_norm_le_of_discrete D
  obtain ⟨R, hR, hbox⟩ := DedekindResidue.exists_box_coord_bound K
  let U : ℝ := Real.exp (2 * (Fintype.card (InfinitePlace K) : ℝ) * R)
  let A : ℝ := (2 * U)⁻¹
  let T₀ : ℝ := A ^ (Module.finrank ℚ K)
  let t₀ : ℝ := T₀ / scale
  have hU : 0 < U := Real.exp_pos _
  have hA : 0 < A := by positivity
  have hT₀ : 0 < T₀ := pow_pos hA _
  have ht₀ : 0 < t₀ := div_pos hT₀ hscale
  have hn : Module.finrank ℚ K ≠ 0 :=
    Nat.ne_of_gt (Module.finrank_pos (R := ℚ) (M := K))
  have hT₀q : T₀ ^ q = A := by
    simpa [T₀, q, one_div] using Real.pow_rpow_inv_natCast hA.le hn
  let V : ℝ := ∑' w : D, Real.exp (-Real.pi * ∑ i : index K,
    ((w : EuclideanSpace ℝ (index K)) i) ^ 2)
  have hV : 0 ≤ V := by
    apply tsum_nonneg
    intro w
    exact (Real.exp_pos _).le
  let C : ℝ := 1 + (residueCount m : ℝ) / (modulusNorm m : ℝ) * V
  let c' : ℝ := Real.pi * δ ^ 2 / (2 * U * scale ^ q)
  have hC : 0 < C := by
    dsimp [C]
    have hmod : 0 < (modulusNorm m : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (modulusNorm_ne_zero m)
    positivity
  have hc' : 0 < c' := by
    dsimp [c']
    positivity
  have hmod : 0 < (modulusNorm m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (modulusNorm_ne_zero m)
  refine ⟨C, c', t₀, hC, hc', ht₀, ?_⟩
  intro t ht ht₀' u hu
  let T : ℝ := scale * t
  let B : ℝ := U * T ^ q
  let a : ℝ := B⁻¹
  let aC : ℝ := Real.exp (-(2 * (Fintype.card (InfinitePlace K) : ℝ) * R)) * T ^ q
  have hT : 0 < T := mul_pos hscale ht
  have hTle : T ≤ T₀ := by
    calc
      T = scale * t := rfl
      _ ≤ scale * t₀ := mul_le_mul_of_nonneg_left ht₀' hscale.le
      _ = T₀ := by dsimp [t₀]; field_simp [ne_of_gt hscale]
  have hTq : T ^ q ≤ A := by
    calc
      T ^ q ≤ T₀ ^ q := Real.rpow_le_rpow hT.le hTle hq.le
      _ = A := hT₀q
  have hB : 0 < B := by dsimp [B]; positivity
  have hBsmall : B ≤ 1 / 2 := by
    dsimp [B]
    calc
      U * T ^ q ≤ U * A := mul_le_mul_of_nonneg_left hTq hU.le
      _ = 1 / 2 := by dsimp [A]; field_simp [hU.ne']
  have hBinv : 2 ≤ B⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hBsmall (inv_nonneg.mpr hB.le)
    rw [mul_inv_cancel₀ hB.ne'] at hmul
    norm_num at hmul
    nlinarith [hmul]
  have ha₀a : (1 : ℝ) ≤ a := by
    dsimp [a]
    linarith
  have hTq_mul : T ^ q = scale ^ q * t ^ q := by
    dsimp [T]
    exact Real.mul_rpow hscale.le ht.le
  have htailExponent :
      Real.exp (-Real.pi * (a - 1) * δ ^ 2) ≤
        Real.exp (-c' * t ^ (-q)) := by
    apply Real.exp_le_exp.mpr
    have hamin : (2 * B)⁻¹ ≤ a - 1 := by
      have hrecipB : (2 * B)⁻¹ = B⁻¹ / 2 := by
        field_simp [hB.ne']
      rw [hrecipB]
      dsimp [a]
      nlinarith [hBinv]
    have hrecip : (2 * B)⁻¹ = (2 * U * scale ^ q)⁻¹ * t ^ (-q) := by
      rw [show B = U * T ^ q by rfl, hTq_mul, Real.rpow_neg ht.le]
      field_simp [ne_of_gt hU, ne_of_gt hscale]
    rw [hrecip] at hamin
    have hfactor : 0 < Real.pi * δ ^ 2 := mul_pos Real.pi_pos (pow_pos hδ 2)
    have hmul := mul_le_mul_of_nonneg_left hamin hfactor.le
    have hc'form : c' = Real.pi * δ ^ 2 * (2 * U * scale ^ q)⁻¹ := by
      dsimp [c']
      ring
    have hpositiveBound : c' * t ^ (-q) ≤ Real.pi * (a - 1) * δ ^ 2 := by
      calc
        c' * t ^ (-q) =
            (Real.pi * δ ^ 2) * ((2 * U * scale ^ q)⁻¹ * t ^ (-q)) := by
              rw [hc'form]
              ring
        _ ≤ (Real.pi * δ ^ 2) * (a - 1) := hmul
        _ = Real.pi * (a - 1) * δ ^ 2 := by ring
    have hneg := neg_le_neg hpositiveBound
    nlinarith
  let S : ℝ := (Real.sqrt (∏ i, placeWeights K
    (heckeWeights K T u) i))⁻¹
  have hprod : ∏ i, placeWeights K (heckeWeights K T u) i = T :=
    DedekindResidue.prod_placeWeights_heckeWeights K hT u
  have hrootT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hweightsLower : ∀ w : InfinitePlace K,
      aC ≤ heckeWeights K T u w := by
    intro w
    have hbase := DedekindResidue.le_heckeWeights_of_bounded K hR
      (hbox u hu) hT.le w
    simpa [aC, q] using hbase
  have hweightsUpper : ∀ w : InfinitePlace K,
      heckeWeights K T u w ≤ B := by
    intro w
    simpa [B, U, q] using heckeWeights_upper_of_bounded hR u (hbox u hu) hT w
  have hcaC : ∀ i, aC ≤ placeWeights K (heckeWeights K T u) i := by
    rintro (w | ⟨w, j⟩) <;> exact hweightsLower w
  have hcB : ∀ i, placeWeights K (heckeWeights K T u) i ≤ B := by
    rintro (w | ⟨w, j⟩) <;> exact hweightsUpper w
  have haC : 0 < aC := by
    dsimp [aC]
    positivity
  have hca : ∀ i, a ≤ (placeWeights K (heckeWeights K T u) i)⁻¹ := by
    intro i
    have hi : 0 < placeWeights K (heckeWeights K T u) i :=
      lt_of_lt_of_le haC (hcaC i)
    have hInv := one_div_le_one_div_of_le hi (hcB i)
    simpa only [one_div, a] using hInv
  have hpoisson := rayTheta_poisson_error_bound (m := m) (J := J) hcop hMJ
    (heckeWeights K T u) (aC := aC) (B := B) (a := a) (a₀ := 1) (δ := δ)
    haC hcaC hB hcB one_pos ha₀a hδ hca hδL
  have hcovscaled : ZLattice.covolume L volume * Real.sqrt scale =
      (modulusNorm m : ℝ) := by
    simpa [L, scale, I] using covolume_ray_scaled m J hcop hMJ
  have hrootScale : 0 < Real.sqrt scale := Real.sqrt_pos.mpr hscale
  have hcovpos : 0 < ZLattice.covolume L volume := by
    have hp : 0 < ZLattice.covolume L volume * Real.sqrt scale := by
      rw [hcovscaled]
      exact hmod
    exact (mul_pos_iff_of_pos_right hrootScale).mp hp
  have hzeroCoeff :
      (residueCount m : ℝ) * (ZLattice.covolume L volume)⁻¹ *
          (Real.sqrt T)⁻¹ =
        (residueCount m : ℝ) / (modulusNorm m : ℝ) *
          t ^ (-(1 : ℝ) / 2) := by
    rw [show Real.sqrt T = Real.sqrt scale * Real.sqrt t by
      rw [show T = scale * t by rfl, Real.sqrt_mul hscale.le]]
    have hscaleRootInv : (ZLattice.covolume L volume)⁻¹ *
        (Real.sqrt scale)⁻¹ = (modulusNorm m : ℝ)⁻¹ := by
      rw [← mul_inv, hcovscaled]
    have hsqrtInv : (Real.sqrt t)⁻¹ = t ^ (-(1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le]
      congr 1
      norm_num
    calc
      (residueCount m : ℝ) * (ZLattice.covolume L volume)⁻¹ *
          (Real.sqrt scale * Real.sqrt t)⁻¹ =
        (residueCount m : ℝ) *
          ((ZLattice.covolume L volume)⁻¹ * (Real.sqrt scale)⁻¹) *
            (Real.sqrt t)⁻¹ := by rw [mul_inv]; ring
      _ = (residueCount m : ℝ) * (modulusNorm m : ℝ)⁻¹ *
            (Real.sqrt t)⁻¹ := by rw [hscaleRootInv]
      _ = (residueCount m : ℝ) / (modulusNorm m : ℝ) *
            t ^ (-(1 : ℝ) / 2) := by
        rw [hsqrtInv]
        congr 3 <;> ring
  have hPabs : |(ZLattice.covolume L volume)⁻¹| =
      (ZLattice.covolume L volume)⁻¹ := abs_of_pos (inv_pos.mpr hcovpos)
  have hSabs : |(Real.sqrt (∏ i, placeWeights K
      (heckeWeights K T u) i))⁻¹| = (Real.sqrt T)⁻¹ := by
    rw [hprod, abs_of_pos (inv_pos.mpr hrootT)]
  have hzeroCoeffAbs :
      (residueCount m : ℝ) * |(ZLattice.covolume L volume)⁻¹| *
          |(Real.sqrt (∏ i, placeWeights K (heckeWeights K T u) i))⁻¹| =
        (residueCount m : ℝ) / (modulusNorm m : ℝ) *
          t ^ (-(1 : ℝ) / 2) := by
    rw [hPabs, hSabs, hzeroCoeff]
  have hzeroCoeffRaw :
      (residueCount m : ℝ) * (ZLattice.covolume L volume)⁻¹ *
          (Real.sqrt (∏ i, placeWeights K (heckeWeights K T u) i))⁻¹ =
        (residueCount m : ℝ) / (modulusNorm m : ℝ) *
          t ^ (-(1 : ℝ) / 2) := by
    rw [hprod]
    exact hzeroCoeff
  have hcoefNonneg :
      0 ≤ (residueCount m : ℝ) / (modulusNorm m : ℝ) *
        t ^ (-(1 : ℝ) / 2) := by positivity
  have hpointC :
      |rayTheta m J hcop (heckeWeights K T u) -
          (residueCount m : ℝ) / (modulusNorm m : ℝ) * t ^ (-(1 : ℝ) / 2)| ≤
        ((residueCount m : ℝ) / (modulusNorm m : ℝ) *
          t ^ (-(1 : ℝ) / 2)) *
          (Real.exp (-c' * t ^ (-q)) * V) := by
    have hcomplex := hpoisson
    rw [hzeroCoeffAbs, hzeroCoeffRaw] at hcomplex
    have hcast : (((rayTheta m J hcop (heckeWeights K T u) : ℝ) : ℂ) -
        (((residueCount m : ℝ) / (modulusNorm m : ℝ) *
          t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)) =
        ((rayTheta m J hcop (heckeWeights K T u) -
          (residueCount m : ℝ) / (modulusNorm m : ℝ) *
            t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real] at hcomplex
    have hcomplex' :
        |rayTheta m J hcop (heckeWeights K T u) -
            (residueCount m : ℝ) / (modulusNorm m : ℝ) * t ^ (-(1 : ℝ) / 2)| ≤
          ((residueCount m : ℝ) / (modulusNorm m : ℝ) *
            t ^ (-(1 : ℝ) / 2)) *
            (Real.exp (-Real.pi * (a - 1) * δ ^ 2) * V) := by
      simpa [V] using hcomplex
    calc
      |rayTheta m J hcop (heckeWeights K T u) -
          (residueCount m : ℝ) / (modulusNorm m : ℝ) * t ^ (-(1 : ℝ) / 2)|
        ≤ ((residueCount m : ℝ) / (modulusNorm m : ℝ) *
          t ^ (-(1 : ℝ) / 2)) *
          (Real.exp (-Real.pi * (a - 1) * δ ^ 2) * V) := hcomplex'
      _ ≤ ((residueCount m : ℝ) / (modulusNorm m : ℝ) *
          t ^ (-(1 : ℝ) / 2)) *
          (Real.exp (-c' * t ^ (-q)) * V) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right htailExponent hV
        · exact hcoefNonneg
  have htailBound :
      |rayTheta m J hcop (heckeWeights K T u) -
          (residueCount m : ℝ) / (modulusNorm m : ℝ) * t ^ (-(1 : ℝ) / 2)| ≤
        C * t ^ (-(1 : ℝ) / 2) * Real.exp (-c' * t ^ (-q)) := by
    calc
      |rayTheta m J hcop (heckeWeights K T u) -
          (residueCount m : ℝ) / (modulusNorm m : ℝ) * t ^ (-(1 : ℝ) / 2)|
        ≤ ((residueCount m : ℝ) / (modulusNorm m : ℝ) *
          t ^ (-(1 : ℝ) / 2)) *
          (Real.exp (-c' * t ^ (-q)) * V) := hpointC
      _ = ((residueCount m : ℝ) / (modulusNorm m : ℝ) * V) *
          (t ^ (-(1 : ℝ) / 2) * Real.exp (-c' * t ^ (-q))) := by ring
      _ ≤ C * t ^ (-(1 : ℝ) / 2) * Real.exp (-c' * t ^ (-q)) := by
        dsimp [C]
        have hfactor : 0 ≤ t ^ (-(1 : ℝ) / 2) * Real.exp (-c' * t ^ (-q)) := by
          positivity
        have hleft : 0 ≤ (residueCount m : ℝ) / (modulusNorm m : ℝ) * V := by
          positivity
        have hsum : (residueCount m : ℝ) / (modulusNorm m : ℝ) * V ≤
            1 + (residueCount m : ℝ) / (modulusNorm m : ℝ) * V := by linarith
        calc
          ((residueCount m : ℝ) / (modulusNorm m : ℝ) * V) *
              (t ^ (-(1 : ℝ) / 2) * Real.exp (-c' * t ^ (-q)))
            ≤ (1 + (residueCount m : ℝ) / (modulusNorm m : ℝ) * V) *
                (t ^ (-(1 : ℝ) / 2) * Real.exp (-c' * t ^ (-q))) :=
                  mul_le_mul_of_nonneg_right hsum hfactor
          _ = (1 + (residueCount m : ℝ) / (modulusNorm m : ℝ) * V) *
                t ^ (-(1 : ℝ) / 2) * Real.exp (-c' * t ^ (-q)) := by ring
  have hqneg : -q = -(1 : ℝ) / (Module.finrank ℚ K : ℝ) := by
    dsimp [q]
    ring
  simpa [T, scale, I, hqneg] using htailBound

end ArtinPrimitiveRoots.Hecke

end
