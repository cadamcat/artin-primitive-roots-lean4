import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUniformBound

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

local instance latticeGeometryMeasurable (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance latticeGeometryBorel (v : FinPlace F) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem lattice_ball_compact_open (v : FinPlace F) (N : ℤ) :
    IsCompact (localBallInt v N) ∧ IsOpen (localBallInt v N) := by
  have hset : localBallInt v 0 = Metric.closedBall (0 : v.adicCompletion F) 1 := by
    ext x
    simpa only [localBallInt, Set.mem_ofPred_eq, WithZero.exp_zero,
      Metric.mem_closedBall, dist_zero_right] using
      (Valued.toNormedField.norm_le_one_iff (L := v.adicCompletion F)
        (Γ₀ := WithZero (Multiplicative ℤ)) (x := x)).symm
  have hzero : IsCompact (localBallInt v 0) := by
    rw [hset]
    exact isCompact_closedBall 0 1
  have hzeroOpen : IsOpen (localBallInt v 0) := by
    rw [hset]
    exact IsUltrametricDist.isOpen_closedBall (0 : v.adicCompletion F) (by norm_num)
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp N)
  have hb0 : b ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := N)
    exact hb.symm.trans (by simp only [h, map_zero])
  let e := Homeomorph.mulLeft₀ b hb0
  have hpre : (fun x : v.adicCompletion F => b * x) ⁻¹' localBallInt v N =
      localBallInt v 0 := by
    ext x
    change Valued.v (b * x) ≤ WithZero.exp N ↔ Valued.v x ≤ 1
    rw [map_mul, hb]
    simpa only [mul_one] using
      (mul_le_mul_iff_right₀ (WithZero.exp_pos (a := N)) :
        WithZero.exp N * Valued.v x ≤ WithZero.exp N * 1 ↔ Valued.v x ≤ 1)
  have himage : e '' localBallInt v 0 = localBallInt v N := by
    rw [← hpre]
    exact Set.image_preimage_eq _ e.surjective
  rw [← himage]
  exact ⟨hzero.image e.continuous, e.isOpenMap _ hzeroOpen⟩

private theorem lattice_annihilator_compact (A : AddCharData F) (v : FinPlace F)
    (hregular : LocalCharacterRegular A v) (M : ℤ) :
    IsCompact (localBallAnnihilator A v M) := by
  have hclosed : IsClosed (localBallAnnihilator A v M) := by
    have hsets : localBallAnnihilator A v M = ⋂ t ∈ localBallInt v M,
        {z : v.adicCompletion F | A.ψ v (t * z) = 1} := by
      ext z
      simp only [localBallAnnihilator, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [hsets]
    apply isClosed_biInter
    intro t _ht
    exact isClosed_eq (hregular.1.comp (continuous_const.mul continuous_id)) continuous_const
  have hex : ∃ y : v.adicCompletion F, A.ψ v y ≠ 1 := by
    by_contra h
    push Not at h
    apply hregular.2.1
    ext y
    simpa only [AddChar.one_apply] using h y
  obtain ⟨y, hy⟩ := hex
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp M)
  have hb0 : b ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := M)
    exact hb.symm.trans (by simp only [h, map_zero])
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  let R := ‖y‖ / ‖b‖ + 1
  have hR : 0 < R := add_pos_of_nonneg_of_pos
    (div_nonneg (norm_nonneg y) (norm_nonneg b)) zero_lt_one
  have hratio : ‖y‖ / ‖b‖ < R := by dsimp only [R]; linarith
  have houter : localBallAnnihilator A v M ⊆ Metric.closedBall (0 : v.adicCompletion F) R := by
    intro z hz
    by_contra h
    have hzr : R < ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using h
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hR.trans hzr)
    have htest : ‖y / z‖ ≤ ‖b‖ := by
      rw [norm_div]
      apply le_trans (div_le_div_of_nonneg_left (norm_nonneg y) hR hzr.le)
      apply le_of_lt
      apply (div_lt_iff₀ hR).mpr
      simpa only [mul_comm] using (div_lt_iff₀ hbnorm).mp hratio
    have ht : y / z ∈ localBallInt v M := by
      change Valued.v (y / z) ≤ WithZero.exp M
      rw [← hb]
      exact (Valued.toNormedField.norm_le_iff (L := v.adicCompletion F)
        (Γ₀ := WithZero (Multiplicative ℤ))).mp htest
    apply hy
    simpa only [div_mul_cancel₀ _ hz0] using hz (y / z) ht
  exact (isCompact_closedBall (0 : v.adicCompletion F) R).of_isClosed_subset hclosed houter

/-- A concrete small compact open subgroup has trivial quadratic phase and compact
bilinear annihilator. A valuation bound makes the quadratic error integral; character
nontriviality bounds the annihilator, and multiplication by 2*a transports compactness.
Supplies the hypotheses of compact-subgroup averaging. -/
theorem local_quadratic_phase_small_subgroup (A : AddCharData F)
    (v : FinPlace F) (hregular : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) :
    ∃ K : AddSubgroup (v.adicCompletion F),
      IsCompact (K : Set (v.adicCompletion F)) ∧
      IsOpen (K : Set (v.adicCompletion F)) ∧
      (∀ y ∈ K, A.ψ v ((a : v.adicCompletion F) * y ^ 2) = 1) ∧
      IsCompact {x : v.adicCompletion F | ∀ y ∈ K,
        A.ψ v ((2 : v.adicCompletion F) * (a : v.adicCompletion F) * x * y) = 1} := by
  let k := WithZero.log
    ((Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (a : _))
  let M := -max k 0
  have ha : Valued.v (a : v.adicCompletion F) = WithZero.exp k :=
    (WithZero.exp_log ((map_ne_zero
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr
      a.ne_zero)).symm
  have hbound : k + 2 * M ≤ 0 := by
    have h0 : (0 : ℤ) ≤ max k 0 := le_max_right k 0
    have hk : k ≤ max k 0 := le_max_left k 0
    dsimp only [M]
    omega
  obtain ⟨hcompact, hopen⟩ := lattice_ball_compact_open v M
  refine ⟨localBallAddSubgroup v M, hcompact, hopen, ?_, ?_⟩
  · intro y hy
    apply A.integral v
    change Valued.v ((a : v.adicCompletion F) * y ^ 2) ≤ 1
    change Valued.v y ≤ WithZero.exp M at hy
    rw [map_mul, map_pow, ha, pow_two]
    calc
      WithZero.exp k * (Valued.v y * Valued.v y) ≤
          WithZero.exp k * (WithZero.exp M * WithZero.exp M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul' hy hy) (by simp)
      _ = WithZero.exp (k + 2 * M) := by
        rw [← WithZero.exp_add, ← WithZero.exp_add]
        congr 1
        ring
      _ ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.mpr hbound
      _ = 1 := WithZero.exp_zero
  · have hc : (2 : v.adicCompletion F) * (a : v.adicCompletion F) ≠ 0 :=
      mul_ne_zero (by norm_num) a.ne_zero
    let e := Homeomorph.mulLeft₀ ((2 : v.adicCompletion F) * (a : v.adicCompletion F)) hc
    have hset : {x : v.adicCompletion F | ∀ y ∈ localBallAddSubgroup v M,
        A.ψ v ((2 : v.adicCompletion F) * (a : v.adicCompletion F) * x * y) = 1} =
        e ⁻¹' localBallAnnihilator A v M := by
      ext x
      change (∀ y ∈ localBallInt v M, A.ψ v (2 * (a : v.adicCompletion F) * x * y) = 1) ↔
        ∀ y ∈ localBallInt v M, A.ψ v (y * (2 * (a : v.adicCompletion F) * x)) = 1
      have hprod : ∀ y : v.adicCompletion F,
          2 * (a : v.adicCompletion F) * x * y = y * (2 * (a : v.adicCompletion F) * x) := by
        intro y
        ring
      simp only [hprod]
    rw [hset]
    exact e.isCompact_preimage.mpr (lattice_annihilator_compact A v hregular M)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
