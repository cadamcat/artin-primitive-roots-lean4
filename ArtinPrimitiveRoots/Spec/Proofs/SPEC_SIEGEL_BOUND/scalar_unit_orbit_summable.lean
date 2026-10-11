import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Module.Free
open scoped MatrixGroups ContDiff BoundedContinuousFunction NNReal

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem scalar_mixed_norm_le
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
    have hsup : Finset.univ.sup
        (fun w : {w : InfinitePlace F // NumberField.InfinitePlace.IsComplex w} =>
          ‖(NumberField.mixedEmbedding F a).2 w‖₊) ≤ ⟨S, hS⟩ := by
      apply Finset.sup_le
      intro w hw
      exact_mod_cast hcoord w.1
    exact NNReal.coe_le_coe.mpr hsup
  rw [Prod.norm_def, hreal, norm_zero]
  exact max_le_iff.mpr ⟨hS, hcomplex⟩

private lemma absFieldNorm_nonneg_scalar (a : F) : 0 ≤ absFieldNorm F a := by
  unfold absFieldNorm
  exact Finset.prod_nonneg fun w hw => sq_nonneg ‖w.embedding a‖

private lemma scalar_embedding_norm_prod_sq (a : F) :
    (∏ w : InfinitePlace F, ‖w.embedding a‖) ^ 2 = absFieldNorm F a := by
  unfold absFieldNorm
  rw [← Finset.prod_pow]

private lemma scalar_denominator_bound_unit (D : ℕ) {a : F}
    (ha : HasDenominatorBound F D a) (ε : (𝓞 F)ˣ) :
    HasDenominatorBound F D (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) := by
  rcases ha with ⟨b, hb⟩
  refine ⟨(ε : 𝓞 F) * b, ?_⟩
  calc
    (D : F) * (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) =
        algebraMap (𝓞 F) F (ε : 𝓞 F) * ((D : F) * a) := by ring
    _ = algebraMap (𝓞 F) F (ε : 𝓞 F) * algebraMap (𝓞 F) F b := by rw [hb]
    _ = algebraMap (𝓞 F) F ((ε : 𝓞 F) * b) := by rw [map_mul]

private lemma scalar_rpow_compare (r β K P N M : ℝ)
    (hr : 0 < r) (hβ : 0 < β) (hK : 0 < K) (hP : 0 < P)
    (hN : 0 < N) (hM : 0 < M) (hNprod : N = P ^ 2)
    (hMbound : M ≤ K * P ^ r⁻¹) :
    N ^ (-β) ≤ K ^ (2 * r * β) * M ^ (-(2 * r * β)) := by
  have hq : 0 < 2 * r * β := mul_pos (mul_pos (by norm_num) hr) hβ
  have hexp : r⁻¹ * (2 * r * β) = 2 * β := by field_simp [hr.ne']
  have hPpow : N ^ β = P ^ (2 * β) := by
    calc
      N ^ β = (P ^ 2) ^ β := by rw [hNprod]
      _ = P ^ (2 * β) := (Real.rpow_natCast_mul (le_of_lt hP) 2 β).symm
  have hpow : M ^ (2 * r * β) ≤ K ^ (2 * r * β) * N ^ β := by
    calc
      M ^ (2 * r * β) ≤ (K * P ^ r⁻¹) ^ (2 * r * β) :=
        Real.rpow_le_rpow (le_of_lt hM) hMbound hq.le
      _ = K ^ (2 * r * β) * (P ^ r⁻¹) ^ (2 * r * β) := by
        rw [Real.mul_rpow (le_of_lt hK)
          (Real.rpow_nonneg (le_of_lt hP) r⁻¹)]
      _ = K ^ (2 * r * β) * P ^ (2 * β) := by
        rw [← Real.rpow_mul (le_of_lt hP) r⁻¹ (2 * r * β), hexp]
      _ = K ^ (2 * r * β) * N ^ β := by
        rw [← hPpow]
  have hdiv : 1 / N ^ β ≤ K ^ (2 * r * β) / M ^ (2 * r * β) :=
    (div_le_div_iff₀ (Real.rpow_pos_of_pos hN β)
      (Real.rpow_pos_of_pos hM (2 * r * β))).2 (by simpa using hpow)
  calc
    N ^ (-β) = 1 / N ^ β := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.inv_rpow hN.le]
      simp
    _ ≤ K ^ (2 * r * β) / M ^ (2 * r * β) := hdiv
    _ = K ^ (2 * r * β) * M ^ (-(2 * r * β)) := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.inv_rpow hM.le]
      simp [div_eq_mul_inv]

/-- Scalar norm weights converge on any family with distinct unit orbits for
exponent greater than one. Scalar variant of
R5. Uses `R4_unit_balance` and Mathlib scalar lattice p-series; feeds
`balanced_denominator_rows_bound`. The row theorem R5 alone has too large a threshold. -/
theorem scalar_unit_orbit_summable (D : ℕ) (hD : 0 < D) (β : ℝ) (hβ : 1 < β)
    {ι : Type*} (c : ι → F)
    (hcD : ∀ i, HasDenominatorBound F D (c i)) (hc0 : ∀ i, c i ≠ 0)
    (huniq : ∀ i j, scalarUnitAssociated (c i) (c j) → i = j) :
    Summable (fun i => Real.rpow (absFieldNorm F (c i)) (-β)) := by
  classical
  let r : ℝ := placeCount F
  have hr : 0 < r := by
    dsimp [r, placeCount]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace F))
  let Etop : Subgroup ((𝓞 F)ˣ) := ⊤
  letI : Etop.FiniteIndex := ⟨by dsimp [Etop]; simp⟩
  obtain ⟨B, hB, hbal⟩ := R4_unit_balance (F := F) Etop
  let t : ι → InfinitePlace F → ℝ := fun i w => ‖w.embedding (c i)‖
  have ht (i : ι) (w : InfinitePlace F) : 0 < t i w := by
    dsimp [t]
    apply norm_pos_iff.mpr
    exact (map_ne_zero_iff _ w.embedding.injective).mpr (hc0 i)
  let ε : ι → (𝓞 F)ˣ := fun i => Classical.choose (hbal (t i) (ht i))
  have hεbal (i : ι) (w : InfinitePlace F) :=
    (Classical.choose_spec (hbal (t i) (ht i))).2 w
  let e : ι → F := fun i => algebraMap (𝓞 F) F (ε i : 𝓞 F)
  let u : ι → F := fun i => e i * c i
  let P : ι → ℝ := fun i => ∏ w : InfinitePlace F, t i w
  have hPpos (i : ι) : 0 < P i := by
    dsimp [P]
    exact Finset.prod_pos fun w hw => ht i w
  have hPlog (i : ι) : Real.log (P i) =
      ∑ w : InfinitePlace F, Real.log (t i w) := by
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
  have hscaledCoord (i : ι) (w : InfinitePlace F) :
      ‖w.embedding (u i)‖ ≤ Real.exp B * P i ^ r⁻¹ := by
    dsimp [u]
    rw [map_mul, norm_mul]
    simpa [t] using hbalancedUpper i w
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDfield : (D : F) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hnormD (w : InfinitePlace F) : ‖w.embedding (D : F)‖ = (D : ℝ) := by simp
  have hDcoord (i : ι) (w : InfinitePlace F) :
      ‖w.embedding ((D : F) * u i)‖ ≤ (D : ℝ) * (Real.exp B * P i ^ r⁻¹) := by
    rw [map_mul, norm_mul, hnormD]
    exact mul_le_mul_of_nonneg_left (hscaledCoord i w) hDreal.le
  let K : ℝ := (D : ℝ) * Real.exp B
  have hK : 0 < K := mul_pos hDreal (Real.exp_pos B)
  let L : Submodule ℤ (NumberField.mixedEmbedding.mixedSpace F) :=
    NumberField.mixedEmbedding.integerLattice F
  have hpointMem (i : ι) :
      NumberField.mixedEmbedding F ((D : F) * u i) ∈ L := by
    obtain ⟨a, ha⟩ := scalar_denominator_bound_unit D (hcD i) (ε i)
    change NumberField.mixedEmbedding F ((D : F) * u i) ∈
      NumberField.mixedEmbedding.integerLattice F
    rw [ha]
    change NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) ∈
      LinearMap.range ((NumberField.mixedEmbedding F).comp
        (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
    exact LinearMap.mem_range.mpr ⟨a, rfl⟩
  let point : ι → NumberField.mixedEmbedding.mixedSpace F :=
    fun i => NumberField.mixedEmbedding F ((D : F) * u i)
  let latticePoint : ι → L := fun i => ⟨point i, hpointMem i⟩
  have hpointNorm (i : ι) : ‖point i‖ ≤ K * P i ^ r⁻¹ := by
    dsimp [point]
    have hS : 0 ≤ (D : ℝ) * (Real.exp B * P i ^ r⁻¹) :=
      mul_nonneg hDreal.le (mul_nonneg (Real.exp_nonneg B)
        (Real.rpow_nonneg (hPpos i).le _))
    have h := scalar_mixed_norm_le ((D : F) * u i)
      ((D : ℝ) * (Real.exp B * P i ^ r⁻¹)) hS (hDcoord i)
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using h
  have hεmap (i j : ι) :
      algebraMap (𝓞 F) F (((ε i)⁻¹ * ε j : (𝓞 F)ˣ) : 𝓞 F) = (e i)⁻¹ * e j := by
    simp [e, map_mul, map_inv₀]
  have hinj : Function.Injective latticePoint := by
    intro i j hij
    apply huniq i j
    have huScaled : (D : F) * u i = (D : F) * u j :=
      NumberField.mixedEmbedding_injective F (congrArg Subtype.val hij)
    have hu : u i = u j := mul_left_cancel₀ hDfield huScaled
    refine ⟨(ε i)⁻¹ * ε j, ?_⟩
    calc
      c i = (e i)⁻¹ * (e i * c i) := by simp [heNZ i]
      _ = (e i)⁻¹ * u i := rfl
      _ = (e i)⁻¹ * u j := by rw [hu]
      _ = ((e i)⁻¹ * e j) * c j := by ring
      _ = algebraMap (𝓞 F) F (((ε i)⁻¹ * ε j : (𝓞 F)ˣ) : 𝓞 F) * c j := by
        rw [← hεmap i j]
  have hpointNZ (i : ι) : point i ≠ 0 := by
    intro hp
    have hzero : NumberField.mixedEmbedding F ((D : F) * u i) =
        NumberField.mixedEmbedding F (0 : F) := by
      simpa [point] using hp
    have hfield : (D : F) * u i = 0 := NumberField.mixedEmbedding_injective F hzero
    have huzero : u i = 0 := (mul_eq_zero.mp hfield).resolve_left hDfield
    have hczero : c i = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (heNZ i)
      simpa [u, e] using huzero
    exact hc0 i hczero
  have hpointNormPos (i : ι) : 0 < ‖point i‖ := norm_pos_iff.mpr (hpointNZ i)
  have hnormpos (i : ι) : 0 < ‖(latticePoint i : L)‖ := by
    simpa [latticePoint] using hpointNormPos i
  have hnormbound (i : ι) : ‖(latticePoint i : L)‖ ≤ K * P i ^ r⁻¹ := by
    simpa [latticePoint] using hpointNorm i
  letI : Finite (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :=
    Module.Finite.finite_basis (Module.Free.chooseBasis ℤ (𝓞 F))
  letI : DiscreteTopology L := by
    change DiscreteTopology (NumberField.mixedEmbedding.integerLattice F)
    infer_instance
  letI : IsZLattice ℝ L := by
    change IsZLattice ℝ (NumberField.mixedEmbedding.integerLattice F)
    infer_instance
  have hLrank : Module.finrank ℤ L = 2 * Fintype.card (InfinitePlace F) := by
    rw [ZLattice.rank ℝ L, NumberField.mixedEmbedding.finrank,
      NumberField.IsTotallyComplex.finrank,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  have hrankR : (Module.finrank ℤ L : ℝ) = 2 * r := by
    rw [hLrank]
    dsimp [r, placeCount]
    norm_num
  have hrank : -(2 * r * β) < -(Module.finrank ℤ L : ℝ) := by
    rw [hrankR]
    nlinarith [mul_pos hr (sub_pos.mpr (show 1 < β by exact hβ))]
  have hlat : Summable (fun z : L => ‖z‖ ^ (-(2 * r * β))) :=
    ZLattice.summable_norm_rpow L (-(2 * r * β)) hrank
  let fLat : L → ℝ≥0 := fun z => ‖z‖₊ ^ (-(2 * r * β))
  have hlatNN : Summable fLat := by
    apply NNReal.summable_coe.mp
    simpa [fLat, NNReal.coe_rpow, coe_nnnorm] using hlat
  have hcompNN := NNReal.summable_comp_injective hlatNN hinj
  let kLat : ℝ≥0 := ⟨K ^ (2 * r * β), by positivity⟩
  have hmajorNN : Summable (fun i => kLat * fLat (latticePoint i)) :=
    hcompNN.mul_left kLat
  have hNpos (i : ι) : 0 < absFieldNorm F (c i) := absFieldNorm_pos_of_ne_zero (hc0 i)
  have hNprod (i : ι) : absFieldNorm F (c i) = P i ^ 2 :=
    (scalar_embedding_norm_prod_sq (c i)).symm
  let targetReal : ι → ℝ := fun i => Real.rpow (absFieldNorm F (c i)) (-β)
  have targetNonneg (i : ι) : 0 ≤ targetReal i := by
    dsimp [targetReal]
    exact Real.rpow_nonneg (absFieldNorm_nonneg_scalar (c i)) _
  let targetNN : ι → ℝ≥0 := fun i => ⟨targetReal i, targetNonneg i⟩
  have hcompare (i : ι) : targetReal i ≤
      K ^ (2 * r * β) * ‖(latticePoint i : L)‖ ^ (-(2 * r * β)) := by
    dsimp [targetReal]
    exact scalar_rpow_compare r β K (P i) (absFieldNorm F (c i))
      ‖(latticePoint i : L)‖ hr (by linarith) hK (hPpos i) (hNpos i)
      (hnormpos i) (hNprod i) (hnormbound i)
  have hcompareNN (i : ι) : targetNN i ≤ kLat * fLat (latticePoint i) := by
    have htargetCoe : (targetNN i : ℝ) = targetReal i := rfl
    have hkLat : (kLat : ℝ) = K ^ (2 * r * β) := rfl
    have hfLat : (fLat (latticePoint i) : ℝ) =
        ‖(latticePoint i : L)‖ ^ (-(2 * r * β)) := by
      simp [fLat, NNReal.coe_rpow, coe_nnnorm, Submodule.coe_norm]
    have hmajorCoe : ((kLat * fLat (latticePoint i) : ℝ≥0) : ℝ) =
        K ^ (2 * r * β) * ‖(latticePoint i : L)‖ ^ (-(2 * r * β)) := by
      rw [NNReal.coe_mul, hkLat, hfLat]
    apply NNReal.coe_le_coe.mp
    rw [htargetCoe, hmajorCoe]
    exact hcompare i
  have htargetNN : Summable targetNN := NNReal.summable_of_le hcompareNN hmajorNN
  have htargetReal : Summable targetReal :=
    (NNReal.summable_mk (f := targetReal) targetNonneg).mp htargetNN
  simpa [targetReal] using htargetReal

end ArtinPrimitiveRoots.A1.Spec
