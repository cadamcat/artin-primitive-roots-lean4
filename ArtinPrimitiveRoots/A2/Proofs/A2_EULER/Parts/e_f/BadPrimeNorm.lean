import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_f
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη}
variable (η : HeckeChar F) (U : FrequencyData S D η)

private theorem exterior_product_formula (D : FieldData F) (S : SData F CE condη)
    (x : S.R) (hx : (x : F) ≠ 0) :
    S.absS (S.diag (x : F)) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) = 1 := by
  have : IsTotallyComplex F := D.isTotallyComplex
  have hprod := prod_abs_eq_one hx
  have hf_supp : (Function.mulSupport fun v => ‖FinitePlace.embedding v (x : F)‖).Finite :=
    finitePlace_mk_hasFiniteMulSupport hx
  have h_split : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (x : F)‖) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf_supp Set.inter_subset_right)
      (f := fun v => ‖FinitePlace.embedding v (x : F)‖)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have h_prod_decomp : (∏ᶠ w : FinitePlace F, w (x : F)) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (x : F)‖) = _
    exact h_split
  rw [h_prod_decomp] at hprod
  have h_absS : S.absS (S.diag (x : F)) =
      (∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ w : InfinitePlace F, w (x : F) ^ w.mult :=
    absS_diag_eq S (x : F)
  have h_prod_absS : S.absS (S.diag (x : F)) * (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) = 1 := by
    rw [h_absS]
    calc ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          (∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖)
      _ = (∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          ((∏ v ∈ S.Sf, ‖FinitePlace.embedding v (x : F)‖) * ∏ᶠ v ∉ S.Sf, ‖FinitePlace.embedding v (x : F)‖) := by ring
      _ = 1 := hprod
  exact h_prod_absS

private theorem bad_prime_local_norm (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (hj : frequencyValuation η U u v ≠ 0) :
    ‖FinitePlace.embedding v (U.repr u : F)‖ ≤ (qI v.asIdeal)⁻¹ := by
  let c := FractionalIdeal.count F v
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr u : F))
  have hc : 1 ≤ c := by
    have hn := (U.sixth_power_free u v hv).1
    change c.toNat ≠ 0 at hj
    dsimp [c] at *
    omega
  rw [norm_embedding_eq_absNorm_zpow v _ (U.repr_nonzero u)]
  change qI v.asIdeal ^ (-c) ≤ (qI v.asIdeal)⁻¹
  calc
    _ ≤ qI v.asIdeal ^ (-1 : ℤ) := zpow_le_zpow_right₀ (qI_prime_gt_one v).le (by omega)
    _ = _ := by simp

theorem bad_norm_product_le (u : U.U) (T : Finset (FinPlace F))
    (hout : ∀ v ∈ T, v ∉ S.Sf)
    (hbad : ∀ v ∈ T, frequencyValuation η U u v ≠ 0) :
    (∏ v ∈ T, qI v.asIdeal) ≤ U.q u := by
  classical
  let f : FinPlace F → ℝ := fun v => ‖FinitePlace.embedding v (U.repr u : F)‖
  have hf : (Function.mulSupport f).Finite := finitePlace_mk_hasFiniteMulSupport
    (U.repr_nonzero u)
  let P := hf.toFinset.filter (fun v => v ∉ S.Sf)
  have hsubset : T ⊆ P := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨hf.mem_toFinset.mpr ?_, hout v hv⟩
    change f v ≠ 1
    have hle := bad_prime_local_norm η U u v (hout v hv) (hbad v hv)
    have hi : (qI v.asIdeal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (qI_prime_gt_one v)
    exact ne_of_lt (hle.trans_lt hi)
  have hfnonneg (v : FinPlace F) : 0 ≤ f v := norm_nonneg _
  have hfle (v : FinPlace F) (hv : v ∉ S.Sf) : f v ≤ 1 :=
    norm_embedding_le_one_of_valuation_le_one v _ ((U.repr u).property v hv)
  have hrest : (∏ v ∈ P \ T, f v) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun v hv => hfnonneg v) ?_
    intro v hv
    exact hfle v (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  have hprod : (∏ v ∈ P, f v) ≤ ∏ v ∈ T, f v := by
    calc
      _ = (∏ v ∈ P \ T, f v) * ∏ v ∈ T, f v := (Finset.prod_sdiff hsubset).symm
      _ ≤ 1 * ∏ v ∈ T, f v := mul_le_mul_of_nonneg_right hrest
        (Finset.prod_nonneg (fun v hv => hfnonneg v))
      _ = _ := one_mul _
  have hlocal : (∏ v ∈ T, f v) ≤ (∏ v ∈ T, qI v.asIdeal)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_le_prod₀ (fun v hv => hfnonneg v)
    intro v hv
    exact bad_prime_local_norm η U u v (hout v hv) (hbad v hv)
  have hformula := exterior_product_formula D S (U.repr u) (U.repr_nonzero u)
  rw [← U.q_eq_absS u] at hformula
  have hfin : (∏ᶠ v ∉ S.Sf, f v) = ∏ v ∈ P, f v :=
    finprod_mem_eq_prod_filter f ((S.Sf : Set _)ᶜ) hf
  change U.q u * (∏ᶠ v ∉ S.Sf, f v) = 1 at hformula
  rw [hfin] at hformula
  have hbound : 1 ≤ U.q u * (∏ v ∈ T, qI v.asIdeal)⁻¹ := by
    calc
      1 = U.q u * (∏ v ∈ P, f v) := hformula.symm
      _ ≤ U.q u * ∏ v ∈ T, f v := mul_le_mul_of_nonneg_left hprod (U.q_pos u).le
      _ ≤ U.q u * (∏ v ∈ T, qI v.asIdeal)⁻¹ :=
        mul_le_mul_of_nonneg_left hlocal (U.q_pos u).le
  have hn : 0 < ∏ v ∈ T, qI v.asIdeal := Finset.prod_pos
    (fun v hv => lt_trans zero_lt_one (qI_prime_gt_one v))
  have hmul := mul_le_mul_of_nonneg_right hbound hn.le
  simpa [mul_assoc, inv_mul_cancel₀ hn.ne'] using hmul

end ArtinPrimitiveRoots.Proofs.e_f
