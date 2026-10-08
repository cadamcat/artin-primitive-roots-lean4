import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadAbsoluteBounds
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.CollisionCounting

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII Classical
noncomputable section

/-- Finite support and a per-pair estimate give the absolute total over any pair predicate. -/
theorem finitePair_norm_sum_filtered_bound {ι : Type*} [DecidableEq ι]
    (T T₀ : Finset ι) (condition : ι → ι → Prop) (f : ι → ι → ℂ) (B : ℝ)
    (hsub : T₀ ⊆ T) (hB : 0 ≤ B)
    (hsupport : ∀ a ∈ T, ∀ b ∈ T, f a b ≠ 0 → a ∈ T₀ ∧ b ∈ T₀)
    (hNorm : ∀ a ∈ T₀, ∀ b ∈ T₀, ‖f a b‖ ≤ B) :
    (∑ a ∈ T, ∑ b ∈ T, if condition a b then ‖f a b‖ else 0) ≤
      ((((T₀ ×ˢ T₀).filter fun ab => condition ab.1 ab.2).card : ℕ) : ℝ) * B := by
  let S := (T ×ˢ T).filter fun ab => condition ab.1 ab.2
  let E := (T₀ ×ˢ T₀).filter fun ab => condition ab.1 ab.2
  have hES : E ⊆ S := by
    intro ab hab
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsub ha, hsub hb⟩, hc⟩
  have heq : (∑ a ∈ T, ∑ b ∈ T, if condition a b then ‖f a b‖ else 0) =
      ∑ ab ∈ E, ‖f ab.1 ab.2‖ := by
    calc
      _ = ∑ ab ∈ S, ‖f ab.1 ab.2‖ := by rw [Finset.sum_filter, Finset.sum_product]
      _ = _ := by
        symm
        apply Finset.sum_subset hES
        intro ab hab hn
        obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hab
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
        have hz : f ab.1 ab.2 = 0 := by
          by_contra hne
          have hs := hsupport _ ha _ hb hne
          exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hs, hc⟩)
        rw [hz, norm_zero]
  rw [heq]
  calc
    _ ≤ ∑ ab ∈ E, B := Finset.sum_le_sum (fun ab hab => by
      have hp := (Finset.mem_filter.mp hab).1
      exact hNorm ab.1 (Finset.mem_product.mp hp).1 ab.2 (Finset.mem_product.mp hp).2)
    _ = _ := by simp [E, nsmul_eq_mul]

theorem rawPairSum_eq_zero_of_eta_zero {K : ℕ} (F : PDFix K) (x Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (ta tb : Fin K → ℕ) (h : F.eta ((tupleProduct ta : ℝ) / Y) = 0 ∨
      F.eta ((tupleProduct tb : ℝ) / Y) = 0) : rawPairSum F x Y family beta ta tb = 0 := by
  rcases h with h | h <;> simp [rawPairSum, h]

theorem comparisonPairSum_eq_zero_of_eta_zero {K : ℕ} (F : PDFix K) (x Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (ta tb : Fin K → ℕ) (h : F.eta ((tupleProduct ta : ℝ) / Y) = 0 ∨
      F.eta ((tupleProduct tb : ℝ) / Y) = 0) : comparisonPairSum F x Y family beta ta tb = 0 := by
  rcases h with h | h <;> simp [comparisonPairSum, h]

/-- Eta support confines a marked tuple to the supported numeric product interval. -/
theorem markedTuple_mem_supported_of_eta {K : ℕ} (F : PDFix K) (hF : F.Valid) (x Y : ℝ)
    (hY : 0 < Y) (t : Fin K → ℕ) (ht : IsMarkedPrimeTuple x K F.a t)
    (heta : F.eta ((tupleProduct t : ℝ) / Y) ≠ 0) : t ∈ supportedTupleChoices x Y F.a := by
  have hb := hF.2.2.2.2.1.2.1 heta
  exact Finset.mem_filter.mpr ⟨mem_markedTupleChoices.mpr ht,
    ⟨by simpa only [one_mul] using (le_div_iff₀ hY).mp hb.1, (div_le_iff₀ hY).mp hb.2⟩⟩

/-- Fixed tuple normalizers are bounded independently of the growing moment length. -/
theorem tupleNormalizer_square_le {x : ℝ} {K : ℕ} (a : Fin K → ℝ) (v : ℝ)
    (hv : 0 < v) (hV : ∀ i, v ≤ bandMass x (a i)) :
    (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 ≤ (v⁻¹ ^ K) ^ 2 := by
  have hp (i : Fin K) : 0 < bandMass x (a i) := hv.trans_le (hV i)
  have hprod : (∏ i : Fin K, (bandMass x (a i))⁻¹) ≤ v⁻¹ ^ K := by
    calc
      _ ≤ ∏ i : Fin K, v⁻¹ := Finset.prod_le_prod₀
        (fun i hi => inv_nonneg.mpr (hp i).le)
        (fun i hi => (inv_le_inv₀ (hp i) hv).mpr (hV i))
      _ = _ := by simp
  exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (hp i).le)) hprod 2

end
end ArtinPrimitiveRoots.TypeII.PD
