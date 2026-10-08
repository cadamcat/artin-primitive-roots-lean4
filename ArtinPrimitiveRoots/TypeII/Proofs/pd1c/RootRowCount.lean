import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootFixedEstimate

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd1c_fixedRootCount_zero (u : ℕ) (V : ℝ) (S : ℕ)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₂ r₂ l₃ r₃ : ℝ)
    (hu₀ : (u : ZMod S) ≠ g₀ 0 0) : pd1c_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ = 0 := by
  have hEmpty : (pd1c_natClosedInterval (l₂ * V) (r₂ * V)).filter
      (pd1c_fixedRootPredicate u S g₀ l₃ r₃) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rcases (Finset.mem_filter.mp hv).2 with ⟨hcop, c, d, hdet, hc0, hcu, hcl, hcr, hgu, hgc, hgv, hgd⟩
    exact hu₀ hgu.symm
  simp only [pd1c_fixedRootCount, hEmpty, Finset.card_empty, Nat.cast_zero]

lemma pd1c_rootResidueCount_rows (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (S : ℕ) (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : 0 ≤ l₁) (hlr₁ : l₁ ≤ r₁) (hl₂ : 0 ≤ l₂) (hlr₂ : l₂ ≤ r₂) :
    rootResidueCount U V S g₀ l₁ r₁ l₂ r₂ l₃ r₃ =
      ∑ u ∈ pd1c_natClosedInterval (l₁ * U) (r₁ * U),
        if (u : ZMod S) = g₀ 0 0 then pd1c_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ else 0 := by
  let Iu := pd1c_natClosedInterval (l₁ * U) (r₁ * U)
  let Iv := pd1c_natClosedInterval (l₂ * V) (r₂ * V)
  let T := (Iu.product Iv).filter (fun uv => pd1c_fixedRootPredicate uv.1 S g₀ l₃ r₃ uv.2)
  have hBu : 0 ≤ r₁ * U := mul_nonneg (hl₁.trans hlr₁) hU.le
  have hBv : 0 ≤ r₂ * V := mul_nonneg (hl₂.trans hlr₂) hV.le
  have hSet : {uv : ℕ × ℕ | Nat.Coprime uv.1 uv.2 ∧ l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
      l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
      ∃ c d : ℤ, (uv.1 : ℤ) * d - (uv.2 : ℤ) * c = 1 ∧
        0 ≤ c ∧ c < uv.1 ∧ l₃ ≤ (c : ℝ) / uv.1 ∧ (c : ℝ) / uv.1 ≤ r₃ ∧
          g₀ 0 0 = (uv.1 : ZMod S) ∧ g₀ 0 1 = (c : ZMod S) ∧
            g₀ 1 0 = (uv.2 : ZMod S) ∧ g₀ 1 1 = (d : ZMod S)} = (T : Set (ℕ × ℕ)) := by
    ext uv
    constructor
    · rintro ⟨hcop, hul, huh, hvl, hvh, hcd⟩
      change uv ∈ T
      have huI : uv.1 ∈ Iu := (pd1c_natClosedInterval_mem _ _ hBu _).mpr
        ⟨(le_div_iff₀ hU).mp hul, (div_le_iff₀ hU).mp huh⟩
      have hvI : uv.2 ∈ Iv := (pd1c_natClosedInterval_mem _ _ hBv _).mpr
        ⟨(le_div_iff₀ hV).mp hvl, (div_le_iff₀ hV).mp hvh⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huI, hvI⟩, hcop, hcd⟩
    · intro hmem
      change uv ∈ T at hmem
      have hdata := Finset.mem_filter.mp hmem
      obtain ⟨huI, hvI⟩ := Finset.mem_product.mp hdata.1
      obtain ⟨hul, huh⟩ := (pd1c_natClosedInterval_mem _ _ hBu _).mp huI
      obtain ⟨hvl, hvh⟩ := (pd1c_natClosedInterval_mem _ _ hBv _).mp hvI
      rcases hdata.2 with ⟨hcop, hcd⟩
      exact ⟨hcop, (le_div_iff₀ hU).mpr hul, (div_le_iff₀ hU).mpr huh,
        (le_div_iff₀ hV).mpr hvl, (div_le_iff₀ hV).mpr hvh, hcd⟩
  unfold rootResidueCount
  rw [hSet, Set.ncard_coe_finset]
  have hCard : (T.card : ℝ) = ∑ u ∈ Iu, pd1c_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ := by
    calc
      _ = ∑ uv ∈ T, (1 : ℝ) := by simp
      _ = ∑ uv ∈ Iu.product Iv, if pd1c_fixedRootPredicate uv.1 S g₀ l₃ r₃ uv.2 then (1 : ℝ) else 0 := by rw [Finset.sum_filter]
      _ = ∑ u ∈ Iu, ∑ v ∈ Iv, if pd1c_fixedRootPredicate u S g₀ l₃ r₃ v then (1 : ℝ) else 0 := by
        rw [Finset.product_eq_sprod, Finset.sum_product]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        rfl
  rw [hCard]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hu₀ : (u : ZMod S) = g₀ 0 0
  · rw [if_pos hu₀]
  · rw [if_neg hu₀, pd1c_fixedRootCount_zero u V S g₀ l₂ r₂ l₃ r₃ hu₀]

end ArtinPrimitiveRoots.TypeII.PD
