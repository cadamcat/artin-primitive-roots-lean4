import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootSwap

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd1c_rootBox_swap_upper (U V : ℝ) (hU : 2 ≤ U) (hV : 2 ≤ V) (S : ℕ)
    (g : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) :
    Prod.swap '' pd1c_rootBox U V S g l₁ r₁ l₂ r₂ l₃ r₃ ⊆
      pd1c_rootBox V U S (pd1c_rootSwapMatrix g) l₂ r₂ l₁ r₁
        (max 0 (1 - r₃ - 1 / (U * V))) (1 - l₃) := by
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  rintro uv ⟨⟨u, v⟩, hmem, rfl⟩
  rcases hmem with ⟨hcop, hul, huh, hvl, hvh, c, d, hdet, hc0, hcu, hcl, hcr, hgu, hgc, hgv, hgd⟩
  have hulo : U ≤ (u : ℝ) := by have h := (le_div_iff₀ hUp).mp hul; nlinarith
  have hvlo : V ≤ (v : ℝ) := by have h := (le_div_iff₀ hVp).mp hvl; nlinarith
  have hu2 : 2 ≤ u := by exact_mod_cast hU.trans hulo
  have hv2 : 2 ≤ v := by exact_mod_cast hV.trans hvlo
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hur : 0 < (u : ℝ) := by exact_mod_cast hup
  have hvr : 0 < (v : ℝ) := by exact_mod_cast hvp
  obtain ⟨hdet', hc0', hcv', hroot⟩ := pd1c_swapped_completion u v hu2 hv2 c d hdet hc0 hcu
  obtain ⟨hgv', hgc', hgu', hgd'⟩ := pd1c_swapped_residues u v S c d g hgu hgc hgv hgd
  have hE : 1 / ((u : ℝ) * v) ≤ 1 / (U * V) :=
    one_div_le_one_div_of_le (mul_pos hUp hVp) (mul_le_mul hulo hvlo hVp.le hur.le)
  have hEp : 0 ≤ 1 / ((u : ℝ) * v) := by positivity
  have hnew0 : 0 ≤ (((v : ℤ) - d : ℤ) : ℝ) / v :=
    div_nonneg (by exact_mod_cast hc0') hvr.le
  have hnewlo : max 0 (1 - r₃ - 1 / (U * V)) ≤ (((v : ℤ) - d : ℤ) : ℝ) / v := by
    apply max_le hnew0
    rw [hroot]
    linarith
  have hnewhi : (((v : ℤ) - d : ℤ) : ℝ) / v ≤ 1 - l₃ := by rw [hroot]; linarith
  exact ⟨hcop.symm, hvl, hvh, hul, huh, (v : ℤ) - d, (u : ℤ) - c,
    hdet', hc0', hcv', hnewlo, hnewhi, hgv', hgc', hgu', hgd'⟩

lemma pd1c_rootCount_swap_upper (U V : ℝ) (hU : 2 ≤ U) (hV : 2 ≤ V) (S : ℕ)
    (g : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : 1 ≤ l₁) (hlr₁ : l₁ ≤ r₁) (hl₂ : 1 ≤ l₂) (hlr₂ : l₂ ≤ r₂) :
    rootResidueCount U V S g l₁ r₁ l₂ r₂ l₃ r₃ ≤
      rootResidueCount V U S (pd1c_rootSwapMatrix g) l₂ r₂ l₁ r₁
        (max 0 (1 - r₃ - 1 / (U * V))) (1 - l₃) := by
  have hUp : 0 < U := by linarith
  have hVp : 0 < V := by linarith
  have hSub := pd1c_rootBox_swap_upper U V hU hV S g l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hl₂
  have hFinite := pd1c_rootBox_finite V U hVp hUp S (pd1c_rootSwapMatrix g) l₂ r₂ l₁ r₁
    (max 0 (1 - r₃ - 1 / (U * V))) (1 - l₃) (by linarith) (by linarith)
  have hInj : Function.Injective (Prod.swap : ℕ × ℕ → ℕ × ℕ) := by
    intro a b hab
    simpa only [Prod.swap_swap] using congrArg Prod.swap hab
  change ((pd1c_rootBox U V S g l₁ r₁ l₂ r₂ l₃ r₃).ncard : ℝ) ≤
    ((pd1c_rootBox V U S (pd1c_rootSwapMatrix g) l₂ r₂ l₁ r₁ (max 0 (1 - r₃ - 1 / (U * V))) (1 - l₃)).ncard : ℝ)
  exact_mod_cast Set.ncard_le_ncard_of_injOn Prod.swap (fun uv huv => hSub ⟨uv, huv, rfl⟩)
    (fun a ha b hb hab => hInj hab) hFinite

lemma pd1c_rootCount_swap_lower (U V : ℝ) (hU : 2 ≤ U) (hV : 2 ≤ V) (S : ℕ)
    (g : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : 1 ≤ l₁) (hlr₁ : l₁ ≤ r₁) (hl₂ : 1 ≤ l₂) (hlr₂ : l₂ ≤ r₂) (hl₃ : 0 ≤ l₃) :
    rootResidueCount V U S (pd1c_rootSwapMatrix g) l₂ r₂ l₁ r₁ (1 - r₃) (1 - l₃ - 1 / (U * V)) ≤
      rootResidueCount U V S g l₁ r₁ l₂ r₂ l₃ r₃ := by
  have h := pd1c_rootCount_swap_upper V U hV hU S (pd1c_rootSwapMatrix g) l₂ r₂ l₁ r₁
    (1 - r₃) (1 - l₃ - 1 / (U * V)) hl₂ hlr₂ hl₁ hlr₁
  have hL : max 0 (1 - (1 - l₃ - 1 / (U * V)) - 1 / (V * U)) = l₃ := by
    rw [mul_comm V U]
    have heq : 1 - (1 - l₃ - 1 / (U * V)) - 1 / (U * V) = l₃ := by ring
    rw [heq, max_eq_right hl₃]
  have hR : 1 - (1 - r₃) = r₃ := by ring
  simpa only [hL, hR, pd1c_rootSwapMatrix_involution] using h

end ArtinPrimitiveRoots.TypeII.PD
