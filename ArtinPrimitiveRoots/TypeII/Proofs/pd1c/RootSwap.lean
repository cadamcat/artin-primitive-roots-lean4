import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootRowCount
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootReversal

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd1c_rootSwapMatrix {S : ℕ} (g : Matrix (Fin 2) (Fin 2) (ZMod S)) : Matrix (Fin 2) (Fin 2) (ZMod S) :=
  !![g 1 0, g 1 0 - g 1 1; g 0 0, g 0 0 - g 0 1]

lemma pd1c_rootSwapMatrix_det {S : ℕ} (g : Matrix (Fin 2) (Fin 2) (ZMod S)) (hg : Matrix.det g = 1) :
    Matrix.det (pd1c_rootSwapMatrix g) = 1 := by
  have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hg
  simp [pd1c_rootSwapMatrix, Matrix.det_fin_two]
  linear_combination h

lemma pd1c_rootSwapMatrix_involution {S : ℕ} (g : Matrix (Fin 2) (Fin 2) (ZMod S)) :
    pd1c_rootSwapMatrix (pd1c_rootSwapMatrix g) = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pd1c_rootSwapMatrix]

lemma pd1c_swapped_completion (u v : ℕ) (hu : 2 ≤ u) (hv : 2 ≤ v) (c d : ℤ)
    (hdet : (u : ℤ) * d - (v : ℤ) * c = 1) (hc0 : 0 ≤ c) (hcu : c < u) :
    (v : ℤ) * ((u : ℤ) - c) - (u : ℤ) * ((v : ℤ) - d) = 1 ∧
      0 ≤ (v : ℤ) - d ∧ (v : ℤ) - d < v ∧
      (((v : ℤ) - d : ℤ) : ℝ) / v = 1 - (c : ℝ) / u - 1 / ((u : ℝ) * v) := by
  obtain ⟨hcp, hdp, hdv⟩ := pd1c_root_completion_strict u v hu hv c d hdet hc0 hcu
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hvr : (v : ℝ) ≠ 0 := by exact_mod_cast hvp.ne'
  refine ⟨by nlinarith [hdet], by omega, by omega, ?_⟩
  have hShift := pd1c_root_reversal_identity u v hup hvp c d hdet
  push_cast
  field_simp
  have hdetR : (u : ℝ) * (d : ℝ) - (v : ℝ) * (c : ℝ) = 1 := by exact_mod_cast hdet
  nlinarith only [hdetR]

lemma pd1c_swapped_residues (u v S : ℕ) (c d : ℤ)
    (g : Matrix (Fin 2) (Fin 2) (ZMod S))
    (hgu : g 0 0 = (u : ZMod S)) (hgc : g 0 1 = (c : ZMod S))
    (hgv : g 1 0 = (v : ZMod S)) (hgd : g 1 1 = (d : ZMod S)) :
    pd1c_rootSwapMatrix g 0 0 = (v : ZMod S) ∧
      pd1c_rootSwapMatrix g 0 1 = (((v : ℤ) - d : ℤ) : ZMod S) ∧
      pd1c_rootSwapMatrix g 1 0 = (u : ZMod S) ∧
      pd1c_rootSwapMatrix g 1 1 = (((u : ℤ) - c : ℤ) : ZMod S) := by
  simp [pd1c_rootSwapMatrix, hgu, hgc, hgv, hgd]

noncomputable def pd1c_rootBox (U V : ℝ) (S : ℕ)
    (g : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) : Set (ℕ × ℕ) :=
  {uv | Nat.Coprime uv.1 uv.2 ∧ l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
    l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
    ∃ c d : ℤ, (uv.1 : ℤ) * d - (uv.2 : ℤ) * c = 1 ∧
      0 ≤ c ∧ c < uv.1 ∧ l₃ ≤ (c : ℝ) / uv.1 ∧ (c : ℝ) / uv.1 ≤ r₃ ∧
      g 0 0 = (uv.1 : ZMod S) ∧ g 0 1 = (c : ZMod S) ∧
        g 1 0 = (uv.2 : ZMod S) ∧ g 1 1 = (d : ZMod S)}

lemma pd1c_rootBox_finite (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (S : ℕ)
    (g : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    (pd1c_rootBox U V S g l₁ r₁ l₂ r₂ l₃ r₃).Finite :=
  pd1c_rootResidueSet_finite U V hU hV S g l₁ r₁ l₂ r₂ l₃ r₃ hr₁ hr₂

lemma pd1c_rootCount_nonneg (U V : ℝ) (S : ℕ) (g : Matrix (Fin 2) (Fin 2) (ZMod S))
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) : 0 ≤ rootResidueCount U V S g l₁ r₁ l₂ r₂ l₃ r₃ := Nat.cast_nonneg _

end ArtinPrimitiveRoots.TypeII.PD
