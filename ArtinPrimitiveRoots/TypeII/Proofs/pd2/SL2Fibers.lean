import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

variable {F : Type*} [Field F]

private def finiteKernelMatrix (t : F) (q : Fˣ × F) : Matrix (Fin 2) (Fin 2) F :=
  !![(q.1 : F), -t * (q.1 : F); q.2, (q.1 : F)⁻¹ - t * q.2]

private lemma finiteKernelMatrix_det (t : F) (q : Fˣ × F) :
    (finiteKernelMatrix t q).det = 1 := by
  rw [Matrix.det_fin_two]
  change (q.1 : F) * ((q.1 : F)⁻¹ - t * q.2) - (-t * (q.1 : F)) * q.2 = 1
  rw [mul_sub, mul_inv_cancel₀ q.1.ne_zero]
  ring

private abbrev FiniteKernelFiber (t : F) :=
  {g : Matrix (Fin 2) (Fin 2) F // g.det = 1 ∧ g 0 0 ≠ 0 ∧ g 0 1 = -t * g 0 0}

private def finiteKernelEquiv (t : F) : Fˣ × F ≃ FiniteKernelFiber t where
  toFun q := ⟨finiteKernelMatrix t q, finiteKernelMatrix_det t q, q.1.ne_zero, rfl⟩
  invFun g := (Units.mk0 (g.1 0 0) g.2.2.1, g.1 1 0)
  left_inv q := by
    apply Prod.ext
    · apply Units.ext
      rfl
    · rfl
  right_inv g := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact g.2.2.2.symm
    · rfl
    · have hd := g.2.1
      rw [Matrix.det_fin_two, g.2.2.2] at hd
      change (g.1 0 0)⁻¹ - t * g.1 1 0 = g.1 1 1
      field_simp [g.2.2.1]
      linear_combination -hd

private def infiniteKernelMatrix (q : Fˣ × F) : Matrix (Fin 2) (Fin 2) F :=
  !![0, (q.1 : F); -(q.1 : F)⁻¹, q.2]

private lemma infiniteKernelMatrix_det (q : Fˣ × F) :
    (infiniteKernelMatrix q).det = 1 := by
  rw [Matrix.det_fin_two]
  change 0 * q.2 - (q.1 : F) * (-(q.1 : F)⁻¹) = 1
  simp [q.1.ne_zero]

private abbrev InfiniteKernelFiber (F : Type*) [Field F] :=
  {g : Matrix (Fin 2) (Fin 2) F // g.det = 1 ∧ g 0 0 = 0}

private lemma infiniteKernelFiber_row_ne_zero (g : InfiniteKernelFiber F) : g.1 0 1 ≠ 0 := by
  intro hc
  have hd := g.2.1
  rw [Matrix.det_fin_two, g.2.2, hc] at hd
  exact (zero_ne_one : (0 : F) ≠ 1) (by simpa using hd)

private def infiniteKernelEquiv : Fˣ × F ≃ InfiniteKernelFiber F where
  toFun q := ⟨infiniteKernelMatrix q, infiniteKernelMatrix_det q, rfl⟩
  invFun g := (Units.mk0 (g.1 0 1) (infiniteKernelFiber_row_ne_zero g), g.1 1 1)
  left_inv q := by
    apply Prod.ext
    · apply Units.ext
      rfl
    · rfl
  right_inv g := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact g.2.2.symm
    · rfl
    · have hd := g.2.1
      rw [Matrix.det_fin_two, g.2.2] at hd
      change -(g.1 0 1)⁻¹ = g.1 1 0
      field_simp [infiniteKernelFiber_row_ne_zero g]
      linear_combination hd
    · rfl

private abbrev SL2Matrices (F : Type*) [Field F] :=
  {g : Matrix (Fin 2) (Fin 2) F // g.det = 1}

private def sl2RowEquiv : SL2Matrices F ≃ (Σ t : F, FiniteKernelFiber t) ⊕ InfiniteKernelFiber F where
  toFun g :=
    if h : g.1 0 0 = 0 then Sum.inr ⟨g.1, g.2, h⟩
    else Sum.inl ⟨-g.1 0 1 / g.1 0 0, ⟨g.1, g.2, h, by field_simp [h]⟩⟩
  invFun q := match q with
    | Sum.inl ⟨_, g⟩ => ⟨g.1, g.2.1⟩
    | Sum.inr g => ⟨g.1, g.2.1⟩
  left_inv g := by
    by_cases h : g.1 0 0 = 0
    · simp only [dif_pos h]
    · simp only [dif_neg h]
  right_inv q := by
    cases q with
    | inl q =>
      obtain ⟨t, g⟩ := q
      simp only [dif_neg g.2.2.1]
      apply congrArg Sum.inl
      have ht : -g.1 0 1 / g.1 0 0 = t := by
        rw [g.2.2.2]
        field_simp [g.2.2.1]
      apply Sigma.ext ht
      apply (Subtype.heq_iff_coe_eq (fun m : Matrix (Fin 2) (Fin 2) F => by
        change (m.det = 1 ∧ m 0 0 ≠ 0 ∧ m 0 1 = -(-g.1 0 1 / g.1 0 0) * m 0 0) ↔
          (m.det = 1 ∧ m 0 0 ≠ 0 ∧ m 0 1 = -t * m 0 0)
        rw [ht])).2
      rfl
    | inr g =>
      simp only [dif_pos g.2.2]

lemma finite_kernel_fiber_card (F : Type*) [Field F] [Fintype F] (t : F) :
    Nat.card {g : Matrix (Fin 2) (Fin 2) F // g.det = 1 ∧ g 0 0 ≠ 0 ∧ g 0 1 = -t * g 0 0} =
      (Fintype.card F - 1) * Fintype.card F := by
  classical
  calc
    _ = Nat.card (Fˣ × F) := (Nat.card_congr (finiteKernelEquiv t)).symm
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_units]

lemma infinite_kernel_fiber_card (F : Type*) [Field F] [Fintype F] :
    Nat.card {g : Matrix (Fin 2) (Fin 2) F // g.det = 1 ∧ g 0 0 = 0} =
      (Fintype.card F - 1) * Fintype.card F := by
  classical
  calc
    _ = Nat.card (Fˣ × F) := (Nat.card_congr (infiniteKernelEquiv (F := F))).symm
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_units]

lemma sl2_matrix_card_by_kernel_lines (F : Type*) [Field F] [Fintype F] :
    Nat.card {g : Matrix (Fin 2) (Fin 2) F // g.det = 1} =
      (Fintype.card F + 1) * ((Fintype.card F - 1) * Fintype.card F) := by
  classical
  have hfinite (t : F) : Nat.card (FiniteKernelFiber t) =
      (Fintype.card F - 1) * Fintype.card F := finite_kernel_fiber_card F t
  have hinfinite : Nat.card (InfiniteKernelFiber F) =
      (Fintype.card F - 1) * Fintype.card F := infinite_kernel_fiber_card F
  calc
    _ = Nat.card ((Σ t : F, FiniteKernelFiber t) ⊕ InfiniteKernelFiber F) :=
      Nat.card_congr (sl2RowEquiv (F := F))
    _ = Nat.card (Σ t : F, FiniteKernelFiber t) + Nat.card (InfiniteKernelFiber F) := Nat.card_sum
    _ = (∑ t : F, Nat.card (FiniteKernelFiber t)) + Nat.card (InfiniteKernelFiber F) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp only [Nat.card_eq_fintype_card]
    _ = _ := by simp only [hfinite, hinfinite, Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

end
end ArtinPrimitiveRoots.TypeII.PD
