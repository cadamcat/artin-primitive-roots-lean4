import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD
open scoped BigOperators

noncomputable section

private theorem clean_finite_average_norm_sq {G : Type*} [Fintype G] [Nonempty G] (a : G → ℂ) :
    ‖(Fintype.card G : ℂ)⁻¹ * ∑ g : G, a g‖ ^ 2 ≤
      (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖a g‖ ^ 2 := by
  classical
  let n : ℝ := Fintype.card G
  have hn0 : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hn : n ≠ 0 := hn0.ne'
  have htriangle : ‖∑ g : G, a g‖ ≤ ∑ g : G, ‖a g‖ := norm_sum_le Finset.univ a
  have htriangleSq : ‖∑ g : G, a g‖ ^ 2 ≤ (∑ g : G, ‖a g‖) ^ 2 := by
    have hdiff : 0 ≤ (∑ g : G, ‖a g‖) - ‖∑ g : G, a g‖ := sub_nonneg.mpr htriangle
    have hsum : 0 ≤ (∑ g : G, ‖a g‖) + ‖∑ g : G, a g‖ := by positivity
    nlinarith [mul_nonneg hdiff hsum]
  have hcs : (∑ g : G, ‖a g‖) ^ 2 ≤
      n * ∑ g : G, ‖a g‖ ^ 2 := by
    simpa [n] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun g : G => ‖a g‖))
  calc
    ‖(Fintype.card G : ℂ)⁻¹ * ∑ g : G, a g‖ ^ 2 =
        n⁻¹ ^ 2 * ‖∑ g : G, a g‖ ^ 2 := by
          rw [norm_mul]
          have hnorm : ‖(Fintype.card G : ℂ)⁻¹‖ = n⁻¹ := by
            simp [n]
          rw [hnorm]
          ring
    _ ≤ n⁻¹ ^ 2 * (∑ g : G, ‖a g‖) ^ 2 := by
        gcongr
    _ ≤ n⁻¹ ^ 2 * (n * ∑ g : G, ‖a g‖ ^ 2) := by
        gcongr
    _ = n⁻¹ * ∑ g : G, ‖a g‖ ^ 2 := by
        field_simp [hn] <;> ring

private theorem clean_finite_equiv_average_contraction {α G : Type*} [DecidableEq α]
    [Fintype G] [Nonempty G] (T : Finset α) (e : G → α ≃ α)
    (hT : ∀ g x, x ∈ T ↔ e g x ∈ T) (μ : α → ℝ)
    (hμ : ∀ x ∈ T, ∀ g, μ (e g x) = μ x)
    (hμ0 : ∀ x ∈ T, 0 ≤ μ x) (f : α → ℂ) :
    (∑ x ∈ T, μ x * ‖(Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (e g x)‖ ^ 2) ≤
      ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
  classical
  have hsum (g : G) :
      (∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2) =
        ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
    calc
      _ = ∑ x ∈ T, μ (e g x) * ‖f (e g x)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hμ x hx g]
      _ = ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
        apply Finset.sum_bij (fun x hx => e g x)
        · intro x hx
          exact (hT g x).mp hx
        · intro x₁ hx₁ x₂ hx₂ heq
          exact (e g).injective heq
        · intro y hy
          refine ⟨(e g).symm y, (hT g ((e g).symm y)).mpr ?_, ?_⟩
          · simpa using hy
          · simp
        · intro x hx
          rfl
  have hdouble :
      (∑ x ∈ T, μ x * ((Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ‖f (e g x)‖ ^ 2)) =
        (Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := by
    calc
      _ = ∑ x ∈ T, ∑ g : G,
            (Fintype.card G : ℝ)⁻¹ * (μ x * ‖f (e g x)‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            μ x * ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f (e g x)‖ ^ 2) =
                (Fintype.card G : ℝ)⁻¹ *
                  (μ x * ∑ g : G, ‖f (e g x)‖ ^ 2) := by ring
            _ = (Fintype.card G : ℝ)⁻¹ *
                  ∑ g : G, μ x * ‖f (e g x)‖ ^ 2 := by rw [Finset.mul_sum]
            _ = ∑ g : G, (Fintype.card G : ℝ)⁻¹ *
                  (μ x * ‖f (e g x)‖ ^ 2) := by rw [Finset.mul_sum]
      _ = ∑ g : G, ∑ x ∈ T,
            (Fintype.card G : ℝ)⁻¹ * (μ x * ‖f (e g x)‖ ^ 2) := by
          rw [Finset.sum_comm]
      _ = (Fintype.card G : ℝ)⁻¹ *
            ∑ g : G, ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := by
          calc
            _ = ∑ g : G, (Fintype.card G : ℝ)⁻¹ *
                  ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro g hg
              rw [← Finset.mul_sum]
            _ = (Fintype.card G : ℝ)⁻¹ *
                  ∑ g : G, ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := by
              rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ x ∈ T, μ x * ((Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ‖f (e g x)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left
          (clean_finite_average_norm_sq (fun g => f (e g x))) (hμ0 x hx)
    _ = (Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := hdouble
    _ = (Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro g hg
        exact hsum g
    _ = ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
        have hcard : (Fintype.card G : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G).ne'
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [hcard]

/-- Active endpoint averaging contracts on a finite permutation-closed set. -/
theorem clean_active_sym_contraction {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ)
    (hm : ∀ s, 0 ≤ memMeasure F S s)
    (hT : ∀ s ∈ T, ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      (s.1, permuteLists σ s.2.1, s.2.2) ∈ T) :
    memNormSqOn F S T (plainOp (logSym F S) f) ≤ memNormSqOn F S T f := by
  classical
  let G := Fin K → Equiv.Perm (Fin (slotCount S.x))
  let e (a : G) : MemPoint S.x K ≃ MemPoint S.x K := {
    toFun := fun s => (s.1, permuteLists a s.2.1, s.2.2)
    invFun := fun s => (s.1, permuteLists (fun i => (a i).symm) s.2.1, s.2.2)
    left_inv := by
      intro s
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext i j
          simp [permuteLists]
        · rfl
    right_inv := by
      intro s
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext i j
          simp [permuteLists]
        · rfl
  }
  have hclosed (a : G) (s : MemPoint S.x K) : s ∈ T ↔ e a s ∈ T := by
    constructor
    · intro hs
      exact hT s hs a
    · intro hs
      have h := hT (e a s) hs (fun i => (a i).symm)
      have he : (s.1, permuteLists (fun i => (a i).symm) (permuteLists a s.2.1),
          s.2.2) = s := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · funext i j
            simp [permuteLists]
          · rfl
      change (s.1, permuteLists (fun i => (a i).symm) (permuteLists a s.2.1),
        s.2.2) ∈ T at h
      rw [he] at h
      exact h
  have hcontract := clean_finite_equiv_average_contraction T e hclosed
    (fun s => memMeasure F S s)
    (fun s hs a => pd4c_memMeasure_activePermute F S s a)
    (fun s hs => hm s) f
  have he (a : G) (s : MemPoint S.x K) :
      e a s = (s.1, permuteLists a s.2.1, s.2.2) := rfl
  simpa only [memNormSqOn, plainOp, logSym, permCount, he, G] using hcontract

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
