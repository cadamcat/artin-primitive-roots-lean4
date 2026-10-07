import ArtinPrimitiveRoots.Hecke.Theta.RayMellinReal

/-!
The real norm sum of one ray class and its agreement with the complex partial zeta series.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField nonZeroDivisors Real ENNReal NNReal Classical

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

def rayClassNormWeight {m : RayClassModulus K} (C : RayClassGroup m)
    (s : ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  if h : IsCoprimeTo m I then
    if rayClass m I h = C then (Ideal.absNorm I : ℝ) ^ (-s) else 0 else 0

theorem summable_rayClassNormWeight {m : RayClassModulus K}
    (C : RayClassGroup m) {s : ℝ} (hs : 1 < s) : Summable (rayClassNormWeight C s) := by
  apply (summable_idealNormRpow hs).of_nonneg_of_le
  · intro I
    unfold rayClassNormWeight
    split_ifs <;> positivity
  · intro I
    unfold rayClassNormWeight
    split_ifs with hI hC
    · have hN : Ideal.absNorm I ≠ 0 := fun h => hI.1 (Ideal.absNorm_eq_zero_iff.mp h)
      simp [idealNormRpowTerm, hN, Real.rpow_neg (Nat.cast_nonneg _)]
    · unfold idealNormRpowTerm
      split_ifs <;> positivity
    · unfold idealNormRpowTerm
      split_ifs <;> positivity

theorem rayClassIdealDirichletTerm_real {m : RayClassModulus K}
    (C : RayClassGroup m) (s : ℝ) (I : Ideal (𝓞 K)) :
    rayClassIdealDirichletTerm C (s : ℂ) I = (rayClassNormWeight C s I : ℂ) := by
  classical
  unfold rayClassIdealDirichletTerm rayClassNormWeight
  split_ifs with hI hC
  · have hN : Ideal.absNorm I ≠ 0 := fun h => hI.1 (Ideal.absNorm_eq_zero_iff.mp h)
    have hpow : (Ideal.absNorm I : ℂ) ^ (-(s : ℂ)) =
        (((Ideal.absNorm I : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by norm_cast,
        show -(s : ℂ) = ((-s : ℝ) : ℂ) by simp, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    simp only [rayIdealDirichletTerm, if_neg hN, charValue, dif_pos hI, MonoidHom.one_apply,
      Units.val_one, one_div]
    rw [← Complex.cpow_neg, hpow]
  · simp
  · simp

theorem rayClassPartialZeta_real {m : RayClassModulus K}
    (C : RayClassGroup m) {s : ℝ} (hs : 1 < s) :
    rayClassPartialZeta C (s : ℂ) = ((∑' I : Ideal (𝓞 K), rayClassNormWeight C s I : ℝ) : ℂ) := by
  unfold rayClassPartialZeta
  simp_rw [rayClassIdealDirichletTerm_real]
  exact (Complex.ofRealCLM.map_tsum (summable_rayClassNormWeight C hs)).symm

/-- The real ideal sum can be restricted to the nonzero integral ideals in the chosen ray class. -/
theorem tsum_rayClassNormWeight_eq {m : RayClassModulus K}
    (C : RayClassGroup m) (s : ℝ) :
    (∑' I : Ideal (𝓞 K), rayClassNormWeight C s I) =
      ∑' b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
        rayClass m (b : Ideal (𝓞 K)) hb = C},
        (Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ (-s) := by
  classical
  let A := {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
    rayClass m (b : Ideal (𝓞 K)) hb = C}
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun b : Function.support (fun b : A =>
      (Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)) => (b.1.1 : Ideal (𝓞 K))) ?_ ?_ ?_
  · intro b c h
    apply Subtype.ext
    apply Subtype.ext
    exact Subtype.ext h
  · intro I hI
    change rayClassNormWeight C s I ≠ 0 at hI
    unfold rayClassNormWeight at hI
    split_ifs at hI with hcop hclass
    · let b : A := ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hcop.1⟩, hcop, hclass⟩
      exact ⟨⟨b, hI⟩, rfl⟩
    · exact (hI rfl).elim
    · exact (hI rfl).elim
  · intro b
    obtain ⟨hb, hclass⟩ := b.1.2
    simp only [rayClassNormWeight, dif_pos hb, if_pos hclass]

theorem summable_rayClass_norm_rpow {m : RayClassModulus K}
    (C : RayClassGroup m) {s : ℝ} (hs : 1 < s) :
    Summable (fun b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
      rayClass m (b : Ideal (𝓞 K)) hb = C} =>
      (Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
  have hinj : Function.Injective (fun b : {b : (Ideal (𝓞 K))⁰ //
      ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)), rayClass m (b : Ideal (𝓞 K)) hb = C} =>
      (b.1 : Ideal (𝓞 K))) := by
    intro b c h
    exact Subtype.ext (Subtype.ext h)
  have hf := (summable_rayClassNormWeight C hs).comp_injective hinj
  apply hf.congr
  intro b
  obtain ⟨hb, hclass⟩ := b.2
  simp [rayClassNormWeight, hb, hclass]

theorem tsum_rayClass_ofReal_norm_sq_rpow {m : RayClassModulus K}
    (C : RayClassGroup m) {σ : ℝ} (hσ : 1 < 2 * σ) :
    (∑' b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
      rayClass m (b : Ideal (𝓞 K)) hb = C},
      ENNReal.ofReal (((Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ 2) ^ (-σ))) =
      ENNReal.ofReal (∑' b : {b : (Ideal (𝓞 K))⁰ //
        ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)), rayClass m (b : Ideal (𝓞 K)) hb = C},
        (Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ (-(2 * σ))) := by
  have hpow : ∀ N : ℕ, ((N : ℝ) ^ 2) ^ (-σ) = (N : ℝ) ^ (-(2 * σ)) := by
    intro N
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hpow]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun b => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (summable_rayClass_norm_rpow C hσ)).symm

end ArtinPrimitiveRoots.Hecke

end
