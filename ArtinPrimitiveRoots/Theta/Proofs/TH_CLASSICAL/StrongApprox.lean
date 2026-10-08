import ArtinPrimitiveRoots.Theta.Cover
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Arithmetic

set_option autoImplicit false
open scoped Classical MatrixGroups Topology
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- A fixed alternating word of four elementary matrices represents every SL2 matrix. -/
theorem th_classical_sl_elementary_factorization {K : Type} [Field K] (g : SL(2, K)) :
    ∃ a b c d : K, Matrix.SpecialLinearGroup.toGL g =
      upperM K a * lowerM K b * upperM K c * lowerM K d := by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with
  | h A B C D hdet =>
    by_cases hB : B = 0
    · have hAD : A * D = 1 := by simpa only [hB, zero_mul, sub_zero] using hdet
      have hA : A ≠ 0 := left_ne_zero_of_mul_eq_one hAD
      have hD : D = 1 / A := by
        apply (eq_div_iff hA).mpr
        simpa only [mul_comm] using hAD
      refine ⟨1, A - 1, -1 / A, A * (C - (A - 1)), ?_⟩
      apply Units.ext
      change !![A, B; C, D] = _
      ext i j
      fin_cases i <;> fin_cases j
      all_goals
        simp [upperM, lowerM, Matrix.mul_apply, Fin.sum_univ_two, hB, hD]
        <;> field_simp [hA]
        <;> ring
        <;> simp
    · have hC : C = (A * D - 1) / B := by
        apply (eq_div_iff hB).mpr
        linear_combination -hdet
      refine ⟨0, (D - 1) / B, B, (A - 1) / B, ?_⟩
      apply Units.ext
      change !![A, B; C, D] = _
      ext i j
      fin_cases i <;> fin_cases j
      all_goals
        simp [upperM, lowerM, Matrix.mul_apply, Fin.sum_univ_two, hC]
        <;> field_simp [hB]
        <;> ring
        <;> simp

variable {F : Type} [Field F] [NumberField F]

set_option maxHeartbeats 400000 in
/-- Rational determinant-one matrices approximate finitely many local matrices while integral
at every other finite place. -/
theorem th_classical_sl_finite_approx (T : Finset (FinPlace F))
    (g : ∀ v : T, SL(2, v.1.adicCompletion F))
    (U : ∀ v : T, Set (GL (Fin 2) (v.1.adicCompletion F)))
    (hU : ∀ v : T, U v ∈ 𝓝 (Matrix.SpecialLinearGroup.toGL (g v))) :
    ∃ γ : GL (Fin 2) F, Matrix.GeneralLinearGroup.det γ = 1 ∧
      (∀ w : FinPlace F, w ∉ T → ∀ i j : Fin 2,
        w.valuation F ((γ : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1) ∧
      ∀ v : T, Matrix.GeneralLinearGroup.map
        (algebraMap F (v.1.adicCompletion F)) γ ∈ U v := by
  classical
  let word (K : Type) [Field K] (a : Fin 4 → K) : GL (Fin 2) K :=
    upperM K (a 0) * lowerM K (a 1) * upperM K (a 2) * lowerM K (a 3)
  choose a b c d hg using fun v : T => th_classical_sl_elementary_factorization (g v)
  let q : ∀ v : T, Fin 4 → v.1.adicCompletion F := fun v => ![a v, b v, c v, d v]
  have hq (v : T) : word (v.1.adicCompletion F) (q v) =
      Matrix.SpecialLinearGroup.toGL (g v) := by
    simpa [word, q] using (hg v).symm
  have hupper (v : T) : Continuous (upperM (v.1.adicCompletion F)) := by
    have heq : upperM (v.1.adicCompletion F) =
        Matrix.GeneralLinearGroup.upperRightHom (R := v.1.adicCompletion F) := by
      funext t
      exact Units.ext rfl
    rw [heq]
    exact Matrix.GeneralLinearGroup.continuous_upperRightHom
  have hlower (v : T) : Continuous (lowerM (v.1.adicCompletion F)) := by
    have heq : lowerM (v.1.adicCompletion F) = fun t =>
        weylM (v.1.adicCompletion F) * upperM (v.1.adicCompletion F) t *
          weylM (v.1.adicCompletion F) := by
      funext t
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j
      all_goals simp [lowerM, upperM, weylM, Matrix.mul_apply, Fin.sum_univ_two]
    rw [heq]
    exact (continuous_const.mul (hupper v)).mul continuous_const
  have hword (v : T) : Continuous (word (v.1.adicCompletion F)) :=
    ((((hupper v).comp (continuous_apply 0)).mul
      ((hlower v).comp (continuous_apply 1))).mul
      ((hupper v).comp (continuous_apply 2))).mul
      ((hlower v).comp (continuous_apply 3))
  have hpre (v : T) : (word (v.1.adicCompletion F)) ⁻¹' (U v) ∈ 𝓝 (q v) :=
    (hword v).continuousAt.preimage_mem_nhds (by simpa only [hq v] using hU v)
  choose V hVU hVopen hqV using fun v : T => mem_nhds_iff.mp (hpre v)
  choose W hW hWV using fun v : T =>
    (isOpen_pi_iff'.mp (hVopen v)) (q v) (hqV v)
  choose ε hε using fun v : T => fun i : Fin 4 =>
    Valued.mem_nhds.mp ((hW v i).1.mem_nhds (hW v i).2)
  let radius (v : T) (i : Fin 4) : WithZero (Multiplicative ℤ) :=
    MonoidWithZeroHom.ValueGroup₀.embedding
      ((ε v i).val : (Valued.v : Valuation (v.1.adicCompletion F)
        (WithZero (Multiplicative ℤ))).ValueGroup₀)
  have hradius (v : T) (i : Fin 4) : radius v i ≠ 0 := by
    intro h
    apply Units.ne_zero (ε v i)
    apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
    rw [map_zero]
    exact h
  choose m hm using fun v : T => fun i : Fin 4 =>
    WithZero.exists_exp_neg_natCast_lt (hradius v i)
  choose r hrint hrclose using fun i : Fin 4 =>
    th_classical_sInteger_finite_approx T (fun v => q v i) (fun v => m v i)
  have hdet_upper (t : F) : Matrix.GeneralLinearGroup.det (upperM F t) = 1 := by
    apply Units.ext
    change Matrix.det !![1, t; 0, 1] = 1
    simp [Matrix.det_fin_two]
  have hdet_lower (t : F) : Matrix.GeneralLinearGroup.det (lowerM F t) = 1 := by
    apply Units.ext
    change Matrix.det !![1, 0; t, 1] = 1
    simp [Matrix.det_fin_two]
  have hprod (w : FinPlace F) (s t : GL (Fin 2) F)
      (hs : ∀ i j, w.valuation F ((s : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
      (ht : ∀ i j, w.valuation F ((t : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1) :
      ∀ i j, w.valuation F ((s * t : GL (Fin 2) F).val i j) ≤ 1 := by
    intro i j
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    apply (w.valuation F).map_sum_le
    intro k hk
    rw [map_mul]
    simpa only [mul_one] using mul_le_mul' (hs i k) (ht k j)
  have hmap_upper (v : T) (t : F) :
      Matrix.GeneralLinearGroup.map (algebraMap F (v.1.adicCompletion F)) (upperM F t) =
        upperM (v.1.adicCompletion F) (algebraMap F (v.1.adicCompletion F) t) := by
    apply Units.ext
    change (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F).map
      (algebraMap F (v.1.adicCompletion F)) =
        !![1, algebraMap F (v.1.adicCompletion F) t; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hmap_lower (v : T) (t : F) :
      Matrix.GeneralLinearGroup.map (algebraMap F (v.1.adicCompletion F)) (lowerM F t) =
        lowerM (v.1.adicCompletion F) (algebraMap F (v.1.adicCompletion F) t) := by
    apply Units.ext
    change (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) F).map
      (algebraMap F (v.1.adicCompletion F)) =
        !![1, 0; algebraMap F (v.1.adicCompletion F) t, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨word F r, ?_, ?_, ?_⟩
  · simp only [word, map_mul, hdet_upper, hdet_lower, mul_one]
  · intro w hw
    have hup (k : Fin 4) : ∀ i j,
        w.valuation F ((upperM F (r k) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [upperM]
      exact hrint k w hw
    have hlo (k : Fin 4) : ∀ i j,
        w.valuation F ((lowerM F (r k) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [lowerM]
      exact hrint k w hw
    exact hprod w _ _ (hprod w _ _ (hprod w _ _ (hup 0) (hlo 1)) (hup 2)) (hlo 3)
  · intro v
    have hmap : Matrix.GeneralLinearGroup.map (algebraMap F (v.1.adicCompletion F))
        (word F r) = word (v.1.adicCompletion F)
          (fun i => algebraMap F (v.1.adicCompletion F) (r i)) := by
      simp only [word, map_mul, hmap_upper, hmap_lower]
    rw [hmap]
    let t : Fin 4 → v.1.adicCompletion F :=
      fun i => algebraMap F (v.1.adicCompletion F) (r i)
    have ht : t ∈ Set.univ.pi (W v) := by
      intro i hi
      apply hε v i
      change Valued.v.restrict
        (algebraMap F (v.1.adicCompletion F) (r i) - q v i) < ε v i
      rw [Valuation.restrict_lt_iff_lt_embedding]
      exact (hrclose i v).trans (hm v i)
    have htV : t ∈ V v := @hWV v t ht
    have htU : t ∈ (word (v.1.adicCompletion F)) ⁻¹' (U v) := @hVU v t htV
    change word (v.1.adicCompletion F) t ∈ U v
    exact htU

end ArtinPrimitiveRoots.A1.Theta
