import ArtinPrimitiveRoots.Spec.Geometry

set_option autoImplicit false

open NumberField Matrix
open scoped MatrixGroups

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem specMinkAbsFieldNormMul (a b : F) :
    absFieldNorm F (a * b) = absFieldNorm F a * absFieldNorm F b := by
  simp [absFieldNorm, Complex.norm_mul, mul_pow, Finset.prod_mul_distrib]

private theorem specMinkAbsFieldNormGeOne (a : 𝓞 F) (ha : a ≠ 0) :
    1 ≤ absFieldNorm F (algebraMap (𝓞 F) F a) := by
  rw [absFieldNorm_eq_abs_norm, ← Algebra.coe_norm_int]
  exact_mod_cast Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

private theorem specMinkSU2TraceNorm (U : SL(2, ℂ)) (hU : U ∈ SU2) :
    ‖Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 := by
  change (U : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ at hU
  have hunit : (U : Matrix (Fin 2) (Fin 2) ℂ) * star (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hU
  have hentry (z : ℂ) : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := by
    calc
      z * (starRingEnd ℂ) z = (starRingEnd ℂ) z * z := mul_comm _ _
      _ = (Complex.normSq z : ℂ) := Complex.normSq_eq_conj_mul_self.symm
  have hrow0 : Complex.normSq (U 0 0) + Complex.normSq (U 0 1) = 1 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hunit
    have hC : (Complex.normSq (U 0 0) : ℂ) + Complex.normSq (U 0 1) = 1 := by
      simpa [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, hentry] using h
    exact_mod_cast hC
  have hrow1 : Complex.normSq (U 1 0) + Complex.normSq (U 1 1) = 1 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hunit
    have hC : (Complex.normSq (U 1 0) : ℂ) + Complex.normSq (U 1 1) = 1 := by
      simpa [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, hentry] using h
    exact_mod_cast hC
  have h00sq : ‖U 0 0‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith [Complex.normSq_nonneg (U 0 1)]
  have h11sq : ‖U 1 1‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith [Complex.normSq_nonneg (U 1 0)]
  have h00 : ‖U 0 0‖ ≤ 1 := by nlinarith [norm_nonneg (U 0 0)]
  have h11 : ‖U 1 1‖ ≤ 1 := by nlinarith [norm_nonneg (U 1 1)]
  have htrace : Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ) = U 0 0 + U 1 1 := by
    simp [Matrix.trace, Fin.sum_univ_two]
  calc
    ‖Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)‖ = ‖U 0 0 + U 1 1‖ := by rw [htrace]
    _ ≤ ‖U 0 0‖ + ‖U 1 1‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add h00 h11
    _ = 2 := by norm_num

private theorem specMinkTraceConj (g U : SL(2, ℂ)) :
    Matrix.trace ((g⁻¹ * U * g : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ) := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := ((g⁻¹ * U : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)
  let B : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)
  calc
    Matrix.trace ((g⁻¹ * U * g : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.trace (A * B) := by simp [A, B, Matrix.SpecialLinearGroup.coe_mul]
    _ = Matrix.trace (B * A) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((U : Matrix (Fin 2) (Fin 2) ℂ)) := by
      change Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) *
        (Matrix.adjugate (g : Matrix (Fin 2) (Fin 2) ℂ) *
          (U : Matrix (Fin 2) (Fin 2) ℂ))) = _
      have hmul : (g : Matrix (Fin 2) (Fin 2) ℂ) *
          Matrix.adjugate (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
        rw [Matrix.mul_adjugate, g.property]
        simp
      rw [← Matrix.mul_assoc, hmul]
      simp

private theorem specMink_SU2_trace_two_eq_one (U : SL(2, ℂ)) (hU : U ∈ SU2)
    (htr : Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ) = 2) : U = 1 := by
  change (U : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ at hU
  have hunit : (U : Matrix (Fin 2) (Fin 2) ℂ) * star (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hU
  have hentry (z : ℂ) : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := by
    calc
      z * (starRingEnd ℂ) z = (starRingEnd ℂ) z * z := mul_comm _ _
      _ = (Complex.normSq z : ℂ) := Complex.normSq_eq_conj_mul_self.symm
  have hrow0 : Complex.normSq (U 0 0) + Complex.normSq (U 0 1) = 1 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hunit
    have hC : (Complex.normSq (U 0 0) : ℂ) + Complex.normSq (U 0 1) = 1 := by
      simpa [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, hentry] using h
    exact_mod_cast hC
  have hrow1 : Complex.normSq (U 1 0) + Complex.normSq (U 1 1) = 1 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hunit
    have hC : (Complex.normSq (U 1 0) : ℂ) + Complex.normSq (U 1 1) = 1 := by
      simpa [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, hentry] using h
    exact_mod_cast hC
  have h00sq : ‖U 0 0‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith [Complex.normSq_nonneg (U 0 1)]
  have h11sq : ‖U 1 1‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith [Complex.normSq_nonneg (U 1 0)]
  have h00 : ‖U 0 0‖ ≤ 1 := by nlinarith [norm_nonneg (U 0 0)]
  have h11 : ‖U 1 1‖ ≤ 1 := by nlinarith [norm_nonneg (U 1 1)]
  have htr' : (U 0 0).re + (U 1 1).re = 2 := by
    have := congrArg Complex.re htr
    simpa [Matrix.trace, Fin.sum_univ_two] using this
  have hre00 : (U 0 0).re = 1 := by
    have hle : (U 0 0).re ≤ 1 := (Complex.re_le_norm _).trans h00
    have hle' : (U 1 1).re ≤ 1 := (Complex.re_le_norm _).trans h11
    linarith
  have hre11 : (U 1 1).re = 1 := by
    have hle : (U 0 0).re ≤ 1 := (Complex.re_le_norm _).trans h00
    have hle' : (U 1 1).re ≤ 1 := (Complex.re_le_norm _).trans h11
    linarith
  have him00 : (U 0 0).im = 0 := by
    have hnormsq : Complex.normSq (U 0 0) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [h00, norm_nonneg (U 0 0)]
    rw [Complex.normSq_apply] at hnormsq
    nlinarith
  have him11 : (U 1 1).im = 0 := by
    have hnormsq : Complex.normSq (U 1 1) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [h11, norm_nonneg (U 1 1)]
    rw [Complex.normSq_apply] at hnormsq
    nlinarith
  have hdiag00 : U 0 0 = 1 := by
    apply Complex.ext <;> simp [hre00, him00]
  have hdiag11 : U 1 1 = 1 := by
    apply Complex.ext <;> simp [hre11, him11]
  have h01sq : Complex.normSq (U 0 1) = 0 := by
    simp [hdiag00] at hrow0
    simpa [hrow0]
  have h10sq : Complex.normSq (U 1 0) = 0 := by
    simp [hdiag11] at hrow1
    simpa [hrow1]
  have h01 : U 0 1 = 0 := Complex.normSq_eq_zero.mp h01sq
  have h10 : U 1 0 = 0 := Complex.normSq_eq_zero.mp h10sq
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hdiag00, hdiag11, h01, h10]

theorem specMink_R11_free_level {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ FreeAction F (congrSubgroup F N) := by
  classical
  let N : Ideal (𝓞 F) := Ideal.span {(5 : 𝓞 F)}
  have hN : N ≠ ⊥ := by
    change Ideal.span {(5 : 𝓞 F)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  refine ⟨N, hN, ?_⟩
  intro γ hγ z hz
  change (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk N) γ) = 1 at hγ
  have h00q : Ideal.Quotient.mk N (γ 0 0) = 1 := by
    have h := congrArg (fun A : SL(2, 𝓞 F ⧸ N) => (A : Matrix (Fin 2) (Fin 2) (𝓞 F ⧸ N)) 0 0) hγ
    simpa using h
  have h11q : Ideal.Quotient.mk N (γ 1 1) = 1 := by
    have h := congrArg (fun A : SL(2, 𝓞 F ⧸ N) => (A : Matrix (Fin 2) (Fin 2) (𝓞 F ⧸ N)) 1 1) hγ
    simpa using h
  have h00mem : γ 0 0 - 1 ∈ N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [map_sub, h00q]
  have h11mem : γ 1 1 - 1 ∈ N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [map_sub, h11q]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (by simpa [N] using h00mem)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (by simpa [N] using h11mem)
  let d : 𝓞 F := γ 0 0 + γ 1 1 - 2
  have hd : d = (5 : 𝓞 F) * (a + b) := by
    dsimp [d]
    change γ 0 0 + γ 1 1 - 2 = 5 * (a + b)
    calc
      _ = (γ 0 0 - 1) + (γ 1 1 - 1) := by ring
      _ = 5 * a + 5 * b := by rw [ha, hb]
      _ = 5 * (a + b) := by ring
  have hlocalTrace (w : InfinitePlace F) :
      ‖w.embedding (algebraMap (𝓞 F) F d)‖ ≤ 4 := by
    let M : SL(2, ℂ) := Matrix.SpecialLinearGroup.map
      (w.embedding.comp (algebraMap (𝓞 F) F)) γ
    let g : SL(2, ℂ) := Quotient.out (z w)
    have hg : QuotientGroup.mk g = z w := Quotient.out_eq (z w)
    have hMaction : M = toInf F (toSLF F γ) w := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      change (w.embedding.comp (algebraMap (𝓞 F) F)) (γ i j) =
        w.embedding (algebraMap (𝓞 F) F (γ i j))
      rfl
    have hz' : toInf F (toSLF F γ) • z = z := by
      simpa only [instMulActionSLF, MulAction.compHom_smul_def, MonoidHom.comp_apply] using hz
    have hfixw : M • (z w) = z w := by
      have h := congrFun hz' w
      simpa [toInf, M, hMaction] using h
    have hfixrep : (QuotientGroup.mk (M * g) : H3) = (QuotientGroup.mk g : H3) := by
      calc
        (QuotientGroup.mk (M * g) : H3) = M • (QuotientGroup.mk g : H3) := by rfl
        _ = M • (z w) := by rw [hg]
        _ = z w := hfixw
        _ = (QuotientGroup.mk g : H3) := hg.symm
    have hrelSetoid : QuotientGroup.leftRel SU2 (M * g) g := Quotient.exact hfixrep
    have hrel : (M * g)⁻¹ * g ∈ SU2 := QuotientGroup.leftRel_apply.mp hrelSetoid
    have hrel' : g⁻¹ * M⁻¹ * g ∈ SU2 := by
      simpa [_root_.mul_inv_rev, mul_assoc] using hrel
    have hconj : g⁻¹ * M * g ∈ SU2 := by
      have h := SU2.inv_mem hrel'
      simpa [_root_.mul_inv_rev, mul_assoc] using h
    let U : SL(2, ℂ) := g⁻¹ * M * g
    have htrU : Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ) := by
      exact specMinkTraceConj g M
    have htrD : w.embedding (algebraMap (𝓞 F) F d) =
        Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ) - 2 := by
      have hM00 : (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
          w.embedding (algebraMap (𝓞 F) F (γ 0 0)) := by
        change (w.embedding.comp (algebraMap (𝓞 F) F)) (γ 0 0) = _
        rfl
      have hM11 : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
          w.embedding (algebraMap (𝓞 F) F (γ 1 1)) := by
        change (w.embedding.comp (algebraMap (𝓞 F) F)) (γ 1 1) = _
        rfl
      change (w.embedding.comp (algebraMap (𝓞 F) F))
          (γ 0 0 + γ 1 1 - 2) = _
      rw [map_sub, map_add]
      rw [Matrix.trace, Fin.sum_univ_two]
      simp only [Matrix.diag_apply, hM00, hM11]
      simp only [RingHom.comp_apply, map_ofNat]
    rw [htrD, ← htrU]
    calc
      ‖Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ) - 2‖ ≤
          ‖Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 + 2 := add_le_add (specMinkSU2TraceNorm U hconj) (by norm_num)
      _ = 4 := by norm_num
  have hnormUpper : absFieldNorm F (algebraMap (𝓞 F) F d) ≤
      (16 : ℝ) ^ Fintype.card (InfinitePlace F) := by
    unfold absFieldNorm
    calc
      ∏ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F d)‖ ^ 2 ≤
          ∏ _w : InfinitePlace F, (16 : ℝ) := by
            apply Finset.prod_le_prod₀
            · intro w hw
              positivity
            · intro w hw
              have h := hlocalTrace w
              nlinarith [norm_nonneg (w.embedding (algebraMap (𝓞 F) F d))]
      _ = (16 : ℝ) ^ Fintype.card (InfinitePlace F) := by simp
  have hpow : (16 : ℝ) ^ Fintype.card (InfinitePlace F) <
      (25 : ℝ) ^ Fintype.card (InfinitePlace F) := by
    have hn : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hm]
    simp only [pow_succ]
    have hpowle : (16 : ℝ) ^ m ≤ (25 : ℝ) ^ m := by gcongr <;> norm_num
    calc
      (16 : ℝ) ^ m * 16 ≤ (25 : ℝ) ^ m * 16 := mul_le_mul_of_nonneg_right hpowle (by norm_num)
      _ < (25 : ℝ) ^ m * 25 := by
        exact mul_lt_mul_of_pos_left (by norm_num : (16 : ℝ) < 25)
          (pow_pos (by norm_num : (0 : ℝ) < 25) m)
  have hd0 : d = 0 := by
    by_contra hd0
    have hcab : a + b ≠ 0 := by
      intro hab
      apply hd0
      rw [hd, hab]
      simp
    have hnormCab : 1 ≤ absFieldNorm F (algebraMap (𝓞 F) F (a + b)) :=
      specMinkAbsFieldNormGeOne (a + b) hcab
    have hnormFive : absFieldNorm F (algebraMap (𝓞 F) F (5 : 𝓞 F)) =
      (25 : ℝ) ^ Fintype.card (InfinitePlace F) := by
      unfold absFieldNorm
      have hcoord (w : InfinitePlace F) :
          ‖w.embedding (algebraMap (𝓞 F) F (5 : 𝓞 F))‖ ^ 2 = (25 : ℝ) := by
        change ‖w.embedding (algebraMap (𝓞 F) F ((5 : ℕ) : 𝓞 F))‖ ^ 2 = 25
        simp only [map_natCast]
        norm_num
      rw [show (fun w : InfinitePlace F =>
          ‖w.embedding (algebraMap (𝓞 F) F (5 : 𝓞 F))‖ ^ 2) = fun _ => (25 : ℝ) from
        funext hcoord]
      simp
    have hnormLower : (25 : ℝ) ^ Fintype.card (InfinitePlace F) ≤
        absFieldNorm F (algebraMap (𝓞 F) F d) := by
      rw [hd, map_mul, specMinkAbsFieldNormMul, hnormFive]
      nlinarith [hnormCab, pow_pos (by norm_num : (0 : ℝ) < 25)
        (Fintype.card (InfinitePlace F))]
    exact not_lt_of_ge hnormLower (lt_of_le_of_lt hnormUpper hpow)
  have hγfix (w : InfinitePlace F) :
      Matrix.SpecialLinearGroup.map (w.embedding.comp (algebraMap (𝓞 F) F)) γ = 1 := by
    let M : SL(2, ℂ) := Matrix.SpecialLinearGroup.map
      (w.embedding.comp (algebraMap (𝓞 F) F)) γ
    let g : SL(2, ℂ) := Quotient.out (z w)
    have hg : QuotientGroup.mk g = z w := Quotient.out_eq (z w)
    have hMaction : M = toInf F (toSLF F γ) w := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      change (w.embedding.comp (algebraMap (𝓞 F) F)) (γ i j) =
        w.embedding (algebraMap (𝓞 F) F (γ i j))
      rfl
    have hz' : toInf F (toSLF F γ) • z = z := by
      simpa only [instMulActionSLF, MulAction.compHom_smul_def, MonoidHom.comp_apply] using hz
    have hfixw : M • (z w) = z w := by
      have h := congrFun hz' w
      simpa [toInf, M, hMaction] using h
    have hfixrep : (QuotientGroup.mk (M * g) : H3) = (QuotientGroup.mk g : H3) := by
      calc
        (QuotientGroup.mk (M * g) : H3) = M • (QuotientGroup.mk g : H3) := by rfl
        _ = M • (z w) := by rw [hg]
        _ = z w := hfixw
        _ = (QuotientGroup.mk g : H3) := hg.symm
    have hrelSetoid : QuotientGroup.leftRel SU2 (M * g) g := Quotient.exact hfixrep
    have hrel : (M * g)⁻¹ * g ∈ SU2 := QuotientGroup.leftRel_apply.mp hrelSetoid
    have hrel' : g⁻¹ * M⁻¹ * g ∈ SU2 := by simpa [_root_.mul_inv_rev, mul_assoc] using hrel
    have hconj : g⁻¹ * M * g ∈ SU2 := by
      have h := SU2.inv_mem hrel'
      simpa [_root_.mul_inv_rev, mul_assoc] using h
    have htrU : Matrix.trace ((g⁻¹ * M * g : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ) := specMinkTraceConj g M
    have htrM : Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
      have htrD : w.embedding (algebraMap (𝓞 F) F d) =
          Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ) - 2 := by
        have hM00 : (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
            w.embedding (algebraMap (𝓞 F) F (γ 0 0)) := by
          change (w.embedding.comp (algebraMap (𝓞 F) F)) (γ 0 0) = _
          rfl
        have hM11 : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
            w.embedding (algebraMap (𝓞 F) F (γ 1 1)) := by
          change (w.embedding.comp (algebraMap (𝓞 F) F)) (γ 1 1) = _
          rfl
        change (w.embedding.comp (algebraMap (𝓞 F) F))
            (γ 0 0 + γ 1 1 - 2) = _
        rw [map_sub, map_add]
        rw [Matrix.trace, Fin.sum_univ_two]
        simp only [Matrix.diag_apply, hM00, hM11]
        simp only [RingHom.comp_apply, map_ofNat]
      have hm : w.embedding (algebraMap (𝓞 F) F d) = 0 := by simp [hd0]
      rw [htrD] at hm
      exact sub_eq_zero.mp hm
    have hUone : g⁻¹ * M * g = 1 :=
      specMink_SU2_trace_two_eq_one (g⁻¹ * M * g) hconj (htrU.trans htrM)
    have hMone : M = 1 := by
      calc
        M = g * (g⁻¹ * M * g) * g⁻¹ := by group
        _ = 1 := by rw [hUone]; group
    exact hMone
  have hγone : γ = 1 := by
    have hw : Nonempty (InfinitePlace F) := Fintype.card_pos_iff.mp Fintype.card_pos
    let w₀ : InfinitePlace F := Classical.choice hw
    have hRingInj : Function.Injective (w₀.embedding.comp (algebraMap (𝓞 F) F)) :=
      w₀.embedding.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 F) F)
    let f : SL(2, 𝓞 F) →* SL(2, ℂ) :=
      Matrix.SpecialLinearGroup.map (w₀.embedding.comp (algebraMap (𝓞 F) F))
    have hinj : Function.Injective f := by
      intro A B h
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      apply hRingInj
      have h' := congrArg (fun M : SL(2, ℂ) => (M : Matrix (Fin 2) (Fin 2) ℂ) i j) h
      change (w₀.embedding.comp (algebraMap (𝓞 F) F)) (A i j) =
        (w₀.embedding.comp (algebraMap (𝓞 F) F)) (B i j) at h'
      exact h'
    apply hinj
    simpa [f] using hγfix w₀
  exact hγone

end ArtinPrimitiveRoots.A1.Spec
