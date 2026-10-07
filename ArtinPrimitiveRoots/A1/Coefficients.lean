import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.A1.Coeff.IdealSummable

/-!
# A1 interface, §6: the coefficient family

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 6. The coefficient family (02a) -/

/-- `P_G(t) = (2√π)^{-1} exp(-(log t)²/4)` (eq:reflection-gaussian). -/
def PG (t : ℝ) : ℝ := (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log t) ^ 2 / 4)

/-- Exterior ideals, squarefree exterior ideals (index types). -/
def SData.ExtIdeal (S : SData F CE condη) := {I : Ideal (𝓞 F) // S.IsExterior I}
def SData.SqfExtIdeal (S : SData F CE condη) := {I : Ideal (𝓞 F) // S.IsExterior I ∧ Squarefree I}

/-- `B_m(Z) = Σ_{𝔠 sqfree, 𝔫} γ_2(𝔠) q_𝔠^{-1/2} q_𝔫^{-1} ϑ(𝔄) χ_𝔄(m) P_G(q_𝔄/Z)`, `𝔄 = 𝔠𝔫³`
(eq:reflection-B-definition). `cgen` picks an allowed generator of each squarefree exterior ideal
(the value does not depend on the choice). -/
def Bm (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (ϑ : HeckeChar F)
    (cgen : S.SqfExtIdeal → F) (m : F) (Z : ℝ) : ℂ :=
  ∑' p : S.SqfExtIdeal × S.ExtIdeal,
    gamma D S A 2 p.1.1 (cgen p.1) *
      ((((Ideal.absNorm p.1.1 : ℝ) ^ (-(1 / 2 : ℝ)) * (Ideal.absNorm p.2.1 : ℝ)⁻¹) : ℝ) : ℂ) *
      ϑ.idealValue (p.1.1 * p.2.1 ^ 3) * chiIdealPow D (p.1.1 * p.2.1 ^ 3) m 1 *
      (PG ((Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) / Z) : ℂ)

private theorem psiC_add (z w : ℂ) : psiC (z + w) = psiC z * psiC w := by
  unfold psiC
  have harg :
      -(4 * Real.pi * Complex.I * ((z + w).re : ℂ)) =
        -(4 * Real.pi * Complex.I * (z.re : ℂ)) +
          -(4 * Real.pi * Complex.I * (w.re : ℂ)) := by
    rw [Complex.add_re, Complex.ofReal_add]
    ring
  rw [harg, Complex.exp_add]

private theorem e_diag_add (S : SData F CE condη) (A : AddCharData F) (x y : F) :
    S.e A (S.diag (x + y)) = S.e A (S.diag x) * S.e A (S.diag y) := by
  classical
  have hdiag : S.diag (x + y) = S.diag x + S.diag y := map_add (S.diag) x y
  unfold SData.e
  rw [hdiag]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, AddChar.map_add_eq_mul]
  simp_rw [psiC_add]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

private theorem count_spanSingleton_div (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private theorem count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) =
      -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private theorem count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
    (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z = v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    count_spanSingleton_div v (algebraMap (𝓞 F) F n) (algebraMap (𝓞 F) F (d : 𝓞 F))
      hmapn hmapd,
    count_spanSingleton_eq_neg_log_intValuation v n hn,
    count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

/-- The additive character on a residue class has finite order: the ideal norm kills it. -/
private theorem e_quotient_norm_one (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (c : Fˣ)
    (hc : S.IsGen (c : F) I) (x : 𝓞 F) :
    ‖S.e A (S.diag (algebraMap (𝓞 F) F x / (c : F)))‖ = 1 := by
  sorry

private theorem chi_norm_one (D : FieldData F) (P : FinPlace F) (x : F)
    (hx : residue P x ≠ 0) : ‖chi D P x‖ = 1 := by
  let ζ : rootsOfUnity 6 (𝓞 F) := chiAlg P x
  have hζ : (ζ : (𝓞 F)ˣ) ^ 6 = 1 :=
    (mem_rootsOfUnity 6 (ζ : (𝓞 F)ˣ)).mp ζ.property
  let ζ0 : 𝓞 F := ((ζ : (𝓞 F)ˣ) : 𝓞 F)
  have hζOF : (((ζ : (𝓞 F)ˣ) : 𝓞 F) ^ 6) = 1 := by
    simpa [ζ0] using congrArg Units.val hζ
  have hζC : (D.σ0 (algebraMap (𝓞 F) F ζ0)) ^ 6 = 1 := by
    calc
      _ = D.σ0 (algebraMap (𝓞 F) F (ζ0 ^ 6)) := by simp only [map_pow]
      _ = 1 := by rw [hζOF]; simp
  have hpow : (chi D P x) ^ 6 = 1 := by
    rw [chi, if_neg hx]
    exact hζC
  have hfin : IsOfFinOrder (chi D P x) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨6, by norm_num, hpow⟩
  exact hfin.norm_eq_one

private theorem chiPow_norm_le_one (D : FieldData F) (P : FinPlace F) (x : F) (j : ℤ) :
    ‖chiPow D P x j‖ ≤ 1 := by
  by_cases hx : residue P x = 0
  · simp [chiPow, hx]
  · simp [chiPow, hx, chi_norm_one D P x hx]

private theorem norm_multiset_map_prod_le_one {α : Type*} (s : Multiset α) (f : α → ℂ)
    (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) <| ih fun x hx =>
      hf x (Multiset.mem_cons_of_mem hx)

private theorem chiIdealPow_norm_le_one (D : FieldData F) (I : Ideal (𝓞 F)) (x : F) (j : ℤ) :
    ‖chiIdealPow D I x j‖ ≤ 1 := by
  unfold chiIdealPow
  apply norm_multiset_map_prod_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using chiPow_norm_le_one D ⟨P, h.1, h.2⟩ x j
  · simp [h]

private theorem HeckeChar.primeValue_norm_le_one (χ : HeckeChar F)
    (hχ : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (v : FinPlace F) :
    ‖χ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with h
  · have hχ' := hχ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
      (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))))
    exact le_of_eq (by simpa [HeckeChar.loc] using hχ')
  · simp

private theorem HeckeChar.idealValue_norm_le_one (χ : HeckeChar F)
    (hχ : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (I : Ideal (𝓞 F)) :
    ‖χ.idealValue I‖ ≤ 1 := by
  unfold HeckeChar.idealValue
  apply norm_multiset_map_prod_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using χ.primeValue_norm_le_one hχ ⟨P, h.1, h.2⟩
  · simp [h]

private theorem PG_power_bound (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → PG t ≤ C * Real.rpow t (-σ) := by
  refine ⟨(2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2), by positivity, ?_⟩
  intro t ht
  have hx : -(Real.log t) ^ 2 / 4 ≤ σ ^ 2 - σ * Real.log t := by
    nlinarith [sq_nonneg (Real.log t - 2 * σ)]
  have he : Real.exp (-(Real.log t) ^ 2 / 4) ≤
      Real.exp (σ ^ 2 - σ * Real.log t) := Real.exp_le_exp.mpr hx
  have hpow : Real.rpow t (-σ) = Real.exp (Real.log t * (-σ)) :=
    Real.rpow_def_of_pos ht _
  rw [PG, hpow]
  calc
    (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log t) ^ 2 / 4) ≤
        (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2 - σ * Real.log t) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2) * Real.exp (Real.log t * (-σ)) := by
      rw [show σ ^ 2 - σ * Real.log t = σ ^ 2 + (-σ * Real.log t) by ring,
        Real.exp_add]
      rw [show -σ * Real.log t = Real.log t * (-σ) by ring]
      ring

private theorem gamma_norm_le_sqrt (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (c : Fˣ)
    (hc : S.IsGen (c : F) I) :
    ‖gamma D S A 2 I (c : F)‖ ≤ (Ideal.absNorm I : ℝ) ^ ((1 : ℝ) / 2) := by
  classical
  have hqpos : 0 < Ideal.absNorm I :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hI.1)⟩
  letI : Finite (𝓞 F ⧸ I) := (Ideal.absNorm_ne_zero_iff I).mp hqpos.ne'
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  let g (x : 𝓞 F ⧸ I) : ℂ :=
    chiIdealPow D I (algebraMap (𝓞 F) F x.out) 2 *
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / (c : F)))
  have hg (x : 𝓞 F ⧸ I) : ‖g x‖ ≤ 1 := by
    dsimp [g]
    calc
      _ ≤ ‖chiIdealPow D I (algebraMap (𝓞 F) F x.out) 2‖ *
          ‖S.e A (S.diag (algebraMap (𝓞 F) F x.out / (c : F)))‖ := norm_mul_le _ _
      _ ≤ 1 := mul_le_one₀ (chiIdealPow_norm_le_one D I _ 2)
        (norm_nonneg _) (e_quotient_norm_one D S A I hI c hc x.out).le
  have hsum : ‖∑ᶠ x : 𝓞 F ⧸ I, g x‖ ≤ (Ideal.absNorm I : ℝ) := by
    calc
      _ = ‖∑ x : 𝓞 F ⧸ I, g x‖ := by
        congr 1
        exact finsum_eq_finsetSum_of_support_subset g (s := Finset.univ)
          (by intro x hx; simp)
      _ ≤ ∑ x : 𝓞 F ⧸ I, ‖g x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : 𝓞 F ⧸ I, (1 : ℝ) := Finset.sum_le_sum fun x _ => hg x
      _ = (Fintype.card (𝓞 F ⧸ I) : ℝ) := by simp
      _ = (Ideal.absNorm I : ℝ) := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  let q : ℝ := Ideal.absNorm I
  have hq : 0 < q := Nat.cast_pos.mpr hqpos
  have hscale : 0 ≤ q ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hq.le _
  change ‖((q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∑ᶠ x : 𝓞 F ⧸ I, g x‖ ≤
    q ^ ((1 : ℝ) / 2)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hscale]
  calc
    q ^ (-(1 / 2 : ℝ)) * ‖∑ᶠ x : 𝓞 F ⧸ I, g x‖ ≤
        q ^ (-(1 / 2 : ℝ)) * q := mul_le_mul_of_nonneg_left hsum hscale
    _ = q ^ ((1 : ℝ) / 2) := by
      calc
        q ^ (-(1 / 2 : ℝ)) * q =
            q ^ (-(1 / 2 : ℝ)) * q ^ (1 : ℝ) := by congr 1; exact (Real.rpow_one q).symm
        _ = q ^ (-(1 / 2 : ℝ) + 1) := by rw [← Real.rpow_add hq]
        _ = q ^ ((1 : ℝ) / 2) := by congr 1 <;> ring

/-- eq:reflection-original-dirichlet-majorant (02a:54–62): absolute convergence. -/
theorem Bm_summable (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (H : HilbertData F)
    (Bd : BData S H) (ϑ : HeckeChar F) (hϑ : ∀ x, ‖((ϑ x : ℂˣ) : ℂ)‖ = 1)
    (cgen : S.SqfExtIdeal → F) (hc : ∀ I, ∃ c : Fˣ, (c : F) = cgen I ∧ S.IsGen (c : F) I.1 ∧ Bd.Allowed c)
    (m : F) (Z : ℝ) (hZ : 0 < Z) :
    Summable fun p : S.SqfExtIdeal × S.ExtIdeal =>
      ‖gamma D S A 2 p.1.1 (cgen p.1) *
      ((((Ideal.absNorm p.1.1 : ℝ) ^ (-(1 / 2 : ℝ)) * (Ideal.absNorm p.2.1 : ℝ)⁻¹) : ℝ) : ℂ) *
      ϑ.idealValue (p.1.1 * p.2.1 ^ 3) * chiIdealPow D (p.1.1 * p.2.1 ^ 3) m 1 *
      (PG ((Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) / Z) : ℂ)‖ := by
  classical
  obtain ⟨C, hC, hPG⟩ := PG_power_bound (3 : ℝ)
  let term (p : S.SqfExtIdeal × S.ExtIdeal) : ℂ :=
    gamma D S A 2 p.1.1 (cgen p.1) *
      ((((Ideal.absNorm p.1.1 : ℝ) ^ (-(1 / 2 : ℝ)) *
        (Ideal.absNorm p.2.1 : ℝ)⁻¹) : ℝ) : ℂ) *
      ϑ.idealValue (p.1.1 * p.2.1 ^ 3) *
      chiIdealPow D (p.1.1 * p.2.1 ^ 3) m 1 *
      (PG ((Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) / Z) : ℂ)
  let major (p : S.SqfExtIdeal × S.ExtIdeal) : ℝ :=
    (C * Z ^ 3) *
      ((Ideal.absNorm p.1.1 : ℝ) ^ (-3 : ℝ) *
        (Ideal.absNorm p.2.1 : ℝ) ^ (-10 : ℝ))
  have hSqf : Summable fun I : S.SqfExtIdeal =>
      (Ideal.absNorm I.1 : ℝ) ^ (-3 : ℝ) := by
    change Summable (fun I : {I : Ideal (𝓞 F) // S.IsExterior I ∧ Squarefree I} =>
      (Ideal.absNorm I.1 : ℝ) ^ (-3 : ℝ))
    have hs := (Coeff.summable_absNorm_rpow (F := F) 3 (by norm_num)).subtype
      (fun I => S.IsExterior I ∧ Squarefree I)
    exact hs.congr (fun I => rfl)
  have hExt : Summable fun I : S.ExtIdeal =>
      (Ideal.absNorm I.1 : ℝ) ^ (-10 : ℝ) := by
    change Summable (fun I : {I : Ideal (𝓞 F) // S.IsExterior I} =>
      (Ideal.absNorm I.1 : ℝ) ^ (-10 : ℝ))
    have hs := (Coeff.summable_absNorm_rpow (F := F) 10 (by norm_num)).subtype
      (fun I => S.IsExterior I)
    exact hs.congr (fun I => rfl)
  have hProd : Summable fun p : S.SqfExtIdeal × S.ExtIdeal =>
      (Ideal.absNorm p.1.1 : ℝ) ^ (-3 : ℝ) *
        (Ideal.absNorm p.2.1 : ℝ) ^ (-10 : ℝ) :=
    hSqf.mul_of_nonneg hExt
      (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hMajor : Summable major := by
    simpa [major] using hProd.mul_left (C * Z ^ 3)
  have hterm (p : S.SqfExtIdeal × S.ExtIdeal) : ‖term p‖ ≤ major p := by
    let I : Ideal (𝓞 F) := p.1.1
    let J : Ideal (𝓞 F) := p.2.1
    let qI : ℝ := (Ideal.absNorm I : ℝ)
    let qJ : ℝ := (Ideal.absNorm J : ℝ)
    obtain ⟨c, hcgen, hcgenI, hallowed⟩ := hc p.1
    have hIext : S.IsExterior I := p.1.2.1
    have hJext : S.IsExterior J := p.2.2
    have hqI : 0 < qI := by
      dsimp [qI, I]
      exact Nat.cast_pos.mpr <| Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨_, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hIext.1)⟩
    have hqJ : 0 < qJ := by
      dsimp [qJ, J]
      exact Nat.cast_pos.mpr <| Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨_, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hJext.1)⟩
    have hnormA :
        (Ideal.absNorm (I * J ^ 3) : ℝ) = qI * qJ ^ (3 : ℕ) := by
      dsimp [qI, qJ]
      norm_cast
      simp [map_mul, map_pow]
    have hqA : 0 < (Ideal.absNorm (I * J ^ 3) : ℝ) := by
      rw [hnormA]
      positivity
    have hgamma0 := gamma_norm_le_sqrt D S A I hIext c hcgenI
    have hgamma : ‖gamma D S A 2 I (cgen p.1)‖ ≤ qI ^ ((1 : ℝ) / 2) := by
      simpa [I, qI, ← hcgen] using hgamma0
    have htheta : ‖ϑ.idealValue (I * J ^ 3)‖ ≤ 1 :=
      HeckeChar.idealValue_norm_le_one ϑ hϑ (I * J ^ 3)
    have hchi : ‖chiIdealPow D (I * J ^ 3) m 1‖ ≤ 1 :=
      chiIdealPow_norm_le_one D (I * J ^ 3) m 1
    have ht : 0 < (Ideal.absNorm (I * J ^ 3) : ℝ) / Z := div_pos hqA hZ
    have hPG' := hPG ((Ideal.absNorm (I * J ^ 3) : ℝ) / Z) ht
    have hcastI : (qI ^ (3 : ℝ))⁻¹ = (qI ^ (3 : ℕ))⁻¹ :=
      congrArg Inv.inv (Real.rpow_natCast qI 3)
    have hcastJ : (qJ ^ (9 : ℝ))⁻¹ = (qJ ^ (9 : ℕ))⁻¹ :=
      congrArg Inv.inv (Real.rpow_natCast qJ 9)
    have hcastZ : Z ^ (3 : ℝ) = Z ^ (3 : ℕ) := Real.rpow_natCast Z 3
    have hnegI : qI ^ (-3 : ℝ) = (qI ^ (3 : ℕ))⁻¹ := by
      calc
        qI ^ (-3 : ℝ) = (qI ^ (3 : ℝ))⁻¹ := Real.rpow_neg hqI.le 3
        _ = (qI ^ (3 : ℕ))⁻¹ := hcastI
    have hnegJ : qJ ^ (-9 : ℝ) = (qJ ^ (9 : ℕ))⁻¹ := by
      calc
        qJ ^ (-9 : ℝ) = (qJ ^ (9 : ℝ))⁻¹ := Real.rpow_neg hqJ.le 9
        _ = (qJ ^ (9 : ℕ))⁻¹ := hcastJ
    have hPGmajorInv :
        PG ((Ideal.absNorm (I * J ^ 3) : ℝ) / Z) ≤
          C * Z ^ 3 * ((qI ^ (3 : ℕ))⁻¹) * ((qJ ^ (9 : ℕ))⁻¹) := by
      have hpower :
          ((qI * qJ ^ (3 : ℕ)) / Z) ^ (-3 : ℝ) =
            (qI ^ (3 : ℕ))⁻¹ * (qJ ^ (9 : ℕ))⁻¹ * Z ^ 3 := by
        rw [Real.div_rpow (mul_nonneg hqI.le (by positivity)) hZ.le,
          Real.mul_rpow hqI.le (by positivity : 0 ≤ qJ ^ (3 : ℕ)),
          ← Real.rpow_natCast qJ 3, ← Real.rpow_mul hqJ.le]
        rw [show ((3 : ℕ) : ℝ) * (-3 : ℝ) = -9 by norm_num,
          Real.rpow_neg hqI.le 3, Real.rpow_neg hqJ.le 9,
          Real.rpow_neg hZ.le 3, div_eq_mul_inv]
        simp only [inv_inv]
        rw [hcastI, hcastJ, hcastZ]
      calc
        _ ≤ C * ((Ideal.absNorm (I * J ^ 3) : ℝ) / Z) ^ (-3 : ℝ) := hPG'
        _ = C * Z ^ 3 * (qI ^ (3 : ℕ))⁻¹ * (qJ ^ (9 : ℕ))⁻¹ := by
          rw [hnormA, hpower]
          ring
    have hPGmajor :
        PG ((Ideal.absNorm (I * J ^ 3) : ℝ) / Z) ≤
          C * Z ^ 3 * qI ^ (-3 : ℝ) * qJ ^ (-9 : ℝ) := by
      rw [← hnegI, ← hnegJ] at hPGmajorInv
      simpa [mul_assoc] using hPGmajorInv
    have hcoef : 0 ≤ qI ^ (-(1 / 2 : ℝ)) * qJ⁻¹ := by positivity
    have hIpow : 0 ≤ qI ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hqI.le _
    have hJinv : 0 ≤ qJ⁻¹ := inv_nonneg.mpr hqJ.le
    have hPGnonneg : 0 ≤ PG ((Ideal.absNorm (I * J ^ 3) : ℝ) / Z) := by
      rw [PG]
      positivity
    have hnormTerm : ‖term p‖ =
        ‖gamma D S A 2 I (cgen p.1)‖ *
          (qI ^ (-(1 / 2 : ℝ)) * qJ⁻¹) *
          ‖ϑ.idealValue (I * J ^ 3)‖ *
          ‖chiIdealPow D (I * J ^ 3) m 1‖ *
          PG ((Ideal.absNorm (I * J ^ 3) : ℝ) / Z) := by
      change ‖gamma D S A 2 I (cgen p.1) *
          (((qI ^ (-(1 / 2 : ℝ)) * qJ⁻¹ : ℝ) : ℂ)) *
          ϑ.idealValue (I * J ^ 3) * chiIdealPow D (I * J ^ 3) m 1 *
          (PG ((Ideal.absNorm (I * J ^ 3) : ℝ) / Z) : ℂ)‖ = _
      simp only [norm_mul, Complex.norm_real]
      rw [Real.norm_of_nonneg hIpow, Real.norm_of_nonneg hJinv,
        Real.norm_of_nonneg hPGnonneg]
    rw [hnormTerm]
    calc
      _ ≤ qI ^ ((1 : ℝ) / 2) *
          (qI ^ (-(1 / 2 : ℝ)) * qJ⁻¹) * 1 * 1 *
          (C * Z ^ 3 * qI ^ (-3 : ℝ) * qJ ^ (-9 : ℝ)) := by
            gcongr
      _ = major p := by
        have hIexp : qI ^ ((1 : ℝ) / 2) * qI ^ (-(1 / 2 : ℝ)) *
            qI ^ (-3 : ℝ) = qI ^ (-3 : ℝ) := by
          rw [← Real.rpow_add hqI]
          simp
        have hJexp : qJ⁻¹ * qJ ^ (-9 : ℝ) = qJ ^ (-10 : ℝ) := by
          rw [← Real.rpow_neg_one qJ, ← Real.rpow_add hqJ]
          norm_num
        dsimp [major]
        calc
          qI ^ ((1 : ℝ) / 2) * (qI ^ (-(1 / 2 : ℝ)) * qJ⁻¹) * 1 * 1 *
              (C * Z ^ 3 * qI ^ (-3 : ℝ) * qJ ^ (-9 : ℝ)) =
              (C * Z ^ 3) *
                (qI ^ ((1 : ℝ) / 2) * qI ^ (-(1 / 2 : ℝ)) * qI ^ (-3 : ℝ)) *
                (qJ⁻¹ * qJ ^ (-9 : ℝ)) := by ring
          _ = (C * Z ^ 3) * qI ^ (-3 : ℝ) * qJ ^ (-10 : ℝ) := by
            rw [hIexp, hJexp] <;> ring
          _ = major p := by ring
  change Summable (fun p : S.SqfExtIdeal × S.ExtIdeal => ‖term p‖)
  exact hMajor.of_nonneg_of_le (fun p => norm_nonneg _) hterm


end ArtinPrimitiveRoots.A1
