import ArtinPrimitiveRoots.A2.Proofs.A2_ADDSIEVE_OPUS.Core

/-!
# Additive large sieve: compact windows and integral row coordinates
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.addsieve_opus

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem absFin_eq_norm' (v : A1.FinPlace F) (x : v.adicCompletion F) :
    A1.absFin v x = ‖x‖ := by
  unfold A1.absFin
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
  exact (FinitePlace.norm_def v x).symm

theorem norm_algebraMap_adic (v : A1.FinPlace F) (x : F) :
    ‖algebraMap F (v.adicCompletion F) x‖ = ‖FinitePlace.embedding v x‖ := by
  rw [← absFin_eq_norm', A1.absFin_algebraMap]

/-- A compact window has bounded archimedean components. -/
theorem compact_arch_bound (S : A1.SData F CE condη) (K : Set S.FS) (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ K, ∀ w : InfinitePlace F, ‖x.2 w‖ ≤ R := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : S.FS => x.2) continuous_snd.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx w => ?_⟩
  exact (norm_le_pi_norm (x.2) w).trans ((hC x hx).trans (le_max_left _ _))

/-- A compact window has bounded finite components. -/
theorem compact_fin_bound (S : A1.SData F CE condη) (K : Set S.FS) (hK : IsCompact K) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x ∈ K, ∀ v : S.Sf, ‖x.1 v‖ ≤ H := by
  have hv : ∀ v : S.Sf, ∃ C : ℝ, ∀ x ∈ K, ‖x.1 v‖ ≤ C := by
    intro v
    exact hK.exists_bound_of_continuousOn
      (f := fun x : S.FS => x.1 v) ((continuous_apply v).comp continuous_fst).continuousOn
  choose C hC using hv
  refine ⟨∑ v, |C v|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x hx v => ?_⟩
  calc ‖x.1 v‖ ≤ C v := hC v x hx
    _ ≤ |C v| := le_abs_self _
    _ ≤ ∑ v, |C v| :=
      Finset.single_le_sum (f := fun v => |C v|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)

/-- An integral scaling making every finite component of a compact window integral. -/
theorem compact_scale (S : A1.SData F CE condη) (K : Set S.FS) (hK : IsCompact K) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ K, ∀ v : S.Sf,
      ‖algebraMap F (v.1.adicCompletion F) (algebraMap (𝓞 F) F c) * x.1 v‖ ≤ 1 := by
  classical
  obtain ⟨H, hH0, hH⟩ := compact_fin_bound S K hK
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hn : 0 < n := Fintype.card_pos
  let π : S.Sf → 𝓞 F := fun v =>
    Classical.choose (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorExistsPrincipalPowerGenerator v.1)
  have hπ (v : S.Sf) : Ideal.span {π v} = v.1.asIdeal ^ n := by
    simpa [n] using Classical.choose_spec
      (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorExistsPrincipalPowerGenerator v.1)
  have hπ0 (v : S.Sf) : π v ≠ 0 := by
    intro hz
    have hpow0 : v.1.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ v.1.ne_bot
    have hspan0 : Ideal.span {π v} = ⊥ := by simp [hz]
    exact hpow0 (hπ v ▸ hspan0)
  let N : ℕ := ⌊H⌋₊ + 1
  have hHN : H < (N : ℝ) := by
    simpa [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one H
  have hpowN : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    have h := one_add_le_pow_of_two_add_nonneg (R := ℝ) (a := 1) (by norm_num) N
    norm_num at h
    linarith
  have hHpow : H ≤ (2 : ℝ) ^ N := le_trans hHN.le hpowN
  let c : 𝓞 F := ∏ v : S.Sf, π v ^ N
  have hc0 : c ≠ 0 := by
    dsimp [c]
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact pow_ne_zero _ (hπ0 v)
  have hfactor (v : S.Sf) (w : A1.FinPlace F) :
      ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π v ^ N))‖ ≤
        if v.1 = w then (1 / 2 : ℝ) ^ N else 1 :=
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorPrincipalPower_norm_bound v.1 w hn (π v) (hπ v) N
  have hnormcS (w : S.Sf) :
      ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ ≤ ((2 : ℝ) ^ N)⁻¹ := by
    have hrepr :
        ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ =
          ∏ v : S.Sf, ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (π v ^ N))‖ := by
      simp [c, map_prod, norm_prod]
    rw [hrepr]
    have hprod :
        (∏ v : S.Sf, ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (π v ^ N))‖) ≤
          ∏ v : S.Sf, if v.1 = w.1 then (1 / 2 : ℝ) ^ N else 1 := by
      apply Finset.prod_le_prod₀
      · intro v _
        exact norm_nonneg _
      · intro v _
        exact hfactor v w.1
    have hprod_ite :
        (∏ v : S.Sf, if v.1 = w.1 then (1 / 2 : ℝ) ^ N else 1) = (1 / 2 : ℝ) ^ N := by
      have heq (v : S.Sf) : (v.1 = w.1) ↔ v = w := Subtype.ext_iff.symm
      simp [heq]
    rw [hprod_ite] at hprod
    have hhalf : (1 / 2 : ℝ) ^ N = ((2 : ℝ) ^ N)⁻¹ := by rw [one_div, inv_pow]
    simpa [hhalf] using hprod
  refine ⟨c, hc0, fun x hx v => ?_⟩
  rw [norm_mul, norm_algebraMap_adic]
  have hmul : ‖FinitePlace.embedding v.1 (algebraMap (𝓞 F) F c)‖ * ‖x.1 v‖ ≤
      ((2 : ℝ) ^ N)⁻¹ * H :=
    mul_le_mul (hnormcS v) (hH x hx v) (norm_nonneg _) (by positivity)
  have hfinal : ((2 : ℝ) ^ N)⁻¹ * H ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  exact hmul.trans hfinal

/-- The constant in the integral-basis coordinate bound of window rows. -/
def coordConst (F : Type) [Field F] [NumberField F] (c : 𝓞 F) (R : ℝ) : ℝ :=
  (‖(NumberField.canonicalEmbedding.latticeBasis F).equivFunL.toContinuousLinearMap‖ + 1) *
    ((1 + ∑ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F c)‖) * R)

theorem coordConst_nonneg (c : 𝓞 F) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ coordConst F c R := by
  unfold coordConst
  have h1 : 0 ≤ 1 + ∑ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F c)‖ := by
    positivity
  positivity

/-- A row of the window, scaled by `c`, is an integer whose integral-basis coordinates are
`O(N^{1/(2r)})`. -/
theorem window_row (D : A1.FieldData F) (S : A1.SData F CE condη) (K : Set S.FS)
    (c : 𝓞 F)
    (hcK : ∀ x ∈ K, ∀ v : S.Sf,
      ‖algebraMap F (v.1.adicCompletion F) (algebraMap (𝓞 F) F c) * x.1 v‖ ≤ 1)
    {R : ℝ} (hR0 : 0 ≤ R) (hRK : ∀ x ∈ K, ∀ w : InfinitePlace F, ‖x.2 w‖ ≤ R)
    {N : ℝ} (hN : 0 < N) (m : S.R) (k : S.FS) (hk : k ∈ K)
    (hm : S.diag (m : F) = S.ell D N hN * k) :
    ∃ y : 𝓞 F, algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F c * (m : F) ∧
      ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
        |(((RingOfIntegers.basis F).equivFun y i : ℤ) : ℝ)| ≤
          coordConst F c R * N ^ ((1 : ℝ) / (2 * A1.numComplex F)) := by
  classical
  -- finite components
  have hfin (v : S.Sf) : algebraMap F (v.1.adicCompletion F) (m : F) = k.1 v := by
    have h := congrArg (fun z : S.FS => z.1 v) hm
    simpa [A1.SData.ell, A1.SData.diag] using h
  have harch (w : InfinitePlace F) :
      w.embedding (m : F) = ((N ^ ((1 : ℝ) / (2 * A1.numComplex F)) : ℝ) : ℂ) * k.2 w := by
    have h := congrArg (fun z : S.FS => z.2 w) hm
    simpa [A1.SData.ell, A1.SData.diag] using h
  -- integrality of `c m`
  have hint : algebraMap (𝓞 F) F c * (m : F) ∈ (algebraMap (𝓞 F) F).range := by
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    by_cases hv : v ∈ S.Sf
    · let vS : S.Sf := ⟨v, hv⟩
      have hlocal : A1.absFin v
          (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c * (m : F))) ≤ 1 := by
        rw [absFin_eq_norm', map_mul, hfin vS]
        exact hcK k hk vS
      rw [A1.absFin_algebraMap] at hlocal
      have hvalnormR :
          ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
            (v.valuation F (algebraMap (𝓞 F) F c * (m : F))) : NNReal) : ℝ) ≤ 1 := by
        simpa [FinitePlace.norm_embedding'] using hlocal
      have hvalnorm :
          WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
            (v.valuation F (algebraMap (𝓞 F) F c * (m : F))) ≤ 1 := by
        exact_mod_cast hvalnormR
      have hvalnorm' :
          WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
            (v.valuation F (algebraMap (𝓞 F) F c * (m : F))) ≤
          WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) 1 := by
        simpa using hvalnorm
      exact (WithZeroMulInt.toNNReal_strictMono
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le.mp hvalnorm'
    · have hc : v.valuation F (algebraMap (𝓞 F) F c) ≤ 1 := by simpa using v.valuation_le_one c
      have hx : v.valuation F (m : F) ≤ 1 := m.property v hv
      rw [map_mul]
      exact mul_le_one' hc hx
  obtain ⟨y, hy⟩ := hint
  refine ⟨y, hy, ?_⟩
  -- archimedean size
  let Mc : ℝ := 1 + ∑ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F c)‖
  let T : ℝ := N ^ ((1 : ℝ) / (2 * A1.numComplex F))
  have hT : 0 ≤ T := Real.rpow_nonneg hN.le _
  have hEmb : ∀ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F y)‖ ≤ Mc * (R * T) := by
    intro w
    have hcEmb : ‖w.embedding (algebraMap (𝓞 F) F c)‖ ≤ Mc := by
      have hsingle : ‖w.embedding (algebraMap (𝓞 F) F c)‖ ≤
          ∑ w' : InfinitePlace F, ‖w'.embedding (algebraMap (𝓞 F) F c)‖ :=
        Finset.single_le_sum (f := fun w' : InfinitePlace F =>
          ‖w'.embedding (algebraMap (𝓞 F) F c)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
      simp only [Mc]
      linarith
    have hmEmb : ‖w.embedding (m : F)‖ ≤ R * T := by
      rw [harch w, norm_mul, Complex.norm_real, Real.norm_of_nonneg hT, mul_comm]
      exact mul_le_mul_of_nonneg_right (hRK k hk w) hT
    rw [hy, map_mul, norm_mul]
    exact mul_le_mul hcEmb hmEmb (norm_nonneg _) (by positivity)
  have hRT : 0 ≤ Mc * (R * T) := by positivity
  intro i
  have h := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralBasis_coords_bound y hRT hEmb i
  refine h.trans (le_of_eq ?_)
  simp only [coordConst, Mc, T]
  ring

end ArtinPrimitiveRoots.Proofs.addsieve_opus
