import ArtinPrimitiveRoots.A2.Proofs.A2_ADDSIEVE_OPUS.Rows

/-!
# Additive large sieve: assembly

`sieve_main` is `lem_additive_sieve` with the window, phase and congruence definitions of
`A2/Poisson/Results.lean` unfolded and with the candidate frequencies described by their
denominator ideals (`candidate_data`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.addsieve_opus

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem phaseChar_basisProduct (D : A1.FieldData F) (S : A1.SData F CE condη)
    (A : A1.AddCharData F) (x : F) (y : 𝓞 F) :
    phaseChar S A x y = ∏ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      OAI.LargePrimeGaps.bvExp
        ((((RingOfIntegers.basis F).equivFun y i : ℤ) : ℝ) * theta S A x i) := by
  rw [ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveCharacter_basisExpansion
    (phaseChar S A x) (phaseChar_norm D S A x) y]
  simp_rw [OAI.LargePrimeGaps.bvExp]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [theta, Module.Basis.equivFun_apply]
  push_cast
  ring

theorem add_pow_le_two_pow_mul (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (n : ℕ) :
    (X + Y) ^ n ≤ 2 ^ n * (X ^ n + Y ^ n) := by
  rcases le_total X Y with h | h
  · calc (X + Y) ^ n ≤ (2 * Y) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * Y ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * (X ^ n + Y ^ n) := by
        have := pow_nonneg hX n
        gcongr
        linarith
  · calc (X + Y) ^ n ≤ (2 * X) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * X ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * (X ^ n + Y ^ n) := by
        have := pow_nonneg hY n
        gcongr
        linarith

theorem rpow_one_div_pow {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (x ^ ((1 : ℝ) / (n : ℝ))) ^ n = x := by
  rw [one_div, Real.rpow_inv_natCast_pow hx hn]

theorem two_mul_numComplex (D : A1.FieldData F) :
    (2 * (A1.numComplex F : ℝ)) = (Module.finrank ℚ F : ℝ) := by
  have : IsTotallyComplex F := D.isTotallyComplex
  have h : 2 * A1.numComplex F = Module.finrank ℚ F := by
    unfold A1.numComplex
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, IsTotallyComplex.finrank]
  exact_mod_cast h

theorem conductorBasisMultiplicationBound_nonneg :
    0 ≤ ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F) := by
  unfold ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound
  positivity

set_option maxHeartbeats 1000000 in
/-- The additive large sieve with the window, phases and congruences unfolded. -/
theorem sieve_main (D : A1.FieldData F) (S : A1.SData F CE condη) (A : A1.AddCharData F)
    (K : Set S.FS) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N V : ℝ, (hN : 2 ≤ N) → 2 ≤ V →
      ∀ W : S.R → Prop,
        (∀ m, W m → ∃ x ∈ K, S.diag (m : F) = S.ell D N (by linarith) * x) →
      ∀ P : Finset S.FS,
        (∀ α ∈ P, ∃ J : Ideal (𝓞 F), ∃ a : F, J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ V ∧
          S.diag a = α ∧ ∀ n ∈ J, ∀ y : 𝓞 F,
            S.e A (S.diag (algebraMap (𝓞 F) F n * algebraMap (𝓞 F) F y * a)) = 1) →
        (∀ α ∈ P, ∀ β ∈ P, α ≠ β → ¬ ∃ r : S.R, α - β = S.diag (r : F)) →
        ∀ b : S.FS → ℂ,
          (∑' m : {m : S.R // W m}, ‖∑ α ∈ P, b α * S.e A (S.diag (m.1 : F) * α)‖ ^ 2 ≤
              C * (N + V ^ 2) * ∑ α ∈ P, ‖b α‖ ^ 2) ∧
          (∀ c' : S.R → ℂ, ∑ α ∈ P,
              ‖∑' m : {m : S.R // W m}, c' m.1 * S.e A (S.diag (m.1 : F) * α)‖ ^ 2 ≤
              C * (N + V ^ 2) * ∑' m : {m : S.R // W m}, ‖c' m.1‖ ^ 2) := by
  classical
  have : IsTotallyComplex F := D.isTotallyComplex
  obtain ⟨c, hc0, hcK⟩ := compact_scale S K hK
  obtain ⟨R, hR0, hRK⟩ := compact_arch_bound S K hK
  have hcF : algebraMap (𝓞 F) F c ≠ 0 := by
    intro h
    exact hc0 ((FaithfulSMul.algebraMap_injective (𝓞 F) F) (by simpa using h))
  let n : ℕ := Module.finrank ℚ F
  have hn : 0 < n := Module.finrank_pos
  have hcardI : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = n :=
    (Module.finrank_eq_card_basis (NumberField.integralBasis F)).symm
  let C1 : ℝ := coordConst F c R
  have hC1 : 0 ≤ C1 := coordConst_nonneg c hR0
  let Bm : ℝ := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F)
  have hBm : 0 ≤ Bm := conductorBasisMultiplicationBound_nonneg
  let Nc : ℝ := (Ideal.absNorm (Ideal.span {c}) : ℝ)
  have hNc : 0 ≤ Nc := Nat.cast_nonneg _
  let C2 : ℝ := 4 * (n : ℝ) * (Bm + 1) * (Nc ^ 2) ^ ((1 : ℝ) / (n : ℝ))
  have hNc0 : 0 < Nc := by
    have hpos : 0 < Ideal.absNorm (Ideal.span {c}) := by
      apply Nat.pos_of_ne_zero
      intro h
      have := Ideal.absNorm_eq_zero_iff.mp h
      exact hc0 (Ideal.span_singleton_eq_bot.mp this)
    show (0 : ℝ) < (Ideal.absNorm (Ideal.span {c}) : ℝ)
    exact_mod_cast hpos
  have hC2 : 0 < C2 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have : 0 < (Nc ^ 2) ^ ((1 : ℝ) / (n : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  let C3 : ℝ := C1 + 3 + 2 * C2
  have hC3 : 0 < C3 := by positivity
  refine ⟨(24 * C3) ^ n, by positivity, ?_⟩
  intro N V hN hV W hW P hPdata hPsep b
  have hN0 : 0 < N := by linarith
  -- integral coordinates of the rows
  have hrow : ∀ m : {m : S.R // W m}, ∃ y : 𝓞 F,
      algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F c * (m.1 : F) ∧
      ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
        |(((RingOfIntegers.basis F).equivFun y i : ℤ) : ℝ)| ≤
          C1 * N ^ ((1 : ℝ) / (2 * A1.numComplex F)) := by
    intro m
    obtain ⟨k, hk, hmk⟩ := hW m.1 m.2
    exact window_row D S K c hcK hR0 hRK hN0 m.1 k hk hmk
  choose y hy hycoord using hrow
  let X : ℝ := N ^ ((1 : ℝ) / (n : ℝ))
  have hXeq : N ^ ((1 : ℝ) / (2 * A1.numComplex F)) = X := by
    simp only [X]
    rw [two_mul_numComplex D]
  have hX1 : 1 ≤ X := Real.one_le_rpow (by linarith) (by positivity)
  let L : ℕ := ⌊C1 * X⌋₊
  let xc : {m : S.R // W m} → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ :=
    fun m i => (RingOfIntegers.basis F).equivFun (y m) i
  have hxL : ∀ m i, |xc m i| ≤ (L : ℤ) := by
    intro m i
    have h := hycoord m i
    rw [hXeq] at h
    have h' : ((xc m i).natAbs : ℝ) ≤ C1 * X := by
      have heq : ((xc m i).natAbs : ℝ) = |((xc m i : ℤ) : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [heq]
      exact h
    have h'' : (xc m i).natAbs ≤ L := Nat.le_floor h'
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h''
  have hinj : Function.Injective xc := by
    intro m m' h
    have hy' : y m = y m' := by
      apply (RingOfIntegers.basis F).equivFun.injective
      funext i
      exact congrFun h i
    have hF : algebraMap (𝓞 F) F c * (m.1 : F) = algebraMap (𝓞 F) F c * (m'.1 : F) := by
      rw [← hy m, ← hy m', hy']
    have hF' : (m.1 : F) = (m'.1 : F) := mul_left_cancel₀ hcF hF
    exact Subtype.ext (Subtype.ext hF')
  have hfinite : Finite {m : S.R // W m} := by
    haveI : Finite (Set.Icc (-(L : ℤ)) (L : ℤ)) := (Set.finite_Icc _ _).to_subtype
    refine Finite.of_injective
      (fun m : {m : S.R // W m} => fun i =>
        (⟨xc m i, Set.mem_Icc.mpr (abs_le.mp (hxL m i))⟩ : Set.Icc (-(L : ℤ)) (L : ℤ))) ?_
    intro m m' h
    apply hinj
    funext i
    have := congrFun h i
    exact congrArg Subtype.val this
  letI : Fintype {m : S.R // W m} := Fintype.ofFinite _
  -- frequency data and separation
  choose! J a hJ hNJ hdiag hann using hPdata
  let θ : S.FS → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ :=
    fun α => theta S A (a α / algebraMap (𝓞 F) F c)
  let Y : ℝ := (V ^ 2) ^ ((1 : ℝ) / (n : ℝ))
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by nlinarith) (by positivity)
  have hCY : 0 < C2 * Y := by positivity
  let D' : ℕ := ⌈C2 * Y⌉₊
  have hD'pos : 0 < D' := Nat.ceil_pos.mpr hCY
  have hsepEq : sepConst F c V = 1 / (C2 * Y) := by
    unfold sepConst
    have hsplit : ((Nc * V) ^ 2) ^ ((1 : ℝ) / (n : ℝ)) =
        (Nc ^ 2) ^ ((1 : ℝ) / (n : ℝ)) * Y := by
      rw [mul_pow]
      exact Real.mul_rpow (by positivity) (by positivity)
    change 1 / (4 * (n : ℝ) * (Bm + 1) * ((Nc * V) ^ 2) ^ ((1 : ℝ) / (n : ℝ))) = 1 / (C2 * Y)
    rw [hsplit]
    simp only [C2]
    ring
  have h1D : 1 / (D' : ℝ) ≤ sepConst F c V := by
    rw [hsepEq]
    exact one_div_le_one_div_of_le hCY (Nat.le_ceil _)
  have hsep : ∀ α ∈ P, ∀ β ∈ P, α ≠ β → ∃ k, ∀ m : ℤ,
      1 / (D' : ℝ) ≤ |θ α k - θ β k - (m : ℝ)| := by
    intro α hα β hβ hne
    have hnot : a α - a β ∉ S.R := by
      intro hmem
      apply hPsep α hα β hβ hne
      refine ⟨⟨a α - a β, hmem⟩, ?_⟩
      calc α - β = S.diag (a α) - S.diag (a β) := by rw [hdiag α hα, hdiag β hβ]
        _ = S.diag (a α - a β) := (map_sub _ _ _).symm
    obtain ⟨k, hk⟩ := phase_separation D S A c hc0 hV (J α) (J β) (a α) (a β)
      (hJ α hα) (hJ β hβ) (hNJ α hα) (hNJ β hβ) (hann α hα) (hann β hβ) hnot
    exact ⟨k, fun m => h1D.trans (hk m)⟩
  -- phases in coordinates
  have hphase : ∀ m : {m : S.R // W m}, ∀ α ∈ P,
      S.e A (S.diag (m.1 : F) * α) =
        ∏ i, OAI.LargePrimeGaps.bvExp ((xc m i : ℝ) * θ α i) := by
    intro m α hα
    calc S.e A (S.diag (m.1 : F) * α) = S.e A (S.diag (m.1 : F) * S.diag (a α)) := by
          rw [hdiag α hα]
      _ = phaseChar S A (a α / algebraMap (𝓞 F) F c) (y m) := by
          rw [phaseChar_apply, ← map_mul, hy m]
          congr 2
          field_simp
      _ = _ := phaseChar_basisProduct D S A _ (y m)
  -- the dual inequality for arbitrary row coefficients
  let Δ : ℝ := (12 * (((L + 1 : ℕ) : ℝ) + 2 * (D' : ℝ))) ^ n
  have hΔ0 : 0 ≤ Δ := by positivity
  have hdual : ∀ g : {m : S.R // W m} → ℂ,
      ∑ α ∈ P, ‖∑ m ∈ Finset.univ, g m * S.e A (S.diag (m.1 : F) * α)‖ ^ 2 ≤
        Δ * ∑ m ∈ Finset.univ, ‖g m‖ ^ 2 := by
    intro g
    have h := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorFiniteDimLargeSieve P θ L D'
      hD'pos hsep Finset.univ xc hxL hinj g
    rw [hcardI] at h
    calc ∑ α ∈ P, ‖∑ m ∈ Finset.univ, g m * S.e A (S.diag (m.1 : F) * α)‖ ^ 2 =
        ∑ α ∈ P, ‖∑ m ∈ Finset.univ, g m *
          ∏ i, OAI.LargePrimeGaps.bvExp ((xc m i : ℝ) * θ α i)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun α hα => ?_
          congr 2
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hphase m α hα]
      _ ≤ Δ * ∑ m ∈ Finset.univ, ‖g m‖ ^ 2 := h
  -- the constant
  have hΔC : Δ ≤ (24 * C3) ^ n * (N + V ^ 2) := by
    have hL : (L : ℝ) ≤ C1 * X := Nat.floor_le (by positivity)
    have hD : (D' : ℝ) ≤ C2 * Y + 1 := (Nat.ceil_lt_add_one hCY.le).le
    have hbase : 12 * (((L + 1 : ℕ) : ℝ) + 2 * (D' : ℝ)) ≤ 12 * C3 * (X + Y) := by
      push_cast
      simp only [C3]
      nlinarith
    have hX0 : 0 ≤ X := by linarith
    have hY0 : 0 ≤ Y := by linarith
    have hXn : X ^ n = N := rpow_one_div_pow (by linarith) hn.ne'
    have hYn : Y ^ n = V ^ 2 := rpow_one_div_pow (by positivity) hn.ne'
    calc Δ ≤ (12 * C3 * (X + Y)) ^ n := pow_le_pow_left₀ (by positivity) hbase n
      _ = (12 * C3) ^ n * (X + Y) ^ n := by rw [mul_pow]
      _ ≤ (12 * C3) ^ n * (2 ^ n * (X ^ n + Y ^ n)) :=
          mul_le_mul_of_nonneg_left (add_pow_le_two_pow_mul X Y hX0 hY0 n) (by positivity)
      _ = (24 * C3) ^ n * (N + V ^ 2) := by
          have h24 : (24 : ℝ) ^ n = 2 ^ n * 12 ^ n := by
            rw [← mul_pow]
            norm_num
          rw [hXn, hYn, mul_pow, mul_pow, h24]
          ring
  constructor
  · rw [tsum_fintype]
    have h := dual_to_primal P Finset.univ
      (fun m α => S.e A (S.diag ((m : {m : S.R // W m}).1 : F) * α)) Δ hΔ0 hdual b
    refine h.trans (mul_le_mul_of_nonneg_right hΔC ?_)
    exact Finset.sum_nonneg fun _ _ => by positivity
  · intro c'
    simp only [tsum_fintype]
    refine (hdual (fun m => c' m.1)).trans (mul_le_mul_of_nonneg_right hΔC ?_)
    exact Finset.sum_nonneg fun _ _ => by positivity

end ArtinPrimitiveRoots.Proofs.addsieve_opus
