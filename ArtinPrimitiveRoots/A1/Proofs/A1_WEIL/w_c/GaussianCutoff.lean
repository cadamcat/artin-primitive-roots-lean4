import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_c.GaussianNormSq

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.a1_weil_sol

variable {F : Type} [Field F] [NumberField F]

private def intRadiusCutoff (k : ℤ) : ℕ := (max 0 k).toNat

private theorem int_le_intRadiusCutoff (k : ℤ) : k ≤ intRadiusCutoff k := by
  have hnonneg : 0 ≤ max 0 k := le_max_left 0 k
  have hcast : (intRadiusCutoff k : ℤ) = max 0 k := by
    simp [intRadiusCutoff, Int.toNat_of_nonneg hnonneg]
  rw [hcast]
  exact le_max_right 0 k

theorem quadraticBallAnnihilator_eventually_trivial
    (A : AddCharData F) (v : FinPlace F) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∀ t ∈ quadraticBallAnnihilator A v N a,
      A.ψ v ((a : v.adicCompletion F) * t ^ 2) = 1 := by
  classical
  have hnontriv : ∃ z : v.adicCompletion F, A.ψ v z ≠ 1 := by
    by_contra hn
    apply hψ.2.1
    ext z
    by_contra h
    exact hn ⟨z, h⟩
  obtain ⟨z₀, hz₀⟩ := hnontriv
  have hz₀ne : z₀ ≠ 0 := by
    intro hz
    subst z₀
    simpa using hz₀
  have htwo : (2 : v.adicCompletion F) ≠ 0 := by norm_num
  have ha : (a : v.adicCompletion F) ≠ 0 := a.ne_zero
  have hva : Valued.v (a : v.adicCompletion F) ≠ 0 :=
    (Valued.v.ne_zero_iff).2 ha
  have hvz₀ : Valued.v z₀ ≠ 0 := (Valued.v.ne_zero_iff).2 hz₀ne
  have hvtwo : Valued.v (2 : v.adicCompletion F) ≠ 0 :=
    (Valued.v.ne_zero_iff).2 htwo
  let α : ℤ := WithZero.log (Valued.v (a : v.adicCompletion F))
  let β : ℤ := WithZero.log (Valued.v z₀) -
    WithZero.log (Valued.v (2 : v.adicCompletion F)) - min 0 α
  let N₀ := intRadiusCutoff β
  have hβN₀ : β ≤ N₀ := int_le_intRadiusCutoff β
  refine ⟨N₀, ?_⟩
  intro N hN t htD
  by_contra hquad
  have hnotInt : (a : v.adicCompletion F) * t ^ 2 ∉ v.adicCompletionIntegers F := by
    intro htint
    exact hquad (A.integral v _ htint)
  have hvalgt : 1 < Valued.v ((a : v.adicCompletion F) * t ^ 2) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hnotInt
    exact not_le.mp hnotInt
  have hqne : Valued.v ((a : v.adicCompletion F) * t ^ 2) ≠ 0 :=
    ne_of_gt (lt_trans (by simp) hvalgt)
  have hqne' : (a : v.adicCompletion F) * t ^ 2 ≠ 0 :=
    (Valued.v.ne_zero_iff).mp hqne
  have htne : t ≠ 0 := by
    intro ht0
    apply hqne'
    simp [ht0]
  have hvt : Valued.v t ≠ 0 := (Valued.v.ne_zero_iff).2 htne
  let τ : ℤ := WithZero.log (Valued.v t)
  have hlogquad : WithZero.log (Valued.v ((a : v.adicCompletion F) * t ^ 2)) =
      α + 2 * τ := by
    rw [Valuation.map_mul, Valuation.map_pow, WithZero.log_mul hva
      (pow_ne_zero _ hvt), WithZero.log_pow]
    dsimp [α, τ]
  have hlogpos : 0 < WithZero.log (Valued.v ((a : v.adicCompletion F) * t ^ 2)) := by
    apply (WithZero.exp_lt_exp).mp
    rw [WithZero.exp_zero, WithZero.exp_log hqne]
    exact hvalgt
  have hlogpos' : 0 < α + 2 * τ := by
    rw [← hlogquad]
    exact hlogpos
  have hsum : min 0 α < α + τ := by omega
  let x : v.adicCompletion F := z₀ / (-2 * (a : v.adicCompletion F) * t)
  have hxne : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero hz₀ne (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr htwo) ha) htne)
  have hvx : Valued.v x =
      Valued.v z₀ / (Valued.v (2 : v.adicCompletion F) *
        Valued.v (a : v.adicCompletion F) * Valued.v t) := by
    dsimp [x]
    simp [Valuation.map_div, Valuation.map_neg, Valuation.map_mul]
  have hvxne : Valued.v x ≠ 0 := (Valued.v.ne_zero_iff).2 hxne
  have hlogx : WithZero.log (Valued.v x) = β + min 0 α - α - τ := by
    rw [hvx, WithZero.log_div hvz₀
      (mul_ne_zero (mul_ne_zero hvtwo hva) hvt),
      WithZero.log_mul (mul_ne_zero hvtwo hva) hvt,
      WithZero.log_mul hvtwo hva]
    dsimp [β, α, τ]
    ring
  have hlogxbound : WithZero.log (Valued.v x) < β := by
    rw [hlogx]
    dsimp [β]
    linarith
  have hxlogN : WithZero.log (Valued.v x) ≤ (N : ℤ) := by
    exact (le_of_lt hlogxbound).trans (hβN₀.trans (by exact_mod_cast hN))
  have hxB : x ∈ localBall v N := by
    change Valued.v x ≤ WithZero.exp (N : ℤ)
    exact (WithZero.log_le_iff_le_exp hvxne).mp hxlogN
  have hDprop : t ∈ localBall v N ∧ ∀ y ∈ localBall v N,
      A.ψ v (-2 * (a : v.adicCompletion F) * y * t) = 1 := by
    simpa [quadraticBallAnnihilator, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_ofPred_eq] using htD
  have hvalchar : A.ψ v (-2 * (a : v.adicCompletion F) * x * t) = A.ψ v z₀ := by
    apply congrArg (A.ψ v)
    dsimp [x]
    field_simp [htwo, ha, htne] <;> ring
  exact hz₀ (by rw [← hvalchar, hDprop.2 x hxB])

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c
