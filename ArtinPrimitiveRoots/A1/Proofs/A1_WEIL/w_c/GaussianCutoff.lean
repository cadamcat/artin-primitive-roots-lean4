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

def linearBallAnnihilator (A : AddCharData F) (v : FinPlace F) (N : ℕ) :
    Set (v.adicCompletion F) :=
  ⋂ x : {x : v.adicCompletion F // x ∈ localBall v N},
    {s | A.ψ v (-2 * x.1 * s) = 1}

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

theorem linearBallAnnihilator_eventually_scalar_invariant
    (A : AddCharData F) (v : FinPlace F) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∀ s ∈ linearBallAnnihilator A v N,
      s ∈ localBall v N ∧ (a : v.adicCompletion F)⁻¹ * s ∈ localBall v N := by
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
  have hvz₀ : Valued.v z₀ ≠ 0 := (Valued.v.ne_zero_iff).2 hz₀ne
  have hvtwo : Valued.v (2 : v.adicCompletion F) ≠ 0 :=
    (Valued.v.ne_zero_iff).2 htwo
  have hva : Valued.v (a : v.adicCompletion F) ≠ 0 :=
    (Valued.v.ne_zero_iff).2 ha
  let γ : ℤ := WithZero.log (Valued.v z₀) - WithZero.log (Valued.v (2 : v.adicCompletion F))
  let α : ℤ := WithZero.log (Valued.v (a : v.adicCompletion F))
  let N₁ := intRadiusCutoff γ
  let N₂ := intRadiusCutoff (γ - α)
  let N₀ := max N₁ N₂
  have hγN₀ : γ ≤ N₀ := by
    exact (int_le_intRadiusCutoff γ).trans (by exact_mod_cast le_max_left N₁ N₂)
  have hγαN₀ : γ - α ≤ N₀ := by
    exact (int_le_intRadiusCutoff (γ - α)).trans (by exact_mod_cast le_max_right N₁ N₂)
  refine ⟨N₀, ?_⟩
  intro N hN s hs
  have hDprop : ∀ x ∈ localBall v N,
      A.ψ v (-2 * x * s) = 1 := by
    simpa [linearBallAnnihilator, Set.mem_iInter, Set.mem_ofPred_eq] using hs
  have hγN : γ ≤ (N : ℤ) := hγN₀.trans (by exact_mod_cast hN)
  have hγαN : γ - α ≤ (N : ℤ) := hγαN₀.trans (by exact_mod_cast hN)
  have sB : s ∈ localBall v N := by
    by_cases hs0 : s = 0
    · simp [hs0, localBall]
    · have hvsne : Valued.v s ≠ 0 := (Valued.v.ne_zero_iff).2 hs0
      by_contra hnotB
      change ¬ Valued.v s ≤ WithZero.exp (N : ℤ) at hnotB
      have hvsGt : WithZero.exp (N : ℤ) < Valued.v s := lt_of_not_ge hnotB
      have hlogGt : (N : ℤ) < WithZero.log (Valued.v s) :=
        (WithZero.lt_log_iff_exp_lt hvsne).mpr hvsGt
      let x : v.adicCompletion F := z₀ / (-2 * s)
      have hxne : x ≠ 0 := by
        dsimp [x]
        exact div_ne_zero hz₀ne (mul_ne_zero (neg_ne_zero.mpr htwo) hs0)
      have hvx : Valued.v x = Valued.v z₀ / (Valued.v (2 : v.adicCompletion F) * Valued.v s) := by
        dsimp [x]
        simp [Valuation.map_neg, Valuation.map_mul]
      have hvxne : Valued.v x ≠ 0 := (Valued.v.ne_zero_iff).2 hxne
      have hlogx : WithZero.log (Valued.v x) = γ - WithZero.log (Valued.v s) := by
        rw [hvx, WithZero.log_div hvz₀ (mul_ne_zero hvtwo hvsne),
          WithZero.log_mul hvtwo hvsne]
        dsimp [γ]
        ring
      have hlogxLe : WithZero.log (Valued.v x) ≤ (N : ℤ) := by
        rw [hlogx]
        have : γ - WithZero.log (Valued.v s) < 0 := by omega
        omega
      have hxB : x ∈ localBall v N := by
        change Valued.v x ≤ WithZero.exp (N : ℤ)
        exact (WithZero.log_le_iff_le_exp hvxne).mp hlogxLe
      have harg : -2 * x * s = z₀ := by
        dsimp [x]
        field_simp [htwo, hs0] <;> ring
      have hchar := hDprop x hxB
      rw [harg] at hchar
      exact hz₀ hchar
  have ainvB : (a : v.adicCompletion F)⁻¹ * s ∈ localBall v N := by
    let s' : v.adicCompletion F := (a : v.adicCompletion F)⁻¹ * s
    by_cases hs'0 : s' = 0
    · have hs0 : s = 0 := by
        have hfactor : (a : v.adicCompletion F) * s' = s := by
          dsimp [s']
          simp [mul_assoc]
        rw [← hfactor, hs'0]
        simp
      simp [hs0, localBall]
    · have hvs'ne : Valued.v s' ≠ 0 := (Valued.v.ne_zero_iff).2 hs'0
      by_contra hnotB
      change ¬ Valued.v s' ≤ WithZero.exp (N : ℤ) at hnotB
      have hvs'gt : WithZero.exp (N : ℤ) < Valued.v s' := lt_of_not_ge hnotB
      have hloggt : (N : ℤ) < WithZero.log (Valued.v s') :=
        (WithZero.lt_log_iff_exp_lt hvs'ne).mpr hvs'gt
      have hsne : s ≠ 0 := by
        intro hs0
        apply hs'0
        simp [s', hs0]
      have hvsne : Valued.v s ≠ 0 := (Valued.v.ne_zero_iff).2 hsne
      have hfactor : (a : v.adicCompletion F) * s' = s := by
        dsimp [s']
        simp [mul_assoc]
      have hlogs : WithZero.log (Valued.v s) = α + WithZero.log (Valued.v s') := by
        calc
          WithZero.log (Valued.v s) = WithZero.log (Valued.v ((a : v.adicCompletion F) * s')) := by
            rw [hfactor]
          _ = WithZero.log (Valued.v (a : v.adicCompletion F)) +
              WithZero.log (Valued.v s') := by
            rw [Valuation.map_mul, WithZero.log_mul hva hvs'ne]
          _ = _ := rfl
      let x : v.adicCompletion F := z₀ / (-2 * s)
      have hxne : x ≠ 0 := by
        dsimp [x]
        exact div_ne_zero hz₀ne (mul_ne_zero (neg_ne_zero.mpr htwo) hsne)
      have hvx : Valued.v x = Valued.v z₀ / (Valued.v (2 : v.adicCompletion F) * Valued.v s) := by
        dsimp [x]
        simp [Valuation.map_neg, Valuation.map_mul]
      have hvxne : Valued.v x ≠ 0 := (Valued.v.ne_zero_iff).2 hxne
      have hlogx : WithZero.log (Valued.v x) = γ - WithZero.log (Valued.v s) := by
        rw [hvx, WithZero.log_div hvz₀ (mul_ne_zero hvtwo hvsne),
          WithZero.log_mul hvtwo hvsne]
        dsimp [γ]
        ring
      have hlogxlt : WithZero.log (Valued.v x) < 0 := by
        rw [hlogx, hlogs]
        dsimp [γ, α]
        omega
      have hxB : x ∈ localBall v N := by
        change Valued.v x ≤ WithZero.exp (N : ℤ)
        apply (WithZero.log_le_iff_le_exp hvxne).mp
        omega
      have harg : -2 * x * s = z₀ := by
        dsimp [x]
        field_simp [htwo, hsne] <;> ring
      have hchar := hDprop x hxB
      rw [harg] at hchar
      exact hz₀ hchar
  exact ⟨sB, ainvB⟩

end ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_c
