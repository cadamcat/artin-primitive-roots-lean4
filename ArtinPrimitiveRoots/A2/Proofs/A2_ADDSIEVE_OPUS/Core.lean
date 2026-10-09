import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.Dictionary
import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.Proofs.A1_DUAL.AnnihilatorCore
import ArtinPrimitiveRoots.Proofs.a2_cond_b.AdditivePhase
import ArtinPrimitiveRoots.Proofs.a2_cond_b.FiniteLargeSieve

/-!
# Additive large sieve: arithmetic core

The additive large sieve `lem_additive_sieve` is reduced to the finite-dimensional large sieve on
`ℤ^n` (`Proofs.a2_cond_b.conductorFiniteDimLargeSieve`).  Rows are put in integral-basis
coordinates after a fixed integral scaling, and the frequencies become additive characters of
`𝓞 F`, separated by `Proofs.a2_cond_b.conductorAdditiveChar_angle_separation`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical ComplexConjugate

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.addsieve_opus

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## Finite duality -/

/-- Duality for a finite matrix: the dual large-sieve inequality implies the primal one with the
same constant. -/
theorem dual_to_primal {α β : Type*} (s : Finset α) (t : Finset β) (M : β → α → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (h : ∀ c : β → ℂ, ∑ a ∈ s, ‖∑ j ∈ t, c j * M j a‖ ^ 2 ≤ Δ * ∑ j ∈ t, ‖c j‖ ^ 2)
    (b : α → ℂ) :
    ∑ j ∈ t, ‖∑ a ∈ s, b a * M j a‖ ^ 2 ≤ Δ * ∑ a ∈ s, ‖b a‖ ^ 2 := by
  classical
  let u : β → ℂ := fun j => ∑ a ∈ s, b a * M j a
  let X : ℝ := ∑ j ∈ t, ‖u j‖ ^ 2
  let W : α → ℂ := fun a => ∑ j ∈ t, conj (u j) * M j a
  let B : ℝ := ∑ a ∈ s, ‖b a‖ ^ 2
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => by positivity
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hXc : ((X : ℝ) : ℂ) = ∑ a ∈ s, b a * W a := by
    calc ((X : ℝ) : ℂ) = ∑ j ∈ t, ((‖u j‖ : ℂ) ^ 2) := by
          simp only [X]
          push_cast
          rfl
      _ = ∑ j ∈ t, conj (u j) * u j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Complex.conj_mul']
      _ = ∑ j ∈ t, ∑ a ∈ s, conj (u j) * (b a * M j a) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ a ∈ s, ∑ j ∈ t, conj (u j) * (b a * M j a) := Finset.sum_comm
      _ = ∑ a ∈ s, b a * W a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [W, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  have hXle : X ≤ ∑ a ∈ s, ‖b a‖ * ‖W a‖ := by
    have h1 : X = ‖((X : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hX0]
    rw [h1, hXc]
    refine (norm_sum_le _ _).trans ?_
    exact le_of_eq (Finset.sum_congr rfl fun a _ => norm_mul _ _)
  have hW : ∑ a ∈ s, ‖W a‖ ^ 2 ≤ Δ * X := by
    have := h (fun j => conj (u j))
    simpa [W, X, Complex.norm_conj] using this
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun a => ‖b a‖) (fun a => ‖W a‖)
  have hsq : X ^ 2 ≤ B * (Δ * X) := by
    have hS0 : 0 ≤ ∑ a ∈ s, ‖b a‖ * ‖W a‖ := Finset.sum_nonneg fun _ _ => by positivity
    calc X ^ 2 ≤ (∑ a ∈ s, ‖b a‖ * ‖W a‖) ^ 2 := pow_le_pow_left₀ hX0 hXle 2
      _ ≤ (∑ a ∈ s, ‖b a‖ ^ 2) * ∑ a ∈ s, ‖W a‖ ^ 2 := hCS
      _ ≤ B * (Δ * X) := mul_le_mul_of_nonneg_left hW hB0
  change X ≤ Δ * B
  rcases hX0.eq_or_lt with hXz | hXpos
  · rw [← hXz]; positivity
  · have : X * X ≤ (Δ * B) * X := by nlinarith
    exact le_of_mul_le_mul_right this hXpos

/-! ## The phase characters on `𝓞 F` -/

/-- The additive character `y ↦ e(diag(y x))` of `𝓞 F`. -/
def phaseChar (S : A1.SData F CE condη) (A : A1.AddCharData F) (x : F) : AddChar (𝓞 F) ℂ where
  toFun y := S.e A (S.diag (algebraMap (𝓞 F) F y * x))
  map_zero_eq_one' := by simp [A1.SData.e, A1.psiC]
  map_add_eq_mul' := by
    intro y z
    rw [map_add, add_mul, map_add, ArtinPrimitiveRoots.Proofs.a1_dual_p.e_add]

theorem phaseChar_apply (S : A1.SData F CE condη) (A : A1.AddCharData F) (x : F) (y : 𝓞 F) :
    phaseChar S A x y = S.e A (S.diag (algebraMap (𝓞 F) F y * x)) := rfl

/-- Every element of `F` has a nonzero natural multiple in `R`. -/
theorem exists_nat_mul_mem_R (S : A1.SData F CE condη) (x : F) :
    ∃ q : ℕ, q ≠ 0 ∧ (q : F) * x ∈ S.R := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · intro h
    have := Ideal.absNorm_eq_zero_iff.mp h
    exact hb0 (Ideal.span_singleton_eq_bot.mp this)
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
      intro h
      exact hb0 ((FaithfulSMul.algebraMap_injective (𝓞 F) F) (by simpa using h))
    have hq : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : F) =
        algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F b := by
      rw [← map_mul, ht, map_natCast]
    rw [hq]
    have heq : algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F b *
        (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) = algebraMap (𝓞 F) F (t * a) := by
      rw [map_mul]
      field_simp
    rw [heq]
    exact Subalgebra.algebraMap_mem S.R (t * a)

theorem phaseChar_norm (D : A1.FieldData F) (S : A1.SData F CE condη) (A : A1.AddCharData F)
    (x : F) (y : 𝓞 F) : ‖phaseChar S A x y‖ = 1 := by
  have : IsTotallyComplex F := D.isTotallyComplex
  obtain ⟨q, hq0, hqR⟩ := exists_nat_mul_mem_R S x
  have hpow : phaseChar S A x y ^ q = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, phaseChar_apply]
    have hmem : algebraMap (𝓞 F) F (q • y) * x =
        algebraMap (𝓞 F) F y * ((q : F) * x) := by
      rw [nsmul_eq_mul, map_mul, map_natCast]
      ring
    rw [hmem]
    have hR : algebraMap (𝓞 F) F y * ((q : F) * x) ∈ S.R :=
      Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem S.R y) hqR
    exact ArtinPrimitiveRoots.Proofs.a1_dual_p.e_diag_R_eq_one D S A ⟨_, hR⟩
  exact Complex.norm_eq_one_of_pow_eq_one hpow hq0

/-! ## Candidate data -/

/-- Every additive candidate is a diagonal field element with a denominator ideal of norm at most
`V` which annihilates its phases. -/
theorem candidate_data (D : A1.FieldData F) (S : A1.SData F CE condη)
    {H : A1.HilbertData F} {Bd : A1.BData S H} (bc : A2.BalancedChoices D S H Bd)
    (A : A1.AddCharData F) {V : ℝ} (hV : 1 ≤ V) {α : S.FS}
    (hα : α = 0 ∨ ∃ I : A1.SData.ExtIdeal S,
      A2.idealNorm I.1 ≤ V ∧ ∃ d : 𝓞 F,
        IsCoprime (Ideal.span {d}) I.1 ∧
        α = S.diag ((algebraMap (𝓞 F) F d) / (bc.gen I : F))) :
    ∃ J : Ideal (𝓞 F), ∃ a : F, J ≠ ⊥ ∧ (Ideal.absNorm J : ℝ) ≤ V ∧ S.diag a = α ∧
      ∀ n ∈ J, ∀ y : 𝓞 F,
        S.e A (S.diag (algebraMap (𝓞 F) F n * algebraMap (𝓞 F) F y * a)) = 1 := by
  rcases hα with h0 | ⟨I, hIV, d, _hcop, hαeq⟩
  · refine ⟨⊤, 0, by simp, by simpa using hV, by simp [h0], ?_⟩
    intro n _ y
    simp [A1.SData.e, A1.psiC]
  · refine ⟨I.1, algebraMap (𝓞 F) F d / (bc.gen I : F), I.2.1, hIV, hαeq.symm, ?_⟩
    intro n hn y
    have h := (S.e_pairing_perfect D A I.1 I.2 (bc.gen I : F) (bc.gen_spec I).1).1 n hn (y * d)
    convert h using 3
    rw [map_mul, map_mul]
    ring

/-! ## Angle separation -/

/-- The integral-basis angle vector of the phase character of `x`. -/
def theta (S : A1.SData F CE condη) (A : A1.AddCharData F) (x : F) :
    Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ :=
  ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveCharacterFrequencyVector (phaseChar S A x)

/-- The separation constant at frequency height `V`, after scaling by `c`. -/
def sepConst (F : Type) [Field F] [NumberField F] (c : 𝓞 F) (V : ℝ) : ℝ :=
  1 / (4 * (Module.finrank ℚ F : ℝ) *
    (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F) + 1) *
      Real.rpow (((Ideal.absNorm (Ideal.span {c}) : ℝ) * V) ^ 2)
        (1 / (Module.finrank ℚ F : ℝ)))

theorem abs_conductorUnitAngle_le (z : ℂ) :
    |ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle z| ≤ 1 / 2 := by
  unfold ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [div_le_iff₀ (by positivity)]
  have := Complex.abs_arg_le_pi z
  linarith

theorem phase_separation (D : A1.FieldData F) (S : A1.SData F CE condη)
    (A : A1.AddCharData F) (c : 𝓞 F) (hc : c ≠ 0) {V : ℝ} (hV : 2 ≤ V)
    (Jα Jβ : Ideal (𝓞 F)) (aα aβ : F) (hJα : Jα ≠ ⊥) (hJβ : Jβ ≠ ⊥)
    (hNα : (Ideal.absNorm Jα : ℝ) ≤ V) (hNβ : (Ideal.absNorm Jβ : ℝ) ≤ V)
    (hannα : ∀ n ∈ Jα, ∀ y : 𝓞 F,
      S.e A (S.diag (algebraMap (𝓞 F) F n * algebraMap (𝓞 F) F y * aα)) = 1)
    (hannβ : ∀ n ∈ Jβ, ∀ y : 𝓞 F,
      S.e A (S.diag (algebraMap (𝓞 F) F n * algebraMap (𝓞 F) F y * aβ)) = 1)
    (hnot : aα - aβ ∉ S.R) :
    ∃ i, ∀ m : ℤ, sepConst F c V ≤
      |theta S A (aα / algebraMap (𝓞 F) F c) i - theta S A (aβ / algebraMap (𝓞 F) F c) i - m| := by
  classical
  have : IsTotallyComplex F := D.isTotallyComplex
  have hcF : algebraMap (𝓞 F) F c ≠ 0 := by
    intro h
    exact hc ((FaithfulSMul.algebraMap_injective (𝓞 F) F) (by simpa using h))
  let x : F := (aα - aβ) / algebraMap (𝓞 F) F c
  let ψ : AddChar (𝓞 F) ℂ := phaseChar S A x
  -- the difference character is nontrivial
  have hψ : ψ ≠ 1 := by
    intro h1
    have htriv : ∀ y : 𝓞 F, S.e A (S.diag (x * algebraMap (𝓞 F) F y)) = 1 := by
      intro y
      have := congrArg (fun χ : AddChar (𝓞 F) ℂ => χ y) h1
      simpa [ψ, phaseChar_apply, mul_comm] using this
    by_cases hx : x ∈ S.R
    · apply hnot
      have heq : aα - aβ = algebraMap (𝓞 F) F c * x := by
        simp only [x]
        field_simp
      rw [heq]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem S.R c) hx
    · obtain ⟨d, hd⟩ := ArtinPrimitiveRoots.Proofs.a1_dual_p.external_character_detector S A.ψ
        A.trivial_on_F A.integral A.unramified x hx
      have hd' : S.e A (S.diag (x * (d : F))) ≠ 1 := by
        simpa [A1.SData.e, A1.psiC, ArtinPrimitiveRoots.Proofs.a1_dual_p.eOnFS] using hd
      exact hd' (htriv d)
  -- the annihilating ideal
  let K : Ideal (𝓞 F) := Ideal.span {c} * (Jα * Jβ)
  have hK : K ≠ ⊥ := by
    have hspan : Ideal.span {c} ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hc
    have hJ : Jα * Jβ ≠ ⊥ := by
      intro h
      rcases Ideal.mul_eq_bot.mp h with h' | h'
      · exact hJα h'
      · exact hJβ h'
    intro h
    rcases Ideal.mul_eq_bot.mp h with h' | h'
    · exact hspan h'
    · exact hJ h'
  have hKann : K ≤ ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveAnnihilator ψ := by
    apply Ideal.mul_le.mpr
    intro u hu z hz y
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hu
    have hzα : z ∈ Jα := (Ideal.mul_le_left : Jα * Jβ ≤ Jα) hz
    have hzβ : z ∈ Jβ := (Ideal.mul_le_right : Jα * Jβ ≤ Jβ) hz
    change S.e A (S.diag (algebraMap (𝓞 F) F (t * c * z * y) * x)) = 1
    have hsplit : algebraMap (𝓞 F) F (t * c * z * y) * x =
        algebraMap (𝓞 F) F z * algebraMap (𝓞 F) F (t * y) * aα -
          algebraMap (𝓞 F) F z * algebraMap (𝓞 F) F (t * y) * aβ := by
      simp only [x, map_mul]
      field_simp
    rw [hsplit, map_sub, sub_eq_add_neg, ArtinPrimitiveRoots.Proofs.a1_dual_p.e_add,
      ArtinPrimitiveRoots.Proofs.a1_dual_p.e_neg, hannα z hzα (t * y), hannβ z hzβ (t * y)]
    simp
  -- the norm bound
  let Nc : ℝ := (Ideal.absNorm (Ideal.span {c}) : ℝ)
  have hNc : 1 ≤ Nc := by
    have hpos : 0 < Ideal.absNorm (Ideal.span {c}) := by
      apply Nat.pos_of_ne_zero
      intro h
      have := Ideal.absNorm_eq_zero_iff.mp h
      exact hc (Ideal.span_singleton_eq_bot.mp this)
    have h1 : 1 ≤ Ideal.absNorm (Ideal.span {c}) := hpos
    show (1 : ℝ) ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)
    exact_mod_cast h1
  have hV' : 2 ≤ Nc * V := by nlinarith
  have hKnorm : (Ideal.absNorm K : ℝ) ≤ (Nc * V) ^ 2 := by
    have hmul : (Ideal.absNorm K : ℝ) =
        Nc * ((Ideal.absNorm Jα : ℝ) * (Ideal.absNorm Jβ : ℝ)) := by
      simp only [K, map_mul, Nat.cast_mul, Nc]
    rw [hmul]
    have h0α : (0 : ℝ) ≤ Ideal.absNorm Jα := Nat.cast_nonneg _
    have h0β : (0 : ℝ) ≤ Ideal.absNorm Jβ := Nat.cast_nonneg _
    have hprod : (Ideal.absNorm Jα : ℝ) * (Ideal.absNorm Jβ : ℝ) ≤ V * V :=
      mul_le_mul hNα hNβ h0β (by linarith)
    calc Nc * ((Ideal.absNorm Jα : ℝ) * (Ideal.absNorm Jβ : ℝ)) ≤ Nc * (V * V) :=
          mul_le_mul_of_nonneg_left hprod (by linarith)
      _ ≤ (Nc * V) ^ 2 := by nlinarith
  obtain ⟨i, hi⟩ := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveChar_angle_separation
    ψ (phaseChar_norm D S A x) hψ K hK hKann hV' hKnorm
  refine ⟨i, fun m => ?_⟩
  have hsep : sepConst F c V ≤
      |ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveCharacterFrequencyVector ψ i| := by
    simpa [sepConst, Nc] using hi
  apply ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAngle_modInteger_lower
    (abs_conductorUnitAngle_le _) hsep
  -- exponential identity
  let B := RingOfIntegers.basis F i
  have hψB : ψ B = phaseChar S A (aα / algebraMap (𝓞 F) F c) B *
      (phaseChar S A (aβ / algebraMap (𝓞 F) F c) B)⁻¹ := by
    simp only [ψ, phaseChar_apply, x]
    rw [← ArtinPrimitiveRoots.Proofs.a1_dual_p.e_neg, ← ArtinPrimitiveRoots.Proofs.a1_dual_p.e_add,
      ← map_neg, ← map_add]
    congr 2
    ring
  have hexpα := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle_exp
    (phaseChar_norm D S A (aα / algebraMap (𝓞 F) F c) B)
  have hexpβ := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle_exp
    (phaseChar_norm D S A (aβ / algebraMap (𝓞 F) F c) B)
  have hexpψ := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle_exp
    (phaseChar_norm D S A x B)
  simp only [theta, ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveCharacterFrequencyVector]
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle
          (phaseChar S A (aα / algebraMap (𝓞 F) F c) B) -
        ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle
          (phaseChar S A (aβ / algebraMap (𝓞 F) F c) B) : ℝ) : ℂ)) =
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle (ψ B) : ℂ))
  rw [hexpψ, hψB, Complex.ofReal_sub, mul_sub, Complex.exp_sub, hexpα, hexpβ, div_eq_mul_inv]

end ArtinPrimitiveRoots.Proofs.addsieve_opus
