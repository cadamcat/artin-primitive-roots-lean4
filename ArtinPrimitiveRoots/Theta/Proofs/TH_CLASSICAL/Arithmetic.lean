import ArtinPrimitiveRoots.A1.Field

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors Topology
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- One integral denominator vanishes at every chosen prime and is a unit at all other primes. -/
theorem th_classical_supported_denominator (T : Finset (FinPlace F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      (∀ v ∈ T, v.valuation F (algebraMap (𝓞 F) F d) < 1) ∧
      ∀ v ∉ T, v.valuation F (algebraMap (𝓞 F) F d) = 1 := by
  classical
  let I : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal
  have hI : I ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v hv => v.ne_bot
  let I₀ : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let n : ℕ := Fintype.card (ClassGroup (𝓞 F))
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hIn : I ^ n ∈ (Ideal (𝓞 F))⁰ := pow_mem I₀.property n
  have hclass : ClassGroup.mk0 ⟨I ^ n, hIn⟩ = 1 := by
    change ClassGroup.mk0 (I₀ ^ n) = 1
    rw [ClassGroup.mk0.map_pow]
    exact pow_card_eq_one
  letI : (I ^ n).IsPrincipal := (ClassGroup.mk0_eq_one_iff hIn).mp hclass
  let d : 𝓞 F := Submodule.IsPrincipal.generator (I ^ n)
  have hdspan : Ideal.span ({d} : Set (𝓞 F)) = I ^ n :=
    Ideal.span_singleton_generator (I ^ n)
  have hd : d ≠ 0 := by
    intro hd0
    apply pow_ne_zero n hI
    rw [← hdspan, hd0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hpow : I ^ n ≤ I := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hk, pow_succ]
    exact Ideal.mul_le_right
  have hdmem : d ∈ I ^ n := Submodule.IsPrincipal.generator_mem (I ^ n)
  refine ⟨d, hd, ?_, ?_⟩
  · intro v hv
    apply (v.valuation_lt_one_iff_mem (K := F) d).mpr
    have hIv : I ≤ v.asIdeal := Ideal.prod_le_inf.trans (Finset.inf_le hv)
    exact (hpow.trans hIv) hdmem
  · intro v hv
    apply (v.valuation_eq_one_iff_notMem (K := F)).mpr
    intro hdv
    have hInV : I ^ n ≤ v.asIdeal := by
      rw [← hdspan]
      exact (Ideal.span_singleton_le_iff_mem (I := v.asIdeal)).mpr hdv
    have hIv : I ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le hInV
    obtain ⟨u, hu, huv⟩ := v.isPrime.prod_le.mp hIv
    have heq : u.asIdeal = v.asIdeal := u.isMaximal.eq_of_le v.isPrime.ne_top huv
    exact hv (HeightOneSpectrum.ext heq ▸ hu)

/-- Global integers approximate every integral element of a single adic completion. -/
theorem th_classical_integer_completion_approx (v : FinPlace F)
    (x : v.adicCompletion F) (hx : Valued.v x ≤ 1) (m : ℕ) :
    ∃ a : 𝓞 F, Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a - x) <
      WithZero.exp (-(m : ℤ)) := by
  obtain ⟨c, hc⟩ := v.valuedAdicCompletion_surjective (K := F)
    (WithZero.exp (-(m : ℤ)))
  have hcpos : 0 < Valued.v.restrict c := by
    rw [Valuation.restrict_pos_iff, hc]
    exact WithZero.exp_pos
  have hball : {z : v.adicCompletion F |
      Valued.v (z - x) < WithZero.exp (-(m : ℤ))} ∈ 𝓝 x := by
    apply Valued.mem_nhds.mpr
    refine ⟨Units.mk0 (Valued.v.restrict c) hcpos.ne', ?_⟩
    intro z hz
    change Valued.v.restrict (z - x) < Valued.v.restrict c at hz
    simpa only [Set.mem_setOf_eq, Valuation.restrict_lt_iff, hc] using hz
  obtain ⟨b, hb⟩ := (v.denseRange_algebraMap (K := F)).mem_nhds hball
  change Valued.v (algebraMap F (v.adicCompletion F) b - x) <
    WithZero.exp (-(m : ℤ)) at hb
  have hrad : WithZero.exp (-(m : ℤ)) ≤ 1 := by simp
  have hbint : v.valuation F b ≤ 1 := by
    have h := Valued.v.map_add_le (hb.le.trans hrad) hx
    simpa only [sub_add_cancel, HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
      v.valuedAdicCompletion_eq_valuation'] using h
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hbint
    (WithZero.expEquiv (-(m : ℤ)))
  have ha' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a -
      algebraMap F (v.adicCompletion F) b) < WithZero.exp (-(m : ℤ)) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation',
      WithZero.coe_expEquiv_apply] using ha
  refine ⟨a, ?_⟩
  have h := Valued.v.map_add_lt ha' hb
  simpa only [sub_add_sub_cancel] using h

/-- One global integer approximates integral targets at every place in a finite set. -/
theorem th_classical_integer_finite_approx (T : Finset (FinPlace F))
    (x : ∀ v : T, v.1.adicCompletion F)
    (hx : ∀ v : T, Valued.v (x v) ≤ 1) (m : T → ℕ) :
    ∃ a : 𝓞 F, ∀ v : T,
      Valued.v (algebraMap (𝓞 F) (v.1.adicCompletion F) a - x v) <
        WithZero.exp (-(m v : ℤ)) := by
  classical
  choose b hb using fun v : T =>
    th_classical_integer_completion_approx v.1 (x v) (hx v) (m v)
  let I : T → Ideal (𝓞 F) := fun v => v.1.asIdeal ^ (m v + 1)
  have hI : Pairwise (fun v w : T => IsCoprime (I v) (I w)) := by
    intro v w hvw
    exact HeightOneSpectrum.isCoprime_pow_of_ne v.1 w.1
      (fun h => hvw (Subtype.ext h)) (m v + 1) (m w + 1)
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal hI b
  refine ⟨a, ?_⟩
  intro v
  have hglob : v.1.intValuation (a - b v) ≤
      WithZero.exp (-((m v + 1 : ℕ) : ℤ)) :=
    (v.1.intValuation_le_pow_iff_mem _ _).mpr (ha v)
  have hprec : WithZero.exp (-((m v + 1 : ℕ) : ℤ)) <
      WithZero.exp (-(m v : ℤ)) := by
    rw [WithZero.exp_lt_exp]
    omega
  have hcmp : Valued.v (algebraMap (𝓞 F) (v.1.adicCompletion F) a -
      algebraMap (𝓞 F) (v.1.adicCompletion F) (b v)) <
        WithZero.exp (-(m v : ℤ)) := by
    rw [← map_sub, IsScalarTower.algebraMap_apply (𝓞 F) F (v.1.adicCompletion F)]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.1.valuedAdicCompletion_eq_valuation',
      v.1.valuation_of_algebraMap] using hglob.trans_lt hprec
  have h := Valued.v.map_add_lt hcmp (hb v)
  simpa only [sub_add_sub_cancel] using h

end ArtinPrimitiveRoots.A1.Theta
