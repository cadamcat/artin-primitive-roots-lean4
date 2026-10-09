import ArtinPrimitiveRoots.A1.AddChar

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

private theorem completion_integer_of_global (v : FinPlace F) (z : F)
    (hz : v.valuation F z ≤ 1) :
    algebraMap F (v.adicCompletion F) z ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    v.valuedAdicCompletion_eq_valuation']
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using hz

private theorem global_principal_part (v : FinPlace F) (z : F) :
    ∃ y : F, v.valuation F (z - y) ≤ 1 ∧
      ∀ q : FinPlace F, q ≠ v → q.valuation F y ≤ 1 := by
  classical
  by_cases hz : z = 0
  · subst z
    exact ⟨0, by simp, fun q _ => by simp⟩
  obtain ⟨num, den, hden, hzdiv⟩ := IsFractionRing.div_surjective (𝓞 F) z
  have hden0 : den ≠ 0 := nonZeroDivisors.ne_zero hden
  have hspan : (Ideal.span {den} : Ideal (𝓞 F)) ≠ ⊥ := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hden0
  have hbadFinite : {q : FinPlace F | 1 < q.valuation F z}.Finite := by
    apply (Ideal.finite_factors hspan).subset
    intro q hq
    by_contra hqden
    have hdenNot : den ∉ q.asIdeal := by
      intro hmem
      exact hqden ((Ideal.dvd_span_singleton).2 hmem)
    have hvalden : q.valuation F (den : F) = 1 :=
      (q.valuation_eq_one_iff_notMem).2 hdenNot
    have hvalz : q.valuation F z ≤ 1 := by
      rw [← hzdiv, map_div₀, hvalden, div_one]
      exact q.valuation_le_one num
    exact not_lt_of_ge hvalz hq
  let B := hbadFinite.toFinset
  let k : FinPlace F → ℕ := fun q => (WithZero.log (q.valuation F z)).toNat
  have hk_nat (q : FinPlace F) (hq : 1 < q.valuation F z) :
      ((k q : ℕ) : ℤ) = WithZero.log (q.valuation F z) := by
    have hq0 : q.valuation F z ≠ 0 := (q.valuation F).ne_zero_iff.mpr hz
    have hlog : 0 < WithZero.log (q.valuation F z) := by
      have hh := (WithZero.log_lt_log (by simp) hq0).2 hq
      simpa using hh
    exact Int.toNat_of_nonneg hlog.le
  let J : Ideal (𝓞 F) := ∏ q ∈ B.erase v, q.asIdeal ^ k q
  have hcop : v.asIdeal ^ k v ⊔ J = ⊤ := by
    apply Ideal.sup_prod_eq_top
    intro q hq
    have hqv : q ≠ v := (Finset.mem_erase.mp hq).1
    let : v.asIdeal.IsMaximal := v.isMaximal
    let : q.asIdeal.IsMaximal := q.isMaximal
    apply Ideal.pow_sup_pow_eq_top
    apply Ideal.isCoprime_iff_sup_eq.mp
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    exact hqv (HeightOneSpectrum.ext heq.symm)
  obtain ⟨b, hb, c, hc, hbc⟩ :=
    Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hcop)
  have hcb : (1 - c : 𝓞 F) = b := (eq_sub_of_add_eq hbc).symm
  have hcorr : v.valuation F (z * (1 - (c : F))) ≤ 1 := by
    by_cases hv : 1 < v.valuation F z
    · have hbval : v.valuation F (b : F) ≤ WithZero.exp (-(k v : ℤ)) := by
        rw [v.valuation_of_algebraMap]
        exact (v.intValuation_le_pow_iff_mem b (k v)).2 hb
      have hvalz : v.valuation F z = WithZero.exp (k v : ℤ) := by
        rw [← WithZero.exp_log ((v.valuation F).ne_zero_iff.mpr hz), hk_nat v hv]
      have hcbF : (1 - (c : F)) = (b : F) := by exact_mod_cast hcb
      rw [hcbF, map_mul, hvalz]
      calc
        WithZero.exp (k v : ℤ) * v.valuation F (b : F) ≤
            WithZero.exp (k v : ℤ) * WithZero.exp (-(k v : ℤ)) :=
          mul_le_mul_of_nonneg_left hbval (by simp)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · rw [map_mul]
      have hcval : v.valuation F (1 - (c : F)) ≤ 1 := by
        exact_mod_cast v.valuation_le_one (1 - c)
      simpa using mul_le_mul (le_of_not_gt hv) hcval (by simp) (by simp)
  refine ⟨z * (c : F), ?_, ?_⟩
  · simpa only [mul_sub, mul_one] using hcorr
  · intro q hqv
    by_cases hq : 1 < q.valuation F z
    · have hqB : q ∈ B := hbadFinite.mem_toFinset.mpr hq
      have hqErase : q ∈ B.erase v := Finset.mem_erase.mpr ⟨hqv, hqB⟩
      have hJle : J ≤ q.asIdeal ^ k q :=
        (Ideal.prod_le_inf (s := B.erase v) (f := fun p => p.asIdeal ^ k p)).trans
          (Finset.inf_le hqErase)
      have hcval : q.valuation F (c : F) ≤ WithZero.exp (-(k q : ℤ)) := by
        rw [q.valuation_of_algebraMap]
        exact (q.intValuation_le_pow_iff_mem c (k q)).2 (hJle hc)
      have hvalz : q.valuation F z = WithZero.exp (k q : ℤ) := by
        rw [← WithZero.exp_log ((q.valuation F).ne_zero_iff.mpr hz), hk_nat q hq]
      rw [map_mul, hvalz]
      calc
        WithZero.exp (k q : ℤ) * q.valuation F (c : F) ≤
            WithZero.exp (k q : ℤ) * WithZero.exp (-(k q : ℤ)) :=
          mul_le_mul_of_nonneg_left hcval (by simp)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · rw [map_mul]
      simpa using mul_le_mul (le_of_not_gt hq) (q.valuation_le_one c) (by simp) (by simp)

private theorem completion_principal_part (v : FinPlace F) (x : v.adicCompletion F) :
    ∃ y : F, x - algebraMap F (v.adicCompletion F) y ∈ v.adicCompletionIntegers F ∧
      ∀ q : FinPlace F, q ≠ v →
        algebraMap F (q.adicCompletion F) y ∈ q.adicCompletionIntegers F := by
  let U : Set (v.adicCompletion F) :=
    {t | x - t ∈ v.adicCompletionIntegers F}
  have hUopen : IsOpen U :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
      (continuous_const.sub continuous_id)
  have hUnonempty : U.Nonempty := ⟨x, by simp [U]⟩
  obtain ⟨z, hz⟩ := (v.denseRange_algebraMap F).exists_mem_open hUopen hUnonempty
  obtain ⟨y, hv, hother⟩ := global_principal_part v z
  refine ⟨y, ?_, fun q hq => completion_integer_of_global q y (hother q hq)⟩
  have hzy := completion_integer_of_global v (z - y) hv
  rw [map_sub] at hzy
  simpa only [sub_add_sub_cancel] using (v.adicCompletionIntegers F).add_mem _ _ hz hzy

/-- The global trace compatibility and local integral kernel determine every finite
character. A CRT multiplier isolates the principal part at one place, so the global
product fixes its value; density then covers every completion element.
Guide: PROOFS.md:480–485; no local trace or continuity hypothesis is assumed. -/
theorem integral_global_character_family_unique (A : AddCharData F)
    (χ : (v : FinPlace F) → AddChar (v.adicCompletion F) ℂ)
    (hχint : ∀ (v : FinPlace F) (x : v.adicCompletion F),
      x ∈ v.adicCompletionIntegers F → χ v x = 1)
    (hχglobal : ∀ z : F,
      (Function.mulSupport fun v => χ v (algebraMap F _ z)).Finite ∧
        (∏ᶠ v, χ v (algebraMap F _ z)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1) :
    ∀ v : FinPlace F, A.ψ v = χ v := by
  intro v
  apply AddChar.ext
  intro x
  obtain ⟨y, hxy, hother⟩ := completion_principal_part v x
  have hprodA := finprod_eq_single
    (fun q : FinPlace F => A.ψ q (algebraMap F (q.adicCompletion F) y)) v
    (fun q hq => A.integral q _ (hother q hq))
  have hprodχ := finprod_eq_single
    (fun q : FinPlace F => χ q (algebraMap F (q.adicCompletion F) y)) v
    (fun q hq => hχint q _ (hother q hq))
  have hA := (A.trivial_on_F y).2
  have hχ := (hχglobal y).2
  rw [hprodA] at hA
  rw [hprodχ] at hχ
  have hval : A.ψ v (algebraMap F (v.adicCompletion F) y) =
      χ v (algebraMap F (v.adicCompletion F) y) :=
    mul_right_cancel₀ (Complex.exp_ne_zero _) (hA.trans hχ.symm)
  calc
    A.ψ v x = A.ψ v (algebraMap F (v.adicCompletion F) y) := by
      conv_lhs => rw [← sub_add_cancel x (algebraMap F (v.adicCompletion F) y)]
      rw [AddChar.map_add_eq_mul, A.integral v _ hxy, one_mul]
    _ = χ v (algebraMap F (v.adicCompletion F) y) := hval
    _ = χ v x := by
      conv_rhs => rw [← sub_add_cancel x (algebraMap F (v.adicCompletion F) y)]
      rw [AddChar.map_add_eq_mul, hχint v _ hxy, one_mul]

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
