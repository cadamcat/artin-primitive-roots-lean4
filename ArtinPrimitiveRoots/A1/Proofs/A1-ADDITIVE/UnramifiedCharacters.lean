import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».IntegralGlobalCharacters
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Analysis.SpecialFunctions.Complex.Log

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors WithZero

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

theorem integralGlobalChar_unramified {F : Type*} [Field F] [NumberField F]
    (ψ : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (hglobal : ∀ z : F,
      (Function.mulSupport fun v => ψ v (algebraMap F (v.adicCompletion F) z)).Finite ∧
        (∏ᶠ v, ψ v (algebraMap F (v.adicCompletion F) z)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1)
    (hint : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      x ∈ v.adicCompletionIntegers F → ψ v x = 1) :
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal →
      (∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F → ψ v x = 1) ∧
      ∀ π : F, HeightOneSpectrum.valuation F v π = WithZero.exp (-1) →
        ∃ x : 𝓞 F, ψ v (algebraMap F (v.adicCompletion F) ((x : F) / π)) ≠ 1 := by
  classical
  intro v hv
  refine ⟨hint v, ?_⟩
  let P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F := v.asIdeal
  have hP0 : P ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot
  have hex : ∃ y : F, y ∈ P⁻¹ ∧ ¬ ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ F y := by
    by_contra hn
    push Not at hn
    apply hv
    apply (differentialIdeal_le_iff (A := ℤ) (K := ℚ) (B := 𝓞 F) (L := F) v.ne_bot).mpr
    intro r hr
    obtain ⟨y, hy, hyr⟩ := Submodule.mem_map.mp hr
    change Algebra.trace ℚ F y = r at hyr
    subst r
    have hyP : y ∈ P⁻¹ := hy
    obtain ⟨n, hncast⟩ := hn y hyP
    rw [Submodule.one_eq_range]
    exact ⟨n, hncast⟩
  obtain ⟨y, hy, hTr⟩ := hex
  have hyMul (a : 𝓞 F) (ha : a ∈ v.asIdeal) :
      ∃ b : 𝓞 F, (a : F) * y = (b : F) := by
    have hmem : (a : F) * y ∈ P * P⁻¹ :=
      FractionalIdeal.mul_mem_mul
        (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 F)) ha) hy
    rw [mul_inv_cancel₀ hP0] at hmem
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 F))).mp hmem
    exact ⟨b, hb.symm⟩
  have localChar_one (w : HeightOneSpectrum (𝓞 F)) (u : F)
      (hu : w.valuation F u ≤ 1) :
      ψ w (algebraMap F (w.adicCompletion F) u) = 1 := by
    apply hint w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      w.valuedAdicCompletion_eq_valuation']
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using hu
  have hawayval (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) :
      w.valuation F y ≤ 1 := by
    have hnotle : ¬ v.asIdeal ≤ w.asIdeal := by
      intro h
      apply hw
      apply HeightOneSpectrum.ext
      exact ((v.isPrime.isMaximal v.ne_bot).eq_of_le w.isPrime.ne_top h).symm
    obtain ⟨a, ha, hwa⟩ := Set.not_subset.mp hnotle
    obtain ⟨b, hb⟩ := hyMul a ha
    have hax : w.valuation F (a : F) = 1 := w.valuation_eq_one_iff_notMem.mpr hwa
    have hInt : w.valuation F (b : F) ≤ 1 := w.valuation_le_one b
    rw [← hb, map_mul, hax, one_mul] at hInt
    exact hInt
  have hψne : ψ v (algebraMap F (v.adicCompletion F) y) ≠ 1 := by
    intro h
    have hp := (hglobal y).2
    rw [finprod_eq_single _ v (fun w hw => localChar_one w y (hawayval w hw)),
      h, one_mul] at hp
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hp
    have hz : -(Algebra.trace ℚ F y : ℂ) = (n : ℂ) := by
      apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
      calc
        (-(Algebra.trace ℚ F y : ℂ)) * (2 * Real.pi * Complex.I) =
            -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F y : ℂ)) := by ring
        _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
    have heqC : ((-n : ℤ) : ℂ) = (Algebra.trace ℚ F y : ℂ) := by
      rw [Int.cast_neg, ← hz, neg_neg]
    exact hTr ⟨-n, by exact_mod_cast heqC⟩
  intro π hπ
  have hπ0 : π ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπpos : 0 < v.valuation F π := by rw [hπ]; exact WithZero.exp_pos
  have hπle : v.valuation F π ≤ 1 := by
    rw [hπ, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer π hπle
  change π * ((d : 𝓞 F) : F) = (n : F) at hnd
  have hdval : v.valuation F ((d : 𝓞 F) : F) = 1 :=
    v.valuation_eq_one_iff_notMem.mpr d.property
  have hnmem : n ∈ v.asIdeal := by
    apply (v.valuation_lt_one_iff_mem (K := F) n).mp
    have hvaln : v.valuation F (n : F) = WithZero.exp (-1) := by
      rw [← hnd, map_mul, hdval, mul_one, hπ]
    rw [hvaln, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  obtain ⟨b, hb⟩ := hyMul n hnmem
  have hpy : v.valuation F (π * y) ≤ 1 := by
    have hInt : v.valuation F (b : F) ≤ 1 := v.valuation_le_one b
    have heq : (n : F) * y = ((d : 𝓞 F) : F) * (π * y) := by rw [← hnd]; ring
    rw [← hb, heq, map_mul, hdval, one_mul] at hInt
    exact hInt
  let γ : (ℤᵐ⁰)ˣ := Units.mk0 (WithZero.exp (-1)) WithZero.exp_ne_zero
  obtain ⟨x, hx⟩ := v.exists_valuation_sub_lt_of_integer hpy γ
  change v.valuation F ((x : F) - π * y) < WithZero.exp (-1) at hx
  have herror : v.valuation F ((x : F) / π - y) ≤ 1 := by
    have heq : (x : F) / π - y = ((x : F) - π * y) / π := by
      field_simp [hπ0]
    rw [heq, map_div₀]
    apply (div_le_one₀ hπpos).mpr
    rw [hπ]
    exact hx.le
  have herrorchar := localChar_one v ((x : F) / π - y) herror
  have hadd : ψ v (algebraMap F (v.adicCompletion F) ((x : F) / π - y)) *
      ψ v (algebraMap F (v.adicCompletion F) y) =
        ψ v (algebraMap F (v.adicCompletion F) ((x : F) / π)) := by
    rw [← AddChar.map_add_eq_mul, ← map_add, sub_add_cancel]
  rw [herrorchar, one_mul] at hadd
  exact ⟨x, fun hxone => hψne (hadd.trans hxone)⟩

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
