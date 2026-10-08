import ArtinPrimitiveRoots.Theta.LocalInt
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Approximation

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- A rational element approximates a restricted finite-adelic family to every prescribed
finitely supported integral precision, with an error bound at all finite places. -/
theorem finite_adelic_additive_approximation
    (x : ∀ v : FinPlace F, v.adicCompletion F)
    (hx : {v : FinPlace F | 1 < absFin v (x v)}.Finite)
    (e : FinPlace F → ℤ) (he : (Function.support e).Finite) :
    ∃ ξ : F, ∀ v : FinPlace F,
      absFin v (x v - algebraMap F (v.adicCompletion F) ξ) ≤ (qv v) ^ (-e v) := by
  classical
  have hvalR (v : FinPlace F) (r : 𝓞 F) :
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    change Valued.v ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
  have hvalRle (v : FinPlace F) (r : 𝓞 F) :
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) ≤ 1 := by
    rw [hvalR]
    exact v.intValuation_le_one r
  have hlocal (v : FinPlace F) : ∃ a : 𝓞 F, a ≠ 0 ∧
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a * x v) ≤ 1 := by
    by_cases hx0 : x v = 0
    · exact ⟨1, one_ne_zero, by simp [hx0]⟩
    obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
    have hπ0 : π ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hπval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) =
        WithZero.exp (-1 : ℤ) := by rw [hvalR, hπ]
    have hxval : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    obtain ⟨n, hn⟩ := Valued.exists_pow_lt_of_le_exp_neg_one hπval.le
      (Units.mk0 (Valued.v (x v)) hxval)⁻¹
    have hn' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) ^ n <
        (Valued.v (x v))⁻¹ := by simpa using hn
    refine ⟨π ^ n, pow_ne_zero n hπ0, ?_⟩
    rw [map_mul, map_pow, map_pow]
    calc
      _ ≤ (Valued.v (x v))⁻¹ * Valued.v (x v) :=
        (mul_lt_mul_of_pos_right hn' (pos_iff_ne_zero.mpr hxval)).le
      _ = 1 := inv_mul_cancel₀ hxval
  choose b hb0 hb using hlocal
  let W := hx.toFinset
  let d : 𝓞 F := ∏ v ∈ W, b v
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hb0 v
  have hden (v : FinPlace F) :
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * x v) ≤ 1 := by
    by_cases hv : v ∈ W
    · have hd : d = (∏ w ∈ W.erase v, b w) * b v := (Finset.prod_erase_mul W b hv).symm
      have hmul : algebraMap (𝓞 F) (v.adicCompletion F) d * x v =
          algebraMap (𝓞 F) (v.adicCompletion F) (∏ w ∈ W.erase v, b w) *
            (algebraMap (𝓞 F) (v.adicCompletion F) (b v) * x v) := by
        simp only [hd, map_mul, mul_assoc]
      rw [hmul, map_mul]
      exact (mul_le_mul (hvalRle v _) (hb v) zero_le zero_le).trans (by simp)
    · have hxle : absFin v (x v) ≤ 1 := le_of_not_gt fun h => hv (hx.mem_toFinset.mpr h)
      have hxval : Valued.v (x v) ≤ 1 :=
        Valued.toNormedField.norm_le_one_iff.mp ((absFin_eq_norm v _).symm ▸ hxle)
      rw [map_mul]
      exact (mul_le_mul (hvalRle v d) hxval zero_le zero_le).trans (by simp)
  let y (v : FinPlace F) : v.adicCompletionIntegers F :=
    ⟨algebraMap (𝓞 F) (v.adicCompletion F) d * x v,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr (hden v)⟩
  let dF : F := algebraMap (𝓞 F) F d
  have hdF : dF ≠ 0 := (IsFractionRing.injective (𝓞 F) F).ne hd0
  let c (v : FinPlace F) : ℤ := FractionalIdeal.count F v
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) dF)
  have hc : (Function.support c).Finite := Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) dF))
  let n (v : FinPlace F) : ℕ := (c v + e v).toNat
  let T := hc.toFinset ∪ he.toFinset
  obtain ⟨r, hr⟩ := HeightOneSpectrum.exists_forall_valued_sub_le (K := F) T y n
  have happrox (v : FinPlace F) :
      Valued.v ((y v : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
        WithZero.exp (-(n v : ℤ)) := by
    by_cases hv : v ∈ T
    · exact hr v hv
    · have hc0 : c v = 0 := by
        by_contra h
        exact hv (Finset.mem_union.mpr (Or.inl (hc.mem_toFinset.mpr h)))
      have he0 : e v = 0 := by
        by_contra h
        exact hv (Finset.mem_union.mpr (Or.inr (he.mem_toFinset.mpr h)))
      have hn0 : n v = 0 := by simp [n, hc0, he0]
      rw [hn0]
      simpa using Valuation.map_sub_le Valued.v (hden v) (hvalRle v r)
  have hnormBound (v : FinPlace F) (z : v.adicCompletion F) (k : ℤ)
      (hz : Valued.v z ≤ WithZero.exp (-k)) : absFin v z ≤ (qv v) ^ (-k) := by
    have hmono := WithZeroMulInt.toNNReal_strictMono
      (HeightOneSpectrum.one_lt_absNorm_nnreal v)
    have hpow : (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (WithZero.exp (-k)) : ℝ) = (qv v) ^ (-k) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v)
        WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log WithZero.exp_ne_zero,
        WithZero.log_exp]
      simp [qv]
    rw [absFin, dite_eq_left (HeightOneSpectrum.absNorm_ne_zero v), ← hpow]
    exact_mod_cast hmono.monotone hz
  have hdNorm (v : FinPlace F) :
      absFin v (algebraMap (𝓞 F) (v.adicCompletion F) d) = (qv v) ^ (-c v) := by
    rw [absFin_eq_norm, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    change ‖FinitePlace.embedding v dF‖ = _
    exact norm_embedding_eq_absNorm_zpow v dF hdF
  refine ⟨algebraMap (𝓞 F) F r / dF, fun v => ?_⟩
  have hdv : algebraMap F (v.adicCompletion F) dF ≠ 0 :=
    (algebraMap F (v.adicCompletion F)).injective.ne hdF
  have hscale : (y v : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r =
      algebraMap (𝓞 F) (v.adicCompletion F) d *
        (x v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r / dF)) := by
    change algebraMap (𝓞 F) (v.adicCompletion F) d * x v -
      algebraMap (𝓞 F) (v.adicCompletion F) r = _
    simp only [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), map_div₀]
    change algebraMap F (v.adicCompletion F) dF * x v -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) = _
    field_simp [hdv]
    dsimp only [dF]
    ring
  have hbound := hnormBound v _ (n v : ℤ) (happrox v)
  rw [hscale, absFin_eq_norm, norm_mul, ← absFin_eq_norm, ← absFin_eq_norm, hdNorm] at hbound
  have hprecision : c v + e v ≤ (n v : ℤ) := by dsimp only [n]; omega
  have hq : 0 < qv v := (zero_lt_one.trans (qv_gt_one v))
  have hpow : (qv v) ^ (-(n v : ℤ)) ≤ (qv v) ^ (-(c v + e v)) :=
    zpow_le_zpow_right₀ (qv_gt_one v).le (neg_le_neg hprecision)
  have hfinal := hbound.trans hpow
  rw [neg_add, zpow_add₀ hq.ne'] at hfinal
  exact le_of_mul_le_mul_left hfinal (zpow_pos hq (-c v))

end ArtinPrimitiveRoots.A1.Theta
