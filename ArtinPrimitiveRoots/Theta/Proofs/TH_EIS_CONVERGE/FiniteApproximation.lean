import ArtinPrimitiveRoots.Theta.LocalInt
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Approximation
import Mathlib.Data.DFinsupp.Defs

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

/-- A rational element belongs to a nonzero fractional ideal exactly when it lies
in the corresponding ideal ball at every finite place. -/
theorem fractionalIdeal_mem_iff_local_bounds
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0) (ξ : F) :
    ξ ∈ (𝔞 : Submodule (𝓞 F) F) ↔
      ∀ v : FinPlace F, absFin v (algebraMap F (v.adicCompletion F) ξ) ≤
        (qv v) ^ (-FractionalIdeal.count F v 𝔞) := by
  classical
  by_cases hξ : ξ = 0
  · subst ξ
    constructor
    · intro _ v
      rw [map_zero, absFin_eq_norm, norm_zero]
      exact (zpow_pos (zero_lt_one.trans (qv_gt_one v)) _).le
    · intro _
      exact (𝔞 : Submodule (𝓞 F) F).zero_mem
  let I := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ξ
  have hI : I ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hξ
  have hnorm (v : FinPlace F) :
      absFin v (algebraMap F (v.adicCompletion F) ξ) =
        (qv v) ^ (-FractionalIdeal.count F v I) := by
    rw [absFin_eq_norm]
    change ‖FinitePlace.embedding v ξ‖ = _
    exact norm_embedding_eq_absNorm_zpow v ξ hξ
  constructor
  · intro hmem v
    have hle : I ≤ 𝔞 := FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
    rw [hnorm]
    exact zpow_le_zpow_right₀ (qv_gt_one v).le
      (neg_le_neg (FractionalIdeal.count_mono F v hI hle))
  · intro hlocal
    have hcounts (v : FinPlace F) :
        FractionalIdeal.count F v 𝔞 ≤ FractionalIdeal.count F v I := by
      have hv := hlocal v
      rw [hnorm, zpow_le_zpow_iff_right₀ (qv_gt_one v)] at hv
      exact neg_le_neg_iff.mp hv
    let J := I * 𝔞⁻¹
    have hJ : J ≠ 0 := mul_ne_zero hI (inv_ne_zero h𝔞)
    have hnonneg (v : FinPlace F) : 0 ≤ FractionalIdeal.count F v J := by
      dsimp only [J]
      rw [FractionalIdeal.count_mul F v hI (inv_ne_zero h𝔞), FractionalIdeal.count_inv]
      have hv := hcounts v
      omega
    have hJle : J ≤ 1 := by
      rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hJ]
      apply finprod_induction (fun K : FractionalIdeal (nonZeroDivisors (𝓞 F)) F => K ≤ 1)
        le_rfl
      · intro K L hK hL
        simpa using mul_le_mul' hK hL
      · intro v
        have hnat := Int.toNat_of_nonneg (hnonneg v)
        rw [← hnat, zpow_natCast]
        have hprime : (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≤ 1 :=
          FractionalIdeal.coeIdeal_le_one
        induction (FractionalIdeal.count F v J).toNat with
        | zero => simp
        | succ n ih => simpa [pow_succ] using mul_le_mul' ih hprime
    have hIle : I ≤ 𝔞 := by
      calc
        I = J * 𝔞 := by dsimp only [J]; rw [mul_assoc, inv_mul_cancel₀ h𝔞, mul_one]
        _ ≤ 1 * 𝔞 := by simpa only [mul_comm] using mul_le_mul_right hJle 𝔞
        _ = 𝔞 := one_mul _
    exact FractionalIdeal.spanSingleton_le_iff_mem.mp hIle

/-- The local additive period subgroup associated with a fractional ideal. -/
def idealLocalPeriods
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (v : FinPlace F) :
    AddSubgroup (v.adicCompletion F) where
  carrier := {x | absFin v x ≤ (qv v) ^ (-FractionalIdeal.count F v 𝔞)}
  zero_mem' := by
    change absFin v 0 ≤ (qv v) ^ (-FractionalIdeal.count F v 𝔞)
    rw [absFin_eq_norm, norm_zero]
    exact (zpow_pos (zero_lt_one.trans (qv_gt_one v)) _).le
  add_mem' := by
    intro x y hx hy
    simp only [absFin_eq_norm] at hx hy ⊢
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  neg_mem' := by
    intro x hx
    simpa only [Set.mem_ofPred_eq, absFin_eq_norm, norm_neg] using hx

/-- Rational classes modulo an ideal give the direct sum of all local additive period quotients. -/
theorem ideal_additive_quotient_equiv
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0) :
    ∃ E : (F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup) ≃+
        (Π₀ v : FinPlace F, (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v),
      ∀ (ξ : F) (v : FinPlace F),
        E (QuotientAddGroup.mk ξ) v =
          QuotientAddGroup.mk (algebraMap F (v.adicCompletion F) ξ) := by
  classical
  let c (v : FinPlace F) : ℤ := FractionalIdeal.count F v 𝔞
  let Q (v : FinPlace F) := (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v
  let C := Π₀ v : FinPlace F, Q v
  let q (ξ : F) (v : FinPlace F) : Q v :=
    QuotientAddGroup.mk (algebraMap F (v.adicCompletion F) ξ)
  have hc : (Function.support c).Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors 𝔞)
  have hfinite (ξ : F) : {v : FinPlace F | q ξ v ≠ 0}.Finite := by
    by_cases hξ : ξ = 0
    · simp [q, hξ]
    let d (v : FinPlace F) : ℤ := FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ξ)
    have hd : (Function.support d).Finite := Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ξ))
    apply (hc.union hd).subset
    intro v hv
    by_contra hnot
    have hc0 : c v = 0 := by
      by_contra h
      exact hnot (Or.inl h)
    have hd0 : d v = 0 := by
      by_contra h
      exact hnot (Or.inr h)
    apply hv
    change (QuotientAddGroup.mk (algebraMap F (v.adicCompletion F) ξ) : Q v) = 0
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    change absFin v (algebraMap F (v.adicCompletion F) ξ) ≤ (qv v) ^ (-c v)
    have hnorm : absFin v (algebraMap F (v.adicCompletion F) ξ) = (qv v) ^ (-d v) := by
      rw [absFin_eq_norm]
      change ‖FinitePlace.embedding v ξ‖ = _
      exact norm_embedding_eq_absNorm_zpow v ξ hξ
    rw [hnorm, hc0, hd0]
  let f0 (ξ : F) : C := DFinsupp.mk (hfinite ξ).toFinset (fun v => q ξ v.1)
  have hfeval (ξ : F) (v : FinPlace F) : f0 ξ v = q ξ v := by
    dsimp only [f0]
    by_cases hv : v ∈ (hfinite ξ).toFinset
    · rw [DFinsupp.mk_of_mem hv]
    · rw [DFinsupp.mk_of_notMem hv]
      exact (not_not.mp fun h => hv ((hfinite ξ).mem_toFinset.mpr h)).symm
  let f : F →+ C :=
    { toFun := f0
      map_zero' := by
        apply DFinsupp.ext
        intro v
        rw [hfeval]
        change (QuotientAddGroup.mk (algebraMap F (v.adicCompletion F) 0) : Q v) = 0
        simp
      map_add' := by
        intro ξ η
        apply DFinsupp.ext
        intro v
        change f0 (ξ + η) v = f0 ξ v + f0 η v
        simp only [hfeval, q, map_add, QuotientAddGroup.mk_add] }
  have hf (ξ : F) (v : FinPlace F) : f ξ v = q ξ v := hfeval ξ v
  let J := (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  have hker : J = f.ker := by
    apply AddSubgroup.ext
    intro ξ
    change ξ ∈ (𝔞 : Submodule (𝓞 F) F) ↔ f ξ = 0
    rw [fractionalIdeal_mem_iff_local_bounds 𝔞 h𝔞 ξ]
    constructor
    · intro hξ
      apply DFinsupp.ext
      intro v
      rw [hf]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (hξ v)
    · intro hξ v
      have hv := congrArg (fun z : C => z v) hξ
      rw [hf, DFinsupp.zero_apply] at hv
      exact (QuotientAddGroup.eq_zero_iff _).mp hv
  have hsurj : Function.Surjective f := by
    intro a
    let x (v : FinPlace F) : v.adicCompletion F := Quotient.out (a v)
    have hx : {v : FinPlace F | 1 < absFin v (x v)}.Finite := by
      apply ((DFinsupp.finite_support a).union hc).subset
      intro v hv
      by_contra hnot
      have hav0 : a v = 0 := by
        by_contra h
        exact hnot (Or.inl h)
      have hc0 : c v = 0 := by
        by_contra h
        exact hnot (Or.inr h)
      have hclass : (QuotientAddGroup.mk (x v) : Q v) = 0 :=
        (Quotient.out_eq (a v)).trans hav0
      have hmem := (QuotientAddGroup.eq_zero_iff _).mp hclass
      change absFin v (x v) ≤ (qv v) ^ (-c v) at hmem
      rw [hc0, neg_zero, zpow_zero] at hmem
      exact (not_le_of_gt hv) hmem
    obtain ⟨ξ, hξ⟩ := finite_adelic_additive_approximation x hx c hc
    refine ⟨ξ, ?_⟩
    apply DFinsupp.ext
    intro v
    rw [hf]
    calc
      q ξ v = (QuotientAddGroup.mk (x v) : Q v) := by
        dsimp only [q]
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        change absFin v (algebraMap F (v.adicCompletion F) ξ - x v) ≤ (qv v) ^ (-c v)
        have hneg : algebraMap F (v.adicCompletion F) ξ - x v =
            -(x v - algebraMap F (v.adicCompletion F) ξ) := by abel
        rw [hneg, absFin_eq_norm, norm_neg]
        simpa only [absFin_eq_norm] using hξ v
      _ = a v := Quotient.out_eq (a v)
  refine ⟨QuotientAddGroup.liftEquiv J hsurj hker, ?_⟩
  intro ξ v
  rw [QuotientAddGroup.liftEquiv_mk]
  exact hf ξ v

open MeasureTheory

/-- Local ideal periods are compact open and have their normalized fractional-ideal mass. -/
theorem idealLocalPeriods_haar_mass
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (v : FinPlace F) (μ : LocHaar v) :
    IsCompact (idealLocalPeriods 𝔞 v : Set (v.adicCompletion F)) ∧
    IsOpen (idealLocalPeriods 𝔞 v : Set (v.adicCompletion F)) ∧
    (μ.μ (idealLocalPeriods 𝔞 v : Set (v.adicCompletion F))).toReal =
      (qv v) ^ (-FractionalIdeal.count F v 𝔞) := by
  classical
  let K := v.adicCompletion F
  let c := FractionalIdeal.count F v 𝔞
  let R : ℝ := (qv v) ^ (-c)
  let U : Set K := idealLocalPeriods 𝔞 v
  let O := v.adicCompletionIntegers F
  let ρ : Kˣ := unifLoc v ^ c
  have hR : 0 < R := zpow_pos (zero_lt_one.trans (qv_gt_one v)) _
  have hπval : Valued.v (unifLoc v : K) = WithZero.exp (-1 : ℤ) := by
    have hcoe : (unifLoc v : K) = algebraMap F K (unif v) := by
      simp [unifLoc, toLoc, K]
    rw [hcoe]
    change Valued.v ((unif v : F) : v.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπnorm : absFin v (unifLoc v : K) = (qv v)⁻¹ := by
    rw [absFin_eq_norm, FinitePlace.norm_def, hπval]
    rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp)]
    rw [WithZero.toAdd_unzero_eq_log (by simp)]
    simp [qv]
  have hρnorm : absFin v (ρ : K) = R := by
    dsimp only [ρ, R]
    rw [absFin_eq_norm, Units.val_zpow_eq_zpow_val, norm_zpow,
      ← absFin_eq_norm v (unifLoc v : K), hπnorm, inv_zpow, zpow_neg]
  have hρval : Valued.v (ρ : K) = WithZero.exp (-c) := by
    dsimp only [ρ]
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπval]
    simp [← WithZero.exp_zsmul]
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hball : U = Metric.closedBall (0 : K) R := by
    ext x
    change absFin v x ≤ R ↔ dist x 0 ≤ R
    rw [absFin_eq_norm, dist_zero_right]
  have hcompact : IsCompact U := by
    rw [hball]
    exact hproper.isCompact_closedBall 0 R
  have hvalset : U = {x : K | Valued.v x ≤ WithZero.exp (-c)} := by
    ext x
    change absFin v x ≤ R ↔ Valued.v x ≤ WithZero.exp (-c)
    rw [← hρnorm, absFin_eq_norm, absFin_eq_norm, ← hρval]
    exact Valued.toNormedField.norm_le_iff
  have hopen : IsOpen U := by
    rw [hvalset]
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hpre (t : K) : (ρ : K) * t ∈ U ↔ t ∈ O := by
    change absFin v ((ρ : K) * t) ≤ R ↔ t ∈ O
    rw [absFin_eq_norm, norm_mul, ← absFin_eq_norm v (ρ : K), hρnorm]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
    simpa only [mul_one] using (mul_le_mul_iff_right₀ hR : R * ‖t‖ ≤ R * 1 ↔ ‖t‖ ≤ 1)
  have hOmeas : MeasurableSet (O : Set K) := (Valued.isOpen_integer K).measurableSet
  have hcomp : (fun t : K => U.indicator (fun _ : K => (1 : ℝ)) ((ρ : K) * t)) =
      (O : Set K).indicator (fun _ : K => (1 : ℝ)) := by
    funext t
    by_cases ht : t ∈ O
    · rw [Set.indicator_of_mem ((hpre t).mpr ht), Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem (mt (hpre t).mp ht), Set.indicator_of_notMem ht]
  have hscale := μ.integral_comp_mul ρ (U.indicator (fun _ : K => (1 : ℝ)))
  rw [hcomp, integral_indicator hOmeas, setIntegral_const,
    integral_indicator hopen.measurableSet, setIntegral_const] at hscale
  have hmassO : μ.μ (O : Set K) = 1 := μ.norm_O
  simp only [measureReal_def, hmassO, ENNReal.toReal_one, smul_eq_mul, mul_one,
    hρnorm] at hscale
  have hm := congrArg (fun z : ℝ => R * z) hscale
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at hm
  exact ⟨hcompact, hopen, hm.symm⟩

end ArtinPrimitiveRoots.A1.Theta
