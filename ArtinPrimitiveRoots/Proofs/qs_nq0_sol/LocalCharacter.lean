import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Generators
import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ResidueUnits
import ArtinPrimitiveRoots.A1.Characters

/-!
# Local quadratic characters for the narrow family

Read the cubed Hilbert symbol through the fixed complex embedding. The
algebraic local character is quadratic because the Hilbert value is a sixth
root of unity. Continuity and global descent are subsequent steps.

The remaining global-character statement, in this module's context, is:
```
theorem qs_nq0_quadratic_character_exists (D : FieldData K) (H : HilbertData K)
    (a : Kˣ) :
    ∃ χ : HeckeChar K, χ ^ 2 = 1 ∧
      (∀ (w : InfinitePlace K) (u : w.Completionˣ), χ.locInf w u = 1) ∧
      (∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a))
```
-/

set_option autoImplicit false

open scoped NumberField Topology
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The cubed Hilbert character at one finite place, read through `D.σ0`. -/
def qsNQQuadraticLocal (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    (v.adicCompletion K)ˣ →* ℂˣ :=
  (powMonoidHom 3 : ℂˣ →* ℂˣ).comp
    ((Units.map D.σ0.toMonoidHom).comp
      ((rootsOfUnity 6 K).subtype.comp
        (MonoidHom.mk' (fun u => H.hilb v a u) (fun u u' => H.mul_right v a u u'))))

/-- Cubing a sextic Hilbert character gives a character whose square is trivial. -/
theorem qs_nq0_quadratic_local_square (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    qsNQQuadraticLocal D H v a ^ 2 = 1 := by
  apply MonoidHom.ext
  intro u
  change (Units.map D.σ0.toMonoidHom (H.hilb v a u : Kˣ) ^ 3) ^ 2 = 1
  have h6 : (H.hilb v a u : Kˣ) ^ 6 = 1 :=
    (mem_rootsOfUnity 6 _).mp (H.hilb v a u).property
  rw [← pow_mul]
  change Units.map D.σ0.toMonoidHom (H.hilb v a u : Kˣ) ^ 6 = 1
  rw [← map_pow, h6, map_one]

/-- Powers with nonzero exponent in the field contain a unit neighborhood of `1`. -/
theorem qs_nq0_power_units_neighborhood (L : Type*)
    [NontriviallyNormedField L] [CompleteSpace L]
    (n : ℕ) (hn : (n : L) ≠ 0) :
    {u : Lˣ | ∃ b : Lˣ, u = b ^ n} ∈ 𝓝 (1 : Lˣ) := by
  have hnNat : n ≠ 0 := by
    intro h
    apply hn
    simp [h]
  have hd : HasStrictDerivAt (fun x : L => x ^ n) (n : L) 1 := by
    simpa using hasStrictDerivAt_pow n (1 : L)
  have hm : Filter.map (fun x : L => x ^ n) (𝓝 1) = 𝓝 1 := by
    simpa using hd.map_nhds_eq hn
  have hp : {x : L | ∃ y : L, x = y ^ n} ∈
      Filter.map (fun x : L => x ^ n) (𝓝 1) := by
    exact Filter.mem_map.mpr (Filter.Eventually.of_forall (fun x => ⟨x, rfl⟩))
  rw [hm] at hp
  filter_upwards [(Units.continuous_val.tendsto (1 : Lˣ)).eventually hp] with u hu
  obtain ⟨y, hy⟩ := hu
  have hy0 : y ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [hy, h, zero_pow hnNat]
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  change (u : L) = y ^ n
  exact hy

/-- The local quadratic Hilbert homomorphism is continuous. -/
theorem qs_nq0_quadratic_local_continuous (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (a : (v.adicCompletion K)ˣ) :
    Continuous (qsNQQuadraticLocal D H v a) := by
  let L := v.adicCompletion K
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let x : L := NumberField.FinitePlace.embedding v (algebraMap (𝓞 K) K t)
  have htK : algebraMap (𝓞 K) K t ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ht0
  have hx0 : x ≠ 0 := (NumberField.FinitePlace.embedding v).injective.ne htK
  have hxnorm : ‖x‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem (K := K) v t).mpr ht
  letI : NontriviallyNormedField L :=
    NontriviallyNormedField.ofNormNeOne ⟨x, hx0, ne_of_lt hxnorm⟩
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hk : (2 : K) = 0 := (algebraMap K L).injective
      (by simpa only [map_ofNat, map_zero] using h)
    exact (two_ne_zero : (2 : K) ≠ 0) hk
  let f : Lˣ →* ℂˣ := qsNQQuadraticLocal D H v a
  apply continuous_of_tendsto_nhds_one f
  have hs := qs_nq0_power_units_neighborhood L 2 h2
  have heq : (fun u : Lˣ => f u) =ᶠ[𝓝 (1 : Lˣ)] (fun _ => (1 : ℂˣ)) := by
    filter_upwards [hs] with u hu
    obtain ⟨b, rfl⟩ := hu
    rw [map_pow]
    have hval := congrArg (fun g : Lˣ →* ℂˣ => g b)
      (qs_nq0_quadratic_local_square D H v a)
    exact hval
  apply (Filter.tendsto_congr' heq).mpr
  exact tendsto_const_nhds

/-- The finite quadratic local product is trivial on principal ideles. -/
theorem qs_nq0_quadratic_product_formula (D : FieldData K) (H : HilbertData K)
    (a b : Kˣ) :
    (Function.mulSupport (fun v : FinPlace K =>
      qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b))).Finite ∧
      ∏ᶠ v : FinPlace K,
        qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) = 1 := by
  let g : rootsOfUnity 6 K →* ℂˣ :=
    (powMonoidHom 3 : ℂˣ →* ℂˣ).comp
      ((Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 K).subtype)
  obtain ⟨hf, hp⟩ := H.product_formula a b
  constructor
  · change Function.HasFiniteMulSupport
      (fun v : FinPlace K => g (H.hilb v (toLoc v a) (toLoc v b)))
    exact Function.HasFiniteMulSupport.fun_comp hf g.map_one
  · change (∏ᶠ v : FinPlace K, g (H.hilb v (toLoc v a) (toLoc v b))) = 1
    rw [← g.map_finprod hf, hp, g.map_one]

/-!
The next local-unit statement is:
```
theorem qs_nq0_quadratic_local_unit_trivial (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ) (ha : v.valuation K (a : K) = 1)
    (u : (v.adicCompletion K)ˣ)
    (hu : u ∈ (v.adicCompletionIntegers K).units) :
    qsNQQuadraticLocal D H v (toLoc v a) u = 1
```
-/

/-- Away from 6, a global valuation-one argument gives an unramified quadratic character. -/
theorem qs_nq0_quadratic_local_unit_trivial (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ) (ha : v.valuation K (a : K) = 1)
    (u : (v.adicCompletion K)ˣ)
    (hu : u ∈ (v.adicCompletionIntegers K).units) :
    qsNQQuadraticLocal D H v (toLoc v a) u = 1 := by
  classical
  let L := v.adicCompletion K
  let f : Lˣ →* ℂˣ := qsNQQuadraticLocal D H v (toLoc v a)
  have hglobal (b : Kˣ) (hb : v.valuation K (b : K) = 1) :
      f (toLoc v b) = 1 := by
    have htame := H.tame v h6 a b
      ((qs_nq0_residue_ne_zero_iff_valuation_one v (a : K)).mpr ha)
    have hcount := qs_nq0_count_spanSingleton_eq_neg_log_valuation v (b : K) b.ne_zero
    rw [hb, WithZero.log_one, neg_zero] at hcount
    rw [hcount, zpow_zero] at htame
    have hhilb : H.hilb v (toLoc v a) (toLoc v b) = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact htame
    change Units.map D.σ0.toMonoidHom (H.hilb v (toLoc v a) (toLoc v b) : Kˣ) ^ 3 = 1
    rw [hhilb]
    simp
  have hf : Continuous f := qs_nq0_quadratic_local_continuous D H v (toLoc v a)
  have hO : IsOpen (v.adicCompletionIntegers K : Set L) :=
    Valued.isOpen_valuationSubring L
  have hOU : IsOpen {t : Lˣ | t ∈ (v.adicCompletionIntegers K).units} := by
    change IsOpen (((fun t : Lˣ => (t : L)) ⁻¹' (v.adicCompletionIntegers K : Set L)) ∩
      ((fun t : Lˣ => ((t⁻¹ : Lˣ) : L)) ⁻¹' (v.adicCompletionIntegers K : Set L)))
    exact (hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv)
  have hneq : IsOpen {t : Lˣ | f t ≠ 1} :=
    (isClosed_eq hf continuous_const).isOpen_compl
  by_contra hnu
  let U : Set Lˣ := {t | t ∈ (v.adicCompletionIntegers K).units ∧ f t ≠ 1}
  have hU : IsOpen U := hOU.inter hneq
  have himage : IsOpen (Units.val '' U) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap U hU
  obtain ⟨b, hb⟩ := (v.denseRange_algebraMap K).exists_mem_open himage
    ⟨(u : L), u, ⟨hu, hnu⟩, rfl⟩
  obtain ⟨t, ht, htb⟩ := hb
  have hb0 : b ≠ 0 := by
    intro h
    apply Units.ne_zero t
    simpa only [h, map_zero] using htb
  have htval : Valued.v (t : L) = 1 :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ht.1
  have hbval : v.valuation K b = 1 := by
    calc
      v.valuation K b = Valued.v (algebraMap K L b) :=
        (v.valuedAdicCompletion_eq_valuation' b).symm
      _ = Valued.v (t : L) := congrArg Valued.v htb.symm
      _ = 1 := htval
  have htloc : t = toLoc v (Units.mk0 b hb0) := by
    apply Units.ext
    exact htb
  apply ht.2
  rw [htloc]
  exact hglobal (Units.mk0 b hb0) hbval

/-!
The next almost-everywhere statement is:
```
theorem qs_nq0_quadratic_local_eventually_unit_trivial
    (D : FieldData K) (H : HilbertData K) (a : Kˣ) :
    ∀ᶠ v : FinPlace K in Filter.cofinite,
      ∀ u : (v.adicCompletion K)ˣ,
        u ∈ (v.adicCompletionIntegers K).units →
          qsNQQuadraticLocal D H v (toLoc v a) u = 1
```
-/

/-- The local quadratic character is trivial on integral units at almost every finite place. -/
theorem qs_nq0_quadratic_local_eventually_unit_trivial
    (D : FieldData K) (H : HilbertData K) (a : Kˣ) :
    ∀ᶠ v : FinPlace K in Filter.cofinite,
      ∀ u : (v.adicCompletion K)ˣ,
        u ∈ (v.adicCompletionIntegers K).units →
          qsNQQuadraticLocal D H v (toLoc v a) u = 1 := by
  have hval (x : K) (hx : x ≠ 0) :
      ∀ᶠ v : FinPlace K in Filter.cofinite, v.valuation K x = 1 := by
    filter_upwards [FractionalIdeal.finite_factors
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x)] with v hv
    have hcount := qs_nq0_count_spanSingleton_eq_neg_log_valuation v x hx
    rw [hv] at hcount
    have hlog : WithZero.log (v.valuation K x) = 0 := neg_eq_zero.mp hcount.symm
    have hv0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    calc
      v.valuation K x = WithZero.exp (WithZero.log (v.valuation K x)) :=
        (WithZero.exp_log hv0).symm
      _ = 1 := by rw [hlog, WithZero.exp_zero]
  filter_upwards [hval (a : K) a.ne_zero, hval (6 : K) (by norm_num)] with v hva hv6
  have h6 : (6 : 𝓞 K) ∉ v.asIdeal :=
    (v.valuation_eq_one_iff_notMem (K := K)).mp (by simpa only [map_ofNat] using hv6)
  intro u hu
  exact qs_nq0_quadratic_local_unit_trivial D H v h6 a hva u hu

/-!
The principal-unit statement has this exact signature:
```
theorem qs_nq0_quadratic_local_principal_unit_trivial
    (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v ((u : v.adicCompletion K) - 1) < 1) :
    qsNQQuadraticLocal D H v (toLoc v a) u = 1
```
-/

/-- Away from six, every quadratic Hilbert character kills the principal units. -/
theorem qs_nq0_quadratic_local_principal_unit_trivial
    (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v ((u : v.adicCompletion K) - 1) < 1) :
    qsNQQuadraticLocal D H v (toLoc v a) u = 1 := by
  classical
  let L := v.adicCompletion K
  let f : Lˣ →* ℂˣ := qsNQQuadraticLocal D H v (toLoc v a)
  have hglobal (b : Kˣ) (hb : v.valuation K ((b : K) - 1) < 1) :
      f (toLoc v b) = 1 := by
    have hres := qs_nq0_residue_eq_one_of_valuation_sub_one_lt_one v (b : K) hb
    have hchi := qs_nq0_chiAlg_eq_one_of_residue_one v h6 (b : K) hres
    have htame := H.tame v h6 b a (by rw [hres]; exact one_ne_zero)
    have hba : H.hilb v (toLoc v b) (toLoc v a) = 1 := by
      apply Subtype.ext
      apply Units.ext
      simpa [hchi] using htame
    have hab := H.skew v (toLoc v a) (toLoc v b)
    rw [hba, mul_one] at hab
    change Units.map D.σ0.toMonoidHom (H.hilb v (toLoc v a) (toLoc v b) : Kˣ) ^ 3 = 1
    rw [hab]
    simp
  have hf : Continuous f := qs_nq0_quadratic_local_continuous D H v (toLoc v a)
  have hball : IsOpen {x : L | Valued.v x < 1} := by
    simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using
      (Valued.isOpen_ball L 1)
  have hPU : IsOpen {t : Lˣ | Valued.v ((t : L) - 1) < 1} :=
    hball.preimage (Units.continuous_val.sub continuous_const)
  have hneq : IsOpen {t : Lˣ | f t ≠ 1} :=
    (isClosed_eq hf continuous_const).isOpen_compl
  by_contra hnu
  let U : Set Lˣ := {t | Valued.v ((t : L) - 1) < 1 ∧ f t ≠ 1}
  have hU : IsOpen U := hPU.inter hneq
  have himage : IsOpen (Units.val '' U) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap U hU
  obtain ⟨b, hb⟩ := (v.denseRange_algebraMap K).exists_mem_open himage
    ⟨(u : L), u, ⟨hu, hnu⟩, rfl⟩
  obtain ⟨t, ht, htb⟩ := hb
  have hb0 : b ≠ 0 := by
    intro h
    apply Units.ne_zero t
    simpa only [h, map_zero] using htb
  have hbval : v.valuation K (b - 1) < 1 := by
    calc
      v.valuation K (b - 1) = Valued.v (algebraMap K L (b - 1)) :=
        (v.valuedAdicCompletion_eq_valuation' (b - 1)).symm
      _ = Valued.v ((t : L) - 1) := by rw [map_sub, map_one, ← htb]
      _ < 1 := ht.1
  have htloc : t = toLoc v (Units.mk0 b hb0) := by
    apply Units.ext
    exact htb
  apply ht.2
  rw [htloc]
  exact hglobal (Units.mk0 b hb0) hbval

/-!
The exterior exponent-one nontriviality step has this exact signature:
```
theorem qs_nq0_quadratic_local_nontrivial
    (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ)
    (ha : FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = 1) :
    ∃ b : Kˣ, v.valuation K (b : K) = 1 ∧
      qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) ≠ 1
```
-/

/-- Exterior exponent one forces the quadratic character to detect a local integral unit. -/
theorem qs_nq0_quadratic_local_nontrivial
    (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ)
    (ha : FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = 1) :
    ∃ b : Kˣ, v.valuation K (b : K) = 1 ∧
      qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) ≠ 1 := by
  obtain ⟨b, hbval, hbpow⟩ := qs_nq0_residue_quadratic_nontrivial v h6
  have hbunit : residue v (b : K) ≠ 0 :=
    (qs_nq0_residue_ne_zero_iff_valuation_one v (b : K)).mpr hbval
  refine ⟨b, hbval, ?_⟩
  intro hlocal
  have hcomplex := congrArg (fun z : ℂˣ => (z : ℂ)) hlocal
  change D.σ0 (((H.hilb v (toLoc v a) (toLoc v b) : Kˣ) : K)) ^ 3 = 1 at hcomplex
  have hab : (((H.hilb v (toLoc v a) (toLoc v b) : Kˣ) : K)) ^ 3 = 1 := by
    apply D.σ0.injective
    simpa only [map_pow, map_one] using hcomplex
  have hskew := congrArg (fun z : rootsOfUnity 6 K => ((z : Kˣ) : K))
    (H.skew v (toLoc v a) (toLoc v b))
  change (((H.hilb v (toLoc v a) (toLoc v b) : Kˣ) : K)) *
    (((H.hilb v (toLoc v b) (toLoc v a) : Kˣ) : K)) = 1 at hskew
  have hba : (((H.hilb v (toLoc v b) (toLoc v a) : Kˣ) : K)) ^ 3 = 1 := by
    have hcubed := congrArg (fun z : K => z ^ 3) hskew
    rwa [mul_pow, hab, one_mul, one_pow] at hcubed
  have htame := H.tame v h6 b a hbunit
  rw [ha, zpow_one] at htame
  have hintegral : (((chiAlg v (b : K) : (𝓞 K)ˣ) : 𝓞 K)) ^ 3 = 1 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_pow, ← htame, map_one]
    exact hba
  apply hbpow
  rw [← qs_nq0_chiAlg_cube_reduction D v h6 (b : K) hbunit, hintegral, map_one]

/-!
The unramified prime-value step has this exact signature:
```
theorem qs_nq0_quadratic_prime_value
    (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ) (ha : v.valuation K (a : K) = 1)
    (χ : HeckeChar K)
    (hloc : χ.loc v = qsNQQuadraticLocal D H v (toLoc v a)) :
    χ.UnramifiedAt v ∧ χ.primeValue v = chi D v (a : K) ^ 3
```
-/

/-- Away from six, the unramified quadratic prime value is the cubed sextic residue symbol. -/
theorem qs_nq0_quadratic_prime_value
    (D : FieldData K) (H : HilbertData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (a : Kˣ) (ha : v.valuation K (a : K) = 1)
    (χ : HeckeChar K)
    (hloc : χ.loc v = qsNQQuadraticLocal D H v (toLoc v a)) :
    χ.UnramifiedAt v ∧ χ.primeValue v = chi D v (a : K) ^ 3 := by
  classical
  have hunram : χ.UnramifiedAt v := by
    intro u hu hui
    rw [hloc]
    exact qs_nq0_quadratic_local_unit_trivial D H v h6 a ha u ⟨hu, hui⟩
  have hres : residue v (a : K) ≠ 0 :=
    (qs_nq0_residue_ne_zero_iff_valuation_one v (a : K)).mpr ha
  have hval : v.valuation K (unif v) = WithZero.exp (-1 : ℤ) :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v).choose_spec
  have hcount : FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (unif v)) = 1 := by
    rw [qs_nq0_count_spanSingleton_eq_neg_log_valuation v (unif v) (unif_ne_zero v),
      hval, WithZero.log_exp]
    norm_num
  have htame := H.tame v h6 a (Units.mk0 (unif v) (unif_ne_zero v)) hres
  simp only [Units.val_mk0, hcount, zpow_one] at htame
  refine ⟨hunram, ?_⟩
  rw [HeckeChar.primeValue, if_pos hunram, hloc]
  change D.σ0 (((H.hilb v (toLoc v a)
    (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) : Kˣ) : K)) ^ 3 = chi D v (a : K) ^ 3
  rw [htame, chi, if_neg hres]

/-!
The exterior ideal-value step has this exact signature:
```
theorem qs_nq0_quadratic_ideal_value
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K)
    (a : Kˣ) (χ : HeckeChar K)
    (hloc : ∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (I : Ideal (𝓞 K)) (hI : Sd.IsExterior I)
    (ha : ∀ v : FinPlace K, I ≤ v.asIdeal → v.valuation K (a : K) = 1) :
    χ.idealValue I = chiIdealPow D I (a : K) 3
```
-/

/-- Primewise unit conditions identify the exterior ideal value with the cubed residue product. -/
theorem qs_nq0_quadratic_ideal_value
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K)
    (a : Kˣ) (χ : HeckeChar K)
    (hloc : ∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (I : Ideal (𝓞 K)) (hI : Sd.IsExterior I)
    (ha : ∀ v : FinPlace K, I ≤ v.asIdeal → v.valuation K (a : K) = 1) :
    χ.idealValue I = chiIdealPow D I (a : K) 3 := by
  classical
  unfold HeckeChar.idealValue chiIdealPow
  apply congrArg (Multiset.prod : Multiset ℂ → ℂ)
  apply Multiset.map_congr rfl
  intro P hP
  split_ifs with hp
  · let v : FinPlace K := ⟨P, hp.1, hp.2⟩
    have hdiv : I ≤ v.asIdeal :=
      Ideal.dvd_iff_le.mp (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
    have hv : v ∉ Sd.Sf := fun hv => hI.2 v hv hdiv
    have h6 : (6 : 𝓞 K) ∉ v.asIdeal := fun h => hv (Sd.over6 v h)
    have hval := ha v hdiv
    have hres : residue v (a : K) ≠ 0 :=
      (qs_nq0_residue_ne_zero_iff_valuation_one v (a : K)).mpr hval
    have hvalue := (qs_nq0_quadratic_prime_value D H v h6 a hval χ (hloc v)).2
    change χ.primeValue v = chiPow D v (a : K) 3
    simpa only [chiPow, ite_eq_right hres, zpow_ofNat] using hvalue
  · rfl

/-!
The finite-place ideal-value step has this exact signature:
```
theorem qs_nq0_ideal_value_finprod
    (χ : HeckeChar K) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    χ.idealValue I = ∏ᶠ v : FinPlace K, χ.primeValue v ^ idealExp v I
```
-/

/-- The normalized-factor ideal value is the product of prime values with their exponents. -/
theorem qs_nq0_ideal_value_finprod
    (χ : HeckeChar K) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    χ.idealValue I = ∏ᶠ v : FinPlace K, χ.primeValue v ^ idealExp v I := by
  classical
  unfold HeckeChar.idealValue
  rw [Multiset.prod_map_eq_finprod]
  rw [← finprod_emb_domain' IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    (fun v : FinPlace K => χ.primeValue v ^ idealExp v I)]
  apply finprod_congr
  intro P
  by_cases hp : P.IsPrime ∧ P ≠ ⊥
  · let v : FinPlace K := ⟨P, hp.1, hp.2⟩
    have hmem : P ∈ Set.range (fun v : FinPlace K => v.asIdeal) := ⟨v, rfl⟩
    rw [dif_pos hp, dif_pos hmem]
    have hv : Classical.choose hmem = v :=
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective (Classical.choose_spec hmem)
    rw [hv]
    congr 1
    exact (Ideal.count_associates_factors_eq hI hp.1 hp.2).symm
  · have hnot : P ∉ Set.range (fun v : FinPlace K => v.asIdeal) := by
      rintro ⟨v, rfl⟩
      exact hp ⟨v.isPrime, v.ne_bot⟩
    simp only [dif_neg hp, one_pow, dif_neg hnot]

/-!
The next local reciprocity step has this exact signature:
```
theorem qs_nq0_quadratic_local_generator_pair
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K)
    (I J : Ideal (𝓞 K)) (a b : Kˣ)
    (ha : Sd.IsGen (a : K) I) (hb : Sd.IsGen (b : K) J)
    (hcoprime : IsCoprime I J)
    (χa χb : HeckeChar K) (v : FinPlace K) (hv : v ∉ Sd.Sf)
    (hloca : χa.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (hlocb : χb.loc v = qsNQQuadraticLocal D H v (toLoc v b)) :
    ((qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) : ℂˣ) : ℂ) =
      χa.primeValue v ^ idealExp v J * χb.primeValue v ^ idealExp v I
```
-/

/-- At an exterior place, coprime generators give the two opposite prime-value factors. -/
theorem qs_nq0_quadratic_local_generator_pair
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K)
    (I J : Ideal (𝓞 K)) (a b : Kˣ)
    (ha : Sd.IsGen (a : K) I) (hb : Sd.IsGen (b : K) J)
    (hcoprime : IsCoprime I J)
    (χa χb : HeckeChar K) (v : FinPlace K) (hv : v ∉ Sd.Sf)
    (hloca : χa.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (hlocb : χb.loc v = qsNQQuadraticLocal D H v (toLoc v b)) :
    ((qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) : ℂˣ) : ℂ) =
      χa.primeValue v ^ idealExp v J * χb.primeValue v ^ idealExp v I := by
  have h6 : (6 : 𝓞 K) ∉ v.asIdeal := fun h => hv (Sd.over6 v h)
  have hunitvalue (c d : Kˣ) (A B : Ideal (𝓞 K))
      (hc : Sd.IsGen (c : K) A) (hd : Sd.IsGen (d : K) B)
      (χ : HeckeChar K)
      (hloc : χ.loc v = qsNQQuadraticLocal D H v (toLoc v c))
      (hzero : idealExp v A = 0) :
      ((qsNQQuadraticLocal D H v (toLoc v c) (toLoc v d) : ℂˣ) : ℂ) =
        χ.primeValue v ^ idealExp v B := by
    have hcount : FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K)) = 0 := by
      rw [hc.2.2 v hv, FractionalIdeal.count_coe K v hc.1.1]
      change (idealExp v A : ℤ) = 0
      rw [hzero, Int.natCast_zero]
    have hlog := qs_nq0_count_spanSingleton_eq_neg_log_valuation v (c : K) c.ne_zero
    rw [hcount] at hlog
    have hz : WithZero.log (v.valuation K (c : K)) = 0 := neg_eq_zero.mp hlog.symm
    have hval : v.valuation K (c : K) = 1 := by
      calc
        v.valuation K (c : K) = WithZero.exp (WithZero.log (v.valuation K (c : K))) :=
          (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr c.ne_zero)).symm
        _ = 1 := by rw [hz, WithZero.exp_zero]
    have hres : residue v (c : K) ≠ 0 :=
      (qs_nq0_residue_ne_zero_iff_valuation_one v (c : K)).mpr hval
    have hprime := (qs_nq0_quadratic_prime_value D H v h6 c hval χ hloc).2
    have htame := H.tame v h6 c d hres
    rw [hd.2.2 v hv, FractionalIdeal.count_coe K v hd.1.1] at htame
    change (((H.hilb v (toLoc v c) (toLoc v d) : Kˣ) : K)) =
      (algebraMap (𝓞 K) K (((chiAlg v (c : K)) : (𝓞 K)ˣ) : 𝓞 K)) ^
        (idealExp v B : ℤ) at htame
    change D.σ0 (((H.hilb v (toLoc v c) (toLoc v d) : Kˣ) : K)) ^ 3 =
      χ.primeValue v ^ idealExp v B
    rw [htame, zpow_natCast, map_pow, hprime, chi, ite_eq_right hres]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hsymm : qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) =
      qsNQQuadraticLocal D H v (toLoc v b) (toLoc v a) := by
    let g : rootsOfUnity 6 K →* ℂˣ :=
      (powMonoidHom 3 : ℂˣ →* ℂˣ).comp
        ((Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 K).subtype)
    have hskew : qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) *
        qsNQQuadraticLocal D H v (toLoc v b) (toLoc v a) = 1 := by
      change g (H.hilb v (toLoc v a) (toLoc v b)) *
        g (H.hilb v (toLoc v b) (toLoc v a)) = 1
      rw [← map_mul, H.skew, map_one]
    have hsquare := congrArg
      (fun f : (v.adicCompletion K)ˣ →* ℂˣ => f (toLoc v b))
      (qs_nq0_quadratic_local_square D H v (toLoc v a))
    change qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) ^ 2 = 1 at hsquare
    calc
      qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) =
          qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) * 1 := (mul_one _).symm
      _ = qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) *
          (qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) *
            qsNQQuadraticLocal D H v (toLoc v b) (toLoc v a)) := by rw [hskew]
      _ = qsNQQuadraticLocal D H v (toLoc v a) (toLoc v b) ^ 2 *
          qsNQQuadraticLocal D H v (toLoc v b) (toLoc v a) := by rw [pow_two, mul_assoc]
      _ = qsNQQuadraticLocal D H v (toLoc v b) (toLoc v a) := by rw [hsquare, one_mul]
  by_cases heI : idealExp v I = 0
  · rw [hunitvalue a b I J ha hb χa hloca heI, heI, pow_zero, mul_one]
  · have heJ : idealExp v J = 0 := by
      by_contra hne
      have hdI : v.asIdeal ∣ I :=
        (Associates.count_ne_zero_iff_dvd ha.1.1 v.irreducible).mp heI
      have hdJ : v.asIdeal ∣ J :=
        (Associates.count_ne_zero_iff_dvd hb.1.1 v.irreducible).mp hne
      exact v.irreducible.not_isUnit (hcoprime.isUnit_of_dvd' hdI hdJ)
    rw [hsymm, hunitvalue b a J I hb ha χb hlocb heJ, heJ, pow_zero, one_mul]

/-!
The quadratic ideal-values step needed by reciprocity and QSFamily has this exact signature:
```
theorem qs_nq0_quadratic_ideal_values
    (χ : HeckeChar K) (hχ : χ ^ 2 = 1) (I : Ideal (𝓞 K)) :
    χ.idealValue I = 0 ∨ χ.idealValue I ^ 2 = 1
```
The following global reciprocity step will use it:
```
theorem qs_nq0_quadratic_reciprocity
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K)
    (Bd : BData Sd H) (I J : Ideal (𝓞 K)) (a b : Kˣ)
    (ha : Sd.IsGen (a : K) I ∧ Bd.Allowed a)
    (hb : Sd.IsGen (b : K) J ∧ Bd.Allowed b)
    (hcoprime : IsCoprime I J)
    (χa χb : HeckeChar K) (hχa : χa ^ 2 = 1)
    (hloca : ∀ v : FinPlace K, χa.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (hlocb : ∀ v : FinPlace K, χb.loc v = qsNQQuadraticLocal D H v (toLoc v b)) :
    χa.idealValue J = χb.idealValue I
```
-/

end ArtinPrimitiveRoots.A2
