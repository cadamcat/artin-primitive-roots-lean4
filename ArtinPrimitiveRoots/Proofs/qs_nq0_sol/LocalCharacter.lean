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

end ArtinPrimitiveRoots.A2
