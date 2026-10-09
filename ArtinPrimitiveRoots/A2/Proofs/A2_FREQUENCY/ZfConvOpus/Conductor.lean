import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs

/-!
# Every Hecke character has a nonzero conductor modulus

Copy of the private chain `conductor_complex_eq_one_of_small_powers` …
`conductor_hecke_continuous_modulus` of `A1/Characters.lean` (lines 218–637, 639–723,
746–790 at `cf661e3d`), which is private there. Used by the totally-complex
`HeckeAnalysis` producer of lane zf-conv-opus.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open Filter Topology
open scoped Classical WithZero
open scoped NumberField AdeleRing FiniteAdeleRing RestrictedProduct

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.zf_conv_opus

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

private theorem conductor_complex_eq_one_of_small_powers {z : ℂ}
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ 1 / 2) : z = 1 := by
  by_contra hz
  have hr : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hgrow (k : ℕ) : (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ 2 ^ k - 1‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = 3 / 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ 3 / 2 * ‖z ^ 2 ^ k - 1‖ := by gcongr
        _ ≤ ‖(z ^ 2 ^ k) ^ 2 - 1‖ := by
          have hw : ‖z ^ 2 ^ k - 1‖ ≤ 1 / 2 := h _
          have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
          have hadd : (3 / 2 : ℝ) ≤ ‖z ^ 2 ^ k + 1‖ := by
            have hnorm := norm_sub_norm_le (2 : ℂ) (-(z ^ 2 ^ k - 1))
            rw [norm_neg, sub_neg_eq_add, htwo] at hnorm
            have heq : (2 : ℂ) + (z ^ 2 ^ k - 1) = z ^ 2 ^ k + 1 := by ring
            rw [heq] at hnorm
            linarith
          have hsq : (z ^ 2 ^ k) ^ 2 - 1 =
              (z ^ 2 ^ k - 1) * (z ^ 2 ^ k + 1) := by ring
          rw [hsq, norm_mul]
          nlinarith [norm_nonneg (z ^ 2 ^ k - 1)]
        _ = ‖z ^ 2 ^ (k + 1) - 1‖ := by rw [← pow_mul, ← pow_succ]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖)
    (by norm_num : (1 : ℝ) < 3 / 2)
  have hlarge : 1 / 2 < (3 / 2 : ℝ) ^ k * ‖z - 1‖ :=
    (div_lt_iff₀ hr).mp hk
  exact (hlarge.trans_le (hgrow k)).not_ge (h (2 ^ k))

private theorem conductor_kills_small_subgroup {G : Type} [Group G]
    (f : G →* ℂˣ) (H : Subgroup G)
    (hsmall : ∀ x ∈ H, ‖((f x : ℂ) - 1)‖ ≤ 1 / 2) : H ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  apply Units.ext
  apply conductor_complex_eq_one_of_small_powers
  intro n
  have hn := hsmall (x ^ n) (H.pow_mem hx n)
  simpa only [map_pow, Units.val_pow_eq_pow_val] using hn

private theorem conductor_local_neighborhood_depth (v : FinPlace F)
    {U : Set (v.adicCompletion F)ˣ} (hU : U ∈ 𝓝 (1 : (v.adicCompletion F)ˣ)) :
    ∃ e : ℕ, 0 < e ∧ ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(e : ℤ)) → u ∈ U := by
  let L := v.adicCompletion F
  rw [(Units.isEmbedding_val₀ (G₀ := L)).isInducing.nhds_eq_comap 1] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hV
  let δ : ℤᵐ⁰ˣ := Units.map
    (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass (Valued.v : Valuation L ℤᵐ⁰)))) γ
  let e : ℕ := (-WithZero.log (δ : ℤᵐ⁰)).toNat + 1
  have hbound : WithZero.exp (-(e : ℤ)) < (δ : ℤᵐ⁰) := by
    rw [← WithZero.exp_log (Units.ne_zero δ), WithZero.exp_lt_exp]
    dsimp only [e]
    omega
  refine ⟨e, by dsimp only [e]; omega, ?_⟩
  intro u hu
  apply hVU
  apply hγ
  change (Valued.v : Valuation L ℤᵐ⁰).restrict ((u : L) - 1) < (γ : _)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hu hbound

private theorem conductor_localUnitGroup_valued_one (v : FinPlace F)
    (x : (v.adicCompletionIntegers F).unitGroup) :
    Valued.v (((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)) = 1 := by
  let O := v.adicCompletionIntegers F
  have hxO : O.valuation ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 :=
    (O.mem_unitGroup_iff (x : (v.adicCompletion F)ˣ)).mp x.property
  have hxInvO : O.valuation
      (((x : (v.adicCompletion F)ˣ)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val]
    rw [(O.valuation).map_inv, hxO]
    simp
  have hxmem : ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ O :=
    O.mem_of_valuation_le_one _ hxO.le
  have hxInvMem :
      (((x : (v.adicCompletion F)ˣ)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ O :=
    O.mem_of_valuation_le_one _ hxInvO.le
  have hxunits : (x : (v.adicCompletion F)ˣ) ∈ O.units := by
    change ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ O ∧
      (((x : (v.adicCompletion F)ˣ)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ O
    exact ⟨hxmem, hxInvMem⟩
  exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mp hxunits

private def conductor_localCongruenceSubgroup (v : FinPlace F) (e : ℕ) :
    Subgroup (v.adicCompletionIntegers F).unitGroup where
  carrier := {x | Valued.v (((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
    WithZero.exp (-(e : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    have hyval := conductor_localUnitGroup_valued_one v y
    have hident :
        (((↑(x * y : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
          v.adicCompletion F) - 1) =
          (((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) *
            ((y : (v.adicCompletion F)ˣ) : v.adicCompletion F) +
          (((y : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) := by
      change ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
          ((y : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 = _
      ring
    change Valued.v (((↑(x * y : (v.adicCompletionIntegers F).unitGroup) :
      (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤ _
    rw [hident]
    exact (Valued.v.map_add_le_max' _ _).trans (max_le (by simpa [hyval] using hx) hy)
  inv_mem' := by
    intro x hx
    have hxinval := conductor_localUnitGroup_valued_one v x⁻¹
    have hident :
        (((↑(x⁻¹ : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
          v.adicCompletion F) - 1) =
          -(((↑(x⁻¹ : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) *
              (((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1)) := by
      let a : v.adicCompletion F := ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      let b : v.adicCompletion F :=
        (((x⁻¹ : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
          v.adicCompletion F)
      have hmul : b * a = 1 := by
        dsimp [a, b]
        have h := congrArg (fun z : (v.adicCompletionIntegers F).unitGroup =>
          ((z : (v.adicCompletion F)ˣ) : v.adicCompletion F)) (inv_mul_cancel x)
        simpa using h
      have hcalc : b - 1 = -(b * (a - 1)) := by
        calc
          b - 1 = -(1 - b) := by ring
          _ = -(b * a - b) := by rw [← hmul]
          _ = -(b * (a - 1)) := by ring
      simpa [a, b] using hcalc
    change Valued.v (((↑(x⁻¹ : (v.adicCompletionIntegers F).unitGroup) :
      (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤ _
    rw [hident, Valued.v.map_neg, Valued.v.map_mul, hxinval, one_mul]
    simpa using hx

private theorem conductor_localUnitGroup_mem_integers (v : FinPlace F)
    (x : (v.adicCompletionIntegers F).unitGroup) :
    ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  have hx := ((v.adicCompletionIntegers F).mem_unitGroup_iff
    (x : (v.adicCompletion F)ˣ)).mp x.property
  exact (v.adicCompletionIntegers F).mem_of_valuation_le_one _ hx.le

private theorem conductor_localUnits_mem_unitGroup (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (huinv : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F) :
    u ∈ (v.adicCompletionIntegers F).unitGroup := by
  let O := v.adicCompletionIntegers F
  let uO : Oˣ := {
    val := ⟨(u : v.adicCompletion F), hu⟩
    inv := ⟨((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), huinv⟩
    val_inv := by apply Subtype.ext; simp
    inv_val := by apply Subtype.ext; simp }
  let z : O.unitGroup := O.unitGroupMulEquiv.symm uO
  have hz : (z : (v.adicCompletion F)ˣ) = u := by
    apply Units.ext
    rfl
  rw [← hz]
  exact z.property

private abbrev conductor_localUnitProduct (F : Type) [Field F] [NumberField F] :=
  ∀ v : FinPlace F, (v.adicCompletionIntegers F).unitGroup

private def conductor_localUnitProductValue (v : FinPlace F)
    (x : (v.adicCompletionIntegers F).unitGroup) : v.adicCompletionIntegers F :=
  ⟨((x : (v.adicCompletion F)ˣ) : v.adicCompletion F),
    conductor_localUnitGroup_mem_integers v x⟩

private noncomputable def conductor_finiteAdeleValue (x : conductor_localUnitProduct F) :
    FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.structureMap
    (fun v : FinPlace F => v.adicCompletion F)
    (fun v : FinPlace F => v.adicCompletionIntegers F)
    Filter.cofinite (fun v => conductor_localUnitProductValue v (x v))

private theorem conductor_finiteAdeleValue_continuous :
    Continuous (conductor_finiteAdeleValue (F := F)) := by
  have hpi : Continuous (fun x : conductor_localUnitProduct F =>
      fun v => conductor_localUnitProductValue v (x v)) := by
    apply continuous_pi
    intro v
    have hval : Continuous (fun x : conductor_localUnitProduct F =>
        ((x v : (v.adicCompletion F)ˣ) : v.adicCompletion F)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
    have h := hval.subtype_mk (fun x => conductor_localUnitGroup_mem_integers v (x v))
    simpa [conductor_localUnitProductValue] using h
  have hsm : Continuous (RestrictedProduct.structureMap
      (fun v : FinPlace F => v.adicCompletion F)
      (fun v : FinPlace F => v.adicCompletionIntegers F) Filter.cofinite) :=
    (RestrictedProduct.isEmbedding_structureMap (R := fun v : FinPlace F => v.adicCompletion F)
      (A := fun v : FinPlace F => v.adicCompletionIntegers F)
      (𝓕 := Filter.cofinite)).continuous
  exact hsm.comp hpi

private noncomputable def conductor_finiteAdeleUnit (x : conductor_localUnitProduct F) :
    (FiniteAdeleRing (𝓞 F) F)ˣ where
  val := conductor_finiteAdeleValue x
  inv := conductor_finiteAdeleValue x⁻¹
  val_inv := by
    apply RestrictedProduct.ext
    intro v
    change (((x v : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) *
      ((((x v : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ)⁻¹ :
        (v.adicCompletion F)ˣ) :
        v.adicCompletion F) = 1
    simp
  inv_val := by
    apply RestrictedProduct.ext
    intro v
    change ((((x v : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ)⁻¹ :
        (v.adicCompletion F)ˣ) :
        v.adicCompletion F) *
      (((x v : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) = 1
    simp

private noncomputable def conductor_finiteAdeleUnitHom :
    conductor_localUnitProduct F →* (FiniteAdeleRing (𝓞 F) F)ˣ where
  toFun := conductor_finiteAdeleUnit
  map_one' := by
    apply Units.ext
    apply RestrictedProduct.ext
    intro v
    rfl
  map_mul' x y := by
    apply Units.ext
    apply RestrictedProduct.ext
    intro v
    change (((x v : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) *
      (((y v : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) =
      (((x v * y v : (v.adicCompletionIntegers F).unitGroup) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F)
    simp

private theorem conductor_finiteAdeleUnit_continuous :
    Continuous (conductor_finiteAdeleUnit (F := F)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact conductor_finiteAdeleValue_continuous (F := F)
  · exact (conductor_finiteAdeleValue_continuous (F := F)).comp continuous_inv

private def conductor_finiteUnitPairOneHom :
    (FiniteAdeleRing (𝓞 F) F)ˣ →* (InfiniteAdeleRing F)ˣ ×
      (FiniteAdeleRing (𝓞 F) F)ˣ where
  toFun x := (1, x)
  map_one' := rfl
  map_mul' x y := by
    change (1, x * y) = (1, x) * (1, y)
    simp

private def conductor_finiteUnitToIdele :
    (FiniteAdeleRing (𝓞 F) F)ˣ →* NumberField.IdeleGroup (𝓞 F) F :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F)
    (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
    conductor_finiteUnitPairOneHom

private def conductor_integralUnitIdeleHom :
    conductor_localUnitProduct F →* NumberField.IdeleGroup (𝓞 F) F :=
  conductor_finiteUnitToIdele.comp conductor_finiteAdeleUnitHom

private noncomputable def conductor_integralUnitIdele (x : conductor_localUnitProduct F) :
    NumberField.IdeleGroup (𝓞 F) F :=
  conductor_integralUnitIdeleHom x

private theorem conductor_integralUnitIdele_continuous :
    Continuous (conductor_integralUnitIdele (F := F)) := by
  change Continuous (fun x : conductor_localUnitProduct F =>
    (Homeomorph.prodUnits (α := InfiniteAdeleRing F)
      (β := FiniteAdeleRing (𝓞 F) F)).symm (1, conductor_finiteAdeleUnit x))
  exact (Homeomorph.prodUnits (α := InfiniteAdeleRing F)
      (β := FiniteAdeleRing (𝓞 F) F)).symm.continuous.comp
    (continuous_const.prodMk (conductor_finiteAdeleUnit_continuous (F := F)))

private def conductor_ideleCharacter (χ : HeckeChar F) :
    ContinuousMonoidHom (NumberField.IdeleGroup (𝓞 F) F) ℂˣ where
  toMonoidHom := χ.toMonoidHom.comp
    (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F))
  continuous_toFun := χ.continuous.comp QuotientGroup.continuous_mk

private def conductor_heckeOnUnitProduct (χ : HeckeChar F) :
    ContinuousMonoidHom (conductor_localUnitProduct F) ℂˣ :=
  (conductor_ideleCharacter χ).comp
    ⟨conductor_integralUnitIdeleHom, conductor_integralUnitIdele_continuous⟩

private theorem conductor_heckeOnUnitProduct_small_nhds (χ : HeckeChar F) :
    {x : conductor_localUnitProduct F |
      ‖((conductor_heckeOnUnitProduct χ x : ℂ) - 1)‖ < 1 / 2} ∈
        𝓝 (1 : conductor_localUnitProduct F) := by
  let B : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hB : B ∈ 𝓝 (1 : ℂˣ) := by
    have hnorm : Continuous (fun z : ℂˣ => ‖(z : ℂ) - 1‖) := by fun_prop
    have hopen : IsOpen ((fun z : ℂˣ => ‖(z : ℂ) - 1‖) ⁻¹' Set.Iio (1 / 2)) :=
      isOpen_Iio.preimage hnorm
    exact hopen.mem_nhds (by norm_num)
  have hTendsto := (conductor_heckeOnUnitProduct χ).continuous.tendsto
    (1 : conductor_localUnitProduct F)
  change (conductor_heckeOnUnitProduct χ) ⁻¹' B ∈
    𝓝 (1 : conductor_localUnitProduct F)
  have hB' : B ∈ 𝓝 ((conductor_heckeOnUnitProduct χ) 1) := by simpa using hB
  exact hTendsto.eventually hB'

private noncomputable def conductor_localUnitSpike (v : FinPlace F)
    (u : (v.adicCompletionIntegers F).unitGroup) : conductor_localUnitProduct F :=
  fun w => if h : w = v then h.symm ▸ u else 1

private theorem conductor_integralUnitIdeleHom_spike (v : FinPlace F)
    (u : (v.adicCompletionIntegers F).unitGroup) :
    conductor_integralUnitIdeleHom (conductor_localUnitSpike v u) =
      NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (u : (v.adicCompletion F)ˣ) := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext
    intro w
    change conductor_localUnitProductValue w (conductor_localUnitSpike v u w) =
      FiniteAdeleRing.ofAdicCompletion F v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) w
    by_cases hw : w = v
    · subst w
      rw [conductor_localUnitSpike, dif_pos rfl, conductor_localUnitProductValue]
      exact ((FiniteAdeleRing.ofAdicCompletion_apply_coe F v
          ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) v).trans
        (Pi.mulSingle_eq_same v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F))).symm
    · rw [conductor_localUnitSpike, dif_neg hw, conductor_localUnitProductValue]
      exact ((FiniteAdeleRing.ofAdicCompletion_apply_coe F v
          ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) w).trans
        (Pi.mulSingle_eq_of_ne (i := v) (i' := w) hw
          ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F))).symm

private theorem conductor_heckeOnUnitProduct_spike (χ : HeckeChar F) (v : FinPlace F)
    (u : (v.adicCompletionIntegers F).unitGroup) :
    conductor_heckeOnUnitProduct χ (conductor_localUnitSpike v u) =
      χ.loc v (u : (v.adicCompletion F)ˣ) := by
  change (conductor_ideleCharacter χ)
      (conductor_integralUnitIdeleHom (conductor_localUnitSpike v u)) = _
  rw [conductor_integralUnitIdeleHom_spike]
  rfl

private theorem conductor_hecke_local_unit_depths (χ : HeckeChar F) :
    ∃ T : Finset (FinPlace F), ∃ e : FinPlace F → ℕ,
      (∀ v, v ∉ T → e v = 0) ∧
      ∀ v (u : (v.adicCompletionIntegers F).unitGroup),
        Valued.v (((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
          WithZero.exp (-(e v : ℤ)) → χ.loc v (u : (v.adicCompletion F)ˣ) = 1 := by
  classical
  have hN := conductor_heckeOnUnitProduct_small_nhds χ
  rw [nhds_pi, Filter.mem_pi'] at hN
  obtain ⟨T, U, hU, hsubset⟩ := hN
  have hAmbient (v : FinPlace F) (hv : v ∈ T) :
      ∃ W : Set (v.adicCompletion F)ˣ, W ∈ 𝓝 (1 : (v.adicCompletion F)ˣ) ∧
        {x : (v.adicCompletionIntegers F).unitGroup | (x : (v.adicCompletion F)ˣ) ∈ W} ⊆ U v := by
    have hUv : U v ∈ 𝓝 (1 : (v.adicCompletionIntegers F).unitGroup) := hU v
    rw [nhds_subtype_eq_comap] at hUv
    obtain ⟨W, hW, hWsub⟩ := Filter.mem_comap.mp hUv
    exact ⟨W, hW, hWsub⟩
  let d (v : FinPlace F) (hv : v ∈ T) :=
    conductor_local_neighborhood_depth v (hAmbient v hv).choose_spec.1
  let e (v : FinPlace F) := if hv : v ∈ T then (d v hv).choose else 0
  have hdepth (v : FinPlace F) (hv : v ∈ T)
      (x : (v.adicCompletionIntegers F).unitGroup)
      (hx : Valued.v (((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
        WithZero.exp (-(e v : ℤ))) : x ∈ U v := by
    have he : e v = (d v hv).choose := by simp [e, hv]
    have hx' : Valued.v (((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
        WithZero.exp (-((d v hv).choose : ℤ)) := by simpa [he] using hx
    have hxW := (d v hv).choose_spec.2 (x : (v.adicCompletion F)ˣ) hx'
    apply (hAmbient v hv).choose_spec.2
    exact hxW
  refine ⟨T, e, ?_, ?_⟩
  · intro v hv
    simp [e, hv]
  · intro v u hu
    let f : (v.adicCompletionIntegers F).unitGroup →* ℂˣ :=
      (χ.loc v).comp (Subgroup.subtype _)
    by_cases hv : v ∈ T
    · let H := conductor_localCongruenceSubgroup v (e v)
      have hsmall : ∀ x ∈ H, ‖((f x : ℂ) - 1)‖ ≤ 1 / 2 := by
        intro x hx
        have hcoords : Set.pi (T : Set (FinPlace F)) U (conductor_localUnitSpike v x) := by
          intro w hw
          by_cases hwv : w = v
          · subst w
            simpa [conductor_localUnitSpike] using hdepth v hv x hx
          · have h1 : (1 : (w.adicCompletionIntegers F).unitGroup) ∈ U w :=
              mem_of_mem_nhds (hU w)
            simpa [conductor_localUnitSpike, hwv] using h1
        have hNspike := hsubset hcoords
        change ‖((conductor_heckeOnUnitProduct χ
          (conductor_localUnitSpike v x) : ℂ) - 1)‖ < 1 / 2 at hNspike
        rw [conductor_heckeOnUnitProduct_spike] at hNspike
        simpa [f] using hNspike.le
      have hker := conductor_kills_small_subgroup f H hsmall
      have hfx : f u = 1 := MonoidHom.mem_ker.mp (hker hu)
      simpa [f] using hfx
    · let H : Subgroup (v.adicCompletionIntegers F).unitGroup := ⊤
      have hsmall : ∀ x ∈ H, ‖((f x : ℂ) - 1)‖ ≤ 1 / 2 := by
        intro x _
        have hcoords : Set.pi (T : Set (FinPlace F)) U (conductor_localUnitSpike v x) := by
          intro w hw
          have hwv : w ≠ v := by
            intro hEq
            subst w
            exact hv hw
          have h1 : (1 : (w.adicCompletionIntegers F).unitGroup) ∈ U w :=
            mem_of_mem_nhds (hU w)
          simpa [conductor_localUnitSpike, hwv] using h1
        have hNspike := hsubset hcoords
        change ‖((conductor_heckeOnUnitProduct χ
          (conductor_localUnitSpike v x) : ℂ) - 1)‖ < 1 / 2 at hNspike
        rw [conductor_heckeOnUnitProduct_spike] at hNspike
        simpa [f] using hNspike.le
      have hker := conductor_kills_small_subgroup f H hsmall
      have hfx : f u = 1 := MonoidHom.mem_ker.mp (hker (by trivial))
      simpa [f] using hfx

private theorem conductor_idealExp_mul_early (v : FinPlace F)
    {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealExp v (I * J) = idealExp v I + idealExp v J := by
  have hcount := FractionalIdeal.count_mul F v
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI :
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hJ :
      (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0)
  rw [← FractionalIdeal.coeIdeal_mul I J,
    FractionalIdeal.count_coe F v (mul_ne_zero hI hJ),
    FractionalIdeal.count_coe F v hI,
    FractionalIdeal.count_coe F v hJ] at hcount
  change (idealExp v (I * J) : ℤ) =
    (idealExp v I : ℤ) + (idealExp v J : ℤ) at hcount
  exact_mod_cast hcount

private theorem conductor_idealExp_top_early (v : FinPlace F) :
    idealExp v (⊤ : Ideal (𝓞 F)) = 0 := by
  unfold idealExp
  rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero v.associates_irreducible]

private theorem conductor_idealExp_pow_early (v : FinPlace F) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (n : ℕ) :
    idealExp v (I ^ n) = n * idealExp v I := by
  induction n with
  | zero => simpa using conductor_idealExp_top_early v
  | succ n ih =>
    rw [pow_succ, conductor_idealExp_mul_early v (pow_ne_zero _ hI) hI, ih]
    rw [Nat.succ_mul]

private theorem conductor_idealExp_prime_early (v w : FinPlace F) :
    (idealExp w v.asIdeal : ℤ) = if w = v then 1 else 0 := by
  have hcoe : FractionalIdeal.count F w
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        (idealExp w v.asIdeal : ℤ) := by
    rw [FractionalIdeal.count_coe F w v.ne_bot]
    rfl
  by_cases hwv : w = v
  · subst w
    simpa using hcoe.symm.trans (FractionalIdeal.count_self F v)
  · have hvw : v ≠ w := Ne.symm hwv
    rw [← hcoe, FractionalIdeal.count_maximal_coprime F w hvw]
    simp [hwv]

private theorem conductor_idealExp_finset_prod_early {α : Type*}
    (T : Finset α) (I : α → Ideal (𝓞 F)) (hI : ∀ a ∈ T, I a ≠ ⊥) :
    (∏ a ∈ T, I a) ≠ ⊥ ∧ ∀ v : FinPlace F,
      idealExp v (∏ a ∈ T, I a) = ∑ a ∈ T, idealExp v (I a) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    intro v
    rw [Finset.prod_empty, Finset.sum_empty]
    simpa only [Ideal.one_eq_top] using conductor_idealExp_top_early v
  | @insert a T hnot ih =>
    have hIa : I a ≠ ⊥ := hI a (by simp)
    have hIT : ∀ b ∈ T, I b ≠ ⊥ := fun b hb => hI b (by simp [hb])
    obtain ⟨hprod, hexp⟩ := ih hIT
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert hnot]
      exact mul_ne_zero hIa hprod
    intro v
    rw [Finset.prod_insert hnot, Finset.sum_insert hnot,
      conductor_idealExp_mul_early v hIa hprod, hexp v]

private theorem conductor_idealExp_ne_zero_iff_dvd_early (v : FinPlace F)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    idealExp v I ≠ 0 ↔ v.asIdeal ∣ I := by
  classical
  have hI' : Associates.mk I ≠ 0 := Associates.mk_ne_zero.mpr hI
  change (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 ↔ v.asIdeal ∣ I
  constructor
  · intro hc
    have hle := Associates.le_of_count_ne_zero hI' v.associates_irreducible hc
    exact (Associates.mk_le_mk_iff_dvd).mp hle
  · intro hdiv
    have hle : Associates.mk v.asIdeal ≤ Associates.mk I :=
      (Associates.mk_le_mk_iff_dvd).mpr hdiv
    have hpow : Associates.mk v.asIdeal ^ 1 ≤ Associates.mk I := by
      simpa only [pow_one] using hle
    have hcount :=
      (Associates.prime_pow_dvd_iff_le hI' v.associates_irreducible).mp hpow
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hcount)

private theorem conductor_idealExp_prime_nat_early (v w : FinPlace F) :
    idealExp v w.asIdeal = if v = w then 1 else 0 := by
  have h := conductor_idealExp_prime_early w v
  by_cases hvw : v = w
  · subst w
    have h' : (idealExp v v.asIdeal : ℤ) = 1 := by simpa using h
    have hNat : idealExp v v.asIdeal = 1 := by exact_mod_cast h'
    simpa using hNat
  · have h' : (idealExp v w.asIdeal : ℤ) = 0 := by simpa [hvw] using h
    have hNat : idealExp v w.asIdeal = 0 := by exact_mod_cast h'
    simpa [hvw] using hNat

private theorem conductor_idealExp_primePower_early (v w : FinPlace F) (n : ℕ) :
    idealExp v (w.asIdeal ^ n) = if v = w then n else 0 := by
  rw [conductor_idealExp_pow_early v w.ne_bot n]
  simp [conductor_idealExp_prime_nat_early]

private theorem conductor_hecke_continuous_modulus (χ : HeckeChar F) :
    ∃ M : Ideal (𝓞 F), M ≠ ⊥ ∧ χ.ConductorDvd M := by
  classical
  obtain ⟨T, e, houtside, hlocal⟩ := conductor_hecke_local_unit_depths χ
  let M : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ e v
  have hMprod := conductor_idealExp_finset_prod_early T
    (fun v => v.asIdeal ^ e v) (fun v _ => pow_ne_zero _ v.ne_bot)
  have hM : M ≠ ⊥ := hMprod.1
  have hexp (v : FinPlace F) :
      idealExp v M = ∑ w ∈ T, if v = w then e w else 0 := by
    calc
      idealExp v M = ∑ w ∈ T, idealExp v (w.asIdeal ^ e w) := hMprod.2 v
      _ = ∑ w ∈ T, if v = w then e w else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact conductor_idealExp_primePower_early v w (e w)
  refine ⟨M, hM, ?_⟩
  intro v u hu huinv hval
  have huG : u ∈ (v.adicCompletionIntegers F).unitGroup :=
    conductor_localUnits_mem_unitGroup v u hu huinv
  let uG : (v.adicCompletionIntegers F).unitGroup := ⟨u, huG⟩
  by_cases hv : v ∈ T
  · have hexpV : idealExp v M = e v := by
      rw [hexp]
      simp [Finset.sum_ite_eq', hv]
    rw [hexpV] at hval
    have hvalG : Valued.v (((uG : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
        WithZero.exp (-(e v : ℤ)) := by simpa [uG] using hval
    simpa [uG] using hlocal v uG hvalG
  · have hexpV : idealExp v M = 0 := by
      rw [hexp]
      simp [Finset.sum_ite_eq', hv]
    rw [hexpV] at hval
    have he : e v = 0 := houtside v hv
    have hvalG : Valued.v (((uG : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
        WithZero.exp (-(e v : ℤ)) := by simpa [uG, he] using hval
    simpa [uG] using hlocal v uG hvalG

/-- Every Hecke character has a nonzero modulus divisible by its conductor. -/
theorem exists_conductorDvd_ne_bot (χ : HeckeChar F) :
    ∃ M : Ideal (𝓞 F), M ≠ ⊥ ∧ χ.ConductorDvd M :=
  conductor_hecke_continuous_modulus χ

/-- Every Hecke character has a primitive conductor (a nonzero conductor modulus of minimal
absolute norm). -/
theorem exists_isPrimitiveConductor (χ : HeckeChar F) :
    ∃ f : Ideal (𝓞 F), ArtinPrimitiveRoots.A2.IsPrimitiveConductor χ f := by
  classical
  obtain ⟨m, hm0, hmc⟩ := exists_conductorDvd_ne_bot χ
  let P : ℕ → Prop := fun n =>
    ∃ f : Ideal (𝓞 F), f ≠ ⊥ ∧ χ.ConductorDvd f ∧ Ideal.absNorm f = n
  have hP : ∃ n, P n := ⟨Ideal.absNorm m, m, hm0, hmc, rfl⟩
  obtain ⟨f, hf0, hfc, hfn⟩ := Nat.find_spec hP
  refine ⟨f, hf0, hfc, ?_⟩
  intro g hg0 hgc
  have hmin := Nat.find_min' hP ⟨g, hg0, hgc, rfl⟩
  omega

end ArtinPrimitiveRoots.Proofs.zf_conv_opus
