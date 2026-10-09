import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.FiniteField
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.ResidueCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.ResidueAdditive
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.Gamma
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.NormTransport
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.LambdaData
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Equality
import ArtinPrimitiveRoots.Hecke.Dict.IdeleCoordinates
import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ResidueUnits
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# A1 interface, §5: Hecke, Kummer, class and Gauss correction characters

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open Filter Topology
open scoped Classical WithZero
open scoped NumberField AdeleRing FiniteAdeleRing RestrictedProduct

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 5. Hecke characters, Kummer / class / Gauss correction characters -/

/-- Hecke characters of `F` (continuous characters of the idele class group; TauCeti's
`HeckeCharacter` is the same type). -/
abbrev HeckeChar (F : Type) [Field F] [NumberField F] :=
  ContinuousMonoidHom (IdeleClassGroup (𝓞 F) F) ℂˣ

/-- Local component at a finite place. -/
def HeckeChar.loc (χ : HeckeChar F) (v : FinPlace F) : (v.adicCompletion F)ˣ →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v)

/-- Local component at an infinite place. -/
def HeckeChar.locInf (χ : HeckeChar F) (w : InfinitePlace F) : w.Completionˣ →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp (IdeleClassGroup.ofCompletion (𝓞 F) F w)

/-- Unramified at `v`: trivial on the local units. -/
def HeckeChar.UnramifiedAt (χ : HeckeChar F) (v : FinPlace F) : Prop :=
  ∀ u : (v.adicCompletion F)ˣ, (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      χ.loc v u = 1

/-- A fixed global uniformizer at `v`. -/
def unif (v : FinPlace F) : F :=
  (HeightOneSpectrum.valuation_exists_uniformizer F v).choose

theorem unif_ne_zero (v : FinPlace F) : unif v ≠ 0 := by
  intro h
  have := (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  rw [← unif, h, map_zero] at this
  exact WithZero.zero_ne_coe this

/-- `χ(𝔭) := χ_v(ϖ_v)` at an unramified `v` (ideal-character convention), else 0. -/
def HeckeChar.primeValue (χ : HeckeChar F) (v : FinPlace F) : ℂ :=
  if χ.UnramifiedAt v then
    ((χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) : ℂˣ) : ℂ) else 0

/-- Ideal value `χ(I) = Π_{P^k ∥ I} χ(P)^k`. -/
def HeckeChar.idealValue (χ : HeckeChar F) (I : Ideal (𝓞 F)) : ℂ :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
    if h : P.IsPrime ∧ P ≠ ⊥ then χ.primeValue ⟨P, h.1, h.2⟩ else 1).prod

/-- Exponent of the prime `v` in an ideal. -/
def idealExp (v : FinPlace F) (I : Ideal (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

/-- A modulus bound for the conductor: `χ` is trivial on the local units `u ≡ 1 mod 𝔭_v^{e_v(𝔪)}`
at every finite `v` (for `e_v(𝔪) = 0`: on all local units); then the conductor divides `𝔪`.
Corrected 2026-10-07: the first version quantified `∀ x ∈ 𝔪` and was vacuous at `x = 0`
(A2 agent, `research/design/A2-ThetaCheck.lean`, `conductorDvd_vacuous`). -/
def HeckeChar.ConductorDvd (χ : HeckeChar F) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ v : FinPlace F, ∀ u : (v.adicCompletion F)ˣ,
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(idealExp v 𝔪 : ℤ)) →
    χ.loc v u = 1

private theorem conductor_local_sixthPowers_mem_nhds (v : FinPlace F) :
    {u : (v.adicCompletion F)ˣ | ∃ b, u = b ^ 6} ∈ 𝓝 (1 : (v.adicCompletion F)ˣ) := by
  let L := v.adicCompletion F
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let x : L := NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F t)
  have htF : algebraMap (𝓞 F) F t ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ht0
  have hx0 : x ≠ 0 := (NumberField.FinitePlace.embedding v).injective.ne htF
  have hxnorm : ‖x‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem (K := F) v t).mpr ht
  letI : NontriviallyNormedField L := NontriviallyNormedField.ofNormNeOne
    ⟨x, hx0, ne_of_lt hxnorm⟩
  have h6 : (6 : L) ≠ 0 := by
    intro h
    have hF : (6 : F) = 0 := (algebraMap F L).injective
      (by simpa only [map_ofNat, map_zero] using h)
    exact (by norm_num : (6 : F) ≠ 0) hF
  have hs : {y : L | ∃ z : L, y = z ^ 6} ∈ 𝓝 (1 : L) := by
    have hd : HasStrictDerivAt (fun y : L => y ^ 6) (6 : L) 1 := by
      simpa using hasStrictDerivAt_pow 6 (1 : L)
    have hm : Filter.map (fun y : L => y ^ 6) (𝓝 1) = 𝓝 1 := by
      simpa using hd.map_nhds_eq h6
    have hp : {y : L | ∃ z : L, y = z ^ 6} ∈ Filter.map (fun y : L => y ^ 6) (𝓝 1) :=
      Filter.mem_map.mpr (Filter.Eventually.of_forall fun y => ⟨y, rfl⟩)
    rw [hm] at hp
    exact hp
  filter_upwards [(Units.continuous_val.tendsto (1 : Lˣ)).eventually hs] with u hu
  obtain ⟨y, hy⟩ := hu
  have hy0 : y ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [hy, h, zero_pow (by decide : 6 ≠ 0)]
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  change (u : L) = y ^ 6
  exact hy

private theorem conductor_local_sixthPower_depth (v : FinPlace F) :
    ∃ e : ℕ, 0 < e ∧ ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(e : ℤ)) →
      ∃ b : (v.adicCompletion F)ˣ, u = b ^ 6 := by
  let L := v.adicCompletion F
  have hs := conductor_local_sixthPowers_mem_nhds v
  rw [(Units.isEmbedding_val₀ (G₀ := L)).isInducing.nhds_eq_comap 1] at hs
  obtain ⟨V, hV, hVs⟩ := Filter.mem_comap.mp hs
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
  apply hVs
  apply hγ
  change (Valued.v : Valuation L ℤᵐ⁰).restrict ((u : L) - 1) < (γ : _)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hu hbound

private theorem conductor_local_sixthPowers_depth_one (v : FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (hnear : Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-1 : ℤ)) :
    ∃ b : (v.adicCompletion F)ˣ, u = b ^ 6 := by
  let L := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let m : Ideal O := IsLocalRing.maximalIdeal O
  have hmax (z : O) : z ∈ m ↔ Valued.v (z : L) < 1 := by
    change z ∈ IsLocalRing.maximalIdeal
      ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
    exact Valuation.mem_maximalIdeal_iff (v := Valued.v)
  have hlt : Valued.v ((u : L) - 1) < 1 := by
    apply lt_of_le_of_lt hnear
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  let uO : O := ⟨(u : L), hu⟩
  have hcong : uO - 1 ∈ m := by
    apply (hmax _).2
    simpa [uO] using hlt
  have h6val : v.valuation F (algebraMap (𝓞 F) F (6 : 𝓞 F)) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).2 h6
  have h6map : (6 : O) = algebraMap (𝓞 F) O (6 : 𝓞 F) := by
    exact (map_natCast (algebraMap (𝓞 F) O) 6).symm
  have hmap6 :
      (algebraMap O L (algebraMap (𝓞 F) O (6 : 𝓞 F)) : L) =
        algebraMap F L (algebraMap (𝓞 F) F (6 : 𝓞 F)) :=
    (v.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (6 : 𝓞 F)).symm
  have hval6O : Valued.v ((6 : O) : L) = 1 := by
    rw [h6map]
    change Valued.v (algebraMap O L (algebraMap (𝓞 F) O (6 : 𝓞 F))) = 1
    rw [hmap6]
    exact (v.valuedAdicCompletion_eq_valuation'
      (algebraMap (𝓞 F) F (6 : 𝓞 F))).trans h6val
  have h6not : (6 : O) ∉ m := by
    intro hmem
    have hlt6 := (hmax (6 : O)).1 hmem
    rw [hval6O] at hlt6
    exact (lt_irrefl 1) hlt6
  have h6unit : IsUnit (6 : O) := IsLocalRing.notMem_maximalIdeal.mp h6not
  letI : HenselianRing O m := inferInstance
  obtain ⟨c, hc, hcnear⟩ := TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem
    (I := m) (J := m) le_rfl (n := 6) h6unit hcong
  have huO_ne : uO ≠ 0 := by
    intro h
    apply Units.ne_zero u
    have h' := congrArg (fun z : O => (z : L)) h
    simpa [uO] using h'
  have hc0 : c ≠ 0 := by
    intro h
    apply huO_ne
    rw [← hc]
    simp [h]
  have hcL0 : (c : L) ≠ 0 := by
    intro h
    apply hc0
    exact Subtype.ext h
  let b : Lˣ := Units.mk0 (c : L) hcL0
  have hcreal : (c : L) ^ 6 = (u : L) := by
    have hc' := congrArg (fun z : O => (z : L)) hc
    simpa using hc'
  refine ⟨b, ?_⟩
  apply Units.ext
  exact hcreal.symm

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

private theorem conductor_residue_zero_iff_mem (v : FinPlace F) (u : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F u) = 0 ↔ u ∈ v.asIdeal := by
  have hres : residue v (algebraMap (𝓞 F) F u) ≠ 0 ↔ u ∉ v.asIdeal :=
    (ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one v
      (algebraMap (𝓞 F) F u)).trans (v.valuation_eq_one_iff_notMem (K := F))
  constructor
  · intro hz
    by_contra hu
    exact (hres.mpr hu) hz
  · intro hu
    by_contra hz
    exact (hres.mp hz) hu

private theorem conductor_kummerLocal_sixth_pow (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    (KummerProofs.kummerLocal D H v a b) ^ 6 = 1 := by
  change Units.map D.σ0.toMonoidHom (H.hilb v a b : Fˣ) ^ 6 = 1
  rw [← map_pow]
  have hb := (mem_rootsOfUnity 6 _).mp (H.hilb v a b).property
  rw [hb, map_one]

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

private noncomputable def conductor_sixthPowerExponent (v : FinPlace F) : ℕ :=
  (conductor_local_sixthPower_depth v).choose

private theorem conductor_sixthPowerExponent_spec (v : FinPlace F) :
    0 < conductor_sixthPowerExponent v ∧ ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) - 1) ≤
        WithZero.exp (-(conductor_sixthPowerExponent v : ℤ)) →
      ∃ b : (v.adicCompletion F)ˣ, u = b ^ 6 :=
  (conductor_local_sixthPower_depth v).choose_spec

private noncomputable def conductor_sfixedModulus (S : SData F CE condη) :
    Ideal (𝓞 F) :=
  ∏ v ∈ S.Sf, v.asIdeal ^ conductor_sixthPowerExponent v

private theorem conductor_sfixedModulus_data (S : SData F CE condη) :
    conductor_sfixedModulus S ≠ ⊥ ∧ ∀ v : FinPlace F,
      idealExp v (conductor_sfixedModulus S) =
        if v ∈ S.Sf then conductor_sixthPowerExponent v else 0 := by
  classical
  let T := S.Sf
  let I : FinPlace F → Ideal (𝓞 F) := fun v => v.asIdeal ^ conductor_sixthPowerExponent v
  have hI (v : FinPlace F) : I v ≠ ⊥ := pow_ne_zero _ v.ne_bot
  have hprod := conductor_idealExp_finset_prod_early T I (fun v _ => hI v)
  have hsum (v : FinPlace F) :
      idealExp v (∏ w ∈ T, I w) = ∑ w ∈ T, if v = w then conductor_sixthPowerExponent w else 0 := by
    calc
      idealExp v (∏ w ∈ T, I w) = ∑ w ∈ T, idealExp v (I w) := hprod.2 v
      _ = ∑ w ∈ T, if v = w then conductor_sixthPowerExponent w else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact conductor_idealExp_primePower_early v w _
  have hformula (v : FinPlace F) :
      idealExp v (conductor_sfixedModulus S) =
        if v ∈ S.Sf then conductor_sixthPowerExponent v else 0 := by
    by_cases hv : v ∈ T
    · rw [show conductor_sfixedModulus S = ∏ w ∈ T, I w by rfl, hsum]
      have hvS : v ∈ S.Sf := by simpa [T] using hv
      rw [Finset.sum_eq_single v]
      · simp [hvS]
      · intro w hw hne
        by_cases hEq : v = w
        · exact (hne hEq.symm).elim
        · simp [hEq]
      · exact (fun hnot => (hnot hv).elim)
    · rw [show conductor_sfixedModulus S = ∏ w ∈ T, I w by rfl, hsum]
      have hvS : v ∉ S.Sf := by simpa [T] using hv
      rw [Finset.sum_eq_zero]
      · simp [hvS]
      · intro w hw
        have hne : v ≠ w := by
          intro hEq
          subst w
          exact hv hw
        simp [hne]
  exact ⟨by simpa [conductor_sfixedModulus, T, I] using hprod.1,
    fun v => hformula v⟩

private theorem conductor_inverse_ConductorDvd (χ : HeckeChar F)
    (M : Ideal (𝓞 F)) (hχ : χ.ConductorDvd M) : χ⁻¹.ConductorDvd M := by
  intro v u hu huinv hval
  have h := hχ v u hu huinv hval
  change (χ.loc v u)⁻¹ = 1
  rw [h]
  simp

private theorem conductor_mul_ConductorDvd (χ ψ : HeckeChar F)
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hχ : χ.ConductorDvd I) (hψ : ψ.ConductorDvd J) :
    (χ * ψ).ConductorDvd (I * J) := by
  intro v u hu huinv hval
  have hexp := conductor_idealExp_mul_early v hI hJ
  have hleI : WithZero.exp (-(idealExp v (I * J) : ℤ)) ≤
      WithZero.exp (-(idealExp v I : ℤ)) := by
    apply WithZero.exp_le_exp.mpr
    rw [hexp]
    omega
  have hleJ : WithZero.exp (-(idealExp v (I * J) : ℤ)) ≤
      WithZero.exp (-(idealExp v J : ℤ)) := by
    apply WithZero.exp_le_exp.mpr
    rw [hexp]
    omega
  have hχloc := hχ v u hu huinv (hval.trans hleI)
  have hψloc := hψ v u hu huinv (hval.trans hleJ)
  change χ.loc v u * ψ.loc v u = 1
  rw [hχloc, hψloc]
  simp

/-- Kummer character `κ_u` (ar:kummer-hecke, 02:285–357): finite order, unramified at exterior
`v` with `v(u) = 0`, and `κ_u(v) = χ_v(u)` there. Package P-ARITH-KUMMER. -/
theorem kummer_exists (D : FieldData F) (S : SData F CE condη) (u : Fˣ) :
    ∃ κ : HeckeChar F, IsOfFinOrder κ ∧ ∀ v : FinPlace F, v ∉ S.Sf → residue v (u : F) ≠ 0 →
      κ.UnramifiedAt v ∧ κ.primeValue v = chi D v (u : F) := by
  obtain ⟨H⟩ := HilbertData.nonempty D
  obtain ⟨κ, hκ, _, hloc⟩ := KummerProofs.kummer_character_exists D H u
  refine ⟨κ, isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hκ⟩, ?_⟩
  intro P hP hu
  have h6 : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hP (S.over6 P h)
  exact KummerProofs.kummer_prime_values D H u κ hloc P h6 hu

/-- eq:kummer-conductor (02:290–298), modulus form: `κ_u` (and `η κ_u^{-1}`) has conductor
dividing a modulus of norm `≤ C·N rad(uR)`. -/
theorem kummer_conductor (D : FieldData F) (S : SData F CE condη) (η : HeckeChar F) :
    ∃ C : ℝ, ∀ u : 𝓞 F, u ≠ 0 → ∀ κ : HeckeChar F,
      (∀ v : FinPlace F, v ∉ S.Sf → residue v (u : F) ≠ 0 →
        κ.UnramifiedAt v ∧ κ.primeValue v = chi D v (u : F)) → IsOfFinOrder κ →
      (∃ 𝔪 : Ideal (𝓞 F), κ.ConductorDvd 𝔪 ∧
        (Ideal.absNorm 𝔪 : ℝ) ≤ C * Ideal.absNorm (Ideal.span {u}).radical) ∧
      (∃ 𝔪 : Ideal (𝓞 F), (η * κ⁻¹).ConductorDvd 𝔪 ∧
        (Ideal.absNorm 𝔪 : ℝ) ≤ C * Ideal.absNorm (Ideal.span {u}).radical) := by
  classical
  obtain ⟨Mη, hMη, hηM⟩ := conductor_hecke_continuous_modulus η
  let MS := conductor_sfixedModulus S
  have hMSdata := conductor_sfixedModulus_data S
  have hMS : MS ≠ ⊥ := hMSdata.1
  let C : ℝ := (Ideal.absNorm MS : ℝ) * max 1 (Ideal.absNorm Mη : ℝ)
  refine ⟨C, ?_⟩
  intro u hu κ hGood hκfinite
  let I : Ideal (𝓞 F) := Ideal.span {u}
  have hI : I ≠ ⊥ := by
    intro h
    exact hu (Ideal.span_singleton_eq_bot.mp (by simpa [I] using h))
  have hRad : I.radical ≠ ⊥ := by
    intro h
    apply hI
    have hle : I ≤ I.radical := Ideal.le_radical
    rw [h] at hle
    exact le_antisymm hle bot_le
  obtain ⟨H⟩ := HilbertData.nonempty D
  let a : Fˣ := Units.mk0 (algebraMap (𝓞 F) F u)
    (RingOfIntegers.coe_ne_zero_iff.mpr hu)
  obtain ⟨κ₀, hκ₀pow, _, hκ₀loc⟩ := KummerProofs.kummer_character_exists D H a
  have hκ₀fin : IsOfFinOrder κ₀ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hκ₀pow⟩
  let κK : KummerProofs.KummerChar F := κ
  let T : Finset (FinPlace F) := S.Sf ∪ (KummerProofs.residue_zero_finite a).toFinset
  have hout (P : FinPlace F) (hP : P ∉ T) :
      P ∉ S.Sf ∧ residue P (a : F) ≠ 0 := by
    simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      not_or] at hP
    exact hP
  have hκEq : κK = κ₀ := by
    apply KummerProofs.finite_order_good_prime_unique κK κ₀ hκfinite hκ₀fin T
    intro P hP
    obtain ⟨hPS, hres⟩ := hout P hP
    have h6 : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hPS (S.over6 P h)
    have h₁ := hGood P hPS hres
    have h₂ := KummerProofs.kummer_prime_values D H a κ₀ hκ₀loc P h6 hres
    exact ⟨h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩
  have hLoc (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
      κ.loc v x = KummerProofs.kummerLocal D H v (toLoc v a) x := by
    change KummerProofs.localComponent κK v x = _
    rw [hκEq]
    exact congrArg (fun f => f x) (hκ₀loc v)
  let Mκ : Ideal (𝓞 F) := MS * I.radical
  have hMκ : Mκ ≠ ⊥ := mul_ne_zero hMS hRad
  have hExpK (v : FinPlace F) :
      idealExp v Mκ = idealExp v MS + idealExp v I.radical := by
    exact conductor_idealExp_mul_early v hMS hRad
  have hκM : κ.ConductorDvd Mκ := by
    intro v x hx hxinv hval
    by_cases hvS : v ∈ S.Sf
    · have hSexp : idealExp v MS = conductor_sixthPowerExponent v := by
        simpa [MS, hvS] using hMSdata.2 v
      have hExpLower : conductor_sixthPowerExponent v ≤ idealExp v Mκ := by
        rw [hExpK, hSexp]
        omega
      have hdepth : WithZero.exp (-(idealExp v Mκ : ℤ)) ≤
          WithZero.exp (-(conductor_sixthPowerExponent v : ℤ)) := by
        apply WithZero.exp_le_exp.mpr
        omega
      have hbound := hval.trans hdepth
      obtain ⟨b, hxb⟩ := (conductor_sixthPowerExponent_spec v).2 x hbound
      calc
        κ.loc v x = KummerProofs.kummerLocal D H v (toLoc v a) x := hLoc v x
        _ = (KummerProofs.kummerLocal D H v (toLoc v a) b) ^ 6 := by
          rw [hxb, map_pow]
        _ = 1 := conductor_kummerLocal_sixth_pow D H v (toLoc v a) b
    · by_cases hres0 : residue v (algebraMap (𝓞 F) F u) = 0
      · have huP : u ∈ v.asIdeal :=
          (conductor_residue_zero_iff_mem v u).mp hres0
        have hIle : I ≤ v.asIdeal := by
          change Ideal.span {u} ≤ v.asIdeal
          rw [Ideal.span_singleton_le_iff_mem]
          exact huP
        have hRadle : I.radical ≤ v.asIdeal := v.isPrime.radical_le_iff.mpr hIle
        have hRadDiv : v.asIdeal ∣ I.radical := Ideal.dvd_iff_le.mpr hRadle
        have hRadCount : idealExp v I.radical ≠ 0 :=
          (conductor_idealExp_ne_zero_iff_dvd_early v hRad).2 hRadDiv
        have hRadPos : 0 < idealExp v I.radical := Nat.pos_iff_ne_zero.mpr hRadCount
        have hSexp : idealExp v MS = 0 := by
          simpa [MS, hvS] using hMSdata.2 v
        have hExpPos : 0 < idealExp v Mκ := by
          rw [hExpK, hSexp]
          omega
        have hdepth : WithZero.exp (-(idealExp v Mκ : ℤ)) ≤
            WithZero.exp (-1 : ℤ) := by
          apply WithZero.exp_le_exp.mpr
          have hInt : 1 ≤ (idealExp v Mκ : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt hExpPos)
          omega
        have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hvS (S.over6 v h)
        obtain ⟨b, hxb⟩ := conductor_local_sixthPowers_depth_one v h6 x hx
          (hval.trans hdepth)
        calc
          κ.loc v x = KummerProofs.kummerLocal D H v (toLoc v a) x := hLoc v x
          _ = (KummerProofs.kummerLocal D H v (toLoc v a) b) ^ 6 := by
            rw [hxb, map_pow]
          _ = 1 := conductor_kummerLocal_sixth_pow D H v (toLoc v a) b
      · have hGoodV := hGood v hvS hres0
        exact hGoodV.1 x hx hxinv
  have hκinvM : κ⁻¹.ConductorDvd Mκ := conductor_inverse_ConductorDvd κ Mκ hκM
  have hTwistM : (η * κ⁻¹).ConductorDvd (Mη * Mκ) :=
    conductor_mul_ConductorDvd η κ⁻¹ Mη Mκ hMη hMκ hηM hκinvM
  have hNormκ : (Ideal.absNorm Mκ : ℝ) =
      (Ideal.absNorm MS : ℝ) * (Ideal.absNorm I.radical : ℝ) := by
    have h := map_mul Ideal.absNorm MS I.radical
    exact_mod_cast h
  have hNormTwist : (Ideal.absNorm (Mη * Mκ) : ℝ) =
      (Ideal.absNorm Mη : ℝ) * (Ideal.absNorm MS : ℝ) *
        (Ideal.absNorm I.radical : ℝ) := by
    have hNat := map_mul Ideal.absNorm Mη Mκ
    have hReal := congrArg (fun n : ℕ => (n : ℝ)) hNat
    rw [Nat.cast_mul, hNormκ] at hReal
    calc
      (Ideal.absNorm (Mη * Mκ) : ℝ) =
          (Ideal.absNorm Mη : ℝ) * (Ideal.absNorm Mκ : ℝ) := by exact_mod_cast hNat
      _ = (Ideal.absNorm Mη : ℝ) * (Ideal.absNorm MS : ℝ) *
          (Ideal.absNorm I.radical : ℝ) := by nlinarith [hReal]
  have hBoundκ : (Ideal.absNorm Mκ : ℝ) ≤ C * Ideal.absNorm I.radical := by
    rw [hNormκ]
    dsimp [C]
    calc
      (Ideal.absNorm MS : ℝ) * (Ideal.absNorm I.radical : ℝ) =
          ((Ideal.absNorm MS : ℝ) * 1) * (Ideal.absNorm I.radical : ℝ) := by ring
      _ ≤ ((Ideal.absNorm MS : ℝ) * max 1 (Ideal.absNorm Mη : ℝ)) *
          (Ideal.absNorm I.radical : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
              (by positivity)
  have hBoundTwist : (Ideal.absNorm (Mη * Mκ) : ℝ) ≤ C * Ideal.absNorm I.radical := by
    rw [hNormTwist]
    dsimp [C]
    calc
      (Ideal.absNorm Mη : ℝ) * (Ideal.absNorm MS : ℝ) *
          (Ideal.absNorm I.radical : ℝ) =
            ((Ideal.absNorm MS : ℝ) * (Ideal.absNorm Mη : ℝ)) *
              (Ideal.absNorm I.radical : ℝ) := by ring
      _ ≤ ((Ideal.absNorm MS : ℝ) * max 1 (Ideal.absNorm Mη : ℝ)) *
          (Ideal.absNorm I.radical : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
              (by positivity)
  exact ⟨⟨Mκ, hκM, by simpa [I] using hBoundκ⟩,
    ⟨Mη * Mκ, hTwistM, by simpa [I] using hBoundTwist⟩⟩

/-- ar:kummer-equality (02:299–300): `κ_u = κ_v ↔ u/v ∈ F^{×6}`. Package P-ARITH-KUMMER. -/
theorem kummer_eq_iff (D : FieldData F) (S : SData F CE condη) (u v : Fˣ) (κu κv : HeckeChar F)
    (hu : ∀ P : FinPlace F, P ∉ S.Sf → residue P (u : F) ≠ 0 →
      κu.UnramifiedAt P ∧ κu.primeValue P = chi D P (u : F))
    (hv : ∀ P : FinPlace F, P ∉ S.Sf → residue P (v : F) ≠ 0 →
      κv.UnramifiedAt P ∧ κv.primeValue P = chi D P (v : F))
    (hfu : IsOfFinOrder κu) (hfv : IsOfFinOrder κv) :
    κu = κv ↔ ∃ t : Fˣ, u / v = t ^ 6 := by
  obtain ⟨H⟩ := HilbertData.nonempty D
  obtain ⟨κu₀, hκu₀, huInf, huloc⟩ := KummerProofs.kummer_character_exists D H u
  obtain ⟨κv₀, hκv₀, hvInf, hvloc⟩ := KummerProofs.kummer_character_exists D H v
  have hfu₀ : IsOfFinOrder κu₀ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hκu₀⟩
  have hfv₀ : IsOfFinOrder κv₀ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hκv₀⟩
  let T := S.Sf ∪ (KummerProofs.residue_zero_finite u).toFinset ∪
    (KummerProofs.residue_zero_finite v).toFinset
  have hout (P : FinPlace F) (hP : P ∉ T) :
      P ∉ S.Sf ∧ residue P (u : F) ≠ 0 ∧ residue P (v : F) ≠ 0 := by
    simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hP
    exact ⟨hP.1.1, hP.1.2, hP.2⟩
  have heu : κu = κu₀ := by
    apply KummerProofs.finite_order_good_prime_unique κu κu₀ hfu hfu₀ T
    intro P hP
    obtain ⟨hPS, huP, _⟩ := hout P hP
    have h6 : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hPS (S.over6 P h)
    have h₁ := hu P hPS huP
    have h₂ := KummerProofs.kummer_prime_values D H u κu₀ huloc P h6 huP
    exact ⟨h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩
  have hev : κv = κv₀ := by
    apply KummerProofs.finite_order_good_prime_unique κv κv₀ hfv hfv₀ T
    intro P hP
    obtain ⟨hPS, _, hvP⟩ := hout P hP
    have h6 : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hPS (S.over6 P h)
    have h₁ := hv P hPS hvP
    have h₂ := KummerProofs.kummer_prime_values D H v κv₀ hvloc P h6 hvP
    exact ⟨h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩
  rw [heu, hev]
  exact KummerProofs.kummer_realization_eq_iff D H u v κu₀ κv₀ huInf hvInf huloc hvloc

private theorem conductor_group_decomp_exists {G : Type} [CommGroup G]
    (E B : Subgroup G) (h : IsCompl E B) (x : G) :
    ∃ e : E, ∃ b : B, (e : G) * b = x := by
  have hx : x ∈ E ⊔ B := by
    rw [h.sup_eq_top]
    exact Subgroup.mem_top x
  rcases (Subgroup.mem_sup (s := E) (t := B) (x := x)).mp hx with
    ⟨e, he, b, hb, hab⟩
  exact ⟨⟨e, he⟩, ⟨b, hb⟩, hab⟩

private theorem conductor_group_decomp_unique {G : Type} [CommGroup G]
    (E B : Subgroup G) (h : IsCompl E B) {x : G} {e₁ e₂ : E} {b₁ b₂ : B}
    (h₁ : (e₁ : G) * b₁ = x) (h₂ : (e₂ : G) * b₂ = x) : b₁ = b₂ := by
  have hquot : (e₂ : G)⁻¹ * e₁ = (b₂ : G) * (b₁ : G)⁻¹ := by
    calc
      (e₂ : G)⁻¹ * e₁ = (((e₂ : G)⁻¹ * e₁) * b₁) * (b₁ : G)⁻¹ :=
        (mul_inv_cancel_right _ _).symm
      _ = ((e₂ : G)⁻¹ * ((e₁ : G) * b₁)) * (b₁ : G)⁻¹ := by
        congr 1
        exact mul_assoc _ _ _
      _ = ((e₂ : G)⁻¹ * ((e₂ : G) * b₂)) * (b₁ : G)⁻¹ := by rw [h₁, h₂]
      _ = (b₂ : G) * (b₁ : G)⁻¹ := by rw [inv_mul_cancel_left]
  have hE : (e₂ : G)⁻¹ * e₁ ∈ E := mul_mem (inv_mem e₂.property) e₁.property
  have hB : (e₂ : G)⁻¹ * e₁ ∈ B := by
    rw [hquot]
    exact mul_mem b₂.property (inv_mem b₁.property)
  have hbot : (e₂ : G)⁻¹ * e₁ ∈ (⊥ : Subgroup G) := by
    rw [← h.inf_eq_bot]
    exact ⟨hE, hB⟩
  have hone : (e₂ : G)⁻¹ * e₁ = 1 := by simpa using hbot
  have hb : (b₂ : G) * (b₁ : G)⁻¹ = 1 := hquot.symm.trans hone
  apply Subtype.ext
  exact (mul_inv_eq_one.mp hb).symm

private noncomputable def conductor_group_chooseE {G : Type} [CommGroup G]
    (E B : Subgroup G) (h : IsCompl E B) (x : G) : E :=
  Classical.choose (conductor_group_decomp_exists E B h x)

private noncomputable def conductor_group_chooseB {G : Type} [CommGroup G]
    (E B : Subgroup G) (h : IsCompl E B) (x : G) : B :=
  Classical.choose (Classical.choose_spec (conductor_group_decomp_exists E B h x))

private theorem conductor_group_choose_spec {G : Type} [CommGroup G]
    (E B : Subgroup G) (h : IsCompl E B) (x : G) :
    (conductor_group_chooseE E B h x : G) * conductor_group_chooseB E B h x = x :=
  Classical.choose_spec (Classical.choose_spec (conductor_group_decomp_exists E B h x))

private noncomputable def conductor_group_projection {G : Type} [CommGroup G]
    (E B : Subgroup G) (h : IsCompl E B) : G →* B where
  toFun := conductor_group_chooseB E B h
  map_one' := by
    exact conductor_group_decomp_unique E B h
      (e₁ := conductor_group_chooseE E B h 1)
      (b₁ := conductor_group_chooseB E B h 1) (e₂ := 1) (b₂ := 1)
      (conductor_group_choose_spec E B h 1) (by simp)
  map_mul' x y := by
    apply conductor_group_decomp_unique E B h
      (e₁ := conductor_group_chooseE E B h (x * y))
      (b₁ := conductor_group_chooseB E B h (x * y))
      (e₂ := conductor_group_chooseE E B h x * conductor_group_chooseE E B h y)
      (b₂ := conductor_group_chooseB E B h x * conductor_group_chooseB E B h y)
      (conductor_group_choose_spec E B h (x * y))
    change ((conductor_group_chooseE E B h x : G) *
          conductor_group_chooseE E B h y) *
        ((conductor_group_chooseB E B h x : G) *
          conductor_group_chooseB E B h y) = _
    calc
      _ = (conductor_group_chooseE E B h x : G) *
            (conductor_group_chooseE E B h y *
            (conductor_group_chooseB E B h x * conductor_group_chooseB E B h y)) :=
          mul_assoc _ _ _
      _ = (conductor_group_chooseE E B h x : G) *
          (conductor_group_chooseB E B h x *
            (conductor_group_chooseE E B h y * conductor_group_chooseB E B h y)) := by
          congr 1
          calc
            _ = ((conductor_group_chooseE E B h y : G) *
                (conductor_group_chooseB E B h x : G)) *
                  (conductor_group_chooseB E B h y : G) :=
                  (mul_assoc _ _ _).symm
            _ = ((conductor_group_chooseB E B h x : G) *
                (conductor_group_chooseE E B h y : G)) *
                  (conductor_group_chooseB E B h y : G) := by
                  congr 1
                  exact mul_comm _ _
            _ = (conductor_group_chooseB E B h x : G) *
                ((conductor_group_chooseE E B h y : G) *
                  (conductor_group_chooseB E B h y : G)) :=
                  mul_assoc _ _ _
      _ = ((conductor_group_chooseE E B h x : G) *
            (conductor_group_chooseB E B h x : G)) *
          ((conductor_group_chooseE E B h y : G) *
            (conductor_group_chooseB E B h y : G)) :=
            (mul_assoc _ _ _).symm
      _ = x * y := by rw [conductor_group_choose_spec, conductor_group_choose_spec]

private theorem conductor_group_projection_fixed {G : Type} [CommGroup G]
    (E B : Subgroup G) (h : IsCompl E B) (x : G) (hx : x ∈ B) :
    (conductor_group_projection E B h x : G) = x := by
  have hb := conductor_group_decomp_unique E B h
    (e₁ := conductor_group_chooseE E B h x)
    (b₁ := conductor_group_chooseB E B h x) (e₂ := 1) (b₂ := ⟨x, hx⟩)
    (conductor_group_choose_spec E B h x) (by simp)
  exact congrArg (fun b : B => (b : G)) hb

private theorem conductor_group_projection_kills {G : Type} [CommGroup G]
    (E B : Subgroup G) (h : IsCompl E B) (x : G) (hx : x ∈ E) :
    conductor_group_projection E B h x = 1 := by
  exact conductor_group_decomp_unique E B h
    (e₁ := conductor_group_chooseE E B h x)
    (b₁ := conductor_group_chooseB E B h x) (e₂ := ⟨x, hx⟩) (b₂ := 1)
    (conductor_group_choose_spec E B h x) (by simp)

private theorem conductor_sixth_root_unit (z : ℂˣ) : ∃ y : ℂˣ, y ^ 6 = z := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (n := 6) (by decide)
  have hy0 : y ≠ 0 := by
    intro h
    have hz : (z : ℂ) = 0 := by simpa [h] using hy.symm
    exact z.ne_zero hz
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  exact hy

private theorem conductor_compU_continuous (S : SData F CE condη) (v : S.Sf) :
    Continuous (S.compU v) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun x : S.FSˣ => ((x : S.FS).1 v : v.1.adicCompletion F))
    exact (continuous_apply v).comp (continuous_fst.comp Units.continuous_val)
  · change Continuous (fun x : S.FSˣ => (((x⁻¹ : S.FSˣ) : S.FS).1 v : v.1.adicCompletion F))
    exact (continuous_apply v).comp (continuous_fst.comp Units.continuous_coe_inv)

private theorem conductor_FS_sixthPowers_mem_nhds (S : SData F CE condη) :
    {x : S.FSˣ | ∃ y, x = y ^ 6} ∈ 𝓝 (1 : S.FSˣ) := by
  classical
  have hlocal (v : S.Sf) :
      {x : S.FSˣ | ∃ y : (v.1.adicCompletion F)ˣ, S.compU v x = y ^ 6} ∈
        𝓝 (1 : S.FSˣ) := by
    have hc : ContinuousAt (S.compU v) (1 : S.FSˣ) :=
      (conductor_compU_continuous S v).continuousAt
    change (S.compU v) ⁻¹' {u : (v.1.adicCompletion F)ˣ | ∃ b, u = b ^ 6} ∈
      𝓝 (1 : S.FSˣ)
    exact hc.preimage_mem_nhds (by simpa using conductor_local_sixthPowers_mem_nhds v.1)
  have hall : ∀ᶠ x : S.FSˣ in 𝓝 1,
      ∀ v ∈ (Finset.univ : Finset S.Sf), ∃ y : (v.1.adicCompletion F)ˣ,
        S.compU v x = y ^ 6 := by
    rw [Filter.eventually_all_finset]
    intro v hv
    exact hlocal v
  filter_upwards [hall] with x hx
  let rf (v : S.Sf) : (v.1.adicCompletion F)ˣ :=
    Classical.choose (hx v (Finset.mem_univ v))
  have hrf (v : S.Sf) : S.compU v x = rf v ^ 6 :=
    Classical.choose_spec (hx v (Finset.mem_univ v))
  let rc (w : InfinitePlace F) : ℂˣ :=
    Classical.choose (conductor_sixth_root_unit (S.compC w x))
  have hrc (w : InfinitePlace F) : rc w ^ 6 = S.compC w x :=
    Classical.choose_spec (conductor_sixth_root_unit (S.compC w x))
  let y : S.FSˣ := {
    val := (fun v => (rf v : v.1.adicCompletion F), fun w => (rc w : ℂ))
    inv := (fun v => ((rf v)⁻¹ : v.1.adicCompletion F), fun w => ((rc w)⁻¹ : ℂ))
    val_inv := by
      apply Prod.ext
      · funext v
        simp
      · funext w
        simp
    inv_val := by
      apply Prod.ext
      · funext v
        simp
      · funext w
        simp
  }
  refine ⟨y, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext v
    calc
      ((x : S.FS).1 v) = (S.compU v x : v.1.adicCompletion F) := rfl
      _ = (rf v ^ 6 : (v.1.adicCompletion F)ˣ) := congrArg Units.val (hrf v)
      _ = ((y ^ 6 : S.FSˣ) : S.FS).1 v := rfl
  · funext w
    calc
      ((x : S.FS).2 w) = (S.compC w x : ℂ) := rfl
      _ = (rc w ^ 6 : ℂˣ) := congrArg Units.val (hrc w).symm
      _ = ((y ^ 6 : S.FSˣ) : S.FS).2 w := rfl

private theorem conductor_continuous_of_sixthPowers {G : Type} [TopologicalSpace G]
    [Group G] [IsTopologicalGroup G] (f : G →* ℂˣ)
    (hpow : {x : G | ∃ y, x = y ^ 6} ∈ 𝓝 (1 : G))
    (htriv : ∀ y : G, f (y ^ 6) = 1) : Continuous f := by
  have heq : (fun x : G => f x) =ᶠ[𝓝 (1 : G)] fun _ => (1 : ℂˣ) := by
    filter_upwards [hpow] with x hx
    obtain ⟨y, rfl⟩ := hx
    exact htriv y
  apply continuous_of_tendsto_nhds_one f
  exact (Filter.tendsto_congr' heq).mpr tendsto_const_nhds

private noncomputable def conductor_localOrder (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ) : ℤ :=
  -WithZero.log (Valued.v (u : v.adicCompletion F))

private theorem conductor_localOrder_mul (v : FinPlace F)
    (x y : (v.adicCompletion F)ˣ) :
    conductor_localOrder v (x * y) = conductor_localOrder v x + conductor_localOrder v y := by
  unfold conductor_localOrder
  change -WithZero.log (Valued.v ((x : v.adicCompletion F) * (y : v.adicCompletion F))) = _
  rw [map_mul, WithZero.log_mul
    ((Valued.v).ne_zero_iff.mpr (Units.ne_zero x))
    ((Valued.v).ne_zero_iff.mpr (Units.ne_zero y))]
  ring

private noncomputable def conductor_localUnramifiedCharacter (v : FinPlace F) (c : ℂˣ) :
    (v.adicCompletion F)ˣ →* ℂˣ :=
  MonoidHom.mk' (fun u => c ^ conductor_localOrder v u) (by
    intro x y
    rw [conductor_localOrder_mul, zpow_add])

private theorem conductor_localUnramifiedCharacter_one_of_unit
    (v : FinPlace F) (c : ℂˣ) (u : (v.adicCompletion F)ˣ)
    (hu : u ∈ (v.adicCompletionIntegers F).units) :
    conductor_localUnramifiedCharacter v c u = 1 := by
  have hv := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
  simp [conductor_localUnramifiedCharacter, conductor_localOrder, hv]

private theorem conductor_localUnramifiedCharacter_unramified
    (v : FinPlace F) (c : ℂˣ) (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (huinv : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F) :
    conductor_localUnramifiedCharacter v c u = 1 :=
  conductor_localUnramifiedCharacter_one_of_unit v c u ⟨hu, huinv⟩

private theorem conductor_localUnramifiedCharacter_continuous
    (v : FinPlace F) (c : ℂˣ) :
    Continuous (conductor_localUnramifiedCharacter v c) := by
  let L := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  have hO : IsOpen (O : Set L) := Valued.isOpen_valuationSubring L
  have hOU : IsOpen {u : Lˣ | u ∈ O.units} := by
    change IsOpen (((fun u : Lˣ => (u : L)) ⁻¹' (O : Set L)) ∩
      ((fun u : Lˣ => ((u⁻¹ : Lˣ) : L)) ⁻¹' (O : Set L)))
    exact (hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv)
  have hU : {u : Lˣ | u ∈ O.units} ∈ 𝓝 (1 : Lˣ) :=
    hOU.mem_nhds (by simp)
  have heq : (fun u : Lˣ => conductor_localUnramifiedCharacter v c u) =ᶠ[𝓝 1]
      fun _ => (1 : ℂˣ) := by
    filter_upwards [hU] with u hu
    exact conductor_localUnramifiedCharacter_one_of_unit v c u hu
  apply continuous_of_tendsto_nhds_one (conductor_localUnramifiedCharacter v c)
  exact (Filter.tendsto_congr' heq).mpr tendsto_const_nhds

private theorem conductor_prime_isExterior (S : SData F CE condη) (v : FinPlace F)
    (hv : v ∉ S.Sf) : S.IsExterior v.asIdeal := by
  refine ⟨v.ne_bot, ?_⟩
  intro w hw hle
  have heq : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hle
  have hplace : v = w := HeightOneSpectrum.ext heq
  exact hv (hplace ▸ hw)

private noncomputable def conductor_globalOrder (v : FinPlace F) (a : Fˣ) : ℤ :=
  -WithZero.log (v.valuation F (a : F))

private theorem conductor_order_eq_idealExp_of_gen (S : SData F CE condη)
    {I : Ideal (𝓞 F)} {a : Fˣ} (hgen : S.IsGen (a : F) I)
    (v : FinPlace F) (hv : v ∉ S.Sf) : conductor_globalOrder v a = idealExp v I := by
  have hspan := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (a : F) hgen.2.1
  have hIcount : FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (idealExp v I : ℤ) := by
    rw [FractionalIdeal.count_coe F v hgen.1.1]
    rfl
  dsimp [conductor_globalOrder]
  calc
    -WithZero.log (v.valuation F (a : F)) =
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) := hspan.symm
    _ = FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
      hgen.2.2 v hv
    _ = (idealExp v I : ℤ) := hIcount

private theorem conductor_idealExp_prime (v w : FinPlace F) :
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

private theorem conductor_globalOrder_mul (v : FinPlace F) (x y : Fˣ) :
    conductor_globalOrder v (x * y) = conductor_globalOrder v x + conductor_globalOrder v y := by
  unfold conductor_globalOrder
  change -WithZero.log (v.valuation F ((x : F) * (y : F))) = _
  rw [map_mul, WithZero.log_mul
    ((v.valuation F).ne_zero_iff.mpr (Units.ne_zero x))
    ((v.valuation F).ne_zero_iff.mpr (Units.ne_zero y))]
  ring

private theorem conductor_globalOrder_inv (v : FinPlace F) (x : Fˣ) :
    conductor_globalOrder v x⁻¹ = -conductor_globalOrder v x := by
  simp [conductor_globalOrder, map_inv₀, WithZero.log_inv]

private theorem conductor_globalOrder_zpow (v : FinPlace F) (x : Fˣ) (n : ℤ) :
    conductor_globalOrder v (x ^ n) = n * conductor_globalOrder v x := by
  simp [conductor_globalOrder, map_zpow₀, WithZero.log_zpow, mul_comm]

private theorem conductor_globalOrder_div (v : FinPlace F) (x y : Fˣ) :
    conductor_globalOrder v (x / y) = conductor_globalOrder v x - conductor_globalOrder v y := by
  rw [div_eq_mul_inv, conductor_globalOrder_mul, conductor_globalOrder_inv]
  ring

private theorem conductor_globalOrder_finset_prod {α : Type*} (v : FinPlace F)
    (T : Finset α) (f : α → Fˣ) :
    conductor_globalOrder v (T.prod f) = ∑ x ∈ T, conductor_globalOrder v (f x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [conductor_globalOrder]
  | @insert x T hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, conductor_globalOrder_mul, ih]

private theorem conductor_zpow_sixth_eq_one (c : ℂˣ) (hc : c ^ 6 = 1) (n : ℤ) :
    (c ^ n) ^ 6 = 1 := by
  calc
    (c ^ n) ^ 6 = (c ^ n) ^ (6 : ℤ) := (zpow_natCast (c ^ n) 6).symm
    _ = (c ^ (6 : ℤ)) ^ n := zpow_comm c n 6
    _ = (c ^ 6) ^ n := rfl
    _ = 1 := by simp [hc]

private theorem conductor_localOrder_toLoc (v : FinPlace F) (a : Fˣ) :
    conductor_localOrder v (toLoc v a) = conductor_globalOrder v a := by
  have hval : Valued.v (toLoc v a : v.adicCompletion F) = v.valuation F (a : F) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = _
    exact v.valuedAdicCompletion_eq_valuation' (a : F)
  simp [conductor_localOrder, conductor_globalOrder, hval]

private noncomputable def conductor_ideleSCoord (D : FieldData F)
    (S : SData F CE condη) : NumberField.IdeleGroup (𝓞 F) F →* S.FSˣ where
  toFun x := {
    val := (fun v => (Dictionary.ideleFiniteCoord v.1 x : v.1.adicCompletion F),
      fun w => (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).toMonoidHom
        (Dictionary.ideleInfiniteCoordUnit w x) : ℂ))
    inv := (fun v => ((Dictionary.ideleFiniteCoord v.1 x)⁻¹ : v.1.adicCompletion F),
      fun w => (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).toMonoidHom
        ((Dictionary.ideleInfiniteCoordUnit w x)⁻¹) : ℂ))
    val_inv := by
      apply Prod.ext
      · funext v
        simpa using (Dictionary.ideleFiniteCoord v.1 x).val_inv
      · funext w
        simpa using (Units.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (D.isTotallyComplex.isComplex w)).toMonoidHom
          (Dictionary.ideleInfiniteCoordUnit w x)).val_inv
    inv_val := by
      apply Prod.ext
      · funext v
        simpa using (Dictionary.ideleFiniteCoord v.1 x).inv_val
      · funext w
        simpa using (Units.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (D.isTotallyComplex.isComplex w)).toMonoidHom
          (Dictionary.ideleInfiniteCoordUnit w x)).inv_val
  }
  map_one' := by
    apply Units.ext
    apply Prod.ext
    · funext v
      simp
    · funext w
      simp
  map_mul' x y := by
    apply Units.ext
    apply Prod.ext
    · funext v
      simp
    · funext w
      simp

private theorem conductor_ideleSCoord_continuous (D : FieldData F)
    (S : SData F CE condη) : Continuous (conductor_ideleSCoord D S) := by
  have hFinCoord (v : FinPlace F) :
      Continuous (Dictionary.ideleFiniteCoord v : NumberField.IdeleGroup (𝓞 F) F →* (v.adicCompletion F)ˣ) := by
    apply Units.continuous_iff.mpr
    exact ⟨((RestrictedProduct.continuous_eval v).comp continuous_snd).comp Units.continuous_val,
      ((RestrictedProduct.continuous_eval v).comp continuous_snd).comp Units.continuous_coe_inv⟩
  have hInfCoord (w : InfinitePlace F) :
      Continuous (Dictionary.ideleInfiniteCoordUnit w :
        NumberField.IdeleGroup (𝓞 F) F →* w.Completionˣ) := by
    apply Units.continuous_iff.mpr
    exact ⟨((continuous_apply w).comp continuous_fst).comp Units.continuous_val,
      ((continuous_apply w).comp continuous_fst).comp Units.continuous_coe_inv⟩
  apply Units.continuous_iff.mpr
  constructor
  · apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact Units.continuous_val.comp (hFinCoord v.1)
    · apply continuous_pi
      intro w
      let eh := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (D.isTotallyComplex.isComplex w)
      exact eh.isometry_toFun.continuous.comp (Units.continuous_val.comp (hInfCoord w))
  · apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (Units.continuous_coe_inv.comp (hFinCoord v.1)).congr fun x =>
        Units.val_inv_eq_inv_val (Dictionary.ideleFiniteCoord v.1 x)
    · apply continuous_pi
      intro w
      let eh := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (D.isTotallyComplex.isComplex w)
      exact eh.isometry_toFun.continuous.comp (Units.continuous_coe_inv.comp (hInfCoord w))

private theorem conductor_ideleSCoord_principal (D : FieldData F)
    (S : SData F CE condη) (a : Fˣ) :
    conductor_ideleSCoord D S (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = S.diagU a := by
  apply Units.ext
  apply Prod.ext
  · funext v
    rfl
  · funext w
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (D.isTotallyComplex.isComplex w)
    have hu : Units.map e.toMonoidHom
        (Dictionary.ideleInfiniteCoordUnit w (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a)) =
      S.compC w (S.diagU a) := by
      have hcomp : S.compC w (S.diagU a) = Units.map w.embedding.toMonoidHom a := by
        apply Units.ext
        rfl
      have hprincipal : Dictionary.ideleInfiniteCoordUnit w
          (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
            Units.map (algebraMap F w.Completion).toMonoidHom a := by
        apply Units.ext
        rfl
      rw [hprincipal, hcomp]
      apply Units.ext
      simp [e, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
        InfinitePlace.Completion.extensionEmbedding_coe]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) hu

private theorem conductor_class_idealValue_finprod (χ : HeckeChar F)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    χ.idealValue I = ∏ᶠ v : FinPlace F, χ.primeValue v ^ idealExp v I := by
  classical
  unfold HeckeChar.idealValue
  rw [Multiset.prod_map_eq_finprod]
  rw [← finprod_emb_domain' IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    (fun v : FinPlace F => χ.primeValue v ^ idealExp v I)]
  apply finprod_congr
  intro P
  by_cases hp : P.IsPrime ∧ P ≠ ⊥
  · let v : FinPlace F := ⟨P, hp.1, hp.2⟩
    have hmem : P ∈ Set.range (fun v : FinPlace F => v.asIdeal) := ⟨v, rfl⟩
    rw [dif_pos hp, dif_pos hmem]
    have hv : Classical.choose hmem = v :=
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective (Classical.choose_spec hmem)
    rw [hv]
    congr 1
    have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
    exact (Ideal.count_associates_factors_eq hI0 hp.1 hp.2).symm
  · have hnot : P ∉ Set.range (fun v : FinPlace F => v.asIdeal) := by
      rintro ⟨v, rfl⟩
      exact hp ⟨v.isPrime, v.ne_bot⟩
    simp only [dif_neg hp, one_pow, dif_neg hnot]

private theorem conductor_class_idealExp_zero_of_ext (S : SData F CE condη)
    (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (v : FinPlace F) (hv : v ∈ S.Sf) :
    idealExp v I = 0 := by
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI.1
  have hnot : v.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors I := by
    intro hmem
    have hdvd : v.asIdeal ∣ I :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
    exact hI.2 v hv (Ideal.le_of_dvd hdvd)
  change (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
  rw [Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]
  exact Multiset.count_eq_zero.mpr hnot

private def conductor_class_factorPlaces (I : Ideal (𝓞 F)) : Finset (FinPlace F) := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors I
  exact M.toFinset.attach.image fun p =>
    ⟨p.1,
      Ideal.isPrime_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor p.1
          (Multiset.mem_toFinset.mp p.2)),
      (UniqueFactorizationMonoid.prime_of_normalized_factor p.1
        (Multiset.mem_toFinset.mp p.2)).ne_zero⟩

private theorem conductor_class_mem_factorPlaces (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v ∈ conductor_class_factorPlaces I) :
    v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  exact Multiset.mem_toFinset.mp p.2

private theorem conductor_class_factorPlaces_dvd (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v ∈ conductor_class_factorPlaces I) : v.asIdeal ∣ I :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (conductor_class_mem_factorPlaces I v hv)

private theorem conductor_class_factorPlaces_of_mem (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    v ∈ conductor_class_factorPlaces I := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨⟨v.asIdeal, Multiset.mem_toFinset.mpr hv⟩, by simp [conductor_class_factorPlaces], ?_⟩
  apply HeightOneSpectrum.ext
  rfl

private theorem conductor_class_exp_zero_of_not_factor (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : FinPlace F) (hv : v ∉ conductor_class_factorPlaces I) : idealExp v I = 0 := by
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
  have hnot : v.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors I := by
    intro hmem
    exact hv (conductor_class_factorPlaces_of_mem I v hmem)
  change (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
  rw [Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]
  exact Multiset.count_eq_zero.mpr hnot

private theorem conductor_class_idealValue_product (χ : HeckeChar F) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) :
    χ.idealValue I = ∏ v ∈ conductor_class_factorPlaces I,
      χ.primeValue v ^ idealExp v I := by
  rw [conductor_class_idealValue_finprod χ I hI]
  have hsupp : Function.mulSupport (fun v : FinPlace F => χ.primeValue v ^ idealExp v I) ⊆
      conductor_class_factorPlaces I := by
    intro v hv
    by_contra hvF
    have hexp := conductor_class_exp_zero_of_not_factor I hI v hvF
    change χ.primeValue v ^ idealExp v I ≠ 1 at hv
    rw [hexp] at hv
    simp at hv
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]

private theorem conductor_finset_product_eq_of_mulSupport_subset {α : Type*} {M : Type*}
    [CommMonoid M] (f : α → M) (A B : Finset α)
    (hA : Function.mulSupport f ⊆ A) (hB : Function.mulSupport f ⊆ B) :
    A.prod f = B.prod f := by
  let U := A ∪ B
  have hAU : A.prod f = U.prod f := by
    apply Finset.prod_subset (by intro x hx; exact Finset.mem_union_left B hx)
    intro x hxU hxA
    by_contra hne
    have hxSupport : x ∈ Function.mulSupport f := by simpa using hne
    exact hxA (hA hxSupport)
  have hBU : B.prod f = U.prod f := by
    apply Finset.prod_subset (by intro x hx; exact Finset.mem_union_right A hx)
    intro x hxU hxB
    by_contra hne
    have hxSupport : x ∈ Function.mulSupport f := by simpa using hne
    exact hxB (hB hxSupport)
  exact hAU.trans hBU.symm

/-- ar:B-character-extension (02:302–303, 359–366): every character of `B` evaluated on allowed
generators extends to a finite-order Hecke character unramified outside `S`. Package
P-ARITH-KUMMER. -/
theorem class_character_extension (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (θB : Bd.B →* ℂˣ) :
    ∃ θ : HeckeChar F, IsOfFinOrder θ ∧ (∀ v : FinPlace F, v ∉ S.Sf → θ.UnramifiedAt v) ∧
      ∀ (I : Ideal (𝓞 F)) (a : Fˣ), S.IsExterior I → S.IsGen (a : F) I → (ha : Bd.Allowed a) →
        θ.idealValue I = ((θB ⟨_, ha⟩ : ℂˣ) : ℂ) := by
  classical
  let q : S.FSˣ →* S.V := QuotientGroup.mk' _
  let projB : S.V →* Bd.B := conductor_group_projection (G := S.V) S.E Bd.B Bd.compl
  let ψ : S.FSˣ →* ℂˣ := θB.comp (projB.comp q)
  have hqpow (x : S.FSˣ) : q (x ^ 6) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    change x ^ 6 ∈ (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
    exact ⟨x, by simp⟩
  have hψpow (x : S.FSˣ) : ψ (x ^ 6) = 1 := by
    change θB (projB (q (x ^ 6))) = 1
    rw [hqpow x]
    simp
  have hψcont : Continuous ψ :=
    conductor_continuous_of_sixthPowers ψ (conductor_FS_sixthPowers_mem_nhds S) hψpow
  let primeChoice (v : FinPlace F) (hv : v ∉ S.Sf) : Fˣ :=
    Classical.choose (Bd.exists_allowed v.asIdeal (conductor_prime_isExterior S v hv))
  have hprimeChoice (v : FinPlace F) (hv : v ∉ S.Sf) :
      S.IsGen (primeChoice v hv : F) v.asIdeal ∧ Bd.Allowed (primeChoice v hv) :=
    Classical.choose_spec (Bd.exists_allowed v.asIdeal (conductor_prime_isExterior S v hv))
  let p (v : FinPlace F) : Fˣ := if hv : v ∉ S.Sf then primeChoice v hv else 1
  have hpgen (v : FinPlace F) (hv : v ∉ S.Sf) :
      S.IsGen (p v : F) v.asIdeal ∧ Bd.Allowed (p v) := by
    simpa only [p, dif_pos hv] using hprimeChoice v hv
  let primeClassValue (v : FinPlace F) : ℂˣ := ψ (S.diagU (p v))
  let localChar (v : FinPlace F) : (v.adicCompletion F)ˣ →* ℂˣ :=
    if hv : v ∈ S.Sf then 1 else conductor_localUnramifiedCharacter v (primeClassValue v)
  have hlocalCharOne (v : FinPlace F) (u : (v.adicCompletion F)ˣ)
      (hu : u ∈ (v.adicCompletionIntegers F).units) : localChar v u = 1 := by
    by_cases hv : v ∈ S.Sf
    · simp [localChar, hv]
    · simp only [localChar, dif_neg hv]
      exact conductor_localUnramifiedCharacter_one_of_unit v (primeClassValue v) u hu
  let A := FiniteAdeleRing (𝓞 F) F
  let coord (v : FinPlace F) : Aˣ →* (v.adicCompletion F)ˣ :=
    (Pi.evalMonoidHom (fun w : FinPlace F => (w.adicCompletion F)ˣ) v).comp
      RestrictedProduct.coeUnits
  have hcoord (v : FinPlace F) : Continuous (coord v) := by
    apply Units.continuous_iff.mpr
    exact ⟨(RestrictedProduct.continuous_eval v).comp Units.continuous_val,
      (RestrictedProduct.continuous_eval v).comp Units.continuous_coe_inv⟩
  have hlocalCharCont (v : FinPlace F) : Continuous (localChar v) := by
    by_cases hv : v ∈ S.Sf
    · simp only [localChar, dif_pos hv]
      change Continuous (fun _ : (v.adicCompletion F)ˣ => (1 : ℂˣ))
      exact continuous_const
    · simpa [localChar, hv] using
        conductor_localUnramifiedCharacter_continuous v (primeClassValue v)
  have hsupp (x : Aˣ) : Function.HasFiniteMulSupport (fun v => localChar v (coord v x)) := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [x.val.2, x.inv.2] with v hx hxi
    exact hlocalCharOne v (coord v x) ⟨hx, hxi⟩
  let g : Aˣ →* ℂˣ := MonoidHom.mk'
    (fun x => ∏ᶠ v : FinPlace F, localChar v (coord v x)) (by
      intro x y
      simp_rw [map_mul]
      exact finprod_mul_distrib (hsupp x) (hsupp y))
  have hOall : IsOpen {x : A | ∀ v : FinPlace F,
      x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem
      (fun v : FinPlace F => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hV : {x : Aˣ | ∀ v : FinPlace F,
      (x : A) v ∈ v.adicCompletionIntegers F} ∈ 𝓝 (1 : Aˣ) := by
    apply (hOall.preimage Units.continuous_val).mem_nhds
    intro v
    exact one_mem _
  have hI : {x : Aˣ | ∀ v : FinPlace F,
      ((x⁻¹ : Aˣ) : A) v ∈ v.adicCompletionIntegers F} ∈ 𝓝 (1 : Aˣ) := by
    apply (hOall.preimage Units.continuous_coe_inv).mem_nhds
    intro v
    exact one_mem _
  have hC : {x : Aˣ | ∀ v : FinPlace F, coord v x ∈
      (v.adicCompletionIntegers F).units} ∈ 𝓝 (1 : Aˣ) := by
    filter_upwards [hV, hI] with x hx hxi
    intro v
    exact ⟨hx v, hxi v⟩
  have heqg : (fun x : Aˣ => g x) =ᶠ[𝓝 (1 : Aˣ)] fun _ => (1 : ℂˣ) := by
    filter_upwards [hC] with x hx
    change (∏ᶠ v : FinPlace F, localChar v (coord v x)) = 1
    apply finprod_eq_one_of_forall_eq_one
    intro v
    exact hlocalCharOne v (coord v x) (hx v)
  have hg : Continuous g := by
    apply continuous_of_tendsto_nhds_one g
    exact (Filter.tendsto_congr' heqg).mpr tendsto_const_nhds
  let adeleProjection : NumberField.IdeleGroup (𝓞 F) F →* Aˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing F) A)
  have hadeleProjection : Continuous adeleProjection := by
    apply Units.continuous_iff.mpr
    exact ⟨continuous_snd.comp Units.continuous_val,
      continuous_snd.comp Units.continuous_coe_inv⟩
  let α : NumberField.IdeleGroup (𝓞 F) F →* ℂˣ :=
    ψ⁻¹ |>.comp (conductor_ideleSCoord D S)
  let β : NumberField.IdeleGroup (𝓞 F) F →* ℂˣ := g.comp adeleProjection
  let G : NumberField.IdeleGroup (𝓞 F) F →* ℂˣ := α * β
  have hψinv : Continuous (ψ⁻¹) := by
    change Continuous (fun x : S.FSˣ => (ψ x)⁻¹)
    exact continuous_inv.comp hψcont
  have hα : Continuous α := hψinv.comp (conductor_ideleSCoord_continuous D S)
  have hβ : Continuous β := hg.comp hadeleProjection
  have hG : Continuous G := by
    change Continuous (fun x : NumberField.IdeleGroup (𝓞 F) F => α x * β x)
    exact hα.mul hβ
  have hprincipalData (a : Fˣ) :
      G (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1 ∧
        ψ (S.diagU a) = ∏ v ∈ (KummerProofs.residue_zero_finite a).toFinset,
          primeClassValue v ^ conductor_globalOrder v a := by
    let T : Finset (FinPlace F) := (KummerProofs.residue_zero_finite a).toFinset
    let n (v : FinPlace F) : ℤ := conductor_globalOrder v a
    let primeProduct : Fˣ := T.prod fun v => p v ^ n v
    let ε : Fˣ := a / primeProduct
    have hprimeOrder (w : FinPlace F) (hw : w ∉ S.Sf) (v : FinPlace F) :
        conductor_globalOrder w (p v) = if w = v then 1 else 0 := by
      by_cases hvS : v ∈ S.Sf
      · have hwv : w ≠ v := by
          intro heq
          subst w
          exact hw hvS
        simp [p, hvS, conductor_globalOrder, hwv]
      · rw [conductor_order_eq_idealExp_of_gen S (hpgen v hvS).1 w hw,
          conductor_idealExp_prime v w]
    have hzeroOrder (w : FinPlace F) (hwT : w ∉ T) :
        conductor_globalOrder w a = 0 := by
      have hres : residue w (a : F) ≠ 0 := by
        intro hres
        exact hwT ((KummerProofs.residue_zero_finite a).mem_toFinset.mpr hres)
      have hval :=
        ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one w (a : F) |>.mp hres
      simp [conductor_globalOrder, hval]
    have hprimeProductOrder (w : FinPlace F) (hw : w ∉ S.Sf) :
        conductor_globalOrder w primeProduct =
          if w ∈ T then n w else 0 := by
      have hprod : conductor_globalOrder w primeProduct =
          ∑ v ∈ T, conductor_globalOrder w (p v ^ n v) := by
        simpa [primeProduct] using
          (conductor_globalOrder_finset_prod w T (fun v => p v ^ n v))
      rw [hprod]
      have hterms : ∀ v ∈ T,
          conductor_globalOrder w (p v ^ n v) = if w = v then n v else 0 := by
        intro v hv
        rw [conductor_globalOrder_zpow, hprimeOrder w hw v]
        by_cases h : w = v <;> simp [h]
      rw [Finset.sum_congr rfl hterms]
      by_cases hwT : w ∈ T
      · have hsingle : (∑ v ∈ T, if w = v then n v else 0) = n w := by
          rw [Finset.sum_eq_single w]
          · simp
          · intro v hv hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot hwT).elim
        simp [hwT, hsingle]
      · have hzero : (∑ v ∈ T, if w = v then n v else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          by_cases h : w = v
          · subst v
            exact (hwT hv).elim
          · simp [h]
        simp [hwT, hzero]
    have hεOrder (w : FinPlace F) (hw : w ∉ S.Sf) :
        conductor_globalOrder w ε = 0 := by
      change conductor_globalOrder w (a / primeProduct) = 0
      rw [conductor_globalOrder_div, hprimeProductOrder w hw]
      by_cases hwT : w ∈ T
      · simp [hwT, n]
      · simp [hwT, n, hzeroOrder w hwT]
    have hεUnit : ε ∈ S.US := by
      change ∀ w : FinPlace F, w ∉ S.Sf → w.valuation F (ε : F) = 1
      intro w hw
      have hne : w.valuation F (ε : F) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr ε.ne_zero
      have hlog : WithZero.log (w.valuation F (ε : F)) = 0 := by
        have h := hεOrder w hw
        dsimp [conductor_globalOrder] at h
        linarith
      calc
        w.valuation F (ε : F) = WithZero.exp (WithZero.log (w.valuation F (ε : F))) :=
          (WithZero.exp_log hne).symm
        _ = 1 := by rw [hlog, WithZero.exp_zero]
    have hfactor : a = ε * primeProduct := by
      dsimp [ε]
      simp [div_eq_mul_inv]
    have hεproj : projB (q (S.diagU ε)) = 1 := by
      apply conductor_group_projection_kills (G := S.V) S.E Bd.B Bd.compl
      change q (S.diagU ε) ∈ S.US.map ((QuotientGroup.mk' _).comp S.diagU)
      exact Subgroup.mem_map.mpr ⟨ε, hεUnit, rfl⟩
    have hψfactor : ψ (S.diagU a) = ∏ v ∈ T, primeClassValue v ^ n v := by
      have hεψ : ψ (S.diagU ε) = 1 := by
        change θB (projB (q (S.diagU ε))) = 1
        rw [hεproj]
        simp
      have hproduct : ψ (S.diagU primeProduct) =
          ∏ v ∈ T, primeClassValue v ^ n v := by
        simp [primeProduct, primeClassValue, map_prod, map_zpow]
      calc
        ψ (S.diagU a) = ψ (S.diagU ε * S.diagU primeProduct) := by rw [hfactor, map_mul]
        _ = ψ (S.diagU ε) * ψ (S.diagU primeProduct) := map_mul ψ _ _
        _ = _ := by rw [hεψ, hproduct]; simp
    have hcoordPrincipal (v : FinPlace F) :
        coord v (adeleProjection (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a)) = toLoc v a := by
      apply Units.ext
      rfl
    have hlocalPrincipal (v : FinPlace F) :
        localChar v (coord v (adeleProjection (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a))) =
          primeClassValue v ^ n v := by
      rw [hcoordPrincipal v]
      by_cases hv : v ∈ S.Sf
      · have hp : p v = 1 := by simp [p, hv]
        simp [localChar, hv, primeClassValue, hp]
      · simp [localChar, hv, conductor_localUnramifiedCharacter,
          conductor_localOrder_toLoc, primeClassValue, n]
    have hsupportPrincipal :
        Function.mulSupport (fun v => localChar v
          (coord v (adeleProjection (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a)))) ⊆ T := by
      intro v hv
      by_contra hvT
      have hzero := hzeroOrder v hvT
      apply hv
      change localChar v
        (coord v (adeleProjection (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a))) = 1
      rw [hlocalPrincipal v]
      have hn : n v = 0 := by simpa [n] using hzero
      rw [hn]
      simp
    have hβprincipal : β (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
        ∏ v ∈ T, primeClassValue v ^ n v := by
      change g (adeleProjection (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a)) = _
      change (∏ᶠ v : FinPlace F, localChar v
        (coord v (adeleProjection (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a)))) = _
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupportPrincipal]
      apply Finset.prod_congr rfl
      intro v hv
      exact hlocalPrincipal v
    have hαprincipal : α (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
        (ψ (S.diagU a))⁻¹ := by
      change (ψ (conductor_ideleSCoord D S (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a)))⁻¹ = _
      rw [conductor_ideleSCoord_principal]
    have hGprincipal : G (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1 := by
      change α (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) *
        β (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1
      rw [hαprincipal, hβprincipal, hψfactor]
      simp
    exact ⟨hGprincipal, by simpa [T, n] using hψfactor⟩
  have hprincipal (a : Fˣ) : G (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = 1 :=
    (hprincipalData a).1
  let N := NumberField.IdeleGroup.principalSubgroup (𝓞 F) F
  have hN : N ≤ G.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact hprincipal a
  let C : IdeleClassGroup (𝓞 F) F →* ℂˣ := QuotientGroup.lift N G hN
  have hC : Continuous C := by
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact hG
  let θ : HeckeChar F := ⟨C, hC⟩
  have hψval6 (x : S.FSˣ) : ψ x ^ 6 = 1 := by
    simpa only [map_pow] using hψpow x
  have hlocalpow (v : FinPlace F) (u : (v.adicCompletion F)ˣ) :
      (localChar v u) ^ 6 = 1 := by
    by_cases hv : v ∈ S.Sf
    · simp [localChar, hv]
    · have hc : (primeClassValue v) ^ 6 = 1 := hψval6 (S.diagU (p v))
      simp only [localChar, dif_neg hv, conductor_localUnramifiedCharacter]
      exact conductor_zpow_sixth_eq_one (primeClassValue v) hc (conductor_localOrder v u)
  have hβpow (x : NumberField.IdeleGroup (𝓞 F) F) : (β x) ^ 6 = 1 := by
    change (g (adeleProjection x)) ^ 6 = 1
    let y : Aˣ := adeleProjection x
    change (∏ᶠ v : FinPlace F, localChar v (coord v y)) ^ 6 = 1
    rw [finprod_pow (hsupp y) 6]
    apply finprod_eq_one_of_forall_eq_one
    intro v
    exact hlocalpow v (coord v y)
  have hαpow (x : NumberField.IdeleGroup (𝓞 F) F) : (α x) ^ 6 = 1 := by
    change ((ψ (conductor_ideleSCoord D S x))⁻¹) ^ 6 = 1
    have hc := hψval6 (conductor_ideleSCoord D S x)
    simp [hc]
  have hGpow (x : NumberField.IdeleGroup (𝓞 F) F) : (G x) ^ 6 = 1 := by
    change (α x * β x) ^ 6 = 1
    rw [mul_pow, hαpow x, hβpow x]
    simp
  have hθpow : θ ^ 6 = 1 := by
    apply ContinuousMonoidHom.ext
    intro z
    refine QuotientGroup.induction_on z (fun x => ?_)
    simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
    change G x ^ 6 = 1
    exact hGpow x
  have hθfin : IsOfFinOrder θ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hθpow⟩
  have hθram (v : FinPlace F) (hv : v ∉ S.Sf) : θ.UnramifiedAt v := by
    intro u hu huinv
    let x := NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u
    have hScoord : conductor_ideleSCoord D S x = 1 := by
      apply Units.ext
      apply Prod.ext
      · funext w
        have hne : w.1 ≠ v := by
          intro heq
          exact hv (heq ▸ w.2)
        change (Dictionary.ideleFiniteCoord w.1 x : w.1.adicCompletion F) = 1
        exact congrArg (fun z : (w.1.adicCompletion F)ˣ => (z : w.1.adicCompletion F))
          (Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne w.1 v hne u)
      · funext w
        change ((Units.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (D.isTotallyComplex.isComplex w)).toMonoidHom
          (Dictionary.ideleInfiniteCoordUnit w x) : ℂˣ) : ℂ) = 1
        simp [x, Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion]
    have hcoordBridge (w : FinPlace F) :
        coord w (adeleProjection x) = Dictionary.ideleFiniteCoord w x := by
      apply Units.ext
      rfl
    have hβone : β x = 1 := by
      change g (adeleProjection x) = 1
      change (∏ᶠ w : FinPlace F, localChar w (coord w (adeleProjection x))) = 1
      apply finprod_eq_one_of_forall_eq_one
      intro w
      by_cases hwv : w = v
      · subst w
        rw [hcoordBridge, Dictionary.ideleFiniteCoord_ofAdicCompletion]
        simp only [localChar, dif_neg hv]
        exact conductor_localUnramifiedCharacter_unramified v (primeClassValue v) u hu huinv
      · have hne : w ≠ v := hwv
        rw [hcoordBridge, Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne w v hne u]
        exact (localChar w).map_one
    have hGone : G x = 1 := by
      change α x * β x = 1
      change (ψ (conductor_ideleSCoord D S x))⁻¹ * β x = 1
      rw [hScoord, hβone]
      simp
    change C (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1
    change G (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = 1
    exact hGone
  have hθlocOutside (v : FinPlace F) (hv : v ∉ S.Sf)
      (u : (v.adicCompletion F)ˣ) : θ.loc v u = localChar v u := by
    let x := NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u
    have hScoord : conductor_ideleSCoord D S x = 1 := by
      apply Units.ext
      apply Prod.ext
      · funext w
        have hne : w.1 ≠ v := by
          intro heq
          exact hv (heq ▸ w.2)
        change (Dictionary.ideleFiniteCoord w.1 x : w.1.adicCompletion F) = 1
        exact congrArg (fun z : (w.1.adicCompletion F)ˣ => (z : w.1.adicCompletion F))
          (Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne w.1 v hne u)
      · funext w
        change ((Units.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (D.isTotallyComplex.isComplex w)).toMonoidHom
          (Dictionary.ideleInfiniteCoordUnit w x) : ℂˣ) : ℂ) = 1
        simp [x, Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion]
    have hcoordBridge (w : FinPlace F) :
        coord w (adeleProjection x) = Dictionary.ideleFiniteCoord w x := by
      apply Units.ext
      rfl
    have hβloc : β x = localChar v u := by
      change g (adeleProjection x) = localChar v u
      change (∏ᶠ w : FinPlace F, localChar w (coord w (adeleProjection x))) = _
      rw [finprod_eq_single _ v (fun w hne => by
        rw [hcoordBridge w,
          Dictionary.ideleFiniteCoord_ofAdicCompletion_of_ne w v hne u]
        simp)]
      rw [hcoordBridge v, Dictionary.ideleFiniteCoord_ofAdicCompletion]
    have hαloc : α x = 1 := by
      change (ψ (conductor_ideleSCoord D S x))⁻¹ = 1
      rw [hScoord]
      simp
    have hGloc : G x = localChar v u := by
      change α x * β x = localChar v u
      rw [hαloc, hβloc]
      simp
    change C (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = localChar v u
    change G (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = localChar v u
    exact hGloc
  have hθprime (v : FinPlace F) (hv : v ∉ S.Sf) :
      θ.primeValue v = (primeClassValue v : ℂ) := by
    have hram := hθram v hv
    rw [HeckeChar.primeValue, if_pos hram]
    let π0 : Fˣ := Units.mk0 (unif v) (unif_ne_zero v)
    have hunif : v.valuation F (unif v) = WithZero.exp (-1 : ℤ) :=
      (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    have hval : v.valuation F (π0 : F) = WithZero.exp (-1 : ℤ) := by
      change v.valuation F (unif v) = _
      exact hunif
    have hOrder : conductor_globalOrder v π0 = 1 := by
      simp [conductor_globalOrder, hval]
    rw [hθlocOutside v hv (toLoc v π0)]
    simp only [localChar, dif_neg hv, conductor_localUnramifiedCharacter]
    change ((primeClassValue v ^ conductor_localOrder v (toLoc v π0) : ℂˣ) : ℂ) =
      (primeClassValue v : ℂ)
    rw [conductor_localOrder_toLoc, hOrder]
    simp
  refine ⟨θ, hθfin, hθram, ?_⟩
  intro I a hI hgen ha
  let R := conductor_class_factorPlaces I
  let T := (KummerProofs.residue_zero_finite a).toFinset
  let f (v : FinPlace F) : ℂ :=
    ((primeClassValue v ^ conductor_globalOrder v a : ℂˣ) : ℂ)
  have hRext (v : FinPlace F) (hv : v ∈ R) : v ∉ S.Sf := by
    intro hvS
    have hdvd := conductor_class_factorPlaces_dvd I v hv
    exact hI.2 v hvS (Ideal.le_of_dvd hdvd)
  have hterm (v : FinPlace F) :
      θ.primeValue v ^ idealExp v I = f v := by
    by_cases hvS : v ∈ S.Sf
    · have hexp := conductor_class_idealExp_zero_of_ext S I hI v hvS
      have hc : primeClassValue v = 1 := by simp [primeClassValue, p, hvS]
      simp [f, hexp, hc]
    · have horder := conductor_order_eq_idealExp_of_gen S hgen v hvS
      rw [hθprime v hvS]
      simp [f, horder, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
  have hideal : θ.idealValue I = R.prod (fun v => f v) := by
    rw [conductor_class_idealValue_product θ I hI.1]
    apply Finset.prod_congr rfl
    intro v hv
    exact hterm v
  have hzeroOrderT (v : FinPlace F) (hvT : v ∉ T) :
      conductor_globalOrder v a = 0 := by
    have hres : residue v (a : F) ≠ 0 := by
      intro hres
      exact hvT ((KummerProofs.residue_zero_finite a).mem_toFinset.mpr hres)
    have hval :=
      ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one v (a : F) |>.mp hres
    simp [conductor_globalOrder, hval]
  have hsupportR : Function.mulSupport f ⊆ R := by
    intro v hv
    by_contra hvR
    have hzero : f v = 1 := by
      by_cases hvS : v ∈ S.Sf
      · have hc : primeClassValue v = 1 := by simp [primeClassValue, p, hvS]
        simp [f, hc]
      · have hexp := conductor_class_exp_zero_of_not_factor I hI.1 v hvR
        have horder := conductor_order_eq_idealExp_of_gen S hgen v hvS
        simp [f, horder, hexp, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
    exact hv (by simpa using hzero)
  have hsupportT : Function.mulSupport f ⊆ T := by
    intro v hv
    by_contra hvT
    have hz := hzeroOrderT v hvT
    have hzero : f v = 1 := by simp [f, hz]
    exact hv (by simpa using hzero)
  have hprodSets : R.prod f = T.prod f :=
    conductor_finset_product_eq_of_mulSupport_subset f R T hsupportR hsupportT
  have hvalProd :
      ((∏ v ∈ T, primeClassValue v ^ conductor_globalOrder v a : ℂˣ) : ℂ) =
        T.prod f := by
    classical
    induction T using Finset.induction_on with
    | empty => simp [f]
    | @insert v T hv ih => simp [hv, f, ih]
  have hψcomplex := congrArg (fun z : ℂˣ => (z : ℂ)) (hprincipalData a).2
  have hψallowed : ψ (S.diagU a) = θB ⟨q (S.diagU a), ha⟩ := by
    have hclass : q (S.diagU a) ∈ Bd.B := by
      change (QuotientGroup.mk (S.diagU a) : S.V) ∈ Bd.B at ha
      exact ha
    have hfixed := conductor_group_projection_fixed (G := S.V) S.E Bd.B Bd.compl
      (q (S.diagU a)) hclass
    have hb : projB (q (S.diagU a)) = ⟨q (S.diagU a), ha⟩ := by
      apply Subtype.ext
      exact hfixed
    change θB (projB (q (S.diagU a))) = _
    exact congrArg θB hb
  calc
    θ.idealValue I = R.prod f := hideal
    _ = T.prod f := hprodSets
    _ = ((∏ v ∈ T, primeClassValue v ^ conductor_globalOrder v a : ℂˣ) : ℂ) := hvalProd.symm
    _ = ((ψ (S.diagU a) : ℂˣ) : ℂ) := hψcomplex.symm
    _ = ((θB ⟨q (S.diagU a), ha⟩ : ℂˣ) : ℂ) := by rw [hψallowed]

/-- Archimedean angular type of a Hecke character at the complex places. -/
def HeckeChar.HasAngularType (D : FieldData F) (χ : HeckeChar F) : Prop :=
  ∀ w : InfinitePlace F, ∃ m : ℤ, (m = 1 ∨ m = -1) ∧
    ∀ z : ℂˣ,
      ((χ.locInf w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z) : ℂˣ) : ℂ) =
        ((z : ℂ) / ‖(z : ℂ)‖) ^ m

namespace a1_gauss_sol

open ArtinPrimitiveRoots.Proofs.a1_gauss_sol

theorem gauss_correction_data (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (H : HilbertData F) (Bd : BData S H)
    (θB : Bd.B →* ℂˣ)
    (hθ : ∀ v : FinPlace F, v ∉ S.Sf → ∀ p : Fˣ,
      ∀ (hpgen : S.IsGen (p : F) v.asIdeal), ∀ (hpAllowed : Bd.Allowed p),
      gamma D S A 3 v.asIdeal (p : F) =
        ((θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), hpAllowed⟩ : ℂˣ) : ℂ)) :
    ∃ G : HeckeChar F, IsOfFinOrder G ∧
      ∀ v : FinPlace F, v ∉ S.Sf → G.UnramifiedAt v ∧
        ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
          G.primeValue v = (starRingEnd ℂ) (chi D v 4) *
            gamma D S A 3 v.asIdeal (p : F) := by
  classical
  obtain ⟨θ, hθfin, hθram, hθideal⟩ := class_character_extension D S H Bd θB
  let four : Fˣ := Units.mk0 (4 : F) (by norm_num)
  obtain ⟨κ, hκfin, hκ⟩ := kummer_exists D S four
  let G : HeckeChar F := θ * κ⁻¹
  refine ⟨G, hθfin.mul hκfin.inv, ?_⟩
  intro v hv
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  have hr4 : residue v (4 : F) = Ideal.Quotient.mk v.asIdeal (4 : 𝓞 F) := by
    simpa only [map_ofNat] using
      ArtinPrimitiveRoots.A2.qs_nq0_residue_algebraMap v (4 : 𝓞 F)
  have hres4 : residue v (4 : F) ≠ 0 := by
    intro hz
    have h4 : (4 : 𝓞 F) ∈ v.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp (hr4.symm.trans hz)
    have h2 : (2 : 𝓞 F) ∈ v.asIdeal :=
      v.isPrime.mem_of_pow_mem 2 (by
        simpa only [show (2 : 𝓞 F) ^ 2 = 4 by norm_num] using h4)
    apply h6
    simpa only [show (3 : 𝓞 F) * 2 = 6 by norm_num] using
      v.asIdeal.mul_mem_left (3 : 𝓞 F) h2
  have hκv := hκ v hv hres4
  change κ.UnramifiedAt v ∧ κ.primeValue v = chi D v 4 at hκv
  have hroot : chi D v 4 ^ 6 = 1 := by
    rw [chi, if_neg hres4]
    have hμ : (((chiAlg v (4 : F) : (𝓞 F)ˣ) : 𝓞 F)) ^ 6 = 1 :=
      (mem_rootsOfUnity' 6 _).mp (chiAlg v (4 : F)).property
    rw [← map_pow, ← map_pow, hμ, map_one, map_one]
  have hinv : (chi D v 4)⁻¹ = (starRingEnd ℂ) (chi D v 4) :=
    Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hroot (by decide))
  have hloc (u : (v.adicCompletion F)ˣ) :
      G.loc v u = θ.loc v u * (κ.loc v u)⁻¹ := rfl
  have hGram : G.UnramifiedAt v := by
    intro u hu huinv
    rw [hloc, hθram v hv u hu huinv, hκv.1 u hu huinv, inv_one, mul_one]
  have hprime : G.primeValue v = θ.primeValue v * (κ.primeValue v)⁻¹ := by
    unfold HeckeChar.primeValue
    rw [if_pos hGram, if_pos (hθram v hv), if_pos hκv.1, hloc,
      Units.val_mul, Units.val_inv_eq_inv_val]
  refine ⟨hGram, ?_⟩
  intro p hp ha
  have hfac : UniqueFactorizationMonoid.normalizedFactors v.asIdeal = {v.asIdeal} := by
    simpa only [normalize_eq] using
      UniqueFactorizationMonoid.normalizedFactors_irreducible v.irreducible
  have hideal : θ.idealValue v.asIdeal = θ.primeValue v := by
    unfold HeckeChar.idealValue
    rw [hfac, Multiset.map_singleton, Multiset.prod_singleton,
      dif_pos ⟨v.isPrime, v.ne_bot⟩]
  have hθvalue : θ.primeValue v = gamma D S A 3 v.asIdeal (p : F) := by
    rw [← hideal]
    exact (hθideal v.asIdeal p hp.1 hp ha).trans (hθ v hv p hp ha).symm
  rw [hprime, hθvalue, hκv.2, hinv]
  exact mul_comm _ _

end a1_gauss_sol

namespace a1_lambda_sol

/-- The A1-LAMBDA endpoint, integrated below the frozen Gauss-character theorem.
The lower-level proof files unfold the Hecke and angular interfaces to avoid an import cycle. -/
theorem lambda_data (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (H : HilbertData F) (Bd : BData S H) :
    ∃ Λ : HeckeChar F, (∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1) ∧
      HeckeChar.HasAngularType D Λ ∧
      ∀ v : FinPlace F, v ∉ S.Sf → Λ.UnramifiedAt v ∧
        ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
          gamma D S A 2 v.asIdeal (p : F) ^ 3 = -Λ.primeValue v := by
  obtain ⟨Λ, hu, ha, hΛ⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_lambda_sol.lambda_data_below D S A
  refine ⟨Λ, hu, ha, ?_⟩
  intro v hv
  exact ⟨(hΛ v hv).1, fun p hp _ => (hΛ v hv).2 (p : F) hp⟩

end a1_lambda_sol

/-- lem:gauss-characters (02:411–436): `Λ` unitary, `G` finite order, both unramified at `v ∉ S`,
with `γ_2(𝔭)³ = -Λ(𝔭)`, `G(𝔭) = conj(χ_𝔭(4))γ_3(𝔭)`, `γ_1(𝔭)γ_2(𝔭) = -Λ(𝔭)G(𝔭)` for every exterior
prime and allowed generator. Package P-ARITH-GAUSS (Λ: P-ARITH-LAMBDA, G: P-WEIL).
Corrected per rev-theta to include `Λ`'s angular type and the cubic-sign character. -/
theorem gauss_characters (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (H : HilbertData F) (Bd : BData S H) :
    ∃ Λ G : HeckeChar F, IsOfFinOrder G ∧
      (∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1) ∧
      HeckeChar.HasAngularType D Λ ∧
      (∃ θB : Bd.B →* ℂˣ, ∀ v : FinPlace F, v ∉ S.Sf →
        ∀ p : Fˣ, ∀ (hpgen : S.IsGen (p : F) v.asIdeal),
          ∀ (hpAllowed : Bd.Allowed p),
          (gamma D S A 3 v.asIdeal (p : F) = 1 ∨
            gamma D S A 3 v.asIdeal (p : F) = -1) ∧
          gamma D S A 3 v.asIdeal (p : F) =
            ((θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), hpAllowed⟩ : ℂˣ) : ℂ)) ∧
      ∀ v : FinPlace F, v ∉ S.Sf → Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
        ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
          gamma D S A 2 v.asIdeal (p : F) ^ 3 = -Λ.primeValue v ∧
          G.primeValue v = (starRingEnd ℂ) (chi D v 4) * gamma D S A 3 v.asIdeal (p : F) ∧
          gamma D S A 1 v.asIdeal (p : F) * gamma D S A 2 v.asIdeal (p : F) =
            -(Λ.primeValue v * G.primeValue v) := by
  sorry

/-- `ϑ = Λ̄ Ḡ η = Λ⁻¹ G⁻¹ η` (unitary) (02:606–608). -/
def vartheta (Λ G η : HeckeChar F) : HeckeChar F := Λ⁻¹ * G⁻¹ * η

/-- `L_S(y) = Π_{v∈S} ϑ_v(y_v)^{-1}` (02:610–613). Complex places through
`ringEquivComplexOfIsComplex`. -/
def SData.LS (S : SData F CE condη) (ϑ : HeckeChar F) (y : S.FSˣ) : ℂ :=
  (∏ v : S.Sf, (((ϑ.loc v.1 (S.compU v y))⁻¹ : ℂˣ) : ℂ)) *
    ∏ w : InfinitePlace F,
      if hw : w.IsComplex then
        (((ϑ.locInf w (Units.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
            (S.compC w y)))⁻¹ : ℂˣ) : ℂ)
      else 1

private def conductor_factorPlaces (I : Ideal (𝓞 F)) : Finset (FinPlace F) := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors I
  exact M.toFinset.attach.image fun p =>
    ⟨p.1,
      Ideal.isPrime_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor p.1
          (Multiset.mem_toFinset.mp p.2)),
      (UniqueFactorizationMonoid.prime_of_normalized_factor p.1
        (Multiset.mem_toFinset.mp p.2)).ne_zero⟩

private theorem conductor_mem_factorPlaces (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v ∈ conductor_factorPlaces I) :
    v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  exact Multiset.mem_toFinset.mp p.2

private theorem conductor_factorPlaces_dvd (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v ∈ conductor_factorPlaces I) : v.asIdeal ∣ I :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (conductor_mem_factorPlaces I v hv)

private theorem conductor_factorPlaces_of_mem (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    v ∈ conductor_factorPlaces I := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨⟨v.asIdeal, Multiset.mem_toFinset.mpr hv⟩, by simp [conductor_factorPlaces], ?_⟩
  apply HeightOneSpectrum.ext
  rfl

private theorem conductor_exp_zero_of_not_factor (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : FinPlace F) (hv : v ∉ conductor_factorPlaces I) : idealExp v I = 0 := by
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
  have hnot : v.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors I := by
    intro hmem
    exact hv (conductor_factorPlaces_of_mem I v hmem)
  change (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
  rw [Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]
  exact Multiset.count_eq_zero.mpr hnot

private theorem conductor_loc_gen_factor_unit
    (S : SData F CE condη) (χ : HeckeChar F)
    (hχ : ∀ v : FinPlace F, v ∉ S.Sf → χ.UnramifiedAt v)
    (I : Ideal (𝓞 F)) (a : Fˣ) (ha : S.IsGen (a : F) I)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    χ.loc v (toLoc v a) =
      χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ idealExp v I := by
  classical
  let n : ℕ := idealExp v I
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using ha.1.1
  have hcount :
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
          (idealExp v I : ℤ) := by
    rw [ha.2.2 v hv, FractionalIdeal.count_coe F v hI0]
    rfl
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (a : F) ha.2.1
  rw [hcount] at hlog
  have hLog : WithZero.log (v.valuation F (a : F)) = -(idealExp v I : ℤ) := by
    linarith
  have hval_nonzero : v.valuation F (a : F) ≠ 0 :=
    (Valuation.ne_zero_iff (v.valuation F)).mpr ha.2.1
  have hval : v.valuation F (a : F) = WithZero.exp (-(idealExp v I : ℤ)) := by
    calc
      v.valuation F (a : F) =
          WithZero.exp (WithZero.log (v.valuation F (a : F))) :=
        (WithZero.exp_log hval_nonzero).symm
      _ = WithZero.exp (-(idealExp v I : ℤ)) := by rw [hLog]
  let π : (v.adicCompletion F)ˣ :=
    toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (unif v)) = _
    calc
      _ = v.valuation F (unif v) := v.valuedAdicCompletion_eq_valuation' (unif v)
      _ = WithZero.exp (-1 : ℤ) :=
        (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπpow : Valued.v ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-(n : ℤ)) := by
    calc
      _ = Valued.v (π : v.adicCompletion F) ^ n := by simp
      _ = WithZero.exp (-(n : ℤ)) := by
        rw [hπval]
        simpa [n] using (WithZero.exp_zsmul (n : ℤ) (-1 : ℤ)).symm
  let u : (v.adicCompletion F)ˣ := toLoc v a * (π ^ n)⁻¹
  have huval : Valued.v (u : v.adicCompletion F) = 1 := by
    calc
      Valued.v (u : v.adicCompletion F) =
          Valued.v (toLoc v a : v.adicCompletion F) *
            (Valued.v ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ := by
              simp [u]
      _ = WithZero.exp (-(n : ℤ)) * (WithZero.exp (-(n : ℤ)))⁻¹ := by
        rw [show Valued.v (toLoc v a : v.adicCompletion F) = v.valuation F (a : F) by
          exact v.valuedAdicCompletion_eq_valuation' (a : F)]
        rw [hval, hπpow]
      _ = 1 := mul_inv_cancel₀ (a := WithZero.exp (-(n : ℤ))) (by simp)
  have hu_mem : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, huval]
  have hu_inv_mem : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [Units.val_inv_eq_inv_val, huval]
  have hlocalUnit : χ.loc v u = 1 := hχ v hv u hu_mem hu_inv_mem
  have hdecomp : u * π ^ n = toLoc v a := by
    dsimp [u]
    group
  have hloc : χ.loc v (toLoc v a) = χ.loc v π ^ n := by
    rw [← hdecomp, map_mul, hlocalUnit, one_mul, map_pow]
  simpa [n, π] using hloc

private theorem conductor_idealValue_finprod (χ : HeckeChar F) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) : χ.idealValue I = ∏ᶠ v : FinPlace F, χ.primeValue v ^ idealExp v I := by
  classical
  unfold HeckeChar.idealValue
  rw [Multiset.prod_map_eq_finprod]
  rw [← finprod_emb_domain' IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    (fun v : FinPlace F => χ.primeValue v ^ idealExp v I)]
  apply finprod_congr
  intro P
  by_cases hp : P.IsPrime ∧ P ≠ ⊥
  · let v : FinPlace F := ⟨P, hp.1, hp.2⟩
    have hmem : P ∈ Set.range (fun v : FinPlace F => v.asIdeal) := ⟨v, rfl⟩
    rw [dif_pos hp, dif_pos hmem]
    have hv : Classical.choose hmem = v :=
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective (Classical.choose_spec hmem)
    rw [hv]
    congr 1
    have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
    exact (Ideal.count_associates_factors_eq hI0 hp.1 hp.2).symm
  · have hnot : P ∉ Set.range (fun v : FinPlace F => v.asIdeal) := by
      rintro ⟨v, rfl⟩
      exact hp ⟨v.isPrime, v.ne_bot⟩
    simp only [dif_neg hp, one_pow, dif_neg hnot]

private theorem conductor_idele_inf_comp
    (D : FieldData F) (S : SData F CE condη) (a : Fˣ) (w : InfinitePlace F) :
    Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom (S.compC w (S.diagU a)) =
      Dictionary.ideleInfiniteCoordUnit w (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)
  have hcomp : S.compC w (S.diagU a) = Units.map w.embedding.toMonoidHom a := by
    apply Units.ext
    rfl
  have hprincipal : Dictionary.ideleInfiniteCoordUnit w
      (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
        Units.map (algebraMap F w.Completion).toMonoidHom a := by
    apply Units.ext
    rfl
  rw [hcomp, hprincipal]
  apply Units.ext
  apply e.injective
  simp [e, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
    InfinitePlace.Completion.extensionEmbedding_coe]

private theorem conductor_units_val_prod {α : Type*} (s : Finset α) (f : α → ℂˣ) :
    ((∏ v ∈ s, f v : ℂˣ) : ℂ) = ∏ v ∈ s, (f v : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih => simp [hv, ih]

private theorem conductor_rp_truncate
    {ι : Type*} {G : ι → Type*} {A : ∀ i, Set (G i)}
    [∀ i, TopologicalSpace (G i)] [∀ i, One (G i)]
    (hA : ∀ i, (1 : G i) ∈ A i) (x : Πʳ i, [G i, A i]) :
    Tendsto (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then x i else 1,
        by
          filter_upwards [show ∀ᶠ i : ι in cofinite, i ∉ s by
            exact (s.finite_toSet.compl_mem_cofinite)] with i hi
          simpa [hi] using hA i⟩ : Πʳ i, [G i, A i])) atTop
      (@nhds (Πʳ i, [G i, A i]) (RestrictedProduct.topologicalSpace G A cofinite) x) := by
  classical
  letI : TopologicalSpace (Πʳ i, [G i, A i]) :=
    RestrictedProduct.topologicalSpace G A cofinite
  let S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  let xS : Πʳ i, [G i, A i]_[𝓟 S] := ⟨x, by
    rw [eventually_principal]
    intro i hi
    simpa [S] using hi⟩
  have hconvPi : Tendsto (fun s : Finset ι => fun i => if i ∈ s then xS i else 1)
      atTop (𝓝 (xS : Π i, G i)) := by
    apply tendsto_pi_nhds.2
    intro i
    have hi : ∀ᶠ s : Finset ι in atTop, i ∈ s :=
      eventually_atTop.2 ⟨{i}, fun s hs => Finset.singleton_subset_iff.mp hs⟩
    have heq : (fun s : Finset ι => if i ∈ s then xS i else 1) =ᶠ[atTop]
        fun _ => xS i := by
      filter_upwards [hi] with s hs
      simp [hs]
    exact tendsto_const_nhds.congr' heq.symm
  letI : TopologicalSpace (Πʳ i, [G i, A i]_[𝓟 S]) :=
    RestrictedProduct.topologicalSpace G A (𝓟 S)
  have hconvS : Tendsto (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then xS i else 1,
        by
          rw [eventually_principal]
          intro i hi
          by_cases his : i ∈ s
          · simp [his]
            change x i ∈ A i at hi
            simpa [xS] using hi
          · simpa [his] using hA i⟩ : Πʳ i, [G i, A i]_[𝓟 S])) atTop
      (@nhds (Πʳ i, [G i, A i]_[𝓟 S])
        (RestrictedProduct.topologicalSpace G A (𝓟 S)) xS) := by
    apply (RestrictedProduct.isEmbedding_coe_of_principal (R := G) (A := A)
      (S := S)).tendsto_nhds_iff.mpr
    change Tendsto (fun s : Finset ι => fun i => if i ∈ s then xS i else 1)
      atTop (𝓝 (xS : Π i, G i))
    exact hconvPi
  have hinc := (RestrictedProduct.continuous_inclusion (R := G) (A := A) hS).continuousAt
    |>.tendsto.comp hconvS
  have hx : RestrictedProduct.inclusion G A hS xS = x := rfl
  have hfun : (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then x i else 1,
        by
          filter_upwards [show ∀ᶠ i : ι in cofinite, i ∉ s by
            exact (s.finite_toSet.compl_mem_cofinite)] with i hi
          simpa [hi] using hA i⟩ : Πʳ i, [G i, A i])) =
      RestrictedProduct.inclusion G A hS ∘ (fun s : Finset ι =>
        (⟨fun i => if i ∈ s then xS i else 1,
          by
            rw [eventually_principal]
            intro i hi
            by_cases his : i ∈ s
            · simp [his]
              change x i ∈ A i at hi
              simpa [xS] using hi
            · simpa [his] using hA i⟩ : Πʳ i, [G i, A i]_[𝓟 S])) := by
    funext s
    apply Subtype.ext
    rfl
  rw [hfun]
  have hnhds : 𝓝 (RestrictedProduct.inclusion G A hS xS) = 𝓝 x :=
    congrArg (fun y => 𝓝 y) hx
  rw [← hnhds]
  exact hinc

private def conductor_finiteSupportTrunc (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then
      (Dictionary.ideleFiniteCoord v x : v.adicCompletion F) else 1,
    by
      filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ T := by simpa using hv
      simp [hv']⟩

private def conductor_ideleSupportTrunc (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) : NumberField.IdeleGroup (𝓞 F) F :=
  (∏ w ∈ Finset.univ,
      NumberField.IdeleGroup.ofCompletion (𝓞 F) F w (Dictionary.ideleInfiniteCoordUnit w x)) *
    ∏ v ∈ T, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (Dictionary.ideleFiniteCoord v x)

private theorem conductor_ideleSupportTrunc_infiniteCoord (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    Dictionary.ideleInfiniteCoord w (conductor_ideleSupportTrunc x T) =
      Dictionary.ideleInfiniteCoord w x := by
  have hunit : Dictionary.ideleInfiniteCoordUnit w (conductor_ideleSupportTrunc x T) =
      Dictionary.ideleInfiniteCoordUnit w x := by
    dsimp [conductor_ideleSupportTrunc]
    rw [map_mul, Dictionary.ideleInfiniteCoordUnit_finsetProduct]
    simp [Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion]
  exact congrArg Units.val hunit

private theorem conductor_ideleSupportTrunc_finiteCoord (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    (((conductor_ideleSupportTrunc x T : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).2 v) =
      conductor_finiteSupportTrunc x T v := by
  classical
  have hcoord : Dictionary.ideleFiniteCoord v (conductor_ideleSupportTrunc x T) =
      if v ∈ T then Dictionary.ideleFiniteCoord v x else 1 := by
    dsimp [conductor_ideleSupportTrunc]
    rw [map_mul]
    have hleft : Dictionary.ideleFiniteCoord v
        (∏ w ∈ Finset.univ,
          NumberField.IdeleGroup.ofCompletion (𝓞 F) F w (Dictionary.ideleInfiniteCoordUnit w x)) = 1 := by
      simp [Dictionary.ideleFiniteCoord_ofCompletion]
    rw [hleft, one_mul, Dictionary.ideleFiniteCoord_finsetProduct]
  calc
    (((conductor_ideleSupportTrunc x T : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).2 v) =
        ((Dictionary.ideleFiniteCoord v (conductor_ideleSupportTrunc x T) :
          (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
      (Dictionary.ideleFiniteCoord_apply v _).symm
    _ = (if v ∈ T then
          (Dictionary.ideleFiniteCoord v x : (v.adicCompletion F)ˣ) else 1) :=
            congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hcoord
    _ = conductor_finiteSupportTrunc x T v := by
      have heval : conductor_finiteSupportTrunc x T v =
          (if v ∈ T then
            (Dictionary.ideleFiniteCoord v x : v.adicCompletion F) else 1) := rfl
      rw [heval]
      by_cases h : v ∈ T <;> simp [h]

private theorem conductor_ideleSupportTrunc_coe (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    (conductor_ideleSupportTrunc x T : AdeleRing (𝓞 F) F) =
      ((x : AdeleRing (𝓞 F) F).1, conductor_finiteSupportTrunc x T) := by
  apply Prod.ext
  · funext w
    exact conductor_ideleSupportTrunc_infiniteCoord x T w
  · apply DFunLike.ext
    intro v
    exact conductor_ideleSupportTrunc_finiteCoord x T v

private theorem conductor_finiteSupportTrunc_tendsto (x : NumberField.IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => conductor_finiteSupportTrunc x T)
      atTop (𝓝 ((x : AdeleRing (𝓞 F) F).2)) := by
  change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (⟨fun v => if v ∈ T then ((x : AdeleRing (𝓞 F) F).2 v) else 1,
        by
          filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
          have hv' : v ∉ T := by simpa using hv
          simp [hv']⟩ : Πʳ v : HeightOneSpectrum (𝓞 F),
            [v.adicCompletion F, v.adicCompletionIntegers F])) atTop
      (@nhds (Πʳ v : HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F])
        (RestrictedProduct.topologicalSpace
          (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => v.adicCompletionIntegers F) cofinite)
        ((x : AdeleRing (𝓞 F) F).2))
  exact conductor_rp_truncate (hA := fun v => by simp)
    ((x : AdeleRing (𝓞 F) F).2)

private theorem conductor_ideleSupportTrunc_inv (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    (conductor_ideleSupportTrunc x T)⁻¹ = conductor_ideleSupportTrunc x⁻¹ T := by
  classical
  simp [conductor_ideleSupportTrunc, map_inv, Finset.prod_inv_distrib]
  ac_rfl

private theorem conductor_ideleSupportTrunc_coe_tendsto (x : NumberField.IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (conductor_ideleSupportTrunc x T : AdeleRing (𝓞 F) F)) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F))) := by
  have hprod : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((x : AdeleRing (𝓞 F) F).1, conductor_finiteSupportTrunc x T)) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F).1, (x : AdeleRing (𝓞 F) F).2)) :=
    (Prod.tendsto_iff _ _).2 ⟨tendsto_const_nhds, conductor_finiteSupportTrunc_tendsto x⟩
  have hfun : (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (conductor_ideleSupportTrunc x T : AdeleRing (𝓞 F) F)) =
      fun T => ((x : AdeleRing (𝓞 F) F).1, conductor_finiteSupportTrunc x T) := by
    funext T
    exact conductor_ideleSupportTrunc_coe x T
  rw [hfun]
  have hxpair : (x : AdeleRing (𝓞 F) F) =
      ((x : AdeleRing (𝓞 F) F).1, (x : AdeleRing (𝓞 F) F).2) := by
    cases x
    rfl
  rw [hxpair]
  exact hprod

private theorem conductor_tendsto_ideleSupportTrunc (x : NumberField.IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => conductor_ideleSupportTrunc x T)
      atTop (𝓝 x) := by
  classical
  have hval := conductor_ideleSupportTrunc_coe_tendsto x
  have hvalInv : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (((conductor_ideleSupportTrunc x T)⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F))
      atTop (𝓝 ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)) := by
    simpa only [conductor_ideleSupportTrunc_inv] using
      conductor_ideleSupportTrunc_coe_tendsto (x⁻¹)
  have hvalInvOp : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      MulOpposite.op (((conductor_ideleSupportTrunc x T)⁻¹ : NumberField.IdeleGroup (𝓞 F) F) :
        AdeleRing (𝓞 F) F)) atTop
      (𝓝 (MulOpposite.op ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F))) :=
    (MulOpposite.opHomeomorph.continuous.tendsto
      ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)).comp hvalInv
  have hEmbed : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      Units.embedProduct (AdeleRing (𝓞 F) F) (conductor_ideleSupportTrunc x T)) atTop
      (𝓝 (Units.embedProduct (AdeleRing (𝓞 F) F) x)) := by
    change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((conductor_ideleSupportTrunc x T : AdeleRing (𝓞 F) F),
        MulOpposite.op (((conductor_ideleSupportTrunc x T)⁻¹ : NumberField.IdeleGroup (𝓞 F) F) :
          AdeleRing (𝓞 F) F))) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F),
        MulOpposite.op ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)))
    rw [Prod.tendsto_iff]
    exact ⟨hval, hvalInvOp⟩
  exact Units.isEmbedding_embedProduct.tendsto_nhds_iff.mpr hEmbed

private theorem conductor_heckeChar_idealValue_eq_LS_of_gen
    (D : FieldData F) (S : SData F CE condη) (χ : HeckeChar F)
    (hχ : ∀ v : FinPlace F, v ∉ S.Sf → χ.UnramifiedAt v)
    (I : Ideal (𝓞 F)) (a : Fˣ) (ha : S.IsGen (a : F) I) :
    χ.idealValue I = S.LS χ (S.diagU a) := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 F)) := S.Sf ∪ conductor_factorPlaces I
  let x : NumberField.IdeleGroup (𝓞 F) F := NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a
  let q : NumberField.IdeleGroup (𝓞 F) F →* IdeleClassGroup (𝓞 F) F :=
    QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)
  let ψ : NumberField.IdeleGroup (𝓞 F) F →* ℂˣ :=
    (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp q
  let locLocal (v : FinPlace F) : ℂˣ := χ.loc v (toLoc v a)
  let infLocal (w : InfinitePlace F) : ℂˣ :=
    χ.locInf w (Dictionary.ideleInfiniteCoordUnit w x)
  let finS : ℂˣ := ∏ v : S.Sf, locLocal v.1
  let infS : ℂˣ := ∏ w : InfinitePlace F, infLocal w
  let factorLocal : ℂˣ :=
    ∏ v ∈ conductor_factorPlaces I,
      χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ idealExp v I
  have hprincipalClass : q x = 1 := by
    change (x : NumberField.IdeleGroup (𝓞 F) F ⧸ NumberField.IdeleGroup.principalSubgroup (𝓞 F) F) = 1
    exact (QuotientGroup.eq_one_iff
      (N := NumberField.IdeleGroup.principalSubgroup (𝓞 F) F) x).mpr (by
        change x ∈ (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F).range
        exact ⟨a, rfl⟩)
  have hprincipal : ψ x = 1 := by
    change χ (q x) = 1
    rw [hprincipalClass, map_one]
  have hψcont : Continuous (fun z : NumberField.IdeleGroup (𝓞 F) F => ψ z) := by
    dsimp [ψ, q]
    exact χ.continuous.comp continuous_quotient_mk'
  have hcoord : ∀ v : FinPlace F,
      Dictionary.ideleFiniteCoord v x = toLoc v a := by
    intro v
    apply Units.ext
    rfl
  have hEval (U : Finset (HeightOneSpectrum (𝓞 F))) :
      ψ (conductor_ideleSupportTrunc x U) =
        (∏ w : InfinitePlace F, infLocal w) * ∏ v ∈ U, locLocal v := by
    calc
      ψ (conductor_ideleSupportTrunc x U) =
          ψ ((∏ w ∈ Finset.univ,
            NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
              (Dictionary.ideleInfiniteCoordUnit w x)) *
            ∏ v ∈ U, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v
              (Dictionary.ideleFiniteCoord v x)) := rfl
      _ = ψ (∏ w ∈ Finset.univ,
            NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
              (Dictionary.ideleInfiniteCoordUnit w x)) *
          ψ (∏ v ∈ U, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v
              (Dictionary.ideleFiniteCoord v x)) := map_mul ψ _ _
      _ = (∏ w : InfinitePlace F, infLocal w) *
          ∏ v ∈ U, χ.loc v (Dictionary.ideleFiniteCoord v x) := by
            rw [map_prod, map_prod]
            rfl
      _ = (∏ w : InfinitePlace F, infLocal w) * ∏ v ∈ U, locLocal v := by
            apply congrArg (fun z : ℂˣ => (∏ w : InfinitePlace F, infLocal w) * z)
            apply Finset.prod_congr rfl
            intro v hv
            rw [hcoord v]
  have htruncLimit : Tendsto (fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
      ψ (conductor_ideleSupportTrunc x U)) atTop (𝓝 (1 : ℂˣ)) := by
    have hlim := hψcont.continuousAt.tendsto.comp
      (conductor_tendsto_ideleSupportTrunc x)
    have hfun : ((fun z => ψ z) ∘ fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
        conductor_ideleSupportTrunc x U) = fun U => ψ (conductor_ideleSupportTrunc x U) := by
      funext U
      rfl
    rw [hfun] at hlim
    simpa [hprincipal] using hlim
  have hlocOne (v : FinPlace F) (hv : v ∉ T) : locLocal v = 1 := by
    have hvS : v ∉ S.Sf := by
      intro h
      exact hv (Finset.mem_union_left _ h)
    have hvF : v ∉ conductor_factorPlaces I := by
      intro h
      exact hv (Finset.mem_union_right _ h)
    have hexp := conductor_exp_zero_of_not_factor I ha.1.1 v hvF
    have hloc := conductor_loc_gen_factor_unit S χ hχ I a ha v hvS
    simpa [locLocal, hexp] using hloc
  have hprodEventually :
      (fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
        ψ (conductor_ideleSupportTrunc x U)) =ᶠ[atTop]
        fun _ => ψ (conductor_ideleSupportTrunc x T) := by
    filter_upwards [eventually_atTop.2 ⟨T, fun U hTU => hTU⟩] with U hTU
    have hlocalProd : (∏ v ∈ U, locLocal v) = ∏ v ∈ T, locLocal v :=
      (Finset.prod_subset hTU (fun v hvU hvT => hlocOne v hvT)).symm
    rw [hEval U, hEval T, hlocalProd]
  have htruncOne : ψ (conductor_ideleSupportTrunc x T) = 1 := by
    have hconst : Tendsto (fun _ : Finset (HeightOneSpectrum (𝓞 F)) =>
        ψ (conductor_ideleSupportTrunc x T)) atTop (𝓝 (1 : ℂˣ)) :=
      htruncLimit.congr' hprodEventually
    exact (tendsto_nhds_unique hconst tendsto_const_nhds).symm
  have hdisj : Disjoint S.Sf (conductor_factorPlaces I) := by
    rw [Finset.disjoint_left]
    intro v hvS hvF
    have hdvd := conductor_factorPlaces_dvd I v hvF
    exact (ha.1.2 v hvS) (Ideal.le_of_dvd hdvd)
  have hfactorGenerator :
      (∏ v ∈ conductor_factorPlaces I, locLocal v) = factorLocal := by
    apply Finset.prod_congr rfl
    intro v hvF
    have hvS : v ∉ S.Sf := by
      intro hv
      exact (ha.1.2 v hv) (Ideal.le_of_dvd (conductor_factorPlaces_dvd I v hvF))
    exact conductor_loc_gen_factor_unit S χ hχ I a ha v hvS
  have htruncProduct : infS * finS * factorLocal = 1 := by
    have h := htruncOne
    rw [hEval T] at h
    change (∏ w : InfinitePlace F, infLocal w) *
      (∏ v ∈ T, locLocal v) = 1 at h
    rw [show T = S.Sf ∪ conductor_factorPlaces I by rfl,
      Finset.prod_union hdisj, hfactorGenerator] at h
    have hattach : (∏ v ∈ S.Sf, locLocal v) = finS :=
      (Finset.prod_attach S.Sf locLocal).symm
    rw [hattach] at h
    change infS * (finS * factorLocal) = 1 at h
    simpa [mul_assoc] using h
  have hfactorSupport : Function.mulSupport
      (fun v : FinPlace F => χ.primeValue v ^ idealExp v I) ⊆ conductor_factorPlaces I := by
    intro v hv
    change χ.primeValue v ^ idealExp v I ≠ 1 at hv
    by_contra hnot
    have hexp := conductor_exp_zero_of_not_factor I ha.1.1 v hnot
    simp [hexp] at hv
  have hprimeValue (v : FinPlace F) (hvF : v ∈ conductor_factorPlaces I) :
      χ.primeValue v =
        ((χ.loc v (toLoc v
          (Units.mk0 (unif v) (unif_ne_zero v))) : ℂˣ) : ℂ) := by
    have hvS : v ∉ S.Sf := by
      intro hv
      exact (ha.1.2 v hv) (Ideal.le_of_dvd (conductor_factorPlaces_dvd I v hvF))
    simp [HeckeChar.primeValue, hχ v hvS]
  have hidealValue : χ.idealValue I = (factorLocal : ℂ) := by
    rw [conductor_idealValue_finprod χ I ha.1.1]
    rw [finprod_eq_prod_of_mulSupport_subset _ hfactorSupport]
    change (∏ v ∈ conductor_factorPlaces I,
      χ.primeValue v ^ idealExp v I) = (factorLocal : ℂ)
    calc
      _ = ∏ v ∈ conductor_factorPlaces I,
          ((χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^
              idealExp v I : ℂˣ) : ℂ) := by
          apply Finset.prod_congr rfl
          intro v hv
          rw [hprimeValue v hv]
          simp [Units.val_pow_eq_pow_val]
      _ = (factorLocal : ℂ) := by
          dsimp [factorLocal]
          exact (conductor_units_val_prod (conductor_factorPlaces I)
            (fun v : FinPlace F =>
              χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ idealExp v I)).symm
  have hcompU (v : S.Sf) : S.compU v (S.diagU a) = toLoc v.1 a := by
    ext
    rfl
  have hcompC (w : InfinitePlace F) (hw : w.IsComplex) :
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
          (S.compC w (S.diagU a)) =
        Dictionary.ideleInfiniteCoordUnit w x :=
    conductor_idele_inf_comp D S a w
  have hLS : S.LS χ (S.diagU a) = ((finS⁻¹ * infS⁻¹ : ℂˣ) : ℂ) := by
    have hfinite :
        (∏ v : S.Sf,
          (((χ.loc v.1 (S.compU v (S.diagU a)))⁻¹ : ℂˣ) : ℂ)) =
            ((finS⁻¹ : ℂˣ) : ℂ) := by
      simp [finS, locLocal, hcompU, Finset.prod_inv_distrib]
    let complexComp (w : InfinitePlace F) (hw : w.IsComplex) : w.Completionˣ :=
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
        (S.compC w (S.diagU a))
    have hterm (w : InfinitePlace F) :
        (if hw : w.IsComplex then
          (((χ.locInf w (complexComp w hw))⁻¹ : ℂˣ) : ℂ)
         else 1) = (((infLocal w)⁻¹ : ℂˣ) : ℂ) := by
      let hw : w.IsComplex := D.isTotallyComplex.isComplex w
      have hcomp : complexComp w hw = Dictionary.ideleInfiniteCoordUnit w x := hcompC w hw
      rw [dif_pos hw]
      change (((χ.locInf w (complexComp w hw))⁻¹ : ℂˣ) : ℂ) =
        (((infLocal w)⁻¹ : ℂˣ) : ℂ)
      rw [hcomp]
    have hinfinite :
        (∏ w : InfinitePlace F,
          if hw : w.IsComplex then
            (((χ.locInf w (complexComp w hw))⁻¹ : ℂˣ) : ℂ)
          else 1) = ((infS⁻¹ : ℂˣ) : ℂ) := by
      calc
        _ = ∏ w : InfinitePlace F, (((infLocal w)⁻¹ : ℂˣ) : ℂ) :=
          Finset.prod_congr rfl (fun w _ => hterm w)
        _ = ((∏ w : InfinitePlace F, (infLocal w)⁻¹ : ℂˣ) : ℂ) := by
          rw [← conductor_units_val_prod Finset.univ (fun w => (infLocal w)⁻¹)]
        _ = ((infS⁻¹ : ℂˣ) : ℂ) := by simp [infS, Finset.prod_inv_distrib]
    unfold SData.LS
    rw [hfinite, hinfinite]
    simp
  have hfactorEq : factorLocal = finS⁻¹ * infS⁻¹ := by
    have hp : factorLocal * (finS * infS) = 1 := by
      calc
        factorLocal * (finS * infS) = infS * finS * factorLocal := by ac_rfl
        _ = 1 := htruncProduct
    calc
      factorLocal = factorLocal * ((finS * infS) * (finS * infS)⁻¹) := by simp
      _ = (factorLocal * (finS * infS)) * (finS * infS)⁻¹ := by group
      _ = (finS * infS)⁻¹ := by rw [hp]; simp
      _ = finS⁻¹ * infS⁻¹ := by simp [mul_comm]
  calc
    χ.idealValue I = (factorLocal : ℂ) := hidealValue
    _ = ((finS⁻¹ * infS⁻¹ : ℂˣ) : ℂ) := congrArg Units.val hfactorEq
    _ = S.LS χ (S.diagU a) := hLS.symm

private theorem hecke_locInf_eq_one_of_finite_order
    (D : FieldData F) (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (w : InfinitePlace F) (z : ℂˣ) :
    χ.locInf w
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z) = 1 := by
  classical
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hχ
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)
  let eh := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)
  let toCompletion : ℂˣ → w.Completionˣ := Units.map e.symm.toMonoidHom
  let f : ℂˣ → ℂˣ := fun x => χ.locInf w (toCompletion x)
  have htoCompletion : Continuous toCompletion := by
    apply Units.continuous_iff.mpr
    change Continuous (fun x : ℂˣ => e.symm (x : ℂ)) ∧
      Continuous (fun x : ℂˣ => e.symm (((x⁻¹ : ℂˣ) : ℂ)))
    exact ⟨(eh.symm.isometry_toFun.continuous).comp Units.continuous_val,
      (eh.symm.isometry_toFun.continuous).comp Units.continuous_coe_inv⟩
  have hloc : Continuous (χ.locInf w) := by
    change Continuous (fun u : w.Completionˣ =>
      χ (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
    exact χ.continuous.comp (IdeleClassGroup.continuous_ofCompletion (𝓞 F) F w)
  have hf : Continuous f := hloc.comp htoCompletion
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hroot : (Set.univ : Set (rootsOfUnity n ℂ)).Finite := Set.finite_univ
  let T : Set ℂˣ := (fun x : rootsOfUnity n ℂ => (x : ℂˣ)) '' Set.univ
  have hT : T.Finite := hroot.image _
  have hTdisc : IsDiscrete T := hT.isDiscrete
  have hpoint (x : ℂˣ) : f x ^ n = 1 := by
    have heval := congrArg (fun ψ : HeckeChar F => ψ
      (IdeleClassGroup.ofCompletion (𝓞 F) F w (toCompletion x))) hpow
    simpa [f, HeckeChar.locInf] using heval
  have hmaps : Set.MapsTo f Set.univ T := by
    intro x _
    change f x ∈ (fun y : rootsOfUnity n ℂ => (y : ℂˣ)) '' Set.univ
    exact ⟨⟨f x, hpoint x⟩, Set.mem_univ _, rfl⟩
  have hconst : f z = f 1 :=
    (isPreconnected_univ : IsPreconnected (Set.univ : Set ℂˣ)).constant_of_mapsTo
      hTdisc hf.continuousOn hmaps (Set.mem_univ z) (Set.mem_univ 1)
  simpa [f, toCompletion] using hconst

/-- eq:vartheta-s (02:615–625): `ϑ(𝔞) = L_S(a)` for every generator, `L_S = 1` on `U_S`, angular
type `±1` at complex places, and `γ_1γ_2ϑ = -η` at exterior primes. Package P-ARITH-GAUSS.
Corrected per rev-theta to require the finite-order and angular hypotheses used by the lemma; C5 of
`sol-gate-theta` also requires the three characters to be unramified outside `S`. -/
theorem vartheta_S (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (H : HilbertData F)
    (Bd : BData S H) (η Λ G : HeckeChar F)
    (hηram : ∀ v : FinPlace F, v ∉ S.Sf → η.UnramifiedAt v)
    (hΛram : ∀ v : FinPlace F, v ∉ S.Sf → Λ.UnramifiedAt v)
    (hGram : ∀ v : FinPlace F, v ∉ S.Sf → G.UnramifiedAt v)
    (hη : IsOfFinOrder η) (hG : IsOfFinOrder G)
    (hΛunitary : ∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1)
    (hΛangular : HeckeChar.HasAngularType D Λ)
    (hΛG : ∀ v : FinPlace F, v ∉ S.Sf → ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
      gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p =
        -(Λ.primeValue v * G.primeValue v)) :
    (∀ (I : Ideal (𝓞 F)) (a : Fˣ), S.IsExterior I → S.IsGen (a : F) I →
      (vartheta Λ G η).idealValue I = S.LS (vartheta Λ G η) (S.diagU a)) ∧
    (∀ ε ∈ S.US, S.LS (vartheta Λ G η) (S.diagU ε) = 1) ∧
    (∀ w : InfinitePlace F, ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ ∀ z : ℂˣ,
      S.LS (vartheta Λ G η) (S.atComplex w z) = ((z : ℂ) / ‖(z : ℂ)‖) ^ m) ∧
    (∀ v : FinPlace F, v ∉ S.Sf → ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
      gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p * (vartheta Λ G η).primeValue v =
        -η.primeValue v) := by
  classical
  have hvarthetaRam : ∀ v : FinPlace F, v ∉ S.Sf → (vartheta Λ G η).UnramifiedAt v := by
    intro v hv u hu huinv
    change (Λ.loc v u)⁻¹ * (G.loc v u)⁻¹ * η.loc v u = 1
    rw [hΛram v hv u hu huinv, hGram v hv u hu huinv, hηram v hv u hu huinv]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I a hI ha
    exact conductor_heckeChar_idealValue_eq_LS_of_gen D S (vartheta Λ G η)
      hvarthetaRam I a ha
  · intro ε hε
    let εUS : S.US := ⟨ε, hε⟩
    have htop : S.IsExterior (⊤ : Ideal (𝓞 F)) := by
      refine ⟨top_ne_bot, ?_⟩
      intro v hv hle
      exact v.isPrime.ne_top (top_le_iff.mp hle)
    have hgen : S.IsGen ((ε : Fˣ) : F) ⊤ := by
      refine ⟨htop, Units.ne_zero (ε : Fˣ), ?_⟩
      intro v hv
      have hval : HeightOneSpectrum.valuation F v ((ε : Fˣ) : F) = 1 :=
        εUS.property v hv
      rw [ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
        v ((ε : Fˣ) : F) (Units.ne_zero (ε : Fˣ)), hval]
      simpa using (FractionalIdeal.count_one F v).symm
    have hLS := conductor_heckeChar_idealValue_eq_LS_of_gen D S
      (vartheta Λ G η) hvarthetaRam ⊤ (ε : Fˣ) hgen
    have htop1 : (⊤ : Ideal (𝓞 F)) = 1 := by
      ext x
      simp
    have htopValue : (vartheta Λ G η).idealValue ⊤ = 1 := by
      unfold HeckeChar.idealValue
      have hnorm : UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
        calc
          UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) =
              UniqueFactorizationMonoid.normalizedFactors (1 : Ideal (𝓞 F)) :=
                congrArg UniqueFactorizationMonoid.normalizedFactors htop1
          _ = 0 := UniqueFactorizationMonoid.normalizedFactors_one
      rw [hnorm]
      simp
    calc
      S.LS (vartheta Λ G η) (S.diagU ε) = (vartheta Λ G η).idealValue ⊤ := hLS.symm
      _ = 1 := htopValue
  · intro w
    obtain ⟨m, hm, hangular⟩ := hΛangular w
    refine ⟨m, hm, ?_⟩
    intro z
    let hw : w.IsComplex := D.isTotallyComplex.isComplex w
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    have hcompU (v : S.Sf) : S.compU v (S.atComplex w z) = 1 := by
      apply Units.ext
      rfl
    have hcompC (w' : InfinitePlace F) :
        S.compC w' (S.atComplex w z) = if w' = w then z else 1 := by
      by_cases h : w' = w
      · subst w'
        apply Units.ext
        simp [SData.compC, SData.atComplex]
      · apply Units.ext
        simp [SData.compC, SData.atComplex, h]
    have hfinite :
        (∏ v : S.Sf,
          (((((vartheta Λ G η).loc v.1 (S.compU v (S.atComplex w z)))⁻¹ : ℂˣ) : ℂ))) = 1 := by
      simp [hcompU]
    let zc : w.Completionˣ := Units.map e.symm.toMonoidHom z
    let localAt (w' : InfinitePlace F) (hw' : w'.IsComplex) : ℂˣ :=
      (vartheta Λ G η).locInf w'
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm.toMonoidHom
          (S.compC w' (S.atComplex w z)))
    have hterm (w' : InfinitePlace F) :
        (if hw' : w'.IsComplex then
          (((localAt w' hw')⁻¹ : ℂˣ) : ℂ) else 1) =
          if w' = w then ((Λ.locInf w zc : ℂˣ) : ℂ) else 1 := by
      let hw' : w'.IsComplex := D.isTotallyComplex.isComplex w'
      rw [dif_pos hw']
      by_cases h : w' = w
      · subst w'
        have hηloc := hecke_locInf_eq_one_of_finite_order D η hη w z
        have hGloc := hecke_locInf_eq_one_of_finite_order D G hG w z
        have hηval : η (IdeleClassGroup.ofCompletion (𝓞 F) F w zc) = 1 := by
          change η.locInf w zc = 1
          exact hηloc
        have hGval : G (IdeleClassGroup.ofCompletion (𝓞 F) F w zc) = 1 := by
          change G.locInf w zc = 1
          exact hGloc
        have hθloc : (vartheta Λ G η).locInf w zc = (Λ.locInf w zc)⁻¹ := by
          change (Λ (IdeleClassGroup.ofCompletion (𝓞 F) F w zc))⁻¹ *
            (G (IdeleClassGroup.ofCompletion (𝓞 F) F w zc))⁻¹ *
            η (IdeleClassGroup.ofCompletion (𝓞 F) F w zc) =
              (Λ (IdeleClassGroup.ofCompletion (𝓞 F) F w zc))⁻¹
          rw [hηval, hGval]
          simp
        have hlocal : localAt w hw = (Λ.locInf w zc)⁻¹ := by
          dsimp [localAt]
          rw [hcompC]
          simpa [zc] using hθloc
        simp [hlocal]
      · have hz1 : S.compC w' (S.atComplex w z) = 1 := by
          rw [hcompC]
          simp [h]
        have hlocal : localAt w' hw' = 1 := by
          dsimp [localAt]
          rw [hcompC]
          simp [h, hz1]
        simp [h, hlocal]
    have hinfinite :
        (∏ w' : InfinitePlace F,
          if hw' : w'.IsComplex then
            (((localAt w' hw')⁻¹ : ℂˣ) : ℂ) else 1) =
          ((Λ.locInf w zc : ℂˣ) : ℂ) := by
      calc
        _ = ∏ w' : InfinitePlace F, (if w' = w then ((Λ.locInf w zc : ℂˣ) : ℂ) else 1) :=
          Finset.prod_congr rfl (fun w' _ => hterm w')
        _ = ((Λ.locInf w zc : ℂˣ) : ℂ) := by
          rw [Finset.prod_eq_single w]
          · simp
          · intro w' hw' hne
            simp [hne]
          · simp
    unfold SData.LS
    rw [hfinite, hinfinite, one_mul]
    exact hangular z
  · intro v hv p hpgen hpAllowed
    let π : (v.adicCompletion F)ˣ := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
    have hloc : (vartheta Λ G η).loc v π =
        (Λ.loc v π)⁻¹ * (G.loc v π)⁻¹ * η.loc v π := by
      let y := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
      have hinv (χ : HeckeChar F) : χ⁻¹ y = (χ y)⁻¹ := rfl
      change (Λ⁻¹ * G⁻¹ * η)
          (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π) =
        (Λ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π))⁻¹ *
          (G (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π))⁻¹ *
            η (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π)
      rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.mul_apply,
        hinv Λ, hinv G]
    have hΛpv : Λ.primeValue v = ((Λ.loc v π : ℂˣ) : ℂ) := by
      simp [HeckeChar.primeValue, π, hΛram v hv]
    have hGpv : G.primeValue v = ((G.loc v π : ℂˣ) : ℂ) := by
      simp [HeckeChar.primeValue, π, hGram v hv]
    have hηpv : η.primeValue v = ((η.loc v π : ℂˣ) : ℂ) := by
      simp [HeckeChar.primeValue, π, hηram v hv]
    have hprime : (vartheta Λ G η).primeValue v =
        (Λ.primeValue v * G.primeValue v)⁻¹ * η.primeValue v := by
      change (if (vartheta Λ G η).UnramifiedAt v then
        (((vartheta Λ G η).loc v π : ℂˣ) : ℂ) else 0) = _
      rw [if_pos (hvarthetaRam v hv), hloc, hΛpv, hGpv, hηpv]
      simp [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev]
      ring
    have hΛne : Λ.primeValue v ≠ 0 := by
      rw [HeckeChar.primeValue, if_pos (hΛram v hv)]
      exact Units.ne_zero _
    have hGne : G.primeValue v ≠ 0 := by
      rw [HeckeChar.primeValue, if_pos (hGram v hv)]
      exact Units.ne_zero _
    rw [hprime, hΛG v hv p hpgen hpAllowed]
    change -(Λ.primeValue v * G.primeValue v) *
      ((Λ.primeValue v * G.primeValue v)⁻¹ * η.primeValue v) = -η.primeValue v
    calc
      -(Λ.primeValue v * G.primeValue v) *
          ((Λ.primeValue v * G.primeValue v)⁻¹ * η.primeValue v) =
        -((Λ.primeValue v * G.primeValue v) *
          ((Λ.primeValue v * G.primeValue v)⁻¹ * η.primeValue v)) := by simp
      _ = -η.primeValue v := by simp [mul_assoc, hΛne, hGne]


end ArtinPrimitiveRoots.A1
