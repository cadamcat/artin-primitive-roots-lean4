import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Types
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ResidueCompatibility

/-! Continuity and unramifiedness of local sextic Hilbert characters. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem kummer_local_continuous (D : FieldData F) (H : HilbertData F)
    (P : FinPlace F) (a : (P.adicCompletion F)ˣ) :
    Continuous (kummerLocal D H P a) := by
  let L := P.adicCompletion F
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  let x : L := NumberField.FinitePlace.embedding P (algebraMap (𝓞 F) F t)
  have htF : algebraMap (𝓞 F) F t ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ht0
  have hx0 : x ≠ 0 := (NumberField.FinitePlace.embedding P).injective.ne htF
  have hxnorm : ‖x‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem (K := F) P t).mpr ht
  letI : NontriviallyNormedField L :=
    NontriviallyNormedField.ofNormNeOne ⟨x, hx0, ne_of_lt hxnorm⟩
  have h6 : (6 : L) ≠ 0 := by
    intro h
    have hF : (6 : F) = 0 := (algebraMap F L).injective
      (by simpa only [map_ofNat, map_zero] using h)
    exact (by norm_num : (6 : F) ≠ 0) hF
  have hs : {u : Lˣ | ∃ b : Lˣ, u = b ^ 6} ∈ 𝓝 (1 : Lˣ) := by
    have hd : HasStrictDerivAt (fun y : L => y ^ 6) (6 : L) 1 := by
      simpa using hasStrictDerivAt_pow 6 (1 : L)
    have hm : Filter.map (fun y : L => y ^ 6) (𝓝 1) = 𝓝 1 := by
      simpa using hd.map_nhds_eq h6
    have hp : {y : L | ∃ z : L, y = z ^ 6} ∈
        Filter.map (fun y : L => y ^ 6) (𝓝 1) :=
      Filter.mem_map.mpr (Filter.Eventually.of_forall (fun y => ⟨y, rfl⟩))
    rw [hm] at hp
    filter_upwards [(Units.continuous_val.tendsto (1 : Lˣ)).eventually hp] with u hu
    obtain ⟨y, hy⟩ := hu
    have hy0 : y ≠ 0 := by
      intro h
      apply Units.ne_zero u
      rw [hy, h, zero_pow (by decide : (6 : ℕ) ≠ 0)]
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    change (u : L) = y ^ 6
    exact hy
  let f : Lˣ →* ℂˣ := kummerLocal D H P a
  apply continuous_of_tendsto_nhds_one f
  have heq : (fun u : Lˣ => f u) =ᶠ[𝓝 (1 : Lˣ)] (fun _ => (1 : ℂˣ)) := by
    filter_upwards [hs] with u hu
    obtain ⟨b, rfl⟩ := hu
    rw [map_pow]
    change Units.map D.σ0.toMonoidHom (H.hilb P a b : Fˣ) ^ 6 = 1
    have hroot : (H.hilb P a b : Fˣ) ^ 6 = 1 :=
      (mem_rootsOfUnity 6 _).mp (H.hilb P a b).property
    rw [← map_pow, hroot, map_one]
  apply (Filter.tendsto_congr' heq).mpr
  exact tendsto_const_nhds

theorem kummer_local_unit_trivial (D : FieldData F) (H : HilbertData F)
    (P : FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal) (a : Fˣ)
    (ha : residue P (a : F) ≠ 0) (x : (P.adicCompletion F)ˣ)
    (hx : x ∈ (P.adicCompletionIntegers F).units) :
    kummerLocal D H P (toLoc P a) x = 1 := by
  classical
  let L := P.adicCompletion F
  let f : Lˣ →* ℂˣ := kummerLocal D H P (toLoc P a)
  have hglobal (b : Fˣ) (hb : P.valuation F (b : F) = 1) :
      f (toLoc P b) = 1 := by
    have hres : residue P (b : F) ≠ 0 :=
      (A2.qs_nq0_residue_ne_zero_iff_valuation_one P (b : F)).mpr hb
    have hcount := ((residue_ne_zero_iff_ord_zero P (b : F)).mp hres).1
    have htame := H.tame P h6 a b ha
    rw [hcount, zpow_zero] at htame
    have hhilb : H.hilb P (toLoc P a) (toLoc P b) = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact htame
    change Units.map D.σ0.toMonoidHom (H.hilb P (toLoc P a) (toLoc P b) : Fˣ) = 1
    rw [hhilb]
    simp
  have hf : Continuous f := kummer_local_continuous D H P (toLoc P a)
  have hO : IsOpen (P.adicCompletionIntegers F : Set L) :=
    Valued.isOpen_valuationSubring L
  have hOU : IsOpen {t : Lˣ | t ∈ (P.adicCompletionIntegers F).units} := by
    change IsOpen (((fun t : Lˣ => (t : L)) ⁻¹' (P.adicCompletionIntegers F : Set L)) ∩
      ((fun t : Lˣ => ((t⁻¹ : Lˣ) : L)) ⁻¹' (P.adicCompletionIntegers F : Set L)))
    exact (hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv)
  have hneq : IsOpen {t : Lˣ | f t ≠ 1} :=
    (isClosed_eq hf continuous_const).isOpen_compl
  by_contra hnu
  let U : Set Lˣ := {t | t ∈ (P.adicCompletionIntegers F).units ∧ f t ≠ 1}
  have hU : IsOpen U := hOU.inter hneq
  have himage : IsOpen (Units.val '' U) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap U hU
  obtain ⟨b, hb⟩ := (P.denseRange_algebraMap F).exists_mem_open himage
    ⟨(x : L), x, ⟨hx, hnu⟩, rfl⟩
  obtain ⟨t, ht, htb⟩ := hb
  have hb0 : b ≠ 0 := by
    intro h
    apply Units.ne_zero t
    simpa only [h, map_zero] using htb
  have htval : Valued.v (t : L) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ht.1
  have hbval : P.valuation F b = 1 := by
    calc
      P.valuation F b = Valued.v (algebraMap F L b) :=
        (P.valuedAdicCompletion_eq_valuation' b).symm
      _ = Valued.v (t : L) := congrArg Valued.v htb.symm
      _ = 1 := htval
  have htloc : t = toLoc P (Units.mk0 b hb0) := by
    apply Units.ext
    exact htb
  apply ht.2
  rw [htloc]
  exact hglobal (Units.mk0 b hb0) hbval

theorem kummer_local_eventually_unit_trivial
    (D : FieldData F) (H : HilbertData F) (a : Fˣ) :
    ∀ᶠ P : FinPlace F in Filter.cofinite,
      ∀ x : (P.adicCompletion F)ˣ,
        x ∈ (P.adicCompletionIntegers F).units →
          kummerLocal D H P (toLoc P a) x = 1 := by
  have hgood (b : Fˣ) :
      ∀ᶠ P : FinPlace F in Filter.cofinite, residue P (b : F) ≠ 0 := by
    apply Filter.eventually_cofinite.mpr
    simpa only [not_not] using residue_zero_finite b
  let six : Fˣ := Units.mk0 (6 : F) (by norm_num)
  filter_upwards [hgood a, hgood six] with P ha hP6
  have hv6 : P.valuation F (6 : F) = 1 :=
    (A2.qs_nq0_residue_ne_zero_iff_valuation_one P (6 : F)).mp hP6
  have h6 : (6 : 𝓞 F) ∉ P.asIdeal :=
    (P.valuation_eq_one_iff_notMem (K := F)).mp (by simpa only [map_ofNat] using hv6)
  intro x hx
  exact kummer_local_unit_trivial D H P h6 a ha x hx

end ArtinPrimitiveRoots.A1.KummerProofs
