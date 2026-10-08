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
  sorry

theorem kummer_local_eventually_unit_trivial
    (D : FieldData F) (H : HilbertData F) (a : Fˣ) :
    ∀ᶠ P : FinPlace F in Filter.cofinite,
      ∀ x : (P.adicCompletion F)ˣ,
        x ∈ (P.adicCompletionIntegers F).units →
          kummerLocal D H P (toLoc P a) x = 1 := by
  sorry

end ArtinPrimitiveRoots.A1.KummerProofs
