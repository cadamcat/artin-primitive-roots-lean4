import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F}

theorem continuedEis_localTorus_continuous
    {v : FinPlace F} (L : FinLocalCover D H v) : Continuous L.a := by
  let K := v.adicCompletion F
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let x : K := NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F t)
  have htF : algebraMap (𝓞 F) F t ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ht0
  have hx0 : x ≠ 0 := (NumberField.FinitePlace.embedding v).injective.ne htF
  have hxnorm : ‖x‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem (K := F) v t).mpr ht
  let : NontriviallyNormedField K :=
    NontriviallyNormedField.ofNormNeOne ⟨x, hx0, ne_of_lt hxnorm⟩
  have hOne : ContinuousAt L.a (1 : Kˣ) := by
    rw [ContinuousAt, L.a_one]
    apply Filter.tendsto_def.mpr
    intro U hU
    obtain ⟨m, hm, hsub⟩ := L.Kc_nhds U hU
    have hBallOpen : IsOpen (ball v (m : ℤ)) :=
      v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
    have hBallZero : (0 : K) ∈ ball v (m : ℤ) := by
      change Valued.v (0 : K) ≤ WithZero.exp (-(m : ℤ))
      rw [map_zero]
      exact zero_le
    have hDiff : Filter.Tendsto (fun u : Kˣ => (u : K) - 1)
        (𝓝 (1 : Kˣ)) (𝓝 (0 : K)) := by
      have hc : Continuous (fun u : Kˣ => (u : K) - (1 : K)) :=
        Units.continuous_val.sub continuous_const
      simpa using hc.tendsto (1 : Kˣ)
    filter_upwards [hDiff.eventually (hBallOpen.mem_nhds hBallZero)] with u hu
    exact hsub (L.a_Kc m hm u hu)
  have h6 : (6 : K) ≠ 0 := by
    intro h
    have hF : (6 : F) = 0 := (algebraMap F K).injective
      (by simpa only [map_ofNat, map_zero] using h)
    exact (by norm_num : (6 : F) ≠ 0) hF
  have hPowers : {u : Kˣ | ∃ b : Kˣ, u = b ^ 6} ∈ 𝓝 (1 : Kˣ) := by
    have hd : HasStrictDerivAt (fun y : K => y ^ 6) (6 : K) 1 := by
      simpa using hasStrictDerivAt_pow 6 (1 : K)
    have hm : Filter.map (fun y : K => y ^ 6) (𝓝 1) = 𝓝 1 := by
      simpa using hd.map_nhds_eq h6
    have hp : {y : K | ∃ b : K, y = b ^ 6} ∈
        Filter.map (fun y : K => y ^ 6) (𝓝 1) :=
      Filter.mem_map.mpr (Filter.Eventually.of_forall fun y => ⟨y, rfl⟩)
    rw [hm] at hp
    filter_upwards [(Units.continuous_val.tendsto (1 : Kˣ)).eventually hp] with u hu
    obtain ⟨b, hb⟩ := hu
    have hb0 : b ≠ 0 := by
      intro h
      apply Units.ne_zero u
      rw [hb, h, zero_pow (by norm_num : (6 : ℕ) ≠ 0)]
    refine ⟨Units.mk0 b hb0, ?_⟩
    apply Units.ext
    exact hb
  apply continuous_iff_continuousAt.mpr
  intro u
  have hDelta : Filter.Tendsto (fun y : Kˣ => u⁻¹ * y)
      (𝓝 u) (𝓝 (1 : Kˣ)) := by
    have hc : Continuous (fun y : Kˣ => u⁻¹ * y) :=
      continuous_const.mul continuous_id
    simpa using hc.tendsto u
  have hLift : Filter.Tendsto (fun y : Kˣ => L.a (u⁻¹ * y))
      (𝓝 u) (𝓝 (1 : L.L)) := by
    simpa only [Function.comp_def, L.a_one] using hOne.tendsto.comp hDelta
  have hModel : Filter.Tendsto (fun y : Kˣ => L.a u * L.a (u⁻¹ * y))
      (𝓝 u) (𝓝 (L.a u)) := by
    simpa only [mul_one] using tendsto_const_nhds.mul hLift
  have hEq : L.a =ᶠ[𝓝 u] (fun y : Kˣ => L.a u * L.a (u⁻¹ * y)) := by
    filter_upwards [hDelta.eventually hPowers] with y hy
    have hHilbRev : H.hilb v (u⁻¹ * y) u = 1 := H.sixth_power v _ _ hy
    have hHilb : H.hilb v u (u⁻¹ * y) = 1 := by
      simpa only [hHilbRev, mul_one] using H.skew v u (u⁻¹ * y)
    have hMuOne : muThree D (1 : rootsOfUnity 6 F) = 1 := by
      apply rootsOfUnity.coe_injective
      simp [muThree]
    have hMul := L.a_mul u (u⁻¹ * y)
    rw [hHilb, hMuOne, map_one, one_mul] at hMul
    simpa only [mul_inv_cancel_left] using hMul.symm
  exact (Filter.tendsto_congr' hEq).mpr hModel

end ArtinPrimitiveRoots.A1.Theta
