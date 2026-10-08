import ArtinPrimitiveRoots.Proofs.th_continue_b.TorusLocal

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem continuedEis_finiteTorus_eventually_level
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I)
    (r : P.RP) (y0 : S.FSˣ) :
    ∀ᶠ y in 𝓝 y0, ∀ v : S.Sf,
      (P.compF v.1 r)⁻¹ *
        (((P.loc v.1).a (S.compU v y0))⁻¹ *
          (P.loc v.1).a (S.compU v y)) * P.compF v.1 r ∈
        (P.loc v.1).Kc (C.m v.1) := by
  classical
  apply Filter.eventually_all.mpr
  intro v
  have hU : Continuous (S.compU v) := by
    unfold SData.compU
    apply Continuous.units_map
    exact (continuous_apply v).comp continuous_fst
  have hA : Continuous (fun y : S.FSˣ => (P.loc v.1).a (S.compU v y)) :=
    (continuedEis_localTorus_continuous (P.loc v.1)).comp hU
  let f (y : S.FSˣ) : (P.loc v.1).L :=
    (P.compF v.1 r)⁻¹ *
      (((P.loc v.1).a (S.compU v y0))⁻¹ *
        (P.loc v.1).a (S.compU v y)) * P.compF v.1 r
  have hF : Continuous f :=
    (continuous_const.mul (continuous_const.mul hA)).mul continuous_const
  have hF0 : f y0 = 1 := by
    simp only [f, inv_mul_cancel, mul_one]
  have hK : ((P.loc v.1).Kc (C.m v.1) : Set (P.loc v.1).L) ∈ 𝓝 (f y0) := by
    rw [hF0]
    exact ((P.loc v.1).Kc_open (C.m v.1) (C.hm v.1 (C.hsub v.2))).mem_nhds
      ((P.loc v.1).Kc (C.m v.1)).one_mem
  exact (hF.tendsto y0).eventually hK

end ArtinPrimitiveRoots.A1.Theta
