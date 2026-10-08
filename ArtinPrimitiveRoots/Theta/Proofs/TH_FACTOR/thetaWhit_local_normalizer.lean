import Mathlib.LinearAlgebra.Basis.VectorSpace
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem local_WvAll_emb (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) (v : FinPlace F) (hv : v ∉ S.Sf)
    (k : (P.loc v).L) :
    WvAll P G μ v (P.emb v k) =
      tameCoord0 (G.B v hv).weyl
        (jacquet (P.loc v) A (μ v) (rtr k (sphWeyl P G v hv (1 / 6)))) := by
  have hh : ∃ k', P.emb v k' = P.emb v k := ⟨k, rfl⟩
  have hchoose : hh.choose = k := P.emb_inj v hh.choose_spec
  unfold WvAll
  rw [dif_pos hv, dif_pos hh, hchoose]

private theorem cv_one_sixth_ne_zero (v : FinPlace F) : cv v (1 / 6 : ℂ) ≠ 0 := by
  have hqpos : 0 < qv v := by linarith [qv_gt_one v]
  have hq0 : (qv v : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hq1 : (qv v : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt (qv_gt_one v))
  have hq2r : (qv v) ^ 2 ≠ (1 : ℝ) := by nlinarith [qv_gt_one v]
  have hq2 : (qv v : ℂ) ^ 2 ≠ 1 := by exact_mod_cast hq2r
  have hpow1 : (qv v : ℂ) ^ (-1 : ℤ) ≠ 1 := by
    rw [zpow_neg, zpow_one]
    intro h
    apply hq1
    have hh := congrArg (fun z : ℂ => z⁻¹) h
    simpa [hq0] using hh
  have hpow2 : (qv v : ℂ) ^ (-2 : ℤ) ≠ 1 := by
    rw [zpow_neg, zpow_ofNat]
    intro h
    apply hq2
    have hh := congrArg (fun z : ℂ => z⁻¹) h
    simpa [hq0] using hh
  have hpow1C : (qv v : ℂ) ^ (-1 : ℂ) ≠ 1 := by
    have he : (-1 : ℂ) = ((-1 : ℤ) : ℂ) := by norm_num
    rw [he, Complex.cpow_intCast]
    exact hpow1
  have hpow2C : (qv v : ℂ) ^ (-2 : ℂ) ≠ 1 := by
    have he : (-2 : ℂ) = ((-2 : ℤ) : ℂ) := by norm_num
    rw [he, Complex.cpow_intCast]
    exact hpow2
  rw [cv, show (-1 : ℂ) - 6 * (1 / 6 : ℂ) = -2 by ring,
    show -6 * (1 / 6 : ℂ) = -1 by ring]
  exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hpow2C))
    (sub_ne_zero.mpr (Ne.symm hpow1C))

private theorem tameCoord0_shellVec (D : FieldData F) (A : AddCharData F)
    {v : FinPlace F} {T : TorusRep D H v} (B : TameTorusBasis T) :
    tameCoord0 B.weyl (shellVec D A B.weyl) = 1 := by
  have h0 : (Module.Basis.mk B.weyl.linIndep B.weyl.spans.ge).coord 0
      (B.weyl.e 0) = 1 :=
    Module.Basis.mk_coord_apply_eq (hli := B.weyl.linIndep)
      (hsp := B.weyl.spans.ge) 0
  have h2 : (Module.Basis.mk B.weyl.linIndep B.weyl.spans.ge).coord 0
      (B.weyl.e 2) = 0 :=
    Module.Basis.mk_coord_apply_ne (hli := B.weyl.linIndep)
      (hsp := B.weyl.spans.ge) (by decide)
  change (Module.Basis.mk B.weyl.linIndep B.weyl.spans.ge).coord 0
    (B.weyl.e 0 + ((qv v : ℂ) ^ (-(1 / 6 : ℂ)) * gaussLoc D A v (-2)) •
      B.weyl.e 2) = 1
  rw [map_add, map_smul, h0, h2]
  simp

/-- The normalized Jacquet coordinate on the local theta space, including the spherical
vector membership needed to apply uniqueness. No global residue functional is used.
Uses frozen `jacquet_spherical_s0`, `jacquet_linear`, `jacquet_equiv`,
`intertwine_spherical`, and `thetaSpace_le`; feeds `thetaWhit_factor_step`. -/
theorem thetaWhit_local_normalizer (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) (v : FinPlace F) (hv : v ∉ S.Sf) :
    sphWeyl P G v hv (1 / 6) ∈ thetaSpace (P.loc v) (G.T v) (μ v) ∧
      ∃ α : ((P.loc v).L → (G.T v).V) →ₗ[ℂ] ℂ,
        IsWhittakerOn (P.loc v) A (thetaSpace (P.loc v) (G.T v) (μ v)) α ∧
        α (sphWeyl P G v hv (1 / 6)) = 1 ∧
        ∀ k : (P.loc v).L, α (rtr k (sphWeyl P G v hv (1 / 6))) =
          WvAll P G μ v (P.emb v k) := by
  classical
  let L := P.loc v
  let T := G.T v
  let B := G.B v hv
  let τ := P.tame v hv
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  let f : L.L → T.V :=
    (spherical_section L τ T B h6 (1 / 6 : ℂ)).choose
  let fw : L.L → T.V := sphWeyl P G v hv (1 / 6)
  let fwW : L.L → T.weyl.V := fw
  have hfdata := (spherical_section L τ T B h6 (1 / 6 : ℂ)).choose_spec
  have hfwdata := (spherical_section L τ T.weyl B.weyl h6 (-(1 / 6 : ℂ))).choose_spec
  have hfsph : sphWeyl P G v hv (1 / 6) = fw := rfl
  have hfw : IsSection L T.weyl (-(1 / 6 : ℂ)) fw := by
    simpa [fw, sphWeyl] using hfwdata.1
  have hcv : cv v (1 / 6 : ℂ) ≠ 0 := cv_one_sixth_ne_zero v
  have hM := intertwine_spherical L τ T B (μ v) h6 (1 / 6 : ℂ) (by norm_num)
    f hfdata.1 hfdata.2.1 hfdata.2.2.1 fw hfw hfwdata.2.1 hfwdata.2.2.1
  have hMspan : intertwine L (μ v) f ∈ thetaSpace L T (μ v) :=
    Submodule.subset_span ⟨f, hfdata.1, rfl⟩
  have hfwspan : fw ∈ thetaSpace L T (μ v) := by
    have hs : (cv v (1 / 6 : ℂ))⁻¹ • intertwine L (μ v) f ∈ thetaSpace L T (μ v) :=
      Submodule.smul_mem _ _ hMspan
    have heq : (cv v (1 / 6 : ℂ))⁻¹ • intertwine L (μ v) f = fw := by
      calc
        (cv v (1 / 6 : ℂ))⁻¹ • intertwine L (μ v) f =
            (cv v (1 / 6 : ℂ))⁻¹ • (cv v (1 / 6 : ℂ) • fw) := by rw [hM]
        _ = fw := by
          rw [smul_smul, inv_mul_cancel₀ hcv, one_smul]
    rw [← heq]
    exact hs
  have hJzero : jacquet L A (μ v) (0 : L.L → T.weyl.V) = 0 := by
    have h := jacquet_linear L T.weyl A (μ v) (-(1 / 6 : ℂ))
      (0 : L.L → T.weyl.V) 0 (by exact (sectionSpace L T.weyl (-(1 / 6 : ℂ))).zero_mem)
      (by exact (sectionSpace L T.weyl (-(1 / 6 : ℂ))).zero_mem) 1
    have hc : jacquet L A (μ v) (0 : L.L → T.weyl.V) +
        jacquet L A (μ v) (0 : L.L → T.weyl.V) =
          jacquet L A (μ v) (0 : L.L → T.weyl.V) + 0 := by
      simpa using h.symm
    exact add_left_cancel hc
  let J : sectionSpace L T.weyl (-(1 / 6 : ℂ)) →ₗ[ℂ] ℂ := {
    toFun := fun f => tameCoord0 B.weyl (jacquet L A (μ v) f.1)
    map_add' := by
      intro f g
      have h := jacquet_linear L T.weyl A (μ v) (-(1 / 6 : ℂ))
        f.1 g.1 f.2 g.2 1
      have hj : jacquet L A (μ v) (f.1 + g.1) =
          jacquet L A (μ v) f.1 + jacquet L A (μ v) g.1 := by simpa using h
      change tameCoord0 B.weyl (jacquet L A (μ v) (f.1 + g.1)) =
        tameCoord0 B.weyl (jacquet L A (μ v) f.1) +
          tameCoord0 B.weyl (jacquet L A (μ v) g.1)
      rw [hj, map_add]
    map_smul' := by
      intro c f
      have h := jacquet_linear L T.weyl A (μ v) (-(1 / 6 : ℂ))
        (0 : L.L → T.weyl.V) f.1
        (sectionSpace L T.weyl (-(1 / 6 : ℂ))).zero_mem f.2 c
      simpa [tameCoord0, hJzero] using congrArg (tameCoord0 B.weyl) h
  }
  obtain ⟨α, hα⟩ := LinearMap.exists_extend J
  have hαon (g : L.L → T.weyl.V) (hg : IsSection L T.weyl (-(1 / 6 : ℂ)) g) :
      α g = tameCoord0 B.weyl (jacquet L A (μ v) g) := by
    let g' : sectionSpace L T.weyl (-(1 / 6 : ℂ)) := ⟨g, hg⟩
    have heq := congrArg (fun ℓ : (sectionSpace L T.weyl (-(1 / 6 : ℂ)) →ₗ[ℂ] ℂ) => ℓ g') hα
    simpa [J, g'] using heq
  have hαwh : IsWhittakerOn L A (thetaSpace L T (μ v)) α := by
    intro g hg t
    have hle := thetaSpace_le L T (μ v)
    have hgsec : IsSection L T.weyl (-(1 / 6 : ℂ)) g := hle.1 hg
    have hng : rtr (L.n (Multiplicative.ofAdd t)) g ∈ thetaSpace L T (μ v) :=
      hle.2 g hg (L.n (Multiplicative.ofAdd t))
    have hnsec : IsSection L T.weyl (-(1 / 6 : ℂ))
        (rtr (L.n (Multiplicative.ofAdd t)) g) := hle.1 hng
    have hj := (jacquet_equiv L T.weyl A (μ v) (-(1 / 6 : ℂ)) g hgsec).1 t
    calc
      α (rtr (L.n (Multiplicative.ofAdd t)) g) =
          tameCoord0 B.weyl (jacquet L A (μ v) (rtr (L.n (Multiplicative.ofAdd t)) g)) :=
        hαon _ hnsec
      _ = (A.ψ v t) * tameCoord0 B.weyl (jacquet L A (μ v) g) := by
        rw [hj]
        simp [map_smul]
      _ = (A.ψ v t) * α g := by rw [← hαon _ hgsec]
  have hcoord : tameCoord0 B.weyl (shellVec D A B.weyl) = 1 :=
    tameCoord0_shellVec D A B
  have ha1 : L.a (1 : (v.adicCompletion F)ˣ) = 1 := L.a_one
  have hfwW : IsSection L T.weyl (-(1 / 6 : ℂ)) fwW := by
    simpa [fwW] using hfw
  have hs0 := jacquet_spherical_s0 L τ T.weyl B.weyl A (μ v) h6
    (fun h => hv (S.different_mem v h)) fwW hfwW hfwdata.2.1 hfwdata.2.2.1 0
  have hbase : jacquet L A (μ v) fwW = shellVec D A B.weyl := by
    have ht : jacquet L A (μ v) (rtr (L.a 1) fwW) = shellVec D A B.weyl := by
      simpa [unifLoc] using hs0.1
    have hr : rtr (L.a 1) fwW = fwW := by
      rw [ha1]
      funext x
      simp [rtr]
    rwa [hr] at ht
  have hnorm : α fw = 1 := by
    have hnormW : α fwW = 1 := by rw [hαon fwW hfwdata.1, hbase, hcoord]
    simpa [fwW] using hnormW
  refine ⟨?_, α, hαwh, hnorm, ?_⟩
  · rw [hfsph]
    exact hfwspan
  · intro k
    have hksec : IsSection L T.weyl (-(1 / 6 : ℂ))
        (rtr k fwW) := hfwW.rtr k
    calc
      α (rtr k (sphWeyl P G v hv (1 / 6))) =
          tameCoord0 B.weyl (jacquet L A (μ v) (rtr k fwW)) := by
        rw [hfsph]
        exact hαon (rtr k fwW) hksec
      _ = WvAll P G μ v (P.emb v k) := (local_WvAll_emb P G μ v hv k).symm

end ArtinPrimitiveRoots.A1.Theta
