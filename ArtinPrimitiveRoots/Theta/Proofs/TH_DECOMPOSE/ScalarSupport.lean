import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.TorusSupport

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Rational diagonal scalar values have one finite support for a common spherical level. -/
theorem finite_diagonal_scalar_support (P : CoverPackage D S H A) (G : GlobalDatum P)
    (sec : ∀ s : ℂ, GlobalSection P G s) (T0 : Finset (FinPlace F))
    (hT0 : ∀ s, (sec s).T0 = T0) (g : P.tc.G) :
    ∃ Ds : Finset (Fˣ ⧸ G.Δ), ∀ δ, δ ∉ Ds → ∀ s,
      scalarOf P G (sec s).f (sec s).fC (P.tc.rat (diagGL δ.out) * g) = 0 := by
  obtain ⟨r, rfl⟩ := P.q_surj g
  let T := T0 ∪ (P.comp_restricted r).toFinset
  let C : Set (Fˣ ⧸ G.Δ) := {δ | ∀ v, v ∉ T → toLoc v δ.out ∈ G.Alag v}
  have hC : C.Finite := finite_exterior_lagrangian_classes P G T
  refine ⟨hC.toFinset, ?_⟩
  intro δ hδ s
  have hnot : ¬ ∀ v, v ∉ T → toLoc v δ.out ∈ G.Alag v := by
    intro h
    exact hδ (hC.mem_toFinset.mpr h)
  push Not at hnot
  obtain ⟨v, hv, hx⟩ := hnot
  have hvT0 : v ∉ T0 := fun h => hv (Finset.mem_union_left _ h)
  have hvsec : v ∉ (sec s).T0 := by simpa only [hT0 s] using hvT0
  have hvS : v ∉ S.Sf := fun h => hvsec ((sec s).sub h)
  have hK : P.compF v r ∈ (P.tame v hvS).Kmax := by
    by_contra h
    apply hv
    exact Finset.mem_union_right _ ((P.comp_restricted r).mem_toFinset.mpr ⟨hvS, h⟩)
  have hdiag : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
      (diagGL δ.out) = diagM _ (toLoc v δ.out) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL, diagM, toLoc]
  let rδ := P.ratRP (diagGL δ.out) * r
  have hq : P.q rδ = P.tc.rat (diagGL δ.out) * P.q r := by
    simp only [rδ, map_mul, P.q_ratRP]
  have hval : (sec s).f v (P.compF v r) = (G.B v hvS).e 0 := by
    calc
      _ = (sec s).f v 1 := by
        simpa only [one_mul] using (sec s).f_sph v hvsec |>.2 1 (P.compF v r) hK
      _ = _ := (sec s).f_sph v hvsec |>.1
  have hcov : (sec s).f v ((P.loc v).a (toLoc v δ.out) * P.compF v r) =
      ((absFin v (toLoc v δ.out) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        (G.T v).σa (toLoc v δ.out) ((sec s).f v (P.compF v r)) := by
    simpa only [ofAdd_zero, map_one, one_mul] using
      (sec s).f_sec v |>.1 0 (toLoc v δ.out) (P.compF v r)
  have hzero : G.lam v ((sec s).f v (P.compF v rδ)) = 0 := by
    rw [show P.compF v rδ = (P.loc v).a (toLoc v δ.out) * P.compF v r by
      simp only [rδ, map_mul, P.compF_ratRP, hdiag, ← (P.loc v).sec_a]]
    rw [hcov, hval, map_smul, tame_lam_sigma_eq_zero P G v hvS _ hx, smul_zero]
  obtain ⟨hsupport, hscalar⟩ := scalarOf_q P G (sec s) rδ
  rw [← hq, hscalar, finprod_eq_zero _ v hzero hsupport, zero_mul]

end ArtinPrimitiveRoots.A1.Theta
