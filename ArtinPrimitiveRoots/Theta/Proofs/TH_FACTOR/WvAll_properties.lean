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

private theorem WvAll_emb (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) (v : FinPlace F) (hv : v ∉ S.Sf)
    (k : (P.loc v).L) :
    WvAll P G μ v (P.emb v k) =
      tameCoord0 (G.B v hv).weyl
        (jacquet (P.loc v) A (μ v) (rtr k (sphWeyl P G v hv (1 / 6)))) := by
  have hh : ∃ k', P.emb v k' = P.emb v k := ⟨k, rfl⟩
  have hchoose : hh.choose = k := P.emb_inj v hh.choose_spec
  unfold WvAll
  rw [dif_pos hv, dif_pos hh, hchoose]

private theorem WvAll_zero_of_not_Gloc (P : CoverPackage D S H A)
    (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v) (v : FinPlace F)
    (hv : v ∉ S.Sf) (h : P.tc.G) (hh : h ∉ P.tc.Gloc v) :
    WvAll P G μ v h = 0 := by
  have hno : ¬ ∃ k, P.emb v k = h := by
    intro hx
    apply hh
    rw [← P.emb_Gloc v hv]
    exact ⟨hx.choose, hx.choose_spec⟩
  unfold WvAll
  rw [dif_pos hv, dif_neg hno]

/-- Local genuine/equivariant/right-invariant/table properties, including zero extension.
Uses the frozen `jacquet_equiv`, `jacquet_spherical_table`, and cover image laws;
feeds frozen `WvAll_spec` and `thetaWhit_factor_iteration`. -/
theorem WvAll_properties (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v) :
    (∀ v, v ∉ S.Sf → ∀ ζ g, WvAll P G μ v (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, WvAll P G μ v (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ g, ∀ k ∈ P.tc.Kext, k ∈ P.tc.Gloc v → WvAll P G μ v (g * k) = WvAll P G μ v g) ∧
    (∀ v, v ∉ S.Sf → ∀ (e : ℤ) (u : (v.adicCompletion F)ˣ),
      (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      WvAll P G μ v (P.tc.a v ((toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ e * u)) =
        sphericalTable D A v e u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv ζ h
    by_cases hh : h ∈ P.tc.Gloc v
    · obtain ⟨k, rfl⟩ : ∃ k : (P.loc v).L, P.emb v k = h := by
        have hr : h ∈ (P.emb v).range := by
          rw [P.emb_Gloc v hv]
          exact hh
        exact hr
      have hz : P.tc.z ζ * P.emb v k = P.emb v ((P.loc v).z ζ * k) := by
        calc
          P.tc.z ζ * P.emb v k = P.emb v ((P.loc v).z ζ) * P.emb v k := by
            rw [← P.emb_z v ζ]
          _ = P.emb v ((P.loc v).z ζ * k) := (P.emb v).map_mul _ _ |>.symm
      let f : (P.loc v).L → (G.T v).weyl.V :=
        (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
          (fun h6 => hv (S.over6 v h6)) (-(1 / 6 : ℂ))).choose
      have hfsph : sphWeyl P G v hv (1 / 6) = f := rfl
      have hspec := (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl
        (G.B v hv).weyl (fun h6 => hv (S.over6 v h6)) (-(1 / 6 : ℂ))).choose_spec
      rw [hz, WvAll_emb P G μ v hv ((P.loc v).z ζ * k), WvAll_emb P G μ v hv k]
      rw [hfsph]
      have heq := (jacquet_equiv (P.loc v) (G.T v).weyl A (μ v) (-(1 / 6 : ℂ))
        (rtr k f) (hspec.1.rtr k)).2 ζ
      have hfun : rtr ((P.loc v).z ζ * k) f = rtr ((P.loc v).z ζ) (rtr k f) := by
        funext x
        simp [rtr, mul_assoc]
      rw [hfun]
      rw [heq]
      simp [tameCoord0, map_smul]
    · have hz : P.tc.z ζ ∈ P.tc.Gloc v := by
        rw [← P.emb_Gloc v hv]
        exact ⟨(P.loc v).z ζ, P.emb_z v ζ⟩
      have hnot : P.tc.z ζ * h ∉ P.tc.Gloc v := by
        intro hh'
        apply hh
        have h' := (P.tc.Gloc v).mul_mem ((P.tc.Gloc v).inv_mem hz) hh'
        simpa using h'
      rw [WvAll_zero_of_not_Gloc P G μ v hv h hh,
        WvAll_zero_of_not_Gloc P G μ v hv (P.tc.z ζ * h) hnot]
      simp
  · intro v hv x h
    by_cases hh : h ∈ P.tc.Gloc v
    · obtain ⟨k, rfl⟩ : ∃ k : (P.loc v).L, P.emb v k = h := by
        have hr : h ∈ (P.emb v).range := by rw [P.emb_Gloc v hv]; exact hh
        exact hr
      have hn : P.tc.n v (Multiplicative.ofAdd x) * P.emb v k =
          P.emb v ((P.loc v).n (Multiplicative.ofAdd x) * k) := by
        calc
          P.tc.n v (Multiplicative.ofAdd x) * P.emb v k =
              P.emb v ((P.loc v).n (Multiplicative.ofAdd x)) * P.emb v k := by
            rw [← P.emb_n v hv (Multiplicative.ofAdd x)]
          _ = P.emb v ((P.loc v).n (Multiplicative.ofAdd x) * k) := (P.emb v).map_mul _ _ |>.symm
      let f : (P.loc v).L → (G.T v).weyl.V :=
        (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
          (fun h6 => hv (S.over6 v h6)) (-(1 / 6 : ℂ))).choose
      have hfsph : sphWeyl P G v hv (1 / 6) = f := rfl
      have hspec := (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl
        (G.B v hv).weyl (fun h6 => hv (S.over6 v h6)) (-(1 / 6 : ℂ))).choose_spec
      rw [hn, WvAll_emb P G μ v hv ((P.loc v).n (Multiplicative.ofAdd x) * k),
        WvAll_emb P G μ v hv k]
      rw [hfsph]
      have heq := ((jacquet_equiv (P.loc v) (G.T v).weyl A (μ v) (-(1 / 6 : ℂ))
        (rtr k f) (hspec.1.rtr k)).1 x)
      have hfun : rtr ((P.loc v).n (Multiplicative.ofAdd x) * k) f =
          rtr ((P.loc v).n (Multiplicative.ofAdd x)) (rtr k f) := by
        funext y
        simp [rtr, mul_assoc]
      rw [hfun, heq]
      simp [tameCoord0, map_smul]
    · have hnmem : P.tc.n v (Multiplicative.ofAdd x) ∈ P.tc.Gloc v :=
        P.tc.n_mem v (Multiplicative.ofAdd x)
      have hnot : P.tc.n v (Multiplicative.ofAdd x) * h ∉ P.tc.Gloc v := by
        intro hh'
        apply hh
        have h' := (P.tc.Gloc v).mul_mem ((P.tc.Gloc v).inv_mem hnmem) hh'
        simpa using h'
      rw [WvAll_zero_of_not_Gloc P G μ v hv h hh,
        WvAll_zero_of_not_Gloc P G μ v hv (P.tc.n v (Multiplicative.ofAdd x) * h) hnot]
      simp
  · intro v hv h k hkK hkG
    by_cases hh : h ∈ P.tc.Gloc v
    · obtain ⟨g, rfl⟩ : ∃ g : (P.loc v).L, P.emb v g = h := by
        have hr : h ∈ (P.emb v).range := by rw [P.emb_Gloc v hv]; exact hh
        exact hr
      obtain ⟨k', rfl⟩ : ∃ k' : (P.loc v).L, P.emb v k' = k := by
        have hr : k ∈ (P.emb v).range := by rw [P.emb_Gloc v hv]; exact hkG
        exact hr
      have hkmax : k' ∈ (P.tame v hv).Kmax := (P.emb_Kext_iff v hv k').mp hkK
      let f : (P.loc v).L → (G.T v).weyl.V :=
        (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
          (fun h6 => hv (S.over6 v h6)) (-(1 / 6 : ℂ))).choose
      have hfsph : sphWeyl P G v hv (1 / 6) = f := rfl
      have hspec := (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl
        (G.B v hv).weyl (fun h6 => hv (S.over6 v h6)) (-(1 / 6 : ℂ))).choose_spec
      rw [show P.emb v g * P.emb v k' = P.emb v (g * k') from
        ((P.emb v).map_mul g k').symm]
      rw [WvAll_emb P G μ v hv (g * k'), WvAll_emb P G μ v hv g]
      rw [hfsph]
      have hsph : ∀ x, f (x * k') = f x := by
        intro x
        exact hspec.2.2.1 x k' hkmax
      have hfun : rtr (g * k') f = rtr g f := by
        funext x
        simpa [rtr, mul_assoc] using hsph (x * g)
      rw [hfun]
    · have hnot : h * k ∉ P.tc.Gloc v := by
        intro hh'
        apply hh
        have h' := (P.tc.Gloc v).mul_mem hh' ((P.tc.Gloc v).inv_mem hkG)
        simpa [mul_assoc] using h'
      rw [WvAll_zero_of_not_Gloc P G μ v hv h hh,
        WvAll_zero_of_not_Gloc P G μ v hv (h * k) hnot]
  · intro v hv e u hu huinv
    let y := unifLoc v ^ e * u
    change WvAll P G μ v (P.tc.a v y) = sphericalTable D A v e u
    rw [← P.emb_a v hv y, WvAll_emb P G μ v hv ((P.loc v).a y)]
    have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h6 => hv (S.over6 v h6)
    let f : (P.loc v).L → (G.T v).weyl.V :=
      (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
        h6 (-(1 / 6 : ℂ))).choose
    have hfsph : sphWeyl P G v hv (1 / 6) = f := rfl
    rw [hfsph]
    have hsph := (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl
      (G.B v hv).weyl h6 (-(1 / 6 : ℂ))).choose_spec
    have htable := jacquet_spherical_table (P.loc v) (P.tame v hv) (G.T v).weyl
      (G.B v hv).weyl A (μ v) h6 (fun h => hv (S.different_mem v h))
      f hsph.1 hsph.2.1 hsph.2.2.1 (tameCoord0 (G.B v hv).weyl) e u ⟨hu, huinv⟩
    have hs0 := jacquet_spherical_s0 (P.loc v) (P.tame v hv) (G.T v).weyl
      (G.B v hv).weyl A (μ v) h6 (fun h => hv (S.different_mem v h))
      f hsph.1 hsph.2.1 hsph.2.2.1 0
    have hcoord : tameCoord0 (G.B v hv).weyl (shellVec D A (G.B v hv).weyl) = 1 := by
      let B := G.B v hv
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
    have ha1 : (P.loc v).a (1 : (v.adicCompletion F)ˣ) = 1 := (P.loc v).a_one
    have hs0₀ : jacquet (P.loc v) A (μ v) f = shellVec D A (G.B v hv).weyl := by
      have htmp : jacquet (P.loc v) A (μ v)
          (rtr ((P.loc v).a 1) f) = shellVec D A (G.B v hv).weyl := by
        simpa [unifLoc] using hs0.1
      have hrt : rtr ((P.loc v).a 1) f = f := by
        rw [ha1]
        funext x
        simp [rtr]
      rwa [hrt] at htmp
    have hbase : tameCoord0 (G.B v hv).weyl
        (jacquet (P.loc v) A (μ v) f) = 1 := by
      rw [hs0₀]
      exact hcoord
    rw [htable]
    rw [hbase]
    simp

end ArtinPrimitiveRoots.A1.Theta
