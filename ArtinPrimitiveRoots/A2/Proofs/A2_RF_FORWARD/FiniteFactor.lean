import ArtinPrimitiveRoots.A1.ThetaInterface

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1

theorem finite_digit_factorization {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {A : AddCharData F} {C : ThetaCover D S H A} {𝓛 : Finset (SChar S)}
    (T : ThetaFamily C 𝓛) (L : SChar S) (hL : L ∈ 𝓛)
    (T0 : Finset (FinPlace F)) (hT0 : ∀ v ∈ T0, v ∉ S.Sf)
    (ν : Fˣ) (y : S.FSˣ)
    (x : (v : {v : FinPlace F // v ∈ T0}) → v.1.adicCompletion F) :
    T.W L (C.rat (diagGL ν) * (C.aS y *
      (T0.attach.toList.map (fun v => C.n v.1 (Multiplicative.ofAdd (x v)))).prod)) =
      T.WS L (C.aS (S.diagU ν) * C.aS y) *
        (∏ v : {v : FinPlace F // v ∈ T0},
          A.ψ v.1 (x v * (toLoc v.1 ν : v.1.adicCompletion F))) *
        (∏ v ∈ T0, T.Wv v (C.a v (toLoc v ν))) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T0),
          T.Wv v (C.a v (toLoc v ν)) := by
  classical
  let V := {v : FinPlace F // v ∈ T0}
  let g : FinPlace F → C.G := fun v =>
    if hv : v ∈ T0 then C.n v (Multiplicative.ofAdd (x ⟨v, hv⟩)) else 1
  have hg : ∀ v ∈ T0, g v ∈ C.Gloc v := by
    intro v hv
    simpa only [g, dif_pos hv] using C.n_mem v (Multiplicative.ofAdd (x ⟨v, hv⟩))
  have hmap : T0.attach.toList.map (fun v => C.n v.1 (Multiplicative.ofAdd (x v))) =
      T0.attach.toList.map (fun v => g v.1) := by
    apply List.map_congr_left
    intro v hv
    simp [g, v.2]
  have hperm0 : (T0.attach.toList.map Subtype.val).Perm T0.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact T0.attach.nodup_toList.map Subtype.val_injective
    · exact T0.nodup_toList
    · ext v
      simp
  have hperm : (T0.attach.toList.map (fun v => g v.1)).Perm (T0.toList.map g) := by
    change List.Perm (List.map (g ∘ Subtype.val) T0.attach.toList) (List.map g T0.toList)
    simpa only [List.map_map] using hperm0.map g
  have hpairNe : T0.attach.toList.Pairwise (· ≠ ·) :=
    List.nodup_iff_pairwise_ne.mp T0.attach.nodup_toList
  have hpair : (T0.attach.toList.map (fun v => g v.1)).Pairwise Commute := by
    exact List.Pairwise.map (fun v : V => g v.1)
      (by
        intro v w hne
        have hvw : v.1 ≠ w.1 := by
          intro heq
          exact hne (Subtype.ext heq)
        exact C.comm_loc v.1 w.1 hvw (g v.1) (hg v.1 v.2) (g w.1) (hg w.1 w.2))
      hpairNe
  have hprod : (T0.attach.toList.map
      (fun v => C.n v.1 (Multiplicative.ofAdd (x v)))).prod =
      (T0.toList.map g).prod := by
    rw [hmap]
    exact List.Perm.prod_eq' hperm hpair
  have harg : C.rat (diagGL ν) * (C.aS y *
      (T0.attach.toList.map (fun v => C.n v.1 (Multiplicative.ofAdd (x v)))).prod) =
      (C.rat (diagGL ν) * C.aS y) * (T0.toList.map g).prod := by
    rw [hprod, mul_assoc]
  have hFactor := T.factor L hL ν false (C.aS y) (C.aS_mem y) T0 hT0 g hg
  simp only [Bool.false_eq_true, if_false, mul_one, one_mul] at hFactor
  rw [← harg] at hFactor
  let φ : FinPlace F → ℂ := fun v => if hv : v ∈ T0 then
    A.ψ v (x ⟨v, hv⟩ * (toLoc v ν : v.adicCompletion F)) else 1
  have hLocal (v : FinPlace F) (hv : v ∈ T0) :
      T.Wv v (C.a v (toLoc v ν) * g v) = φ v * T.Wv v (C.a v (toLoc v ν)) := by
    have hLift : C.a v (toLoc v ν) * g v =
        C.n v (Multiplicative.ofAdd (x ⟨v, hv⟩ * (toLoc v ν : v.adicCompletion F))) *
          C.a v (toLoc v ν) := by
      have h := C.lift_na v (x ⟨v, hv⟩ * (toLoc v ν : v.adicCompletion F)) (toLoc v ν)
      simpa [g, hv, mul_assoc] using h.symm
    rw [hLift, T.Wv_equiv v (hT0 v hv)]
    simp only [φ, dif_pos hv]
  have hφ : (∏ v ∈ T0, φ v) = ∏ v : V,
      A.ψ v.1 (x v * (toLoc v.1 ν : v.1.adicCompletion F)) := by
    have huniv : T0.attach = (Finset.univ : Finset V) :=
      Finset.eq_univ_iff_forall.mpr (fun v => Finset.mem_attach T0 v)
    calc
      _ = ∏ v ∈ T0.attach, φ v.1 := (Finset.prod_attach T0 φ).symm
      _ = _ := by
        rw [huniv]
        apply Finset.prod_congr rfl
        intro v hv
        simp only [φ, dif_pos v.2]
  have hLocalProd : (∏ v ∈ T0, T.Wv v (C.a v (toLoc v ν) * g v)) =
      (∏ v : V, A.ψ v.1 (x v * (toLoc v.1 ν : v.1.adicCompletion F))) *
        ∏ v ∈ T0, T.Wv v (C.a v (toLoc v ν)) := by
    calc
      _ = ∏ v ∈ T0, φ v * T.Wv v (C.a v (toLoc v ν)) :=
        Finset.prod_congr rfl (fun v hv => hLocal v hv)
      _ = _ := by rw [Finset.prod_mul_distrib, hφ]
  rw [hLocalProd] at hFactor
  calc
    _ = T.WS L (C.aS (S.diagU ν) * C.aS y) *
      ((∏ v : V, A.ψ v.1 (x v * (toLoc v.1 ν : v.1.adicCompletion F))) *
        (∏ v ∈ T0, T.Wv v (C.a v (toLoc v ν)))) *
      ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T0), T.Wv v (C.a v (toLoc v ν)) := hFactor
    _ = _ := by ring

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
