import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

private lemma orbit_pair_realize
    (hratio : LeadRatioContract (S := S))
    (ur : U.U × S.ExtIdeal) :
    ∃ (x : S.R) (γ0 : Gamma S), (x : F) ≠ 0 ∧
      (x : F) = ((γ0.1 : Fˣ) : F) * (U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6 := by
  obtain ⟨x, hx0, ε, a, ha, hx⟩ := U.decomposition_surjective ur.1 ur.2
  obtain ⟨τ, hτ⟩ := hratio ur.2.1 (a : F) (bc.gen ur.2 : F) ha (bc.gen_spec ur.2).1
  let γ0 : Gamma S := ⟨(ε * τ) ^ 6, ⟨ε * τ, rfl⟩⟩
  refine ⟨x, γ0, hx0, ?_⟩
  rw [hx, hτ]
  simp only [γ0, Subgroup.coe_pow, Subgroup.coe_mul, Units.val_pow_eq_pow_val, Units.val_mul]
  ring

private def orbit_pair_witness
    (hratio : LeadRatioContract (S := S))
    (ur : U.U × S.ExtIdeal) :
    { p : S.R × Gamma S // (p.1 : F) ≠ 0 ∧
      (p.1 : F) = ((p.2.1 : Fˣ) : F) * (U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6 } :=
  Classical.indefiniteDescription _ (by
    obtain ⟨x, γ0, hx0, hx⟩ := orbit_pair_realize (bc := bc) (η := η) (U := U) hratio ur
    exact ⟨(x, γ0), hx0, hx⟩)

private lemma orbit_transport_val
    (hratio : LeadRatioContract (S := S))
    (p : (U.U × S.ExtIdeal) × Gamma S) :
    (((Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F
        (p.2.1 * ((orbit_pair_witness (bc := bc) (η := η) (U := U) hratio p.1).1.2.1)⁻¹ : S.US) : S.R) *
        (orbit_pair_witness (bc := bc) (η := η) (U := U) hratio p.1).1.1 : S.R) : F) =
      ((p.2.1 : Fˣ) : F) * (U.repr p.1.1 : F) * (bc.gen p.1.2 : F) ^ 6 := by
  let ur := p.1
  let γ := p.2
  let w := orbit_pair_witness (bc := bc) (η := η) (U := U) hratio ur
  let x0 := w.1.1
  let γ0 := w.1.2
  let diff : S.US := γ.1 * (γ0.1)⁻¹
  let diffR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F diff
  have hunit : (diff : Fˣ) * (γ0.1 : Fˣ) = (γ.1 : Fˣ) := by
    change (((γ.1 * (γ0.1)⁻¹ : S.US) : Fˣ) * (γ0.1 : Fˣ)) = (γ.1 : Fˣ)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hunitF : ((diff : Fˣ) : F) * ((γ0.1 : Fˣ) : F) = ((γ.1 : Fˣ) : F) := by
    rw [← Units.val_mul, hunit]
  have hx0 := w.2.2
  calc (((diffR : S.R) * x0 : S.R) : F)
    _ = ((diff : Fˣ) : F) * (x0 : F) := rfl
    _ = ((diff : Fˣ) : F) * (((γ0.1 : Fˣ) : F) * (U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6) := by
      rw [hx0]
    _ = (((diff : Fˣ) : F) * ((γ0.1 : Fˣ) : F)) * (U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6 := by
      ring
    _ = ((γ.1 : Fˣ) : F) * (U.repr ur.1 : F) * (bc.gen ur.2 : F) ^ 6 := by
      rw [hunitF]

private lemma orbit_transport_ne
    (hratio : LeadRatioContract (S := S))
    (p : (U.U × S.ExtIdeal) × Gamma S) :
    (((Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F
        (p.2.1 * ((orbit_pair_witness (bc := bc) (η := η) (U := U) hratio p.1).1.2.1)⁻¹ : S.US) : S.R) *
        (orbit_pair_witness (bc := bc) (η := η) (U := U) hratio p.1).1.1 : S.R) : F) ≠ 0 := by
  let w := orbit_pair_witness (bc := bc) (η := η) (U := U) hratio p.1
  let diff : S.US := p.2.1 * (w.1.2.1)⁻¹
  exact mul_ne_zero (Units.ne_zero (diff : Fˣ)) w.2.1

private def orbit_to_subtype
    (hratio : LeadRatioContract (S := S))
    (p : (U.U × S.ExtIdeal) × Gamma S) : {x : S.R // (x : F) ≠ 0} :=
  ⟨(Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F
      (p.2.1 * ((orbit_pair_witness (bc := bc) (η := η) (U := U) hratio p.1).1.2.1)⁻¹ : S.US) : S.R) *
      (orbit_pair_witness (bc := bc) (η := η) (U := U) hratio p.1).1.1,
   orbit_transport_ne (bc := bc) (η := η) (U := U) hratio p⟩

private lemma orbit_to_subtype_val
    (hratio : LeadRatioContract (S := S))
    (p : (U.U × S.ExtIdeal) × Gamma S) :
    ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p).1 : F) =
      ((p.2.1 : Fˣ) : F) * (U.repr p.1.1 : F) * (bc.gen p.1.2 : F) ^ 6 :=
  orbit_transport_val (bc := bc) (η := η) (U := U) hratio p

private lemma orbit_to_subtype_injective
    (hclass : LeadClassContract (bc := bc) η U)
    (hratio : LeadRatioContract (S := S)) :
    Function.Injective (orbit_to_subtype (bc := bc) (η := η) (U := U) hratio) := by
  intro p1 p2 hp
  have hval : ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p1).1 : F) =
      ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p2).1 : F) := by
    rw [hp]
  have h1 : ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p1).1 : F) =
      ((p1.2.1 : Fˣ) : F) * (U.repr p1.1.1 : F) * (bc.gen p1.1.2 : F) ^ 6 :=
    orbit_to_subtype_val (bc := bc) (η := η) (U := U) hratio p1
  have h2 : ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p2).1 : F) =
      ((p2.2.1 : Fˣ) : F) * (U.repr p2.1.1 : F) * (bc.gen p2.1.2 : F) ^ 6 :=
    orbit_to_subtype_val (bc := bc) (η := η) (U := U) hratio p2
  let x : S.R := (orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p1).1
  have hxne : (x : F) ≠ 0 := (orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p1).2
  obtain ⟨ur0, ⟨γ0, hx0⟩, huniq⟩ := hclass x hxne
  have hp1_ur : p1.1 = ur0 := by
    apply huniq p1.1
    refine ⟨p1.2, ?_⟩
    exact h1
  have hp2_ur : p2.1 = ur0 := by
    apply huniq p2.1
    refine ⟨p2.2, ?_⟩
    calc (x : F)
      _ = ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p1).1 : F) := rfl
      _ = ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p2).1 : F) := hval
      _ = ((p2.2.1 : Fˣ) : F) * (U.repr p2.1.1 : F) * (bc.gen p2.1.2 : F) ^ 6 := h2
  have hur : p1.1 = p2.1 := hp1_ur.trans hp2_ur.symm
  have hp21 : p2.1 = p1.1 := hur.symm
  have hp21_1 : p2.1.1 = p1.1.1 := by rw [hp21]
  have hp21_2 : p2.1.2 = p1.1.2 := by rw [hp21]
  have hγ_eq : ((p1.2.1 : Fˣ) : F) = ((p2.2.1 : Fˣ) : F) := by
    have hcancel : ((p1.2.1 : Fˣ) : F) *
        ((U.repr p1.1.1 : F) * (bc.gen p1.1.2 : F) ^ 6) =
        ((p2.2.1 : Fˣ) : F) *
        ((U.repr p1.1.1 : F) * (bc.gen p1.1.2 : F) ^ 6) := by
      calc ((p1.2.1 : Fˣ) : F) * ((U.repr p1.1.1 : F) * (bc.gen p1.1.2 : F) ^ 6)
        _ = ((p1.2.1 : Fˣ) : F) * (U.repr p1.1.1 : F) * (bc.gen p1.1.2 : F) ^ 6 := by ring
        _ = ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p1).1 : F) := h1.symm
        _ = ((orbit_to_subtype (bc := bc) (η := η) (U := U) hratio p2).1 : F) := hval
        _ = ((p2.2.1 : Fˣ) : F) * (U.repr p2.1.1 : F) * (bc.gen p2.1.2 : F) ^ 6 := h2
        _ = ((p2.2.1 : Fˣ) : F) * ((U.repr p1.1.1 : F) * (bc.gen p1.1.2 : F) ^ 6) := by
          rw [hp21_1, hp21_2]; ring
    have hC_ne : (U.repr p1.1.1 : F) * (bc.gen p1.1.2 : F) ^ 6 ≠ 0 := by
      apply mul_ne_zero (U.repr_nonzero p1.1.1)
      exact pow_ne_zero 6 (Units.ne_zero (bc.gen p1.1.2))
    exact mul_right_cancel₀ hC_ne hcancel
  have hγ_units : (p1.2.1 : Fˣ) = (p2.2.1 : Fˣ) := Units.ext hγ_eq
  have hγ_us : p1.2.1 = p2.2.1 := Subtype.ext hγ_units
  have hγ : p1.2 = p2.2 := Subtype.ext hγ_us
  exact Prod.ext hur hγ

private lemma orbit_to_subtype_surjective
    (hclass : LeadClassContract (bc := bc) η U)
    (hratio : LeadRatioContract (S := S)) :
    Function.Surjective (orbit_to_subtype (bc := bc) (η := η) (U := U) hratio) := by
  intro y
  obtain ⟨ur, ⟨γ, hxγ⟩, -⟩ := hclass y.1 y.2
  let p : (U.U × S.ExtIdeal) × Gamma S := (ur, γ)
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [orbit_to_subtype_val (bc := bc) (η := η) (U := U) hratio p, hxγ]

/-- IMPL: realize every triple in S.R and use pair and Gamma uniqueness. -/
theorem orbit_equiv
    (hclass : LeadClassContract (bc := bc) η U)
    (hratio : LeadRatioContract (S := S)) :
    LeadEquivContract (bc := bc) η U := by
  let e : ((U.U × S.ExtIdeal) × Gamma S) ≃ {x : S.R // (x : F) ≠ 0} :=
    Equiv.ofBijective (orbit_to_subtype (bc := bc) (η := η) (U := U) hratio)
      ⟨orbit_to_subtype_injective (bc := bc) (η := η) (U := U) hclass hratio,
       orbit_to_subtype_surjective (bc := bc) (η := η) (U := U) hclass hratio⟩
  refine ⟨e, fun p => orbit_to_subtype_val (bc := bc) (η := η) (U := U) hratio p⟩

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
