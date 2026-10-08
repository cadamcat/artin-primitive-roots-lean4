import Mathlib

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- A finite cokernel and finitely many kernel power classes give finitely many
power classes in every shifted power fiber. This is the group step in cubic Selmer finiteness. -/
theorem finite_power_fiber_classes {A B : Type*} [CommGroup A] [CommGroup B]
    (φ : A →* B) (n : ℕ) (r : B) [Finite (B ⧸ φ.range)]
    [Finite (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range)] :
    Set.Finite ((QuotientGroup.mk' (powMonoidHom n : A →* A).range) ''
      {a : A | ∃ b : B, φ a = b ^ n * r}) := by
  classical
  let Q := B ⧸ φ.range
  let U := φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range
  let p : A →* A ⧸ (powMonoidHom n : A →* A).range :=
    QuotientGroup.mk' _
  let x : Q → A := fun q =>
    if h : ∃ a : A, φ a = (Quotient.out q) ^ n * r then h.choose else 1
  let f : Q × U → A ⧸ (powMonoidHom n : A →* A).range :=
    fun q => p (x q.1 * (Quotient.out q.2 : φ.ker).val)
  apply (Set.finite_range f).subset
  rintro z ⟨a, ⟨b, hab⟩, rfl⟩
  let q : Q := QuotientGroup.mk b
  have hbq : b / Quotient.out q ∈ φ.range :=
    QuotientGroup.eq_iff_div_mem.mp (Quotient.out_eq q).symm
  obtain ⟨t, ht⟩ := hbq
  have hbt : b = Quotient.out q * φ t := by
    rw [ht, mul_div_cancel]
  have hx : ∃ a : A, φ a = (Quotient.out q) ^ n * r := by
    refine ⟨a / t ^ n, ?_⟩
    rw [map_div, map_pow, hab, hbt, mul_pow]
    rw [mul_right_comm _ (φ t ^ n) r, mul_div_cancel_right]
  have hxt : φ (x q) = (Quotient.out q) ^ n * r := by
    dsimp only [x]
    rw [dite_eq_left hx]
    exact hx.choose_spec
  let u : φ.ker := ⟨a / (t ^ n * x q), by
    apply MonoidHom.mem_ker.mpr
    rw [map_div, map_mul, map_pow, hab, hbt, mul_pow, hxt]
    rw [mul_comm (Quotient.out q ^ n) (φ t ^ n), mul_assoc, div_self']⟩
  let qU : U := QuotientGroup.mk u
  have huq : (Quotient.out qU : φ.ker) / u ∈
      (powMonoidHom n : φ.ker →* φ.ker).range :=
    QuotientGroup.eq_iff_div_mem.mp (Quotient.out_eq qU)
  obtain ⟨v, hv⟩ := huq
  have hv' : (v : A) ^ n = (Quotient.out qU : φ.ker).val / (u : A) :=
    congrArg (fun w : φ.ker => (w : A)) hv
  have hu : (Quotient.out qU : φ.ker).val = (u : A) * (v : A) ^ n := by
    rw [hv', mul_div_cancel]
  have ha : a = t ^ n * (x q * (u : A)) := by
    change a = t ^ n * (x q * (a / (t ^ n * x q)))
    rw [← mul_assoc, mul_div_cancel]
  have hp (t : A) : p (t ^ n) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨t, rfl⟩
  refine ⟨(q, qU), ?_⟩
  change p (x q * (Quotient.out qU : φ.ker).val) = p a
  calc
    _ = p (x q * (u : A)) := by
      rw [hu, ← mul_assoc, map_mul, hp, mul_one]
    _ = p a := by simp only [ha, map_mul, hp, one_mul]

open scoped NumberField nonZeroDivisors in
/-- Shifted power fibers of principal fractional ideals have finitely many rational power classes. -/
theorem finite_principal_power_fiber_classes (F : Type*) [Field F] [NumberField F]
    (n : ℕ) (hn : n ≠ 0) (r : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Set.Finite ((QuotientGroup.mk' (powMonoidHom n : Fˣ →* Fˣ).range) ''
      {a : Fˣ | ∃ J : (FractionalIdeal (𝓞 F)⁰ F)ˣ,
        toPrincipalIdeal (𝓞 F) F a = J ^ n * r}) := by
  classical
  let φ : Fˣ →* (FractionalIdeal (𝓞 F)⁰ F)ˣ := toPrincipalIdeal (𝓞 F) F
  let j : (𝓞 F)ˣ →* φ.ker :=
    { toFun := fun u => ⟨Units.map (algebraMap (𝓞 F) F).toMonoidHom u, by
        apply MonoidHom.mem_ker.mpr
        change toPrincipalIdeal (𝓞 F) F (Units.map (algebraMap (𝓞 F) F).toMonoidHom u) = 1
        apply Units.ext
        simp only [coe_toPrincipalIdeal, Units.val_one, Units.coe_map]
        rw [← FractionalIdeal.spanSingleton_one (S := (𝓞 F)⁰)]
        apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
        refine ⟨u⁻¹, ?_⟩
        simp [Units.smul_def, Algebra.smul_def]⟩
      map_one' := by apply Subtype.ext; exact (Units.map _).map_one
      map_mul' := by intro u v; apply Subtype.ext; exact (Units.map _).map_mul u v }
  have hj : Function.Surjective j := by
    intro k
    have hk : toPrincipalIdeal (𝓞 F) F k.val = 1 := k.property
    have hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ (k.val : F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ (1 : F) := by
      have h := congrArg (fun J : (FractionalIdeal (𝓞 F)⁰ F)ˣ => (J : FractionalIdeal (𝓞 F)⁰ F)) hk
      simpa only [coe_toPrincipalIdeal, Units.val_one, FractionalIdeal.spanSingleton_one] using h
    obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
    have hue : Units.map (algebraMap (𝓞 F) F).toMonoidHom u * k.val = 1 := by
      apply Units.ext
      change algebraMap (𝓞 F) F (u : 𝓞 F) * (k.val : F) = 1
      simpa only [Units.smul_def, Algebra.smul_def] using hu
    refine ⟨u⁻¹, ?_⟩
    apply Subtype.ext
    change Units.map (algebraMap (𝓞 F) F).toMonoidHom (u⁻¹) = k.val
    apply mul_left_cancel (a := Units.map (algebraMap (𝓞 F) F).toMonoidHom u)
    rw [map_inv, mul_inv_cancel, hue]
  let : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  let : Group.FG φ.ker := Group.fg_of_surjective (f := j) hj
  let : Finite ((FractionalIdeal (𝓞 F)⁰ F)ˣ ⧸ φ.range) :=
    Finite.of_equiv (ClassGroup (𝓞 F)) (ClassGroup.equiv (R := 𝓞 F) F).toEquiv
  let : (powMonoidHom n : φ.ker →* φ.ker).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg φ.ker hn
  exact finite_power_fiber_classes φ n r

end ArtinPrimitiveRoots.A1.Theta
