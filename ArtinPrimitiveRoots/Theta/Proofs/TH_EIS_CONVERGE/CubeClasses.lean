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

open scoped NumberField nonZeroDivisors in
/-- Rational elements with cubic valuation classes supported in a finite set have finitely many cube classes. -/
theorem finite_cubic_valuation_classes (F : Type*) [Field F] [NumberField F]
    (W : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    Set.Finite ((QuotientGroup.mk' (powMonoidHom 3 : Fˣ →* Fˣ).range) ''
      {a : Fˣ | ∀ v, v ∉ W → (3 : ℤ) ∣
        FractionalIdeal.count F v (toPrincipalIdeal (𝓞 F) F a : FractionalIdeal (𝓞 F)⁰ F)}) := by
  classical
  let V := IsDedekindDomain.HeightOneSpectrum (𝓞 F)
  let FI := FractionalIdeal (𝓞 F)⁰ F
  let p : V → FIˣ := fun v => Units.mk0 (v.asIdeal : FI)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  let e (c : W → Fin 3) (v : V) : ℤ :=
    if hv : v ∈ W then (c ⟨v, hv⟩).val else 0
  let offset (c : W → Fin 3) : FIˣ := ∏ v ∈ W, p v ^ e c v
  let fiber (c : W → Fin 3) : Set (Fˣ ⧸ (powMonoidHom 3 : Fˣ →* Fˣ).range) :=
    (QuotientGroup.mk' (powMonoidHom 3 : Fˣ →* Fˣ).range) ''
      {a : Fˣ | ∃ J : FIˣ, toPrincipalIdeal (𝓞 F) F a = J ^ 3 * offset c}
  have hf : (⋃ c : W → Fin 3, fiber c).Finite :=
    Set.finite_iUnion fun c => finite_principal_power_fiber_classes F 3 (by decide) (offset c)
  apply hf.subset
  rintro q ⟨a, ha, rfl⟩
  let I : FIˣ := toPrincipalIdeal (𝓞 F) F a
  let d : V → ℤ := fun v => FractionalIdeal.count F v (I : FI)
  have hd : (Function.support d).Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (I : FI))
  let S : Finset V := hd.toFinset ∪ W
  have hW : W ⊆ S := Finset.subset_union_right
  have hout (v : V) (hv : v ∉ S) : d v = 0 := by
    by_contra h
    exact hv (Finset.mem_union.mpr (Or.inl (hd.mem_toFinset.mpr h)))
  have hfactor : I = ∏ v ∈ S, p v ^ d v := by
    apply Units.ext
    simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val]
    change (I : FI) = ∏ v ∈ S, (v.asIdeal : FI) ^ d v
    calc
      _ = ∏ᶠ v : V, (v.asIdeal : FI) ^ d v :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' F (Units.ne_zero I)).symm
      _ = _ := finprod_eq_prod_of_mulSupport_subset _
        (Function.mulSupport_subset_iff'.mpr fun v hv => by rw [hout v hv, zpow_zero])
  let c : W → Fin 3 := fun v => ⟨(d v.val % 3).toNat, by
    have h0 := Int.emod_nonneg (d v.val) (by norm_num : (3 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos (d v.val) (by norm_num : (0 : ℤ) < 3)
    omega⟩
  have he (v : V) : e c v = d v % 3 := by
    dsimp only [e]
    split_ifs with hv
    · change ((d v % 3).toNat : ℤ) = d v % 3
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
    · exact (Int.emod_eq_zero_of_dvd (ha v hv)).symm
  let J : FIˣ := ∏ v ∈ S, p v ^ (d v / 3)
  have hterm (v : V) : p v ^ d v = (p v ^ (d v / 3)) ^ 3 * p v ^ e c v := by
    have hdecomp : d v = (d v / 3) * 3 + e c v := by rw [he]; omega
    calc
      p v ^ d v = p v ^ ((d v / 3) * 3 + e c v) := congrArg (fun k : ℤ => p v ^ k) hdecomp
      _ = _ := by
        rw [zpow_add, zpow_mul]
        exact congrArg (fun t : FIˣ => t * p v ^ e c v)
          (zpow_natCast (p v ^ (d v / 3)) 3)
  have hoffset : (∏ v ∈ S, p v ^ e c v) = offset c := by
    apply (Finset.prod_subset hW ?_).symm
    intro v hvS hvW
    simp only [e, dite_eq_right hvW, zpow_zero]
  have hsplit : I = J ^ 3 * offset c := by
    calc
      I = ∏ v ∈ S, p v ^ d v := hfactor
      _ = ∏ v ∈ S, (p v ^ (d v / 3)) ^ 3 * p v ^ e c v :=
        Finset.prod_congr rfl fun v _ => hterm v
      _ = (∏ v ∈ S, p v ^ (d v / 3)) ^ 3 * ∏ v ∈ S, p v ^ e c v := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow]
      _ = _ := by rw [hoffset]
  exact Set.mem_iUnion.mpr ⟨c, a, ⟨J, hsplit⟩, rfl⟩

end ArtinPrimitiveRoots.A1.Theta
