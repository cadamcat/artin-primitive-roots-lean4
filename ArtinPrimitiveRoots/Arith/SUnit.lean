import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.GroupTheory.IndexNSmul

/-!
# Dirichlet's S-unit theorem

For a finite set of finite places of a number field, the S-unit group is finitely generated,
its torsion subgroup is the roots of unity, and its rank is the unit rank plus the number of
places in S.
-/

noncomputable section

open scoped nonZeroDivisors Classical

namespace ArtinPrimitiveRoots.Arith

open NumberField

variable (K : Type*) [Field K] [NumberField K]
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))

private abbrev sUnitGroup :=
  Set.unit (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K

private abbrev sUnitPlaces :=
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // v ∈ S}

/-- Evaluation of a valuation on the unit group of the fraction field. -/
private noncomputable def placeValuationHom
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Kˣ →* Multiplicative ℤ :=
  (WithZero.unitsWithZeroEquiv).toMonoidHom.comp
    (Units.map (v.valuation K).toMonoidHom)

private theorem placeValuationHom_eq_one_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    placeValuationHom K v x = 1 ↔ v.valuation K (x : K) = 1 := by
  constructor
  · intro h
    have h' : Units.map (v.valuation K).toMonoidHom x = 1 := by
      apply (WithZero.unitsWithZeroEquiv).injective
      change placeValuationHom K v x = 1
      exact h
    have hv := congrArg Units.val h'
    simpa [Units.coe_map] using hv
  · intro h
    have h' : Units.map (v.valuation K).toMonoidHom x = 1 := by
      apply Units.ext
      simpa [Units.coe_map] using h
    simp [placeValuationHom, h']
    rfl

private theorem placeValuationHom_toAdd
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    Multiplicative.toAdd (placeValuationHom K v x) =
      WithZero.log (v.valuation K (x : K)) := by
  simp [placeValuationHom, WithZero.toAdd_unzero_eq_log, Units.coe_map]

private theorem fractional_count_span_power
    (v w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {a : 𝓞 K} (ha : Ideal.span {a} = v.asIdeal ^ n) :
    FractionalIdeal.count K w (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) =
      if w = v then n else 0 := by
  classical
  rw [ha, FractionalIdeal.coeIdeal_pow]
  by_cases hwv : w = v
  · subst w
    simpa using (FractionalIdeal.count_pow_self K v n)
  · have hvw : v ≠ w := Ne.symm hwv
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime K w hvw]
    simp [hwv]

/-- The vector of valuations at the finite places in `S`. -/
private noncomputable def sUnitValuation :
    sUnitGroup K S →* (sUnitPlaces K S → Multiplicative ℤ) where
  toFun x v := placeValuationHom K v.1 x
  map_one' := by
    funext v
    exact (placeValuationHom K v.1).map_one
  map_mul' x y := by
    funext v
    exact (placeValuationHom K v.1).map_mul x y

private noncomputable def sUnitCoordsEquiv :
    Additive (sUnitPlaces K S → Multiplicative ℤ) ≃ₗ[ℤ]
      (sUnitPlaces K S → ℤ) where
  toFun x v := Multiplicative.toAdd (x.toMul v)
  invFun x := Additive.ofMul (fun v => Multiplicative.ofAdd (x v))
  left_inv x := by ext v; rfl
  right_inv x := by ext v; rfl
  map_add' x y := by ext v; simp
  map_smul' n x := by ext v; simp

private noncomputable def sUnitValuationAdd :
    Additive (sUnitGroup K S) →+ (sUnitPlaces K S → ℤ) :=
  (sUnitCoordsEquiv K S).toAddEquiv.toAddMonoidHom.comp
    (MonoidHom.toAdditive (sUnitValuation K S))

private theorem sUnitValuationAdd_ker :
    (sUnitValuationAdd K S).ker = (sUnitValuation K S).ker.toAddSubgroup := by
  ext x
  change sUnitValuationAdd K S x = 0 ↔ x ∈ (sUnitValuation K S).ker.toAddSubgroup
  constructor
  · intro hx
    have h0 : (MonoidHom.toAdditive (sUnitValuation K S)) x = 0 :=
      (sUnitCoordsEquiv K S).injective (by simpa [sUnitValuationAdd] using hx)
    change sUnitValuation K S x.toMul = 1 at h0
    exact (MonoidHom.mem_ker).mpr h0
  · intro hx
    have h0 : sUnitValuation K S x.toMul = 1 := (MonoidHom.mem_ker).mp hx
    have ha : (MonoidHom.toAdditive (sUnitValuation K S)) x = 0 := by
      change sUnitValuation K S x.toMul = 1
      exact h0
    simpa [sUnitValuationAdd] using congrArg (sUnitCoordsEquiv K S) ha

/-- The S-unit group away from no finite places is the ordinary unit group. -/
private noncomputable def emptySUnitEquiv :
    Set.unit (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) K ≃* (𝓞 K)ˣ := by
  let h : Set.integer (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) K =
      (⊥ : Subalgebra (𝓞 K) K) := IsDedekindDomain.integer_empty (𝓞 K) K
  exact (Set.unitEquivUnitsInteger (∅ : Set _) K).trans
    ((Units.mapEquiv (Subalgebra.equivOfEq _ _ h).toMulEquiv).trans
      (Units.mapEquiv
        (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 K) K)).toMulEquiv))

private noncomputable def sUnitKernelToEmpty :
    (sUnitValuation K S).ker →*
      Set.unit (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) K where
  toFun x := ⟨x.1, by
    intro v _
    by_cases hvS : v ∈ S
    · have hx : sUnitValuation K S x.1 = 1 := by
        have hx := x.2
        change sUnitValuation K S x.1 = 1 at hx
        exact hx
      have hval := congrFun hx ⟨v, hvS⟩
      exact (placeValuationHom_eq_one_iff K v x.1).mp hval
    · exact x.1.property v hvS
    ⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private noncomputable def emptyToSUnitKernel :
    Set.unit (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) K →*
      (sUnitValuation K S).ker where
  toFun x := ⟨⟨x.1, by
      intro v hvS
      exact x.2 v (by simp)
    ⟩, by
      rw [MonoidHom.mem_ker]
      ext v
      apply (placeValuationHom_eq_one_iff K v.1 x.1).2
      exact x.2 v.1 (by simp)
    ⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private theorem emptyToSUnitKernel_surjective :
    Function.Surjective (emptyToSUnitKernel K S) := by
  intro x
  refine ⟨sUnitKernelToEmpty K S x, ?_⟩
  apply Subtype.ext
  rfl

private theorem sUnitKernelToEmpty_injective :
    Function.Injective (sUnitKernelToEmpty K S) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : Set.unit (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) K =>
      (z : Kˣ)) h

private theorem sUnitKernelToEmpty_surjective :
    Function.Surjective (sUnitKernelToEmpty K S) := by
  intro x
  refine ⟨emptyToSUnitKernel K S x, ?_⟩
  apply Subtype.ext
  rfl

private noncomputable def sUnitKernelToOUnits :
    (sUnitValuation K S).ker →* (𝓞 K)ˣ :=
  (emptySUnitEquiv K).toMonoidHom.comp (sUnitKernelToEmpty K S)

private noncomputable def sUnitKernelEquivOUnits :
    (sUnitValuation K S).ker ≃* (𝓞 K)ˣ :=
  MulEquiv.ofBijective (sUnitKernelToOUnits K S) ⟨
    (emptySUnitEquiv K).injective.comp (sUnitKernelToEmpty_injective K S),
    (emptySUnitEquiv K).surjective.comp (sUnitKernelToEmpty_surjective K S)⟩

private noncomputable def sUnitTorsionToKernel :
    CommGroup.torsion (sUnitGroup K S) →* (sUnitValuation K S).ker where
  toFun x := ⟨x.1, by
    have hx : IsOfFinOrder (x.1 : sUnitGroup K S) := x.2
    have hmap : IsOfFinOrder (sUnitValuation K S x.1) := by
      obtain ⟨n, hn, hp⟩ := (isOfFinOrder_iff_pow_eq_one).mp hx
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      rw [← map_pow, hp, map_one]
    exact (MonoidHom.mem_ker).mpr ((isOfFinOrder_iff_eq_one _).mp hmap)
    ⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private noncomputable def sUnitTorsionToOUnits :
    CommGroup.torsion (sUnitGroup K S) →* (𝓞 K)ˣ :=
  (sUnitKernelEquivOUnits K S).toMonoidHom.comp (sUnitTorsionToKernel K S)

private noncomputable def sUnitTorsionToRoots :
    CommGroup.torsion (sUnitGroup K S) →* NumberField.Units.torsion K where
  toFun x := ⟨sUnitTorsionToOUnits K S x, by
    obtain ⟨n, hn, hp⟩ := (isOfFinOrder_iff_pow_eq_one).mp x.2
    have hp' : x ^ n = 1 := Subtype.ext hp
    exact (isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, by
      rw [← map_pow, hp', map_one]⟩
    ⟩
  map_one' := by
    apply Subtype.ext
    exact (sUnitTorsionToOUnits K S).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (sUnitTorsionToOUnits K S).map_mul x y

private theorem exists_principal_power_generator (v : sUnitPlaces K S) :
    ∃ a : 𝓞 K,
      Ideal.span {a} = v.1.asIdeal ^ Fintype.card (ClassGroup (𝓞 K)) := by
  let p0 : (Ideal (𝓞 K))⁰ := ⟨v.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.1.ne_bot⟩
  let n := Fintype.card (ClassGroup (𝓞 K))
  have hClass : ClassGroup.mk0 p0 ^ n = 1 := by
    simpa [n] using (pow_card_eq_one (x := ClassGroup.mk0 p0))
  have hn0 : v.1.asIdeal ^ n ≠ 0 := pow_ne_zero _ v.1.ne_bot
  have hClassPow :
      ClassGroup.mk0 ⟨v.1.asIdeal ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr hn0⟩ = 1 := by
    change ClassGroup.mk0 (p0 ^ n) = 1
    rw [map_pow]
    exact hClass
  have hPrincipal : (v.1.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hn0)).mp hClassPow
  obtain ⟨a, ha⟩ := hPrincipal.principal
  exact ⟨a, ha.symm⟩

private theorem valuation_eq_exp_neg_fractional_count
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ≠ 0) :
    v.valuation K (algebraMap (𝓞 K) K a) =
      WithZero.exp (-FractionalIdeal.count K v
        (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [v.valuation_of_algebraMap, v.intValuation_if_neg ha]
  congr 1
  have hspan : Ideal.span {a} ≠ ⊥ := by
    intro h
    exact ha (Ideal.span_singleton_eq_bot.mp h)
  have hfrac : (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hspan
  rw [FractionalIdeal.count_well_defined K v hfrac (a := 1)
    (J := Ideal.span {a}) (by simp)]
  rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one,
    Associates.factors_one, Associates.count_zero v.associates_irreducible]
  ring

private theorem exists_sUnit_basis_image (v : sUnitPlaces K S) :
    ∃ x : sUnitGroup K S,
      sUnitValuationAdd K S (Additive.ofMul x) =
        (Pi.single (M := fun _ : sUnitPlaces K S => ℤ) v
          (Fintype.card (ClassGroup (𝓞 K)) : ℤ)) := by
  classical
  obtain ⟨a, ha⟩ := exists_principal_power_generator K S v
  have ha0 : a ≠ 0 := by
    intro hz
    have hpow0 : v.1.asIdeal ^ Fintype.card (ClassGroup (𝓞 K)) = ⊥ := by
      simpa [hz] using ha.symm
    exact (pow_ne_zero _ v.1.ne_bot) hpow0
  have hnonzero : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h
    apply ha0
    exact (IsFractionRing.injective (𝓞 K) K) (by simpa using h)
  let u : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) hnonzero
  have hcount (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      FractionalIdeal.count K w (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) =
        if w = v.1 then (Fintype.card (ClassGroup (𝓞 K)) : ℤ) else 0 := by
    simpa using (fractional_count_span_power K v.1 w
      (Fintype.card (ClassGroup (𝓞 K))) ha)
  have hvaluationInv (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      w.valuation K ((u⁻¹ : Kˣ) : K) =
        WithZero.exp (FractionalIdeal.count K w
          (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K)) := by
    calc
      w.valuation K ((u⁻¹ : Kˣ) : K) = (w.valuation K (u : K))⁻¹ := by
        rw [Units.val_inv_eq_inv_val, map_inv₀]
      _ = (WithZero.exp (-FractionalIdeal.count K w
            (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K)))⁻¹ := by
          change (w.valuation K (algebraMap (𝓞 K) K a))⁻¹ = _
          exact congrArg (fun z : WithZero (Multiplicative ℤ) => z⁻¹)
            (valuation_eq_exp_neg_fractional_count K w ha0)
      _ = WithZero.exp (FractionalIdeal.count K w
            (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K)) := by
          rw [WithZero.exp_neg, inv_inv]
  let x : sUnitGroup K S := ⟨u⁻¹, by
    intro w hw
    have hwv : w ≠ v.1 := by
      intro h
      exact hw (h ▸ v.2)
    rw [hvaluationInv w, hcount w]
    simp [hwv]
  ⟩
  refine ⟨x, ?_⟩
  ext w
  change Multiplicative.toAdd (placeValuationHom K w.1 (x : Kˣ)) =
    (Pi.single (M := fun _ : sUnitPlaces K S => ℤ) v
      (Fintype.card (ClassGroup (𝓞 K)) : ℤ)) w
  rw [placeValuationHom_toAdd, hvaluationInv w.1, hcount w.1]
  by_cases hw : w = v
  · subst w
    simp [Pi.single]
  · simp [Pi.single, hw]

private theorem nsmulRange_le_sUnitValuationRange :
    (nsmulAddMonoidHom
        (α := sUnitPlaces K S → ℤ) (Fintype.card (ClassGroup (𝓞 K)))).range ≤
      (sUnitValuationAdd K S).toIntLinearMap.range.toAddSubgroup := by
  classical
  intro z hz
  obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hz
  have hdecomp :
      (Fintype.card (ClassGroup (𝓞 K)) : ℕ) • y =
        ∑ i : sUnitPlaces K S,
          y i • Pi.single (M := fun _ : sUnitPlaces K S => ℤ) i
            (Fintype.card (ClassGroup (𝓞 K)) : ℤ) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [Pi.single_apply]
      ring
    · intro j hj hji
      simp [Pi.single_apply, hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  change (Fintype.card (ClassGroup (𝓞 K)) : ℕ) • y ∈
    (sUnitValuationAdd K S).toIntLinearMap.range
  rw [hdecomp]
  apply Submodule.sum_mem
  intro i hi
  obtain ⟨x, hx⟩ := exists_sUnit_basis_image K S i
  exact Submodule.smul_mem _ (y i) ⟨Additive.ofMul x, hx⟩

private theorem sUnitValuationRange_finiteIndex :
    ((sUnitValuationAdd K S).toIntLinearMap.range).toAddSubgroup.FiniteIndex := by
  classical
  let M := sUnitPlaces K S → ℤ
  let n := Fintype.card (ClassGroup (𝓞 K))
  have hn : n ≠ 0 := (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 K))).ne'
  haveI : Module.Free ℤ M := inferInstance
  haveI : Module.Finite ℤ M := inferInstance
  have hN : (nsmulAddMonoidHom (α := M) n).range.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff, AddSubgroup.index_range_nsmul]
    exact pow_ne_zero _ hn
  letI : (nsmulAddMonoidHom (α := M) n).range.FiniteIndex := hN
  exact AddSubgroup.finiteIndex_of_le (nsmulRange_le_sUnitValuationRange K S)

private theorem sUnitValuationLinearMap_ker_eq :
    (sUnitValuationAdd K S).toIntLinearMap.ker =
      ((sUnitValuation K S).ker.toAddSubgroup).toIntSubmodule := by
  rw [AddMonoidHom.coe_toIntLinearMap_ker, sUnitValuationAdd_ker]

private noncomputable def sUnitKernelAddEquiv :
    Additive ((sUnitValuation K S).ker) ≃+
      ↥(((sUnitValuation K S).ker.toAddSubgroup).toIntSubmodule) where
  toFun x := ⟨Additive.ofMul (x.toMul : sUnitGroup K S), x.toMul.property⟩
  invFun x := Additive.ofMul ⟨x.1.toMul, x.2⟩
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl

private noncomputable def sUnitQuotientAddEquiv :
    Additive (sUnitGroup K S ⧸ CommGroup.torsion (sUnitGroup K S)) ≃+
      Additive (sUnitGroup K S) ⧸
        (CommGroup.torsion (sUnitGroup K S)).toAddSubgroup.toIntSubmodule := by
  let H := CommGroup.torsion (sUnitGroup K S)
  let f : Additive (sUnitGroup K S) →+ Additive (sUnitGroup K S ⧸ H) :=
    MonoidHom.toAdditive (QuotientGroup.mk' H)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H (y.toMul)
    exact ⟨Additive.ofMul x, rfl⟩
  have hker : f.ker = H.toAddSubgroup := by
    change (MonoidHom.toAdditive (QuotientGroup.mk' H)).ker = H.toAddSubgroup
    rw [MonoidHom.coe_toAdditive_ker, QuotientGroup.ker_mk']
  have hmap : f.ker.map (AddEquiv.refl (Additive (sUnitGroup K S))) =
      H.toAddSubgroup := by
    simpa using hker
  exact (QuotientAddGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientAddGroup.congr f.ker H.toAddSubgroup (AddEquiv.refl _) hmap)

private theorem sUnitTorsionToRoots_injective :
    Function.Injective (sUnitTorsionToRoots K S) := by
  intro x y h
  apply Subtype.ext
  have hO : sUnitTorsionToOUnits K S x = sUnitTorsionToOUnits K S y :=
    congrArg (fun z : NumberField.Units.torsion K => (z : (𝓞 K)ˣ)) h
  have hK := (sUnitKernelEquivOUnits K S).injective hO
  exact congrArg (fun z : (sUnitValuation K S).ker => (z : sUnitGroup K S)) hK

private theorem sUnitTorsionToRoots_surjective :
    Function.Surjective (sUnitTorsionToRoots K S) := by
  intro ζ
  let e := sUnitKernelEquivOUnits K S
  let x : (sUnitValuation K S).ker := e.symm ζ.1
  have hx : IsOfFinOrder x := by
    obtain ⟨n, hn, hp⟩ := (isOfFinOrder_iff_pow_eq_one).mp ζ.2
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply e.injective
    simpa [x, map_pow] using hp
  have hxS : IsOfFinOrder (x : sUnitGroup K S) := by
    obtain ⟨n, hn, hp⟩ := (isOfFinOrder_iff_pow_eq_one).mp hx
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    simpa using congrArg (fun z : (sUnitValuation K S).ker => (z : sUnitGroup K S)) hp
  let y : CommGroup.torsion (sUnitGroup K S) := ⟨x.1, hxS⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have hy : sUnitTorsionToKernel K S y = x := by
    apply Subtype.ext
    rfl
  change e (sUnitTorsionToKernel K S y) = ζ.1
  rw [hy]
  exact e.apply_symm_apply ζ.1

/-- The torsion subgroup of the S-unit group is the group of roots of unity of `K`.

The equivalence is the one induced by viewing roots of unity as units of `𝓞 K` and then as
S-units. -/
theorem sUnit_torsion :
    Nonempty (CommGroup.torsion
      (Set.unit (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K) ≃*
      NumberField.Units.torsion K) := by
  exact ⟨MulEquiv.ofBijective (sUnitTorsionToRoots K S)
    ⟨sUnitTorsionToRoots_injective K S, sUnitTorsionToRoots_surjective K S⟩⟩

/-- The S-unit group of a number field is finitely generated. -/
theorem sUnit_fg : Monoid.FG
    (Set.unit (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K) := by
  classical
  haveI : Group.FG (𝓞 K)ˣ :=
    Group.fg_iff_monoid_fg.mpr (inferInstance : Monoid.FG (𝓞 K)ˣ)
  have hEmpty : Group.FG
      (Set.unit (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) K) :=
    Group.fg_of_surjective (f := (emptySUnitEquiv K).symm.toMonoidHom)
      (emptySUnitEquiv K).symm.surjective
  letI : Group.FG
      (Set.unit (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) K) := hEmpty
  have hKernelGroup : Group.FG ((sUnitValuation K S).ker) :=
    Group.fg_of_surjective (f := emptyToSUnitKernel K S)
      (emptyToSUnitKernel_surjective K S)
  have hKernelAdd : ((sUnitValuation K S).ker).toAddSubgroup.FG :=
    (Subgroup.fg_iff_add_fg (sUnitValuation K S).ker).mp
      ((Group.fg_iff_subgroup_fg (sUnitValuation K S).ker).mp hKernelGroup)
  rw [Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg,
    ← Module.Finite.iff_addGroup_fg, Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (sUnitValuationAdd K S).toIntLinearMap ?_ ?_
  · haveI : Finite (sUnitPlaces K S) := inferInstance
    haveI : Module.Finite ℤ (sUnitPlaces K S → ℤ) := inferInstance
    haveI : IsNoetherian ℤ (sUnitPlaces K S → ℤ) := inferInstance
    have hrange :
        (LinearMap.range (sUnitValuationAdd K S).toIntLinearMap).FG :=
      IsNoetherian.noetherian _
    simpa [Submodule.map_top] using hrange
  · rw [inf_of_le_right le_top, AddMonoidHom.coe_toIntLinearMap_ker,
      Submodule.fg_iff_addSubgroup_fg, sUnitValuationAdd_ker,
      AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact hKernelAdd

/-- The torsion-free rank of the S-unit group is the unit rank plus the number of finite places
in `S`. -/
theorem sUnit_rank :
    Module.finrank ℤ (Additive ((Set.unit
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K) ⧸
      CommGroup.torsion (Set.unit
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v ∈ S) K))) =
      NumberField.Units.rank K + S.card := by
  classical
  have hReduce :
      Module.finrank ℤ
        (Additive ((sUnitGroup K S) ⧸ CommGroup.torsion (sUnitGroup K S))) =
        Module.finrank ℤ (Additive (sUnitGroup K S)) := by
    calc
      Module.finrank ℤ
          (Additive ((sUnitGroup K S) ⧸ CommGroup.torsion (sUnitGroup K S))) =
          Module.finrank ℤ
            (Additive (sUnitGroup K S) ⧸
              (CommGroup.torsion (sUnitGroup K S)).toAddSubgroup.toIntSubmodule) :=
        LinearEquiv.finrank_eq (sUnitQuotientAddEquiv K S).toIntLinearEquiv
      _ = Module.finrank ℤ (Additive (sUnitGroup K S)) := by
        have hTors :
            (CommGroup.torsion (sUnitGroup K S)).toAddSubgroup =
              AddCommGroup.torsion (Additive (sUnitGroup K S)) := by
          ext x
          exact isOfFinAddOrder_ofMul_iff.symm
        rw [hTors]
        exact finrank_quotient_torsion_eq
  rw [hReduce]
  let f := (sUnitValuationAdd K S).toIntLinearMap
  let M := sUnitPlaces K S → ℤ
  have hAddMonoidFG : AddMonoid.FG (Additive (sUnitGroup K S)) :=
    (Monoid.fg_iff_add_fg).mp (sUnit_fg K S)
  have hAddGroupFG : AddGroup.FG (Additive (sUnitGroup K S)) :=
    AddGroup.fg_iff_addMonoid_fg.mpr hAddMonoidFG
  haveI : Module.Finite ℤ (Additive (sUnitGroup K S)) :=
    Module.Finite.iff_addGroup_fg.mpr hAddGroupFG
  have hNull :
      Module.finrank ℤ (Additive (sUnitGroup K S)) =
        Module.finrank ℤ f.range + Module.finrank ℤ f.ker := by
    rw [← LinearEquiv.finrank_eq f.quotKerEquivRange]
    exact (f.ker).finrank_quotient_add_finrank.symm
  haveI : (f.range).toAddSubgroup.FiniteIndex := sUnitValuationRange_finiteIndex K S
  haveI : Module.Finite ℤ M := inferInstance
  haveI : Module.IsTorsionFree ℤ M := inferInstance
  let eRange : ↥f.range.toAddSubgroup ≃ₗ[ℤ] ↥f.range :=
    { toFun := fun x => ⟨x.1, by
        change x.1 ∈ (f.range.toAddSubgroup).toIntSubmodule
        exact x.2⟩
      invFun := fun x => ⟨x.1, by
        change x.1 ∈ f.range.toAddSubgroup
        exact x.2⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl
      map_add' := fun x y => by apply Subtype.ext; rfl
      map_smul' := fun n x => by apply Subtype.ext; rfl }
  have hRangeRank : Module.finrank ℤ f.range = Module.finrank ℤ M := by
    calc
      Module.finrank ℤ f.range = Module.finrank ℤ f.range.toAddSubgroup :=
        (LinearEquiv.finrank_eq eRange).symm
      _ = Module.finrank ℤ M := AddSubgroup.finrank_eq_of_finiteIndex f.range.toAddSubgroup
  have hTargetRank : Module.finrank ℤ M = S.card := by
    rw [Module.finrank_fintype_fun_eq_card]
    simpa [sUnitPlaces] using
      (Fintype.card_of_subtype S (fun _ => Iff.rfl))
  have hKerEq := sUnitValuationLinearMap_ker_eq K S
  let eKer : f.ker ≃ₗ[ℤ] Additive ((sUnitValuation K S).ker) :=
    (LinearEquiv.ofEq _ _ hKerEq).trans (sUnitKernelAddEquiv K S).toIntLinearEquiv.symm
  have hKerRank : Module.finrank ℤ f.ker = NumberField.Units.rank K := by
    calc
      Module.finrank ℤ f.ker =
          Module.finrank ℤ (Additive ((sUnitValuation K S).ker)) :=
        LinearEquiv.finrank_eq eKer
      _ = Module.finrank ℤ (Additive (𝓞 K)ˣ) :=
        LinearEquiv.finrank_eq
          (sUnitKernelEquivOUnits K S).toAdditive.toIntLinearEquiv
      _ = NumberField.Units.rank K := NumberField.Units.finrank_eq K
  omega

end ArtinPrimitiveRoots.Arith

end
