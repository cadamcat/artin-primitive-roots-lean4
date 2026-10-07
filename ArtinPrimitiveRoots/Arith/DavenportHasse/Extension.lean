import ArtinPrimitiveRoots.Arith.DavenportHasse.Polynomial

namespace ArtinPrimitiveRoots.Arith

noncomputable instance dhFintypePolynomialDegreeLE {k : Type*} [Field k] [Fintype k]
    (n : ℕ) : Fintype {p : Polynomial k // p.natDegree ≤ n} := by
  classical
  let coeffVec : {p : Polynomial k // p.natDegree ≤ n} → Fin (n + 1) → k :=
    fun p i => p.val.coeff i
  have hinj : Function.Injective coeffVec := by
    intro p q h
    apply Subtype.ext
    apply Polynomial.ext
    intro i
    by_cases hi : i ≤ n
    · have hcoeff := congrFun h ⟨i, by omega⟩
      exact hcoeff
    · have hp0 := (Polynomial.natDegree_le_iff_coeff_eq_zero.mp p.property) i
        (Nat.lt_of_not_ge hi)
      have hq0 := (Polynomial.natDegree_le_iff_coeff_eq_zero.mp q.property) i
        (Nat.lt_of_not_ge hi)
      simp [hp0, hq0]
  letI : Finite {p : Polynomial k // p.natDegree ≤ n} := Finite.of_injective coeffVec hinj
  exact Fintype.ofFinite _

abbrev dhIrrBounded (k : Type*) [Field k] (n : ℕ) :=
  {p : {p : Polynomial k // p.natDegree ≤ n} // p.val.Monic ∧ Irreducible p.val}

noncomputable instance dhFintypeIrrBounded {k : Type*} [Field k] [Fintype k] (n : ℕ) :
    Fintype (dhIrrBounded k n) := by
  classical
  infer_instance

theorem norm_eq_minpoly_coeff_pow {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (x : K) :
    Algebra.norm k x =
      ((-1 : k) ^ (minpoly k x).natDegree * (minpoly k x).coeff 0) ^
        Module.finrank (IntermediateField.adjoin k {x}) K := by
  have hx : IsIntegral k x := IsIntegral.of_finite k x
  rw [Algebra.norm_eq_norm_adjoin k x]
  rw [← IntermediateField.adjoin.powerBasis_gen hx]
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (IntermediateField.adjoin.powerBasis hx)]
  simp [IntermediateField.adjoin.powerBasis_dim, IntermediateField.minpoly_gen]

theorem dhLiftWeight_eq_dhPolyWeight_pow {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (x : K) :
    (-1 : ℂ) ^ Module.finrank k K *
        (χ (Algebra.norm k x) * ψ (Algebra.trace k K x)) =
      dhPolyWeight χ ψ (minpoly k x) ^
        Module.finrank (IntermediateField.adjoin k {x}) K := by
  let E := IntermediateField.adjoin k {x}
  have hx : IsIntegral k x := IsIntegral.of_finite k x
  have hd : Module.finrank k E = (minpoly k x).natDegree := IntermediateField.adjoin.finrank hx
  have hdim := Module.finrank_mul_finrank k E K
  have htrace := trace_eq_finrank_mul_minpoly_nextCoeff k x
  have hnorm := norm_eq_minpoly_coeff_pow (k := k) (K := K) x
  rw [hnorm, htrace]
  rw [← nsmul_eq_mul, ψ.map_nsmul_eq_pow]
  simp only [dhPolyWeight, map_pow]
  have hdeg : Module.finrank k K = (minpoly k x).natDegree *
      Module.finrank E K := by simpa [E, hd] using hdim.symm
  rw [hdeg, pow_mul]
  ring

noncomputable def dhMinpolyFinset {k K : Type*} [Field k] [Field K] [Fintype K]
    [Algebra k K] : Finset (Polynomial k) := by
  classical
  exact Finset.univ.image (fun x : K => minpoly k x)

abbrev dhMinpolyRange {k K : Type*} [Field k] [Field K] [Fintype K] [Algebra k K] :=
  {p : Polynomial k // p ∈ dhMinpolyFinset (k := k) (K := K)}

noncomputable def dhMinpolyFiberEquiv {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (p : dhMinpolyRange (k := k) (K := K)) :
    {x : K // minpoly k x = p.val} ≃ p.val.rootSet K := by
  classical
  have hpw : ∃ x₀ : K, minpoly k x₀ = p.val := by
    obtain ⟨x₀, -, hx₀⟩ := Finset.mem_image.mp p.property
    exact ⟨x₀, hx₀⟩
  let x₀ := Classical.choose hpw
  have hx₀ : minpoly k x₀ = p.val := Classical.choose_spec hpw
  have hx₀I : IsIntegral k x₀ := IsIntegral.of_finite k x₀
  have hpm : p.val.Monic := by rw [← hx₀]; exact minpoly.monic hx₀I
  have hpi : Irreducible p.val := by rw [← hx₀]; exact minpoly.irreducible hx₀I
  refine
    { toFun := fun x => ⟨x.val, ?_⟩
      invFun := fun y => ⟨y.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Polynomial.Monic.mem_rootSet hpm]
    calc
      Polynomial.aeval x.val p.val =
          Polynomial.aeval x.val (minpoly k x.val) := congrArg _ x.property.symm
      _ = 0 := minpoly.aeval k x.val
  · have hy := Polynomial.aeval_eq_zero_of_mem_rootSet y.property
    have hdiv : minpoly k y.val ∣ p.val := minpoly.dvd k y.val hy
    have hminI : Irreducible (minpoly k y.val) :=
      minpoly.irreducible (IsIntegral.of_finite k y.val)
    have hnotUnit : ¬ IsUnit (minpoly k y.val) := by
      intro hu
      have hone := (minpoly.monic (IsIntegral.of_finite k y.val)).isUnit_iff.mp hu
      have hpos := hminI.natDegree_pos
      rw [hone, Polynomial.natDegree_one] at hpos
      norm_num at hpos
    rcases hpi.dvd_iff.mp hdiv with hu | hassoc
    · exact (hnotUnit hu).elim
    · exact Polynomial.eq_of_monic_of_associated
        (minpoly.monic (IsIntegral.of_finite k y.val)) hpm hassoc.symm
  · intro x
    apply Subtype.ext
    rfl
  · intro y
    apply Subtype.ext
    rfl

noncomputable instance dhFintypeMinpolyFiber {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (p : Polynomial k) :
    Fintype {x : K // minpoly k x = p} := by
  classical
  letI : DecidablePred (fun x : K => minpoly k x = p) := Classical.decPred _
  exact Fintype.ofFinite _

theorem dhMinpolyFiber_card {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (p : dhMinpolyRange (k := k) (K := K)) :
    Fintype.card {x : K // minpoly k x = p.val} = p.val.natDegree := by
  classical
  rw [Fintype.card_congr (dhMinpolyFiberEquiv p)]
  obtain ⟨x₀, -, hx₀⟩ := Finset.mem_image.mp p.property
  have hx₀I : IsIntegral k x₀ := IsIntegral.of_finite k x₀
  have hsep : p.val.Separable := by
    rw [← hx₀]
    exact PerfectField.separable_of_irreducible (minpoly.irreducible hx₀I)
  have hsplit : (p.val.map (algebraMap k K)).Splits := by
    rw [← hx₀]
    exact IsGalois.splits k x₀
  exact Polynomial.card_rootSet_eq_natDegree hsep hsplit

noncomputable def dhMinpolyDecompEquiv {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] :
    K ≃ Σ p : dhMinpolyRange (k := k) (K := K),
      {x : K // minpoly k x = p.val} := by
  classical
  refine
    { toFun := fun x =>
        ⟨⟨minpoly k x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩, ⟨x, rfl⟩⟩
      invFun := fun y => y.2.val
      left_inv := fun _ => rfl
      right_inv := ?_ }
  intro y
  rcases y with ⟨⟨p, hp⟩, ⟨x, hx⟩⟩
  have hxp : minpoly k x = p := by simpa using hx
  subst p
  rfl

noncomputable def dhLiftWeight {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K]
    [Algebra k K] (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (x : K) : ℂ :=
  (-1 : ℂ) ^ Module.finrank k K *
    (χ (Algebra.norm k x) * ψ (Algebra.trace k K x))

theorem dhLiftWeight_sum_minpoly {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (χ : MulChar k ℂ) (ψ : AddChar k ℂ) :
    ∑ x : K, dhLiftWeight χ ψ x =
      ∑ p : dhMinpolyRange (k := k) (K := K),
        (p.val.natDegree : ℂ) * (dhPolyWeight χ ψ p.val) ^
          (Module.finrank k K / p.val.natDegree) := by
  classical
  change (∑ x : K,
      (fun z : Σ p : dhMinpolyRange (k := k) (K := K),
        {x : K // minpoly k x = p.val} => dhLiftWeight χ ψ z.2.val)
        (dhMinpolyDecompEquiv (k := k) (K := K) x)) = _
  rw [Equiv.sum_comp (dhMinpolyDecompEquiv (k := k) (K := K))
    (fun z => dhLiftWeight χ ψ z.2.val)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  have hpw : ∃ x₀ : K, minpoly k x₀ = p.val := by
    obtain ⟨x₀, -, hx₀⟩ := Finset.mem_image.mp p.property
    exact ⟨x₀, hx₀⟩
  let x₀ := Classical.choose hpw
  have hx₀ : minpoly k x₀ = p.val := Classical.choose_spec hpw
  have hx₀I : IsIntegral k x₀ := IsIntegral.of_finite k x₀
  have hdvd : p.val.natDegree ∣ Module.finrank k K := by
    have h := minpoly.degree_dvd (K := k) (L := K) hx₀I
    rw [hx₀] at h
    exact h
  have hdpos : 0 < p.val.natDegree := by
    rw [← hx₀]
    exact (minpoly.irreducible hx₀I).natDegree_pos
  have hinner (x : {x : K // minpoly k x = p.val}) :
      dhLiftWeight χ ψ x.val =
        dhPolyWeight χ ψ p.val ^ (Module.finrank k K / p.val.natDegree) := by
    have hxI : IsIntegral k x.val := IsIntegral.of_finite k x.val
    have hrel : Module.finrank (IntermediateField.adjoin k {x.val}) K =
        Module.finrank k K / p.val.natDegree := by
      have hd := IntermediateField.adjoin.finrank hxI
      rw [x.property] at hd
      have hdim := Module.finrank_mul_finrank k (IntermediateField.adjoin k {x.val}) K
      rw [hd] at hdim
      calc
        Module.finrank (IntermediateField.adjoin k {x.val}) K =
            (p.val.natDegree * Module.finrank (IntermediateField.adjoin k {x.val}) K) /
              p.val.natDegree := by rw [Nat.mul_div_cancel_left _ hdpos]
        _ = Module.finrank k K / p.val.natDegree := by rw [hdim]
    have h := dhLiftWeight_eq_dhPolyWeight_pow χ ψ x.val
    rw [x.property, hrel] at h
    simpa [dhLiftWeight] using h
  calc
    ∑ x : {x : K // minpoly k x = p.val}, dhLiftWeight χ ψ x.val =
        ∑ x : {x : K // minpoly k x = p.val},
          dhPolyWeight χ ψ p.val ^ (Module.finrank k K / p.val.natDegree) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hinner x
    _ = (Fintype.card {x : K // minpoly k x = p.val} : ℂ) *
          dhPolyWeight χ ψ p.val ^ (Module.finrank k K / p.val.natDegree) := by simp
    _ = (p.val.natDegree : ℂ) *
          dhPolyWeight χ ψ p.val ^ (Module.finrank k K / p.val.natDegree) := by
            rw [dhMinpolyFiber_card p]

noncomputable def dhEulerFactor {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) (p : dhIrrBounded k n) : PowerSeries ℂ :=
  PowerSeries.subst (PowerSeries.X ^ p.val.val.natDegree)
    (dhGeom (dhPolyWeight χ ψ p.val.val))

@[simp] theorem coeff_dhEulerFactor {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) (p : dhIrrBounded k n) (j : ℕ) :
    PowerSeries.coeff j (dhEulerFactor χ ψ n p) =
      if p.val.val.natDegree ∣ j then
        (dhPolyWeight χ ψ p.val.val) ^ (j / p.val.val.natDegree)
      else 0 := by
  rw [dhEulerFactor, PowerSeries.coeff_subst_X_pow
    (p.property.2.natDegree_pos.ne')]
  simp [coeff_dhGeom]

noncomputable def dhEulerProduct {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) : PowerSeries ℂ :=
  ∏ p : dhIrrBounded k n, dhEulerFactor χ ψ n p

noncomputable def dhEulerGeomFactor (a : ℂ) (d : ℕ) : PowerSeries ℂ :=
  PowerSeries.subst (PowerSeries.X ^ d) (dhGeom a)

noncomputable def dhEulerGeomInverseFactor (a : ℂ) (d : ℕ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X ^ d

theorem dhEulerGeomFactor_mul_inverse (a : ℂ) (d : ℕ) (hd : d ≠ 0) :
    dhEulerGeomFactor a d * dhEulerGeomInverseFactor a d = 1 := by
  let x : PowerSeries ℂ := PowerSeries.X ^ d
  have hx : PowerSeries.HasSubst x := by
    dsimp [x]
    exact PowerSeries.HasSubst.X_pow hd
  have hC : (PowerSeries.substAlgHom hx) (PowerSeries.C a) = PowerSeries.C a := by
    exact (PowerSeries.substAlgHom hx).commutes a
  have hlin : (1 - PowerSeries.C a * PowerSeries.X).subst x =
      1 - PowerSeries.C a * PowerSeries.X ^ d := by
    rw [← PowerSeries.coe_substAlgHom hx, map_sub, map_mul,
      PowerSeries.substAlgHom_X hx]
    rw [map_one, hC]
  calc
    _ = (dhGeom a).subst x * (1 - PowerSeries.C a * PowerSeries.X).subst x := by
      simp [dhEulerGeomFactor, dhEulerGeomInverseFactor, hlin, x]
    _ = (dhGeom a * (1 - PowerSeries.C a * PowerSeries.X)).subst x :=
      (PowerSeries.subst_mul hx _ _).symm
    _ = (1 : PowerSeries ℂ).subst x := by rw [dhGeom_mul_one_sub]
    _ = 1 := by
      rw [← PowerSeries.coe_substAlgHom hx, map_one]

theorem derivative_one_sub_C_mul_X_pow (a : ℂ) (d : ℕ) :
    PowerSeries.derivative (1 - PowerSeries.C a * PowerSeries.X ^ d) =
      -(PowerSeries.C a * PowerSeries.C (d : ℂ) * PowerSeries.X ^ (d - 1)) := by
  have hpow : PowerSeries.derivative (PowerSeries.X ^ d : PowerSeries ℂ) =
      PowerSeries.C (d : ℂ) * PowerSeries.X ^ (d - 1) := by
    rw [PowerSeries.derivative_pow]
    simp [PowerSeries.derivative_X, mul_assoc]
  rw [map_sub, PowerSeries.derivative_one, Derivation.leibniz,
    PowerSeries.derivative_C, hpow]
  simp only [smul_eq_mul, mul_zero, add_zero, zero_sub]
  ring

theorem dhEulerGeomFactor_log_derivative (a : ℂ) (d : ℕ) (hd : d ≠ 0) :
    PowerSeries.X * PowerSeries.derivative (dhEulerGeomFactor a d) *
        dhEulerGeomInverseFactor a d =
      PowerSeries.C (d : ℂ) * PowerSeries.C a * PowerSeries.X ^ d *
        dhEulerGeomFactor a d := by
  have hlocal := dhEulerGeomFactor_mul_inverse a d hd
  have hderiv := congrArg PowerSeries.derivative hlocal
  have hprod : PowerSeries.derivative (dhEulerGeomFactor a d) *
      dhEulerGeomInverseFactor a d =
      dhEulerGeomFactor a d *
        (PowerSeries.C a * PowerSeries.C (d : ℂ) * PowerSeries.X ^ (d - 1)) := by
    rw [Derivation.leibniz, PowerSeries.derivative_one] at hderiv
    change dhEulerGeomFactor a d •
        PowerSeries.derivative (1 - PowerSeries.C a * PowerSeries.X ^ d) +
      dhEulerGeomInverseFactor a d •
        PowerSeries.derivative (dhEulerGeomFactor a d) = 0 at hderiv
    rw [derivative_one_sub_C_mul_X_pow] at hderiv
    rw [smul_eq_mul] at hderiv
    have htemp : dhEulerGeomInverseFactor a d *
        PowerSeries.derivative (dhEulerGeomFactor a d) =
          -(dhEulerGeomFactor a d *
            -(PowerSeries.C a * PowerSeries.C (d : ℂ) * PowerSeries.X ^ (d - 1))) := by
      linear_combination hderiv
    calc
      _ = dhEulerGeomInverseFactor a d *
          PowerSeries.derivative (dhEulerGeomFactor a d) := by ring
      _ = _ := by rw [htemp]; ring
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hpow : PowerSeries.X * PowerSeries.X ^ (d - 1) =
      (PowerSeries.X : PowerSeries ℂ) ^ d := by
    calc
      PowerSeries.X * PowerSeries.X ^ (d - 1) =
          PowerSeries.X ^ (d - 1) * PowerSeries.X := mul_comm _ _
      _ = PowerSeries.X ^ ((d - 1) + 1) := (pow_succ _ _).symm
      _ = PowerSeries.X ^ d := by rw [Nat.sub_add_cancel hdpos]
  calc
    _ = PowerSeries.X *
          (PowerSeries.derivative (dhEulerGeomFactor a d) *
            dhEulerGeomInverseFactor a d) := by ring
    _ = PowerSeries.X *
          (dhEulerGeomFactor a d *
            (PowerSeries.C a * PowerSeries.C (d : ℂ) * PowerSeries.X ^ (d - 1))) := by
          rw [hprod]
    _ = PowerSeries.C (d : ℂ) * PowerSeries.C a * PowerSeries.X ^ d *
          dhEulerGeomFactor a d := by
            calc
              _ = PowerSeries.C (d : ℂ) * PowerSeries.C a *
                  (PowerSeries.X * PowerSeries.X ^ (d - 1)) * dhEulerGeomFactor a d := by ring
              _ = _ := by rw [hpow]

theorem derivative_prod_erase {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → PowerSeries ℂ) :
    PowerSeries.derivative (∏ i ∈ s, f i) =
      ∑ i ∈ s, PowerSeries.derivative (f i) * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    have htail :
        ∑ i ∈ s, PowerSeries.derivative (f i) *
            ∏ j ∈ (insert a s).erase i, f j =
          f a * ∑ i ∈ s, PowerSeries.derivative (f i) *
            ∏ j ∈ s.erase i, f j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := by
        intro h
        subst i
        exact ha hi
      rw [Finset.erase_insert_of_ne hia.symm]
      have ha' : a ∉ s.erase i := fun h => ha (Finset.mem_of_mem_erase h)
      rw [Finset.prod_insert ha']
      ring
    rw [htail, ih]
    ring

noncomputable def dhEulerInverseFactor {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) (p : dhIrrBounded k n) :
    PowerSeries ℂ :=
  dhEulerGeomInverseFactor (dhPolyWeight χ ψ p.val.val) p.val.val.natDegree

noncomputable def dhEulerInverseProduct {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) : PowerSeries ℂ :=
  ∏ p : dhIrrBounded k n, dhEulerInverseFactor χ ψ n p

theorem dhEulerFactor_mul_inverse {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) (p : dhIrrBounded k n) :
    dhEulerFactor χ ψ n p * dhEulerInverseFactor χ ψ n p = 1 := by
  exact dhEulerGeomFactor_mul_inverse (dhPolyWeight χ ψ p.val.val)
    p.val.val.natDegree p.property.2.natDegree_pos.ne'

theorem dhEulerProduct_mul_inverse {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) :
    dhEulerProduct χ ψ n * dhEulerInverseProduct χ ψ n = 1 := by
  rw [dhEulerProduct, dhEulerInverseProduct, ← Finset.prod_mul_distrib]
  simp [dhEulerFactor_mul_inverse]

set_option maxHeartbeats 1000000 in
theorem dhEulerProduct_log_derivative {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) :
    PowerSeries.X * PowerSeries.derivative (dhEulerProduct χ ψ n) *
        dhEulerInverseProduct χ ψ n =
      ∑ p : dhIrrBounded k n,
        PowerSeries.C (p.val.val.natDegree : ℂ) *
          PowerSeries.C (dhPolyWeight χ ψ p.val.val) *
          PowerSeries.X ^ p.val.val.natDegree * dhEulerFactor χ ψ n p := by
  classical
  let q := fun p : dhIrrBounded k n => dhEulerFactor χ ψ n p
  let r := fun p : dhIrrBounded k n => dhEulerInverseFactor χ ψ n p
  have hlocal (p : dhIrrBounded k n) : q p * r p = 1 := by
    exact dhEulerFactor_mul_inverse χ ψ n p
  have hderiv : PowerSeries.derivative (dhEulerProduct χ ψ n) =
      ∑ p : dhIrrBounded k n,
        PowerSeries.derivative (q p) *
          ∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, q j := by
    simpa [dhEulerProduct, q] using
      (derivative_prod_erase (Finset.univ : Finset (dhIrrBounded k n)) q)
  have hrest (p : dhIrrBounded k n) :
      (∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, q j) *
          (∏ j : dhIrrBounded k n, r j) = r p := by
    have hp : p ∈ (Finset.univ : Finset (dhIrrBounded k n)) := Finset.mem_univ _
    calc
      _ = (∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, q j) *
          (r p * ∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, r j) := by
            rw [Finset.mul_prod_erase (s := Finset.univ) (f := r) hp]
      _ = r p *
          ((∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, q j) *
            ∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, r j) := by ring
      _ = r p * ∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p,
            (q j * r j) := by rw [← Finset.prod_mul_distrib]
      _ = r p := by simp [hlocal]
  calc
    PowerSeries.X * PowerSeries.derivative (dhEulerProduct χ ψ n) *
        dhEulerInverseProduct χ ψ n =
      PowerSeries.X *
        (∑ p : dhIrrBounded k n,
          PowerSeries.derivative (q p) *
            ∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, q j) *
          (∏ p : dhIrrBounded k n, r p) := by
            rw [hderiv, dhEulerInverseProduct]
    _ = ∑ p : dhIrrBounded k n,
          PowerSeries.X *
            (PowerSeries.derivative (q p) *
              (∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, q j) *
              (∏ j : dhIrrBounded k n, r j)) := by
            rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ p : dhIrrBounded k n,
          PowerSeries.X * (PowerSeries.derivative (q p) * r p) := by
            apply Finset.sum_congr rfl
            intro p hp
            calc
              _ = PowerSeries.X *
                  (PowerSeries.derivative (q p) *
                    ((∏ j ∈ (Finset.univ : Finset (dhIrrBounded k n)).erase p, q j) *
                      (∏ j : dhIrrBounded k n, r j))) := by ring
              _ = _ := by rw [hrest p]
    _ = ∑ p : dhIrrBounded k n,
          PowerSeries.C (p.val.val.natDegree : ℂ) *
            PowerSeries.C (dhPolyWeight χ ψ p.val.val) *
            PowerSeries.X ^ p.val.val.natDegree * dhEulerFactor χ ψ n p := by
            apply Finset.sum_congr rfl
            intro p hp
            calc
              _ = PowerSeries.X * PowerSeries.derivative (q p) * r p := by ring
              _ = _ := by
                simpa [q, r, dhEulerFactor, dhEulerInverseFactor,
                  dhEulerGeomFactor, dhEulerGeomInverseFactor] using
                  (dhEulerGeomFactor_log_derivative
                  (dhPolyWeight χ ψ p.val.val) p.val.val.natDegree
                  p.property.2.natDegree_pos.ne')

theorem dhEulerLogTerm_coeff {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (bound : ℕ)
    (p : dhIrrBounded k bound) (j : ℕ) (hj : 0 < j) :
    PowerSeries.coeff j
      (PowerSeries.C (p.val.val.natDegree : ℂ) *
        PowerSeries.C (dhPolyWeight χ ψ p.val.val) *
        PowerSeries.X ^ p.val.val.natDegree * dhEulerFactor χ ψ bound p) =
      if p.val.val.natDegree ∣ j then
        (p.val.val.natDegree : ℂ) *
          (dhPolyWeight χ ψ p.val.val) ^ (j / p.val.val.natDegree)
      else 0 := by
  let d := p.val.val.natDegree
  let a := dhPolyWeight χ ψ p.val.val
  have hdpos : 0 < d := p.property.2.natDegree_pos
  have hddef : d = p.val.val.natDegree := rfl
  have hcoeff : PowerSeries.coeff j
        (PowerSeries.C (d : ℂ) * PowerSeries.C a * PowerSeries.X ^ d *
          dhEulerFactor χ ψ bound p) =
      (d : ℂ) * a * PowerSeries.coeff j
        (PowerSeries.X ^ d * dhEulerFactor χ ψ bound p) := by
    rw [show PowerSeries.C (d : ℂ) * PowerSeries.C a * PowerSeries.X ^ d *
          dhEulerFactor χ ψ bound p =
        PowerSeries.C (d : ℂ) *
          (PowerSeries.C a * (PowerSeries.X ^ d * dhEulerFactor χ ψ bound p)) by ring]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    ring
  change PowerSeries.coeff j
      (PowerSeries.C (d : ℂ) * PowerSeries.C a * PowerSeries.X ^ d *
        dhEulerFactor χ ψ bound p) =
    if d ∣ j then (d : ℂ) * a ^ (j / d) else 0
  by_cases hdiv : d ∣ j
  · have hle : d ≤ j := Nat.le_of_dvd hj hdiv
    have hshift : d ∣ j - d := by
      rw [Nat.dvd_sub_self_right]
      exact Or.inl hdiv
    have hquot : (j - d) / d + 1 = j / d := by
      apply Nat.mul_left_cancel hdpos
      calc
        d * ((j - d) / d + 1) = d * ((j - d) / d) + d := by
          rw [Nat.mul_add]
          simp
        _ = (j - d) + d := by rw [Nat.mul_div_cancel' hshift]
        _ = j := Nat.sub_add_cancel hle
        _ = d * (j / d) := (Nat.mul_div_cancel' hdiv).symm
    rw [if_pos hdiv, hcoeff, PowerSeries.coeff_X_pow_mul', if_pos hle,
      coeff_dhEulerFactor, if_pos hshift, ← hddef, ← hquot, pow_succ]
    ring
  · by_cases hle : d ≤ j
    · have hne : d ≠ j := by
        intro heq
        apply hdiv
        rw [← heq]
      have hlt : d < j := lt_of_le_of_ne hle hne
      have hshift : ¬ d ∣ j - d := by
        rw [Nat.dvd_sub_self_right]
        exact not_or.mpr ⟨hdiv, Nat.not_le_of_gt hlt⟩
      rw [if_neg hdiv, hcoeff, PowerSeries.coeff_X_pow_mul', if_pos hle,
        coeff_dhEulerFactor, if_neg hshift]
      simp
    · rw [if_neg hdiv, hcoeff, PowerSeries.coeff_X_pow_mul', if_neg hle]
      simp

noncomputable def dhFactorExp {k : Type*} [Field k] [Fintype k] [DecidableEq k] (n : ℕ)
    (h : Polynomial k) : dhIrrBounded k n →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm fun p => factorization h p.val.val

@[simp] theorem dhFactorExp_apply {k : Type*} [Field k] [Fintype k] [DecidableEq k] (n : ℕ)
    (h : Polynomial k) (p : dhIrrBounded k n) :
    dhFactorExp n h p = factorization h p.val.val := by
  classical
  simp [dhFactorExp]

noncomputable def dhFactorPoly {k : Type*} [Field k] [Fintype k] {n : ℕ}
    (m : dhIrrBounded k n →₀ ℕ) : Polynomial k :=
  ∏ p : dhIrrBounded k n, p.val.val ^ m p

theorem dhFactorPoly_monic {k : Type*} [Field k] [Fintype k] {n : ℕ}
    (m : dhIrrBounded k n →₀ ℕ) : (dhFactorPoly m).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro p hp
  exact p.property.1.pow _

theorem dhFactorPoly_natDegree {k : Type*} [Field k] [Fintype k] {n : ℕ}
    (m : dhIrrBounded k n →₀ ℕ) :
    (dhFactorPoly m).natDegree =
      ∑ p : dhIrrBounded k n, p.val.val.natDegree * m p := by
  classical
  rw [dhFactorPoly, Polynomial.natDegree_prod_of_monic]
  · simp [Polynomial.natDegree_pow, mul_comm]
  · intro p hp
    exact p.property.1.pow _

theorem dhFactorPoly_weight {k : Type*} [Field k] [Fintype k] {n : ℕ}
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (m : dhIrrBounded k n →₀ ℕ) :
    dhPolyWeight χ ψ (dhFactorPoly m) =
      ∏ p : dhIrrBounded k n, (dhPolyWeight χ ψ p.val.val) ^ m p := by
  classical
  have hp (p : dhIrrBounded k n) (r : ℕ) :
      dhPolyWeight χ ψ (p.val.val ^ r) = (dhPolyWeight χ ψ p.val.val) ^ r := by
    induction r with
    | zero => simp [dhPolyWeight, Polynomial.nextCoeff]
    | succ r ih =>
        rw [pow_succ, dhPolyWeight_mul χ ψ (p.property.1.pow r) p.property.1, ih]
        ring
  have hmonic (s : Finset (dhIrrBounded k n)) :
      (∏ p ∈ s, p.val.val ^ m p).Monic := by
    apply Polynomial.monic_prod_of_monic s (fun p => p.val.val ^ m p)
    intro p hp'
    exact p.property.1.pow _
  have hprod (s : Finset (dhIrrBounded k n)) :
      dhPolyWeight χ ψ (∏ p ∈ s, p.val.val ^ m p) =
        ∏ p ∈ s, (dhPolyWeight χ ψ p.val.val) ^ m p := by
    induction s using Finset.induction_on with
    | empty => simp [dhPolyWeight, Polynomial.nextCoeff]
    | @insert p s hp' ih =>
        rw [Finset.prod_insert hp', Finset.prod_insert hp',
          dhPolyWeight_mul χ ψ (p.property.1.pow (m p)) (hmonic s), ih, hp]
  simpa [dhFactorPoly] using hprod Finset.univ

theorem factorization_dhFactorPow {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    {n : ℕ} (p : dhIrrBounded k n) (r : ℕ) :
    factorization (p.val.val ^ r) = Finsupp.single p.val.val r := by
  classical
  rw [factorization, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible p.property.2]
  have hnorm : normalize p.val.val = p.val.val :=
    (Polynomial.normalize_eq_self_iff_monic p.property.1.ne_zero).2 p.property.1
  rw [hnorm]
  simp

theorem factorization_dhFactorPoly {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    {n : ℕ} (m : dhIrrBounded k n →₀ ℕ) :
    factorization (dhFactorPoly m) =
      ∑ p : dhIrrBounded k n, Finsupp.single p.val.val (m p) := by
  classical
  have hprod : ∀ s : Finset (dhIrrBounded k n),
      factorization (∏ q ∈ s, q.val.val ^ m q) =
        ∑ q ∈ s, Finsupp.single q.val.val (m q) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert q s hqs ih =>
        let r := ∏ t ∈ s, t.val.val ^ m t
        have hr : r.Monic :=
          Polynomial.monic_prod_of_monic s (fun t => t.val.val ^ m t) fun t ht =>
            (t.property.1).pow _
        rw [Finset.prod_insert hqs, factorization_mul
          (pow_ne_zero _ q.property.1.ne_zero) hr.ne_zero,
          factorization_dhFactorPow q (m q), ih, Finset.sum_insert hqs]
  simpa [dhFactorPoly] using hprod Finset.univ

theorem dhFactorExp_dhFactorPoly {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    {n : ℕ} (m : dhIrrBounded k n →₀ ℕ) :
    dhFactorExp n (dhFactorPoly m) = m := by
  classical
  ext p
  change factorization (dhFactorPoly m) p.val.val = m p
  rw [factorization_dhFactorPoly]
  rw [Finsupp.finsetSum_apply]
  have heq : ∀ q : dhIrrBounded k n, (q.val.val : Polynomial k) = p.val.val ↔ q = p := by
    intro q
    constructor
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · rintro rfl
      rfl
  simp [Finsupp.single_apply, heq]

theorem factorization_support_dhIrrBounded {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] {n : ℕ} {h q : Polynomial k} (hh : h.Monic)
    (hn : h.natDegree ≤ n) (hq : factorization h q ≠ 0) :
    ∃ p : dhIrrBounded k n, p.val.val = q := by
  classical
  have hcount : Multiset.count q (UniqueFactorizationMonoid.normalizedFactors h) ≠ 0 := by
    simpa [factorization_eq_count] using hq
  have hmem : q ∈ UniqueFactorizationMonoid.normalizedFactors h :=
    Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount)
  rcases (Polynomial.mem_normalizedFactors_iff (p := q) (q := h) hh.ne_zero).mp hmem with
    ⟨hqirr, hqmonic, hqdvd⟩
  have hqdeg : q.natDegree ≤ n :=
    hqmonic.natDegree_le_of_dvd hh.ne_zero hqdvd |>.trans hn
  exact ⟨⟨⟨q, hqdeg⟩, ⟨hqmonic, hqirr⟩⟩, rfl⟩

theorem dhFactorPoly_factorExp {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    {n : ℕ} (h : Polynomial k) (hh : h.Monic) (hn : h.natDegree ≤ n) :
    dhFactorPoly (dhFactorExp n h) = h := by
  classical
  let m := dhFactorExp n h
  have hfac : factorization (dhFactorPoly m) = factorization h := by
    ext q
    by_cases hrep : ∃ p : dhIrrBounded k n, p.val.val = q
    · obtain ⟨p, hpq⟩ := hrep
      have hm : m p = factorization h q := by
        dsimp [m]
        rw [dhFactorExp_apply]
        simpa [hpq]
      rw [factorization_dhFactorPoly, Finsupp.finsetSum_apply]
      have heq : ∀ r : dhIrrBounded k n, r.val.val = q ↔ r = p := by
        intro r
        constructor
        · intro hr
          apply Subtype.ext
          apply Subtype.ext
          exact hr.trans hpq.symm
        · rintro rfl
          exact hpq
      simp [Finsupp.single_apply, heq, hm]
    · have hq0 : factorization h q = 0 := by
        by_contra hq0
        obtain ⟨p, hpq⟩ := factorization_support_dhIrrBounded hh hn hq0
        exact hrep ⟨p, hpq⟩
      rw [factorization_dhFactorPoly, Finsupp.finsetSum_apply]
      have hne : ∀ r : dhIrrBounded k n, r.val.val ≠ q := by
        intro r hr
        exact hrep ⟨r, hr⟩
      simp [Finsupp.single_apply, hne, hq0]
  have hassoc : Associated (dhFactorPoly m) h :=
    associated_of_factorization_eq _ _ (dhFactorPoly_monic m).ne_zero hh.ne_zero hfac
  exact Polynomial.eq_of_monic_of_associated (dhFactorPoly_monic m) hh hassoc

noncomputable def dhFactorDegree {k : Type*} [Field k] [Fintype k] {n : ℕ}
    (m : dhIrrBounded k n →₀ ℕ) : ℕ :=
  ∑ p : dhIrrBounded k n, p.val.val.natDegree * m p

noncomputable def dhFactorEquiv {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    (n : ℕ) :
    {m : dhIrrBounded k n →₀ ℕ // dhFactorDegree m = n} ≃
      {h : Polynomial k // h.Monic ∧ h.natDegree = n} where
  toFun m := ⟨dhFactorPoly m.val, dhFactorPoly_monic m.val, by
    have hdeg : (dhFactorPoly m.val).natDegree = dhFactorDegree m.val := by
      simpa [dhFactorDegree] using dhFactorPoly_natDegree m.val
    exact hdeg.trans m.property⟩
  invFun h := by
    refine ⟨dhFactorExp n h.val, ?_⟩
    calc
      dhFactorDegree (dhFactorExp n h.val) =
          (dhFactorPoly (dhFactorExp n h.val)).natDegree := by
            exact (dhFactorPoly_natDegree _).symm
      _ = h.val.natDegree := by
        rw [dhFactorPoly_factorExp h.val h.property.1 h.property.2.le]
      _ = n := h.property.2
  left_inv m := by
    apply Subtype.ext
    exact dhFactorExp_dhFactorPoly m.val
  right_inv h := by
    apply Subtype.ext
    exact dhFactorPoly_factorExp h.val h.property.1 h.property.2.le

noncomputable def dhFactorEquivBelow {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    (bound degree : ℕ) (hbound : degree ≤ bound) :
    {m : dhIrrBounded k bound →₀ ℕ // dhFactorDegree m = degree} ≃
      {h : Polynomial k // h.Monic ∧ h.natDegree = degree} where
  toFun m := ⟨dhFactorPoly m.val, dhFactorPoly_monic m.val, by
    have hdeg : (dhFactorPoly m.val).natDegree = dhFactorDegree m.val := by
      simpa [dhFactorDegree] using dhFactorPoly_natDegree m.val
    exact hdeg.trans m.property⟩
  invFun h := by
    refine ⟨dhFactorExp bound h.val, ?_⟩
    calc
      dhFactorDegree (dhFactorExp bound h.val) =
          (dhFactorPoly (dhFactorExp bound h.val)).natDegree := by
            exact (dhFactorPoly_natDegree _).symm
      _ = h.val.natDegree := by
        rw [dhFactorPoly_factorExp h.val h.property.1 (h.property.2.le.trans hbound)]
      _ = degree := h.property.2
  left_inv m := by
    apply Subtype.ext
    exact dhFactorExp_dhFactorPoly m.val
  right_inv h := by
    apply Subtype.ext
    exact dhFactorPoly_factorExp h.val h.property.1 (h.property.2.le.trans hbound)

abbrev dhGoodAntidiag {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    (bound degree : ℕ) :=
  {l : dhIrrBounded k bound →₀ ℕ //
    l ∈ (Finset.finsuppAntidiag (Finset.univ : Finset (dhIrrBounded k bound)) degree).filter
      (fun l => ∀ p : dhIrrBounded k bound, p.val.val.natDegree ∣ l p)}

noncomputable def dhDegreeMultipleFinsupp {k : Type*} [Field k] [Fintype k]
    {n : ℕ} (m : dhIrrBounded k n →₀ ℕ) : dhIrrBounded k n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun p => p.val.val.natDegree * m p)

noncomputable def dhDegreeDivFinsupp {k : Type*} [Field k] [Fintype k]
    {n : ℕ} (l : dhIrrBounded k n →₀ ℕ) : dhIrrBounded k n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun p => l p / p.val.val.natDegree)

@[simp] theorem dhDegreeMultipleFinsupp_apply {k : Type*} [Field k] [Fintype k]
    {n : ℕ} (m : dhIrrBounded k n →₀ ℕ) (p : dhIrrBounded k n) :
    dhDegreeMultipleFinsupp m p = p.val.val.natDegree * m p := by
  simp [dhDegreeMultipleFinsupp]

@[simp] theorem dhDegreeDivFinsupp_apply {k : Type*} [Field k] [Fintype k]
    {n : ℕ} (l : dhIrrBounded k n →₀ ℕ) (p : dhIrrBounded k n) :
    dhDegreeDivFinsupp l p = l p / p.val.val.natDegree := by
  simp [dhDegreeDivFinsupp]

theorem dhDegreeMultiple_mem_antidiag {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    {bound degree : ℕ} (m : dhIrrBounded k bound →₀ ℕ)
    (hm : dhFactorDegree m = degree) :
    dhDegreeMultipleFinsupp m ∈ Finset.finsuppAntidiag Finset.univ degree := by
  rw [Finset.mem_finsuppAntidiag]
  constructor
  · simpa [dhDegreeMultipleFinsupp, dhFactorDegree] using hm
  · exact Finset.subset_univ _

noncomputable def dhDegreeAntidiagEquiv {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] (bound degree : ℕ) :
    {m : dhIrrBounded k bound →₀ ℕ // dhFactorDegree m = degree} ≃
      dhGoodAntidiag (k := k) bound degree where
  toFun m := ⟨dhDegreeMultipleFinsupp m.val,
      Finset.mem_filter.mpr ⟨dhDegreeMultiple_mem_antidiag m.val m.property, fun p =>
        ⟨m.val p, by simp [dhDegreeMultipleFinsupp]⟩⟩⟩
  invFun l := ⟨dhDegreeDivFinsupp l.val, by
    have hl : l.val ∈ Finset.finsuppAntidiag Finset.univ degree :=
      (Finset.mem_filter.mp l.property).1
    have hg := (Finset.mem_filter.mp l.property).2
    rw [dhFactorDegree]
    calc
      ∑ p : dhIrrBounded k bound,
          p.val.val.natDegree * dhDegreeDivFinsupp l.val p =
          ∑ p : dhIrrBounded k bound, l.val p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [dhDegreeDivFinsupp_apply]
          exact Nat.mul_div_cancel' (hg p)
      _ = degree := (Finset.mem_finsuppAntidiag.mp hl).1⟩
  left_inv m := by
    apply Subtype.ext
    ext p
    change (p.val.val.natDegree * m.val p) / p.val.val.natDegree = m.val p
    exact Nat.mul_div_cancel_left _ p.property.2.natDegree_pos
  right_inv l := by
    apply Subtype.ext
    ext p
    change p.val.val.natDegree * (l.val p / p.val.val.natDegree) = l.val p
    exact Nat.mul_div_cancel' ((Finset.mem_filter.mp l.property).2 p)

noncomputable instance dhFintypeFactorDegree {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] (bound degree : ℕ) :
    Fintype {m : dhIrrBounded k bound →₀ ℕ // dhFactorDegree m = degree} :=
  Fintype.ofEquiv (dhGoodAntidiag (k := k) bound degree)
    (dhDegreeAntidiagEquiv (k := k) bound degree).symm

theorem dhGoodAntidiag_sum {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    (bound degree : ℕ) (f : (dhIrrBounded k bound →₀ ℕ) → ℂ) :
    ∑ l : dhGoodAntidiag (k := k) bound degree, f l.val =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (dhIrrBounded k bound)) degree,
        if ∀ p : dhIrrBounded k bound, p.val.val.natDegree ∣ l p then f l else 0 := by
  classical
  let anti := Finset.finsuppAntidiag (Finset.univ : Finset (dhIrrBounded k bound)) degree
  let good := fun l : dhIrrBounded k bound →₀ ℕ =>
    ∀ p : dhIrrBounded k bound, p.val.val.natDegree ∣ l p
  change (∑ l : {l : dhIrrBounded k bound →₀ ℕ // l ∈ anti.filter good}, f l.val) =
    ∑ l ∈ anti, if good l then f l else 0
  calc
    ∑ l : {l : dhIrrBounded k bound →₀ ℕ // l ∈ anti.filter good}, f l.val =
        ∑ l ∈ anti.filter good, f l := Finset.sum_attach _ _
    _ = ∑ l ∈ anti, if good l then f l else 0 := by rw [Finset.sum_filter]

theorem dhDegreeDivFinsupp_mul_apply {k : Type*} [Field k] [Fintype k]
    {n : ℕ} (m : dhIrrBounded k n →₀ ℕ) (p : dhIrrBounded k n) :
    dhDegreeDivFinsupp (dhDegreeMultipleFinsupp m) p = m p := by
  rw [dhDegreeDivFinsupp_apply, dhDegreeMultipleFinsupp_apply]
  exact Nat.mul_div_cancel_left _ p.property.2.natDegree_pos

theorem dhLSeries_coeff_factorization {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) :
    PowerSeries.coeff n (dhLSeries χ ψ) =
      ∑ m : {m : dhIrrBounded k n →₀ ℕ // dhFactorDegree m = n},
        ∏ p : dhIrrBounded k n, (dhPolyWeight χ ψ p.val.val) ^ m.val p := by
  classical
  rw [dhLSeries, PowerSeries.coeff_mk]
  calc
    ∑ h : {h : Polynomial k // h.Monic ∧ h.natDegree = n}, dhPolyWeight χ ψ h.val =
        ∑ m : {m : dhIrrBounded k n →₀ ℕ // dhFactorDegree m = n},
          dhPolyWeight χ ψ (dhFactorEquiv n m).val :=
      (Equiv.sum_comp (dhFactorEquiv n) (fun h => dhPolyWeight χ ψ h.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      exact dhFactorPoly_weight χ ψ m.val

theorem dhEulerProduct_coeff_factorization {k : Type*} [Field k] [Fintype k] [DecidableEq k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (bound degree : ℕ) :
    PowerSeries.coeff degree (dhEulerProduct χ ψ bound) =
      ∑ m : {m : dhIrrBounded k bound →₀ ℕ // dhFactorDegree m = degree},
        ∏ p : dhIrrBounded k bound, (dhPolyWeight χ ψ p.val.val) ^ m.val p := by
  classical
  let good (l : dhIrrBounded k bound →₀ ℕ) :=
    ∀ p : dhIrrBounded k bound, p.val.val.natDegree ∣ l p
  let value (l : dhIrrBounded k bound →₀ ℕ) :=
    ∏ p : dhIrrBounded k bound,
      (dhPolyWeight χ ψ p.val.val) ^ dhDegreeDivFinsupp l p
  have hterm (l : dhIrrBounded k bound →₀ ℕ) :
      (∏ p : dhIrrBounded k bound,
        if p.val.val.natDegree ∣ l p then
          (dhPolyWeight χ ψ p.val.val) ^ (l p / p.val.val.natDegree) else 0) =
        if good l then value l else 0 := by
    by_cases hg : good l
    · rw [if_pos hg]
      apply Finset.prod_congr rfl
      intro p hp
      rw [if_pos (hg p), dhDegreeDivFinsupp_apply]
    · have hg' : ∃ p : dhIrrBounded k bound,
          ¬ p.val.val.natDegree ∣ l p := by
        change ¬ (∀ p : dhIrrBounded k bound, p.val.val.natDegree ∣ l p) at hg
        exact not_forall.mp hg
      obtain ⟨p, hp⟩ := hg'
      rw [if_neg hg]
      rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hp])]
  rw [dhEulerProduct, PowerSeries.coeff_prod]
  simp_rw [coeff_dhEulerFactor]
  calc
    ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (dhIrrBounded k bound)) degree,
        (∏ p : dhIrrBounded k bound,
          if p.val.val.natDegree ∣ l p then
            (dhPolyWeight χ ψ p.val.val) ^ (l p / p.val.val.natDegree) else 0)
      = ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (dhIrrBounded k bound)) degree,
          if good l then value l else 0 := by
            apply Finset.sum_congr rfl
            intro l hl
            exact hterm l
    _ = ∑ l : dhGoodAntidiag (k := k) bound degree, value l.val :=
          (dhGoodAntidiag_sum bound degree value).symm
    _ = ∑ m : {m : dhIrrBounded k bound →₀ ℕ // dhFactorDegree m = degree},
          ∏ p : dhIrrBounded k bound, (dhPolyWeight χ ψ p.val.val) ^ m.val p := by
          calc
            _ = ∑ m : {m : dhIrrBounded k bound →₀ ℕ // dhFactorDegree m = degree},
                value (dhDegreeAntidiagEquiv (k := k) bound degree m).val :=
              (Equiv.sum_comp (dhDegreeAntidiagEquiv (k := k) bound degree)
                (fun l => value l.val)).symm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro m hm
              have hdiv (p : dhIrrBounded k bound) :
                  p.val.val.natDegree * m.val p / p.val.val.natDegree = m.val p :=
                Nat.mul_div_cancel_left _ p.property.2.natDegree_pos
              simp [value, dhDegreeAntidiagEquiv, dhDegreeDivFinsupp,
                dhDegreeMultipleFinsupp, hdiv]

theorem dhEulerProduct_coeff_eq_dhLSeries {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (bound degree : ℕ) (hbound : degree ≤ bound) :
    PowerSeries.coeff degree (dhEulerProduct χ ψ bound) =
      PowerSeries.coeff degree (dhLSeries χ ψ) := by
  rw [dhEulerProduct_coeff_factorization]
  rw [dhLSeries, PowerSeries.coeff_mk]
  let e := dhFactorEquivBelow (k := k) bound degree hbound
  calc
    ∑ m : {m : dhIrrBounded k bound →₀ ℕ // dhFactorDegree m = degree},
        ∏ p : dhIrrBounded k bound, (dhPolyWeight χ ψ p.val.val) ^ m.val p =
      ∑ m : {m : dhIrrBounded k bound →₀ ℕ // dhFactorDegree m = degree},
        dhPolyWeight χ ψ (dhFactorPoly m.val) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact (dhFactorPoly_weight χ ψ m.val).symm
    _ = ∑ h : {h : Polynomial k // h.Monic ∧ h.natDegree = degree},
          dhPolyWeight χ ψ h.val :=
        Equiv.sum_comp e (fun h => dhPolyWeight χ ψ h.val)

theorem dhEulerProduct_constantCoeff {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (bound : ℕ)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    PowerSeries.constantCoeff (dhEulerProduct χ ψ bound) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    dhEulerProduct_coeff_eq_dhLSeries χ ψ bound 0 (Nat.zero_le _),
    dhLSeries_eq_one_sub χ ψ hχ hψ]
  simp

theorem dhEulerInverseProduct_eq_inv {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (bound : ℕ)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    dhEulerInverseProduct χ ψ bound = (dhEulerProduct χ ψ bound)⁻¹ := by
  let F := dhEulerProduct χ ψ bound
  let R := dhEulerInverseProduct χ ψ bound
  have hconst : PowerSeries.constantCoeff F = 1 := by
    exact dhEulerProduct_constantCoeff χ ψ bound hχ hψ
  have hprod : F * R = 1 := dhEulerProduct_mul_inverse χ ψ bound
  have hinv : F⁻¹ * F = 1 := by
    have h := PowerSeries.mul_inv_cancel F (by rw [hconst]; norm_num)
    simpa [mul_comm] using h
  calc
    R = 1 * R := by simp
    _ = (F⁻¹ * F) * R := by rw [hinv]
    _ = F⁻¹ * (F * R) := by ring
    _ = F⁻¹ := by rw [hprod]; simp

theorem dhGeom_gauss_eq_dhLSeries_inv {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    dhGeom (gaussSum χ ψ) = (dhLSeries χ ψ)⁻¹ := by
  let F := dhLSeries χ ψ
  have hseries := dhLSeries_eq_one_sub χ ψ hχ hψ
  have hconst : PowerSeries.constantCoeff F = 1 := by
    change PowerSeries.constantCoeff (dhLSeries χ ψ) = 1
    rw [hseries]
    simp
  have hprod : F * dhGeom (gaussSum χ ψ) = 1 := by
    change dhLSeries χ ψ * dhGeom (gaussSum χ ψ) = 1
    rw [hseries]
    simpa [mul_comm] using dhGeom_mul_one_sub (gaussSum χ ψ)
  have hinv : F⁻¹ * F = 1 := by
    have h := PowerSeries.mul_inv_cancel F (by rw [hconst]; norm_num)
    simpa [mul_comm] using h
  calc
    dhGeom (gaussSum χ ψ) = 1 * dhGeom (gaussSum χ ψ) := by simp
    _ = (F⁻¹ * F) * dhGeom (gaussSum χ ψ) := by rw [hinv]
    _ = F⁻¹ * (F * dhGeom (gaussSum χ ψ)) := by ring
    _ = F⁻¹ := by rw [hprod]; simp

theorem coeff_inv_eq_of_prefix {R : Type*} [Field R] (F G : PowerSeries R) (N : ℕ)
    (hprefix : ∀ j ≤ N, PowerSeries.coeff j F = PowerSeries.coeff j G) :
    ∀ j ≤ N, PowerSeries.coeff j F⁻¹ = PowerSeries.coeff j G⁻¹ := by
  have hconst : PowerSeries.constantCoeff F = PowerSeries.constantCoeff G := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      hprefix 0 (Nat.zero_le _)
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst j
      simp [PowerSeries.coeff_inv, hconst]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      rw [PowerSeries.coeff_inv, PowerSeries.coeff_inv, if_neg hj0, if_neg hj0, hconst]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hlt : x.2 < j
      · simp only [if_pos hlt]
        have hsum : x.1 + x.2 = j :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        have hx1 : x.1 ≤ N := by omega
        have hx2 : x.2 ≤ N := le_trans (Nat.le_of_lt hlt) hj
        rw [hprefix x.1 hx1, ih x.2 hlt hx2]
      · simp [hlt]

theorem dhIrrBounded_exists_minpoly {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (n : ℕ)
    (hn : Module.finrank k K = n) (p : dhIrrBounded k n)
    (hdvd : p.val.val.natDegree ∣ n) :
    ∃ x : K, minpoly k x = p.val.val := by
  classical
  let f := p.val.val
  have hdivX : f ∣ (Polynomial.X ^ (Nat.card k) ^ n - Polynomial.X) := by
    exact (p.property.2.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := n)).mp hdvd
  have hcard : Fintype.card K = Fintype.card k ^ n := by
    simpa [hn] using (Module.card_eq_pow_finrank (K := k) (V := K))
  let g : Polynomial k := Polynomial.X ^ Fintype.card K - Polynomial.X
  have hdivCard : f ∣ g := by
    dsimp [g]
    have hdivX' : f ∣ Polynomial.X ^ (Fintype.card k) ^ n - Polynomial.X := by
      simpa only [Nat.card_eq_fintype_card] using hdivX
    rw [hcard]
    exact hdivX'
  have hsplitBase : (g.map (algebraMap k K)).Splits :=
    (FiniteField.isSplittingField_sub K k).splits
  have hdivMap : f.map (algebraMap k K) ∣ g.map (algebraMap k K) :=
    (Polynomial.map_dvd_map (algebraMap k K)
      (FaithfulSMul.algebraMap_injective k K) p.property.1).2 hdivCard
  have hsplit : (f.map (algebraMap k K)).Splits :=
    hsplitBase.of_dvd
      (Polynomial.map_ne_zero (FiniteField.X_pow_card_sub_X_ne_zero k
        (Fintype.one_lt_card : 1 < Fintype.card K))) hdivMap
  have hmapDegree : (f.map (algebraMap k K)).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective k K) f
  have hdegree : (f.map (algebraMap k K)).natDegree ≠ 0 := by
    rw [hmapDegree]
    exact p.property.2.natDegree_pos.ne'
  obtain ⟨x, hxroot⟩ := Multiset.exists_mem_of_ne_zero (hsplit.roots_ne_zero hdegree)
  have hxroot' : Polynomial.IsRoot (f.map (algebraMap k K)) x :=
    Polynomial.isRoot_of_mem_roots hxroot
  have hxEval : (f.map (algebraMap k K)).eval x = 0 := hxroot'
  have hxaeval : Polynomial.aeval x f = 0 := by
    change f.eval₂ (algebraMap k K) x = 0
    rw [← Polynomial.eval_map]
    exact hxEval
  have hxI : IsIntegral k x := IsIntegral.of_finite k x
  have hminIrr : Irreducible (minpoly k x) := minpoly.irreducible hxI
  have hminDvd : minpoly k x ∣ f := minpoly.dvd k x hxaeval
  have hminNotUnit : ¬ IsUnit (minpoly k x) := by
    intro hu
    have hone := (minpoly.monic hxI).isUnit_iff.mp hu
    have hpos := hminIrr.natDegree_pos
    rw [hone, Polynomial.natDegree_one] at hpos
    norm_num at hpos
  rcases p.property.2.dvd_iff.mp hminDvd with hu | hassoc
  · exact (hminNotUnit hu).elim
  · exact ⟨x, Polynomial.eq_of_monic_of_associated (minpoly.monic hxI)
      p.property.1 hassoc.symm⟩

noncomputable def dhMinpolyIrrDividesEquiv {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (n : ℕ)
    (hn : Module.finrank k K = n) :
    {p : dhIrrBounded k n // p.val.val.natDegree ∣ n} ≃
      dhMinpolyRange (k := k) (K := K) := by
  classical
  let f : {p : dhIrrBounded k n // p.val.val.natDegree ∣ n} →
      dhMinpolyRange (k := k) (K := K) := fun p => by
    refine ⟨p.val.val.val, ?_⟩
    obtain ⟨x, hx⟩ := dhIrrBounded_exists_minpoly n hn p.val p.property
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : dhMinpolyRange (k := k) (K := K) => z.val) hpq
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp q.property
    let g := minpoly k x
    have hxI : IsIntegral k x := IsIntegral.of_finite k x
    have hgdiv : g.natDegree ∣ n := by
      have h := minpoly.degree_dvd (K := k) (L := K) hxI
      rw [hx, hn] at h
      simpa [g, hx] using h
    have hnpos : 0 < n := by rw [← hn]; exact Module.finrank_pos
    have hgle : g.natDegree ≤ n := Nat.le_of_dvd hnpos hgdiv
    let p : dhIrrBounded k n :=
      ⟨⟨g, hgle⟩, ⟨minpoly.monic hxI, minpoly.irreducible hxI⟩⟩
    refine ⟨⟨p, hgdiv⟩, ?_⟩
    apply Subtype.ext
    exact hx
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

@[simp] theorem dhMinpolyIrrDividesEquiv_val {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (n : ℕ)
    (hn : Module.finrank k K = n)
    (p : {p : dhIrrBounded k n // p.val.val.natDegree ∣ n}) :
    (dhMinpolyIrrDividesEquiv (k := k) (K := K) n hn p).val = p.val.val.val := rfl

theorem dhLiftWeight_sum_irredDivides {k K : Type*} [Field k] [Fintype k]
    [Field K] [Fintype K] [Algebra k K] (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (n : ℕ) (hn : Module.finrank k K = n) :
    ∑ x : K, dhLiftWeight χ ψ x =
      ∑ p : {p : dhIrrBounded k n // p.val.val.natDegree ∣ n},
        (p.val.val.val.natDegree : ℂ) *
          dhPolyWeight χ ψ p.val.val.val ^ (n / p.val.val.val.natDegree) := by
  rw [dhLiftWeight_sum_minpoly, hn]
  let e := dhMinpolyIrrDividesEquiv (k := k) (K := K) n hn
  calc
    ∑ q : dhMinpolyRange (k := k) (K := K),
        (q.val.natDegree : ℂ) * dhPolyWeight χ ψ q.val ^
          (n / q.val.natDegree) =
      ∑ p : {p : dhIrrBounded k n // p.val.val.natDegree ∣ n},
        (e p).val.natDegree * dhPolyWeight χ ψ (e p).val ^
          (n / (e p).val.natDegree) :=
      (Equiv.sum_comp e (fun q : dhMinpolyRange (k := k) (K := K) =>
        (q.val.natDegree : ℂ) * dhPolyWeight χ ψ q.val ^
          (n / q.val.natDegree))).symm
    _ = _ := by simp [e]

theorem dhEulerProduct_log_derivative_coeff {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n
        (PowerSeries.X * PowerSeries.derivative (dhEulerProduct χ ψ n) *
          dhEulerInverseProduct χ ψ n) =
      ∑ p : {p : dhIrrBounded k n // p.val.val.natDegree ∣ n},
        (p.val.val.val.natDegree : ℂ) *
          (dhPolyWeight χ ψ p.val.val.val) ^ (n / p.val.val.val.natDegree) := by
  classical
  rw [dhEulerProduct_log_derivative, map_sum]
  let pred (p : dhIrrBounded k n) := p.val.val.natDegree ∣ n
  let term (p : dhIrrBounded k n) :=
    (p.val.val.natDegree : ℂ) * (dhPolyWeight χ ψ p.val.val) ^
      (n / p.val.val.natDegree)
  calc
    ∑ p : dhIrrBounded k n,
        PowerSeries.coeff n
          (PowerSeries.C (p.val.val.natDegree : ℂ) *
            PowerSeries.C (dhPolyWeight χ ψ p.val.val) *
            PowerSeries.X ^ p.val.val.natDegree * dhEulerFactor χ ψ n p) =
      ∑ p : dhIrrBounded k n, if pred p then term p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact dhEulerLogTerm_coeff χ ψ n p n hn
    _ = ∑ p : {p : dhIrrBounded k n // pred p}, term p.val := by
      let f := fun p : dhIrrBounded k n => if pred p then term p else 0
      have hfull :
          (∑ p : dhIrrBounded k n, f p) =
            (∑ p : {p : dhIrrBounded k n // pred p}, f p.val) +
              ∑ p : {p : dhIrrBounded k n // ¬ pred p}, f p.val :=
        (Fintype.sum_subtype_add_sum_subtype pred f).symm
      have htrue :
          (∑ p : {p : dhIrrBounded k n // pred p}, f p.val) =
            ∑ p : {p : dhIrrBounded k n // pred p}, term p.val := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [f, p.property]
      have hfalse :
          (∑ p : {p : dhIrrBounded k n // ¬ pred p}, f p.val) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        simp [f, p.property]
      calc
        _ = (∑ p : {p : dhIrrBounded k n // pred p}, f p.val) +
              ∑ p : {p : dhIrrBounded k n // ¬ pred p}, f p.val := hfull
        _ = _ := by rw [htrue, hfalse]; simp

end ArtinPrimitiveRoots.Arith
