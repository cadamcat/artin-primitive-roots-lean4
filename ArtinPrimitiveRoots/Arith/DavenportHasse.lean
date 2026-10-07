import Mathlib
import ArtinPrimitiveRoots.Arith.DavenportHasse.Polynomial
import ArtinPrimitiveRoots.Arith.DavenportHasse.Extension

/-!
# Davenport–Hasse lifting for Jacobi sums

The multiplicative characters are pulled back along the field norm.
-/

namespace ArtinPrimitiveRoots.Arith

/-- Pull back a multiplicative character along the algebra norm. -/
noncomputable def normLift {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [Module.Free k K]
    (χ : MulChar k ℂ) : MulChar K ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (Units.map (Algebra.norm k)))

/-- The norm pullback agrees with evaluation on the norm, including at zero. -/
@[simp] theorem normLift_apply {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [Module.Free k K]
    (χ : MulChar k ℂ) (x : K) : normLift χ x = χ (Algebra.norm k x) := by
  change MulChar.ofUnitHom (χ.toUnitHom.comp (Units.map (Algebra.norm k))) x = _
  by_cases hx : x = 0
  · subst x
    rw [MulChar.map_zero, Algebra.norm_zero, MulChar.map_zero]
  · have hxU : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hxU.unit_spec, MulChar.ofUnitHom_coe]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulChar.coe_toUnitHom,
      Units.coe_map]

theorem normLift_mul {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [Module.Free k K] (α β : MulChar k ℂ) :
    normLift (k := k) (K := K) (α * β) =
      normLift (k := k) (K := K) α * normLift (k := k) (K := K) β := by
  apply MulChar.ext'
  intro x
  simp [normLift_apply]

theorem normLift_ne_one {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K]
    [Algebra k K] (α : MulChar k ℂ) (hα : α ≠ 1) :
    normLift (k := k) (K := K) α ≠ 1 := by
  intro h
  apply hα
  ext y
  obtain ⟨x, hx⟩ := FiniteField.unitsMap_norm_surjective k K y
  have hxval : Algebra.norm k (x : K) = (y : k) := by
    simpa [Units.coe_map] using congrArg (fun u : kˣ => (u : k)) hx
  have hval := congrArg (fun ϕ : MulChar K ℂ => ϕ (x : K)) h
  simpa [normLift_apply, hxval] using hval

/-- Pull back an additive character along the field trace. -/
noncomputable def traceLift {k K : Type*} [Field k] [Field K] [Algebra k K]
    (ψ : AddChar k ℂ) : AddChar K ℂ :=
  ψ.compAddMonoidHom (Algebra.trace k K).toAddMonoidHom

@[simp] theorem traceLift_apply {k K : Type*} [Field k] [Field K] [Algebra k K]
    (ψ : AddChar k ℂ) (x : K) : traceLift ψ x = ψ (Algebra.trace k K x) := rfl

theorem traceLift_ne_one {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K]
    [Algebra k K] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) :
    traceLift (k := k) (K := K) ψ ≠ 1 := by
  intro h
  apply hψ
  ext y
  have htr : Function.Surjective (Algebra.trace k K) := Algebra.trace_surjective k K
  obtain ⟨x, hx⟩ := htr y
  have hval := congrArg (fun ϕ : AddChar K ℂ => ϕ x) h
  simpa [traceLift, hx] using hval

/-- Davenport–Hasse lifting for Gauss sums over finite fields. -/
theorem gaussSum_lift {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K]
    [Algebra k K] (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hf : 1 ≤ Module.finrank k K) :
    gaussSum (normLift (k := k) (K := K) χ) (traceLift ψ) =
        (-1 : ℂ) ^ (Module.finrank k K - 1) *
        gaussSum χ ψ ^ Module.finrank k K := by
  classical
  let n := Module.finrank k K
  let g := gaussSum χ ψ
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hf
  have hprefix : ∀ j ≤ n,
      PowerSeries.coeff j (dhEulerProduct χ ψ n) =
        PowerSeries.coeff j (dhLSeries χ ψ) := by
    intro j hj
    exact dhEulerProduct_coeff_eq_dhLSeries χ ψ n j hj
  have hinvE := dhEulerInverseProduct_eq_inv χ ψ n hχ hψ
  have hinvL := dhGeom_gauss_eq_dhLSeries_inv χ ψ hχ hψ
  have hprefixInv : ∀ j ≤ n,
      PowerSeries.coeff j (dhEulerInverseProduct χ ψ n) =
        PowerSeries.coeff j (dhGeom g) := by
    intro j hj
    calc
      PowerSeries.coeff j (dhEulerInverseProduct χ ψ n) =
          PowerSeries.coeff j (dhEulerProduct χ ψ n)⁻¹ := by rw [hinvE]
      _ = PowerSeries.coeff j (dhLSeries χ ψ)⁻¹ :=
        coeff_inv_eq_of_prefix (dhEulerProduct χ ψ n) (dhLSeries χ ψ) n hprefix j hj
      _ = PowerSeries.coeff j (dhGeom g) := by rw [← hinvL]
  have hderivPrefix (j : ℕ) (hj : j ≤ n) :
      PowerSeries.coeff j (PowerSeries.X *
          PowerSeries.derivative (dhEulerProduct χ ψ n)) =
        PowerSeries.coeff j (PowerSeries.X *
          PowerSeries.derivative (dhLSeries χ ψ)) := by
    cases j with
    | zero => simp
    | succ j =>
      have hj' : j + 1 ≤ n := by omega
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        hprefix (j + 1) hj']
  have hlogPrefix :
      PowerSeries.coeff n
          (PowerSeries.X * PowerSeries.derivative (dhEulerProduct χ ψ n) *
            dhEulerInverseProduct χ ψ n) =
        PowerSeries.coeff n
          (PowerSeries.X * PowerSeries.derivative (dhLSeries χ ψ) * dhGeom g) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro x hx
    have hsum : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hx1 : x.1 ≤ n := by omega
    have hx2 : x.2 ≤ n := by omega
    rw [hderivPrefix x.1 hx1, hprefixInv x.2 hx2]
  have hEulerCoeff := dhEulerProduct_log_derivative_coeff χ ψ n hn
  have hBaseCoeff :
      PowerSeries.coeff n
          (PowerSeries.X * PowerSeries.derivative (dhLSeries χ ψ) * dhGeom g) = -g ^ n := by
    simpa [dhEulerLogDerivative, g, n, hn.ne'] using
      (dhEulerLogDerivative_coeff χ ψ hχ hψ n)
  have hpowerSum :
      ∑ p : {p : dhIrrBounded k n // p.val.val.natDegree ∣ n},
          (p.val.val.val.natDegree : ℂ) *
            (dhPolyWeight χ ψ p.val.val.val) ^ (n / p.val.val.val.natDegree) =
        -g ^ n := by
    calc
      _ = PowerSeries.coeff n
          (PowerSeries.X * PowerSeries.derivative (dhEulerProduct χ ψ n) *
            dhEulerInverseProduct χ ψ n) := hEulerCoeff.symm
      _ = PowerSeries.coeff n
          (PowerSeries.X * PowerSeries.derivative (dhLSeries χ ψ) * dhGeom g) := hlogPrefix
      _ = -g ^ n := hBaseCoeff
  have hliftSum := dhLiftWeight_sum_irredDivides χ ψ n rfl
  have hweighted : ∑ x : K, dhLiftWeight χ ψ x = -g ^ n := hliftSum.trans hpowerSum
  have hGaussWeight :
      ∑ x : K, dhLiftWeight χ ψ x =
        (-1 : ℂ) ^ n * gaussSum (normLift (k := k) (K := K) χ)
          (traceLift (k := k) (K := K) ψ) := by
    simp only [dhLiftWeight, normLift_apply, traceLift_apply, n]
    rw [← Finset.mul_sum]
    simp [gaussSum]
  have hgauss : (-1 : ℂ) ^ n *
      gaussSum (normLift (k := k) (K := K) χ) (traceLift ψ) = -g ^ n :=
    hGaussWeight.symm.trans hweighted
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← pow_add]
    have hnn : n + n = 2 * n := by omega
    rw [hnn, pow_mul]
    norm_num
  calc
    gaussSum (normLift (k := k) (K := K) χ) (traceLift ψ) =
        ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
          gaussSum (normLift (k := k) (K := K) χ) (traceLift ψ) := by
            rw [hsign, one_mul]
    _ = (-1 : ℂ) ^ n *
          ((-1 : ℂ) ^ n *
            gaussSum (normLift (k := k) (K := K) χ) (traceLift ψ)) := by ring
    _ = (-1 : ℂ) ^ n * (-g ^ n) := by rw [hgauss]
    _ = (-1 : ℂ) ^ (n + 1) * g ^ n := by rw [pow_succ]; ring
    _ = (-1 : ℂ) ^ (n - 1) * g ^ n := by
      have hnexp : n + 1 = (n - 1) + 2 := by omega
      rw [hnexp, pow_add]
      norm_num

theorem jacobiSum_lift {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K]
    [Algebra k K] (α β : MulChar k ℂ) (hα : α ≠ 1) (hβ : β ≠ 1)
    (hαβ : α * β ≠ 1) (hf : 1 ≤ Module.finrank k K) :
    jacobiSum (normLift (k := k) (K := K) α) (normLift (k := k) (K := K) β) =
      (-1 : ℂ) ^ (Module.finrank k K - 1) *
        jacobiSum α β ^ Module.finrank k K := by
  let ψ : AddChar k ℂ := AddChar.FiniteField.primitiveChar_to_Complex k
  let ψK : AddChar K ℂ := traceLift (k := k) (K := K) ψ
  have hψprim : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive k
  have hψ : ψ ≠ 1 := by
    intro h
    have h1 := hψprim (a := (1 : k)) one_ne_zero
    simpa [h] using h1
  have hψKneq : ψK ≠ 1 := traceLift_ne_one (k := k) (K := K) ψ hψ
  have hψKprim : ψK.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψKneq
  have hcardk : (Fintype.card k : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card k ≠ 0)
  have hcardK : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  have hαβK : normLift (k := k) (K := K) α * normLift β ≠ 1 := by
    rw [← normLift_mul]
    exact normLift_ne_one (α * β) hαβ
  have hbase : jacobiSum α β =
      gaussSum α ψ * gaussSum β ψ / gaussSum (α * β) ψ :=
    jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hcardk hαβ hψprim
  have hlift : jacobiSum (normLift (k := k) (K := K) α)
      (normLift (k := k) (K := K) β) =
      gaussSum (normLift α) ψK * gaussSum (normLift β) ψK /
        gaussSum (normLift α * normLift β) ψK :=
    jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hcardK hαβK hψKprim
  let n := Module.finrank k K
  let s : ℂ := (-1 : ℂ) ^ (n - 1)
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact pow_ne_zero _ (by norm_num)
  have hgab0 : gaussSum (α * β) ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcardk hαβ hψprim
  have hga := gaussSum_lift α ψ hα hψ hf
  have hgb := gaussSum_lift β ψ hβ hψ hf
  have hgab := gaussSum_lift (α * β) ψ hαβ hψ hf
  calc
    jacobiSum (normLift (k := k) (K := K) α) (normLift β) =
        gaussSum (normLift α) ψK * gaussSum (normLift β) ψK /
          gaussSum (normLift α * normLift β) ψK := hlift
    _ = s * jacobiSum α β ^ n := by
      rw [hga, hgb, ← normLift_mul, hgab, hbase]
      dsimp [s, n]
      rw [div_pow, mul_pow]
      field_simp [hs0, hgab0]

end ArtinPrimitiveRoots.Arith
