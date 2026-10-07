import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Hecke.Boundary
import Mathlib.FieldTheory.Finite.Basic

/-!
# §7 algebraic field and splitting nodes

Blueprint nodes `spl:kummer-degree`, `spl:discriminant-bound`, `spl:field-bounds`,
`sp:compositum`, and `alg:splitting-test`; source `07-splitting.tex:37-99` and
`01a-reduction.tex:69-99`.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Ext.SplittingInputs

private theorem kummer_no_root (a : ℤ) (ha : 1 < |a|) (q : ℕ) [NeZero q]
    (hq : q.Prime) (hqlarge : Nat.log2 a.natAbs < q) :
    ∀ b : cyclotomicField q, b ^ q ≠ (a : cyclotomicField q) := by
  let E := cyclotomicField q
  letI : IsCyclotomicExtension {q} ℚ (cyclotomicField q) :=
    CyclotomicField.isCyclotomicExtension q ℚ
  have hdegree : Module.finrank ℚ E = q - 1 := by
    simpa [Nat.totient_prime hq] using IsCyclotomicExtension.Rat.finrank q E
  intro b hb
  have hnorm : (Algebra.norm ℚ b) ^ q = (a : ℚ) ^ (q - 1) := by
    calc
      (Algebra.norm ℚ b) ^ q = Algebra.norm ℚ (b ^ q) := by simp
      _ = Algebra.norm ℚ (algebraMap ℚ E (a : ℚ)) := by
        congr 1
      _ = (a : ℚ) ^ Module.finrank ℚ E := by rw [Algebra.norm_algebraMap]
      _ = (a : ℚ) ^ (q - 1) := by rw [hdegree]
  have hcop : q.Coprime (q - 1) := by
    simpa using (Nat.coprime_self_sub_right (n := q) (m := 1) (by omega : 1 ≤ q)).2
      (show Nat.Coprime q 1 by simp)
  obtain ⟨r, _, hr⟩ := (pow_eq_pow_iff_of_coprime hcop).mp hnorm
  have hrInt : IsIntegral ℤ r := by
    apply IsIntegral.of_pow hq.pos
    rw [← hr]
    exact isIntegral_intCast a
  let rO : 𝓞 ℚ := ⟨r, hrInt⟩
  let z : ℤ := Rat.ringOfIntegersEquiv rO
  have hzcast : (z : ℚ) = r := by
    change ((Rat.ringOfIntegersEquiv rO : ℤ) : ℚ) = r
    rw [Rat.ringOfIntegersEquiv_apply_coe]
    rfl
  have hz : z ^ q = a := by
    have hzQ : (z : ℚ) ^ q = (a : ℚ) := by rw [hzcast, ← hr]
    exact_mod_cast hzQ
  have ha2 : 2 ≤ a.natAbs := by
    have : (1 : ℤ) < (a.natAbs : ℤ) := by
      simpa only [Int.abs_eq_natAbs] using ha
    exact_mod_cast this
  have hnat : z.natAbs ^ q = a.natAbs := by
    simpa using congrArg Int.natAbs hz
  have hz2 : 2 ≤ z.natAbs := by
    by_contra h
    have hzle : z.natAbs ≤ 1 := by omega
    have hpow : z.natAbs ^ q ≤ 1 := by
      calc
        z.natAbs ^ q ≤ 1 ^ q := Nat.pow_le_pow_left hzle q
        _ = 1 := by simp
    omega
  have htwo : 2 ^ q ≤ a.natAbs := by
    rw [← hnat]
    exact Nat.pow_le_pow_left hz2 q
  have hlog : q ≤ Nat.log 2 a.natAbs :=
    (Nat.le_log_iff_pow_le Nat.one_lt_two (by omega : a.natAbs ≠ 0)).2 htwo
  exact (not_le_of_gt hqlarge) (by simpa [Nat.log2_eq_log_two] using hlog)

/-- **`spl:kummer-degree`**, `07-splitting.tex:37-51`. For `q > log₂ |a|`, the Kummer
polynomial is irreducible over `E_q`, its splitting field has relative degree `q`, and the
absolute degree is `q(q-1)`. The Galois group over `E_q` is identified with `μ_q` by
`ext:kummer-galois`. -/
theorem spl_kummer_degree (a : ℤ) (ha : 1 < |a|) (q : ℕ) [NeZero q] (hq : q.Prime)
    (hqlarge : Nat.log2 a.natAbs < q) :
    Irreducible (kummerPolynomial a q) ∧
      Module.finrank (cyclotomicField q) (kummerField a q) = q ∧
      Module.finrank ℚ (cyclotomicField q) = q - 1 ∧
      kummerDegree a q = q * (q - 1) ∧
      Nonempty (Gal(kummerField a q / cyclotomicField q) ≃*
        rootsOfUnity q (cyclotomicField q)) := by
  let E := cyclotomicField q
  let K := kummerField a q
  letI : IsCyclotomicExtension {q} ℚ (cyclotomicField q) :=
    CyclotomicField.isCyclotomicExtension q ℚ
  letI : Polynomial.IsSplittingField E K
      (Polynomial.X ^ q - Polynomial.C (a : E)) :=
    Polynomial.IsSplittingField.splittingField (Polynomial.X ^ q - Polynomial.C (a : E))
  have hEdegree : Module.finrank ℚ E = q - 1 := by
    simpa [Nat.totient_prime hq] using IsCyclotomicExtension.Rat.finrank q E
  have hroot : ∀ b : E, b ^ q ≠ (a : E) := kummer_no_root a ha q hq hqlarge
  have hirr : Irreducible (kummerPolynomial a q) := by
    exact ext_kummer_irreducible hq hroot
  have hζ : (primitiveRoots q E).Nonempty := by
    refine ⟨IsCyclotomicExtension.zeta q ℚ E, ?_⟩
    exact (mem_primitiveRoots (NeZero.pos q)).2 (IsCyclotomicExtension.zeta_spec q ℚ E)
  have hrel : Module.finrank E K = q := by
    exact finrank_of_isSplittingField_X_pow_sub_C hζ hirr K
  have habs : Module.finrank ℚ K = q * (q - 1) := by
    rw [← Module.finrank_mul_finrank ℚ E K, hrel]
    rw [hEdegree]
    ring
  refine ⟨hirr, hrel, ?_, ?_, ?_⟩
  · exact hEdegree
  · simpa [kummerDegree] using habs
  · exact ext_kummer_galois hζ hirr

theorem kummer_discriminant_bound (a : ℤ) (ha : 1 < |a|) (q : ℕ) [NeZero q]
    (hq : q.Prime) (hqlarge : Nat.log2 a.natAbs < q) :
    absoluteDiscriminant (kummerField a q) ≤
      (q : ℝ) ^ (q * (q - 2)) *
        ((q : ℝ) ^ q * (a.natAbs : ℝ) ^ (q - 1)) ^ (q - 1) ∧
    (NumberField.discr (kummerField a q)).natAbs ∣
      q ^ (q * (q - 2)) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
  let E := cyclotomicField q
  let K := kummerField a q
  letI : IsCyclotomicExtension {q} ℚ (cyclotomicField q) :=
    CyclotomicField.isCyclotomicExtension q ℚ
  letI : Polynomial.IsSplittingField E K (Polynomial.X ^ q - Polynomial.C (a : E)) :=
    Polynomial.IsSplittingField.splittingField (Polynomial.X ^ q - Polynomial.C (a : E))
  obtain ⟨hirr, hrel, hEdeg, _, _⟩ := spl_kummer_degree a ha q hq hqlarge
  haveI : FiniteDimensional E K := Polynomial.IsSplittingField.finiteDimensional K
    (kummerPolynomial a q)
  let α : K := rootOfSplitsXPowSubC (NeZero.pos q) (a : E) K
  have hαpow : α ^ q = algebraMap E K (a : E) := rootOfSplitsXPowSubC_pow (a : E) K
  have hcast : algebraMap E K (a : E) = (a : K) := by
    calc
      algebraMap E K (a : E) = algebraMap E K (algebraMap ℤ E a) := by rfl
      _ = algebraMap ℤ K a := (IsScalarTower.algebraMap_apply ℤ E K a).symm
      _ = (a : K) := by simp
  have hαpow' : α ^ q = (a : K) := hαpow.trans hcast
  have hαInt : IsIntegral ℤ α := by
    apply IsIntegral.of_pow (NeZero.pos q)
    rw [hαpow']
    exact isIntegral_intCast a
  have hαIntE : IsIntegral E α := IsIntegral.of_finite E α
  have hαeval : Polynomial.aeval α (kummerPolynomial a q) = 0 := by
    simp [kummerPolynomial, hαpow, hcast]
  have hmonic : (kummerPolynomial a q).Monic :=
    Polynomial.monic_X_pow_sub_C (a : E) (NeZero.ne q)
  have hminpoly : minpoly E α = kummerPolynomial a q :=
    (minpoly.eq_of_irreducible_of_monic hirr hαeval hmonic).symm
  have hminDegree : Module.finrank E (IntermediateField.adjoin E {α}) = q := by
    rw [IntermediateField.adjoin.finrank hαIntE, hminpoly]
    change (Polynomial.X ^ q - Polynomial.C (a : E)).natDegree = q
    rw [Polynomial.natDegree_X_pow_sub_C]
  have hrel' : Module.finrank E K = q := by simpa [E, K] using hrel
  have hmul := Module.finrank_mul_finrank E (IntermediateField.adjoin E {α}) K
  have hsubDegree : Module.finrank (IntermediateField.adjoin E {α}) K = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hq.pos
    simpa [hminDegree, hrel'] using hmul
  have hfieldTop : IntermediateField.adjoin E {α} = ⊤ :=
    IntermediateField.finrank_eq_one_iff_eq_top.mp hsubDegree
  have hgen : Algebra.adjoin E {α} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hαIntE.isAlgebraic).mp hfieldTop
  let pb : PowerBasis E K := PowerBasis.ofAdjoinEqTop hαIntE hgen
  have hnormα : Algebra.norm E α = (-1 : E) ^ q * -(a : E) := by
    calc
      Algebra.norm E α = Algebra.norm E pb.gen := by
        rw [PowerBasis.ofAdjoinEqTop_gen hαIntE hgen]
      _ = (-1 : E) ^ pb.dim * Polynomial.coeff (minpoly E pb.gen) 0 :=
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
      _ = (-1 : E) ^ q * -(a : E) := by
        rw [PowerBasis.ofAdjoinEqTop_dim hαIntE hgen,
          PowerBasis.ofAdjoinEqTop_gen hαIntE hgen, hminpoly, kummerPolynomial]
        rw [Polynomial.natDegree_X_pow_sub_C]
        simp [hq.ne_zero]
        exact (NeZero.ne q).symm
  let A := 𝓞 E
  let B := 𝓞 K
  let αO : B := ⟨α, hαInt⟩
  have hαOcoe : algebraMap B K αO = α := by
    change (αO : K) = α
    rfl
  have hαOInt : IsIntegral A αO := Algebra.IsIntegral.isIntegral αO
  have hminpolyO : minpoly E α = (minpoly A αO).map (algebraMap A E) := by
    have h := minpoly.isIntegrallyClosed_eq_field_fractions E K hαOInt
    rw [hαOcoe] at h
    exact h
  let d : B := Polynomial.aeval αO (Polynomial.derivative (minpoly A αO))
  have hcomp : (algebraMap E K).comp (algebraMap A E) =
      (algebraMap B K).comp (algebraMap A B) := by
    rw [← IsScalarTower.algebraMap_eq A E K, ← IsScalarTower.algebraMap_eq A B K]
  have hdEval := Polynomial.map_aeval_eq_aeval_map hcomp
    (Polynomial.derivative (minpoly A αO)) αO
  have hdK : (d : K) = (q : K) * α ^ (q - 1) := by
    calc
      (d : K) = Polynomial.aeval α (Polynomial.derivative (minpoly E α)) := by
        simpa [d, hαOcoe, ← Polynomial.derivative_map, ← hminpolyO] using hdEval
      _ = (q : K) * α ^ (q - 1) := by
        rw [hminpoly]
        simp [kummerPolynomial, Polynomial.derivative_X_pow, hq.ne_zero]
  have hnormdE : Algebra.norm E (d : K) =
      (q : E) ^ q * ((-1 : E) ^ q * -(a : E)) ^ (q - 1) := by
    have hIntCast (z : ℤ) : algebraMap E K (z : E) = (z : K) := by
      change algebraMap E K (algebraMap ℤ E z) = algebraMap ℤ K z
      exact (IsScalarTower.algebraMap_apply ℤ E K z).symm
    have hqcast : (q : K) = algebraMap E K (q : E) := by
      calc
        (q : K) = ((q : ℤ) : K) := by norm_cast
        _ = algebraMap E K ((q : ℤ) : E) := (hIntCast q).symm
        _ = algebraMap E K (q : E) := by norm_cast
    rw [hdK, map_mul, map_pow, hqcast,
      Algebra.norm_algebraMap, hrel, hnormα]
  have hnormdQ : Algebra.norm ℚ (d : K) =
      (q : ℚ) ^ (q * (q - 1)) *
        (((-1 : ℚ) ^ q * -(a : ℚ)) ^ ((q - 1) * (q - 1))) := by
    have htower : Algebra.norm ℚ (Algebra.norm E (d : K)) = Algebra.norm ℚ (d : K) :=
      Algebra.norm_norm
    have hqCast : (q : E) = algebraMap ℚ E (q : ℚ) := by norm_cast
    have hgammaCast : (-1 : E) ^ q * -(a : E) =
        algebraMap ℚ E ((-1 : ℚ) ^ q * -(a : ℚ)) := by
      calc
        (-1 : E) ^ q * -(a : E) =
            algebraMap ℤ E (-1) ^ q * algebraMap ℤ E (-a) := by simp
        _ = algebraMap ℤ E (((-1 : ℤ) ^ q) * -a) := by
          rw [← map_pow, ← map_mul]
        _ = algebraMap ℚ E (algebraMap ℤ ℚ (((-1 : ℤ) ^ q) * -a)) :=
          IsScalarTower.algebraMap_apply ℤ ℚ E _
        _ = algebraMap ℚ E ((-1 : ℚ) ^ q * -(a : ℚ)) := by
          simp [map_mul, map_pow, map_neg]
    calc
      Algebra.norm ℚ (d : K) = Algebra.norm ℚ (Algebra.norm E (d : K)) := htower.symm
      _ = (Algebra.norm ℚ (q : E)) ^ q *
          (Algebra.norm ℚ ((-1 : E) ^ q * -(a : E))) ^ (q - 1) := by
        rw [hnormdE, map_mul, map_pow, map_pow]
      _ = (q : ℚ) ^ (q * (q - 1)) *
          (((-1 : ℚ) ^ q * -(a : ℚ)) ^ ((q - 1) * (q - 1))) := by
        rw [hqCast, hgammaCast, Algebra.norm_algebraMap, hEdeg,
          Algebra.norm_algebraMap, hEdeg]
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (q - 1) q]
  have hnormdInt : Algebra.norm ℤ d =
      (q : ℤ) ^ (q * (q - 1)) *
        (((-1 : ℤ) ^ q * -a) ^ ((q - 1) * (q - 1))) := by
    have hcastNorm : (Algebra.norm ℤ d : ℚ) =
        (q : ℚ) ^ (q * (q - 1)) *
          (((-1 : ℚ) ^ q * -(a : ℚ)) ^ ((q - 1) * (q - 1))) := by
      rw [Algebra.coe_norm_int]
      exact hnormdQ
    exact_mod_cast hcastNorm
  have hprincipalNorm : Ideal.absNorm (Ideal.span ({d} : Set B)) =
      (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
    rw [Ideal.absNorm_span_singleton, hnormdInt]
    simp [Int.natAbs_mul, Int.natAbs_pow, pow_mul, mul_comm]
    rw [← mul_pow]
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    simp at ha
  have haNatPos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
  have hprincipalPos : 0 < Ideal.absNorm (Ideal.span ({d} : Set B)) := by
    rw [hprincipalNorm]
    exact pow_pos (Nat.mul_pos (pow_pos hq.pos _) (pow_pos haNatPos _)) _
  have hcond := conductor_mul_differentIdeal (A := A) (K := E) (L := K) αO hgen
  have hnormProd : Ideal.absNorm (conductor A αO) *
      Ideal.absNorm (differentIdeal A B) = Ideal.absNorm (Ideal.span ({d} : Set B)) := by
    have := congrArg Ideal.absNorm hcond
    simpa only [map_mul] using this
  have hcondPos : 0 < Ideal.absNorm (conductor A αO) := by
    by_contra h
    have hzero : Ideal.absNorm (conductor A αO) = 0 := Nat.eq_zero_of_not_pos h
    rw [hzero, zero_mul] at hnormProd
    exact (Nat.ne_of_gt hprincipalPos) hnormProd.symm
  have hdiffNorm : Ideal.absNorm (differentIdeal A B) ≤
      (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
    calc
      Ideal.absNorm (differentIdeal A B) ≤
          Ideal.absNorm (conductor A αO) * Ideal.absNorm (differentIdeal A B) :=
        Nat.le_mul_of_pos_left _ hcondPos
      _ = (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
        rw [hnormProd, hprincipalNorm]
  have hdiscTower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    E (𝓞 E) K (𝓞 K)
  have hEdisc : (NumberField.discr E).natAbs = q ^ (q - 2) := by
    have h := ext_cyclotomic_disc (q := q) hq
    have h' : ((NumberField.discr E).natAbs : ℝ) = (q : ℝ) ^ (q - 2) := by
      simpa [absoluteDiscriminant, Nat.cast_natAbs] using h
    exact_mod_cast h'
  have hdiscNat : (NumberField.discr K).natAbs ≤
      q ^ (q * (q - 2)) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
    rw [hdiscTower, hEdisc]
    calc
      Ideal.absNorm (differentIdeal A B) * (q ^ (q - 2)) ^ Module.finrank E K ≤
          (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) * (q ^ (q - 2)) ^ Module.finrank E K :=
        Nat.mul_le_mul_right _ hdiffNorm
      _ = q ^ (q * (q - 2)) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
        rw [hrel]
        calc
          _ = (q ^ (q - 2)) ^ q * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by ac_rfl
          _ = q ^ ((q - 2) * q) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by rw [← pow_mul]
          _ = q ^ (q * (q - 2)) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
            rw [Nat.mul_comm (q - 2) q]
  have hdiscReal : ((NumberField.discr K).natAbs : ℝ) ≤
      (q : ℝ) ^ (q * (q - 2)) *
        ((q : ℝ) ^ q * (a.natAbs : ℝ) ^ (q - 1)) ^ (q - 1) := by
    exact_mod_cast hdiscNat
  have hdiscDvd : (NumberField.discr K).natAbs ∣
      q ^ (q * (q - 2)) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
    have hEpow : (q ^ (q - 2)) ^ q = q ^ (q * (q - 2)) := by
      rw [← pow_mul, Nat.mul_comm (q - 2) q]
    refine ⟨Ideal.absNorm (conductor A αO), ?_⟩
    calc
      q ^ (q * (q - 2)) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) =
          q ^ (q * (q - 2)) * Ideal.absNorm (Ideal.span ({d} : Set B)) := by
        rw [hprincipalNorm]
      _ = q ^ (q * (q - 2)) *
          (Ideal.absNorm (conductor A αO) * Ideal.absNorm (differentIdeal A B)) := by
        rw [hnormProd]
      _ = (Ideal.absNorm (differentIdeal A B) * (q ^ (q - 2)) ^ q) *
          Ideal.absNorm (conductor A αO) := by rw [hEpow]; ac_rfl
      _ = (NumberField.discr K).natAbs * Ideal.absNorm (conductor A αO) := by
        rw [hdiscTower, hEdisc, hrel]
  refine ⟨?_, hdiscDvd⟩
  simpa [absoluteDiscriminant, Nat.cast_natAbs] using hdiscReal

theorem kummer_isGalois_rat (a : ℤ) (q : ℕ) [NeZero q] :
    IsGalois ℚ (kummerField a q) := by
  let E := cyclotomicField q
  let K := kummerField a q
  let f : Polynomial ℚ := Polynomial.cyclotomic q ℚ
  let g : Polynomial ℚ := Polynomial.X ^ q - Polynomial.C (a : ℚ)
  letI : IsCyclotomicExtension {q} ℚ (cyclotomicField q) :=
    CyclotomicField.isCyclotomicExtension q ℚ
  letI : Polynomial.IsSplittingField E K
      (Polynomial.X ^ q - Polynomial.C (a : E)) :=
    Polynomial.IsSplittingField.splittingField (Polynomial.X ^ q - Polynomial.C (a : E))
  have hmapg : g.map (algebraMap ℚ E) = kummerPolynomial a q := by
    simp [g, kummerPolynomial]
  have hcycloNe : f ≠ 0 :=
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos q)).ne_zero
  have hbinomNe : g ≠ 0 := by
    exact Polynomial.X_pow_sub_C_ne_zero (NeZero.pos q) (a : ℚ)
  letI : Polynomial.IsSplittingField ℚ E f :=
    Polynomial.IsSplittingField.splittingField f
  have hsplitG : Polynomial.IsSplittingField E K (kummerPolynomial a q) :=
    Polynomial.IsSplittingField.splittingField (kummerPolynomial a q)
  letI : Polynomial.IsSplittingField E K (g.map (algebraMap ℚ E)) := by
    rw [hmapg]
    exact hsplitG
  letI : Polynomial.IsSplittingField ℚ K (f * g) :=
    Polynomial.IsSplittingField.mul (F := ℚ) (K := E) (L := K) f g
      hcycloNe hbinomNe
  letI : Normal ℚ K := Normal.of_isSplittingField (f * g)
  letI : Algebra.IsSeparable ℚ K := by infer_instance
  exact ⟨⟩

/-- **`spl:discriminant-bound`**, `07-splitting.tex:53-68`. The norm-argument degree node and
the discriminant tower yield the power-basis discriminant bound and a logarithmic estimate. The
constant depends on `a`, not on `q`. -/
theorem spl_discriminant_bound (a : ℤ) (ha : 1 < |a|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q.Prime →
      Nat.log2 a.natAbs < q →
        absoluteDiscriminant (kummerField a q) ≤
            (q : ℝ) ^ (q * (q - 2)) *
              ((q : ℝ) ^ q * (a.natAbs : ℝ) ^ (q - 1)) ^ (q - 1) ∧
          Real.log (absoluteDiscriminant (kummerField a q)) + kummerDegree a q ≤
            C * (kummerDegree a q : ℝ) * Real.log (2 * (q : ℝ)) := by
  have haNat2 : 2 ≤ a.natAbs := by
    have h : (1 : ℤ) < (a.natAbs : ℤ) := by
      simpa only [Int.abs_eq_natAbs] using ha
    exact_mod_cast h
  have haReal1 : 1 ≤ (a.natAbs : ℝ) := by
    have hnat : 1 ≤ a.natAbs := le_trans (by decide) haNat2
    exact_mod_cast hnat
  have hlogA : 0 ≤ Real.log (a.natAbs : ℝ) := Real.log_nonneg haReal1
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := 2 + (1 + Real.log (a.natAbs : ℝ)) / Real.log (4 : ℝ)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro q _ hq hqlarge
  have hq2Nat : 2 ≤ q := hq.two_le
  obtain ⟨_, _, _, hdegree, _⟩ := spl_kummer_degree a ha q hq hqlarge
  have hdisc := (kummer_discriminant_bound a ha q hq hqlarge).1
  let r : ℝ := q
  let b : ℝ := a.natAbs
  let n : ℝ := (q * (q - 1) : ℕ)
  let U : ℝ := r ^ (q * (q - 2)) * (r ^ q * b ^ (q - 1)) ^ (q - 1)
  let L : ℝ := Real.log (2 * r)
  let A : ℝ := Real.log b
  let R : ℝ := L / Real.log (4 : ℝ)
  have hrPos : 0 < r := by dsimp [r]; exact_mod_cast hq.pos
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast (le_trans (by decide) haNat2)
  have hLnonneg : 0 ≤ L := by
    apply Real.log_nonneg
    dsimp [L, r]
    have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq2Nat
    nlinarith
  have hlogrNonneg : 0 ≤ Real.log r := by
    apply Real.log_nonneg
    dsimp [r]
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hq2Nat)
  have hA_nonneg : 0 ≤ A := by simpa [A, b] using hlogA
  have hrq : Real.log r ≤ L := by
    apply Real.log_le_log hrPos
    dsimp [L, r]
    have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq2Nat
    nlinarith
  have hL4 : Real.log (4 : ℝ) ≤ L := by
    apply Real.log_le_log (by norm_num)
    dsimp [L, r]
    have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq2Nat
    nlinarith
  have hlogU : Real.log U =
      ((q * (q - 2) + q * (q - 1) : ℕ) : ℝ) * Real.log r +
        (((q - 1) * (q - 1) : ℕ) : ℝ) * A := by
    dsimp [U, r, b, A]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
    rw [Real.log_pow]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
    rw [Real.log_pow]
    push_cast
    ring
  have hcoef : 0 ≤ ((q * (q - 2) + q * (q - 1) : ℕ) : ℝ) := by positivity
  have hcoefBound :
      ((q * (q - 2) + q * (q - 1) : ℕ) : ℝ) ≤ 2 * n := by
    dsimp [n]
    push_cast [Nat.cast_sub hq2Nat, Nat.cast_sub (by omega : 1 ≤ q)]
    have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq2Nat
    nlinarith
  have haCoefBound :
      (((q - 1) * (q - 1) : ℕ) : ℝ) ≤ n := by
    dsimp [n]
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
    have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq2Nat
    nlinarith
  have hlogUle : Real.log U ≤ 2 * n * L + n * A := by
    rw [hlogU]
    calc
      ((q * (q - 2) + q * (q - 1) : ℕ) : ℝ) * Real.log r +
          (((q - 1) * (q - 1) : ℕ) : ℝ) * A ≤
          ((q * (q - 2) + q * (q - 1) : ℕ) : ℝ) * L +
            (((q - 1) * (q - 1) : ℕ) : ℝ) * A := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hrq hcoef)
          (le_refl _)
      _ ≤ 2 * n * L + n * A := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hcoefBound hLnonneg)
          (mul_le_mul_of_nonneg_right haCoefBound hA_nonneg)
  have hRone : 1 ≤ R := by
    dsimp [R]
    exact (one_le_div hlog4).2 hL4
  have hnNonneg : 0 ≤ n := by positivity
  have hscaleOne : n ≤ n * R := by
    simpa using mul_le_mul_of_nonneg_left hRone hnNonneg
  have hscaleA : n * A ≤ n * A * R :=
    by simpa using mul_le_mul_of_nonneg_left hRone (mul_nonneg hnNonneg hA_nonneg)
  have hsmall : n * A + n ≤ ((1 + A) / Real.log (4 : ℝ)) * n * L := by
    calc
      n * A + n ≤ n * A * R + n * R := add_le_add hscaleA hscaleOne
      _ = ((1 + A) / Real.log (4 : ℝ)) * n * L := by
        dsimp [R]
        ring
  have htotal : Real.log U + n ≤ C * n * L := by
    calc
      Real.log U + n ≤ 2 * n * L + (n * A + n) := by linarith [hlogUle]
      _ ≤ 2 * n * L + ((1 + A) / Real.log (4 : ℝ)) * n * L :=
        add_le_add_right hsmall (2 * n * L)
      _ = C * n * L := by
        dsimp [C]
        ring
  have hDpos : 0 < absoluteDiscriminant (kummerField a q) := by
    have hne := NumberField.discr_ne_zero (kummerField a q)
    have hcast : (NumberField.discr (kummerField a q) : ℝ) ≠ 0 := by exact_mod_cast hne
    simpa [absoluteDiscriminant] using abs_pos.mpr hcast
  have hUpos : 0 < U := by
    dsimp [U, r, b]
    positivity
  have hlogD : Real.log (absoluteDiscriminant (kummerField a q)) ≤ Real.log U :=
    Real.log_le_log hDpos (by simpa [U, r, b] using hdisc)
  have hdegreeReal : (kummerDegree a q : ℝ) = n := by
    dsimp [n]
    exact_mod_cast hdegree
  have hfinal :
      Real.log (absoluteDiscriminant (kummerField a q)) +
          (kummerDegree a q : ℝ) ≤ C * (kummerDegree a q : ℝ) * L := by
    rw [hdegreeReal]
    have hlogDn : Real.log (absoluteDiscriminant (kummerField a q)) + n ≤ Real.log U + n := by
      linarith [hlogD]
    exact hlogDn.trans htotal
  refine ⟨hdisc, ?_⟩
  simpa [L] using hfinal

private theorem eq_of_pow_eq_mod_prime {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) [P.IsPrime] {m : ℕ} (hmpos : 0 < m) {x y c : R}
    (hm : (m : R) ∉ P) (hc : c ∉ P) (hx : x ^ m = c) (hy : y ^ m = c)
    (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have hprod : (x - y) * (∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)) = 0 := by
    rw [(Commute.all x y).mul_geom_sum₂ m, hx, hy]
    simp
  have hsum0 : ∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i) = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact (hne (sub_eq_zero.mp h)).elim
    · exact h
  have hxyQ : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y :=
    Ideal.Quotient.eq.mpr hxy
  have hsumQ : ∑ i ∈ Finset.range m,
      (Ideal.Quotient.mk P x) ^ i * (Ideal.Quotient.mk P y) ^ (m - 1 - i) = 0 := by
    simpa only [map_sum, map_mul, map_pow, map_zero] using
      congrArg (Ideal.Quotient.mk P) hsum0
  have hsumEq : ∑ i ∈ Finset.range m,
      (Ideal.Quotient.mk P x) ^ i * (Ideal.Quotient.mk P y) ^ (m - 1 - i) =
        (m : R ⧸ P) * (Ideal.Quotient.mk P x) ^ (m - 1) := by
    simp_rw [← hxyQ]
    calc
      ∑ i ∈ Finset.range m, (Ideal.Quotient.mk P x) ^ i *
          (Ideal.Quotient.mk P x) ^ (m - 1 - i) =
        ∑ i ∈ Finset.range m, (Ideal.Quotient.mk P x) ^ (m - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← pow_add]
          congr 1
          simp only [Finset.mem_range] at hi
          omega
      _ = (m : R ⧸ P) * (Ideal.Quotient.mk P x) ^ (m - 1) := by simp
  have hmQ : Ideal.Quotient.mk P (m : R) ≠ 0 := by
    intro h
    exact hm (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hcQ : Ideal.Quotient.mk P c ≠ 0 := by
    intro h
    exact hc (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hxQ : Ideal.Quotient.mk P x ≠ 0 := by
    intro h
    apply hcQ
    rw [← hx, map_pow, h, zero_pow (Nat.ne_of_gt hmpos)]
  have hzero : (m : R ⧸ P) * (Ideal.Quotient.mk P x) ^ (m - 1) = 0 :=
    hsumEq.symm.trans hsumQ
  exact (mul_ne_zero hmQ (pow_ne_zero _ hxQ)) hzero

/-- **`alg:splitting-test`** (only `⇐`), `01a-reduction.tex:69-99`. The elementary Kummer
congruences imply complete splitting in `K_q`. The explicit `p ∤ aq` hypothesis is retained from
the source statement. -/
theorem alg_splitting_test (a : ℤ) (ha0 : a ≠ 0) (p q : ℕ) [NeZero q]
    (hp : p.Prime) (hq : q.Prime)
    (hpaq : ¬ (p : ℤ) ∣ a * (q : ℤ))
    (hclass : q ∣ p - 1)
    (hpow : (a : ZMod p) ^ ((p - 1) / q) = 1) :
    splitsCompletely (kummerField a q) p := by
  let K := kummerField a q
  letI : IsGalois ℚ K := kummer_isGalois_rat a q
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  letI : Fact p.Prime := ⟨hp⟩
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  letI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hpne).mpr hpInt
  obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
    (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover
  letI : P.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  have hFrob := ext_frobenius (R := ℤ) (S := 𝓞 K) (G := Gal(K/ℚ)) P
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [← P.over_def (Ideal.span {(p : ℤ)})]
    exact (Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv).trans (Nat.card_zmod p)
  have hpaInt : ¬ (p : ℤ) ∣ a := by
    intro hpa
    exact hpaq (dvd_mul_of_dvd_left hpa (q : ℤ))
  have hqInt : ¬ (p : ℤ) ∣ (q : ℤ) := by
    intro hq'
    exact hpaq (dvd_mul_of_dvd_right hq' a)
  have haNotP : (a : 𝓞 K) ∉ P := by
    intro haP
    have haP' : algebraMap ℤ (𝓞 K) a ∈ P := by simpa using haP
    have haSpan : a ∈ Ideal.span {(p : ℤ)} :=
      (P.mem_of_liesOver (Ideal.span {(p : ℤ)}) a).2 haP'
    exact hpaInt (Ideal.mem_span_singleton.mp haSpan)
  have hqNotP : (q : 𝓞 K) ∉ P := by
    intro hqP
    have hqP' : algebraMap ℤ (𝓞 K) (q : ℤ) ∈ P := by exact_mod_cast hqP
    have hqSpan : (q : ℤ) ∈ Ideal.span {(p : ℤ)} :=
      (P.mem_of_liesOver (Ideal.span {(p : ℤ)}) (q : ℤ)).2 hqP'
    exact hqInt (Ideal.mem_span_singleton.mp hqSpan)
  let e : ℕ := (p - 1) / q
  have hpowDvd : (p : ℤ) ∣ a ^ e - 1 := by
    have hz : ((a ^ e - 1 : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub, Int.cast_pow, hpow]
      simp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ e - 1) p).mp hz
  have hpEq : p = q * e + 1 := by
    have hdiv : e * q = p - 1 := by
      dsimp [e]
      exact Nat.div_mul_cancel hclass
    calc
      p = (p - 1) + 1 := by omega
      _ = e * q + 1 := by rw [hdiv]
      _ = q * e + 1 := by rw [Nat.mul_comm]
  have hpMem : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := by
    exact (P.mem_of_liesOver (Ideal.span {(p : ℤ)}) (p : ℤ)).1
      (Ideal.mem_span_singleton_self _)
  have hpowCastP : algebraMap ℤ (𝓞 K) (a ^ e - 1) ∈ P := by
    obtain ⟨c, hc⟩ := hpowDvd
    rw [hc, map_mul]
    simpa [mul_comm] using P.mul_mem_left (algebraMap ℤ (𝓞 K) c) hpMem
  have h1NotP : (1 : 𝓞 K) ∉ P := by
    intro h
    exact hPprime.ne_top (P.eq_top_iff_one.mpr h)
  let σ : Gal(K/ℚ) := arithFrobAt ℤ Gal(K/ℚ) P
  have hpowAction {x : 𝓞 K} (hx : x ^ q = (a : 𝓞 K)) : x ^ p - x ∈ P := by
    have hxp : x ^ p = x * (a : 𝓞 K) ^ e := by
      calc
        x ^ p = x ^ (q * e + 1) := by rw [hpEq]
        _ = (x ^ q) ^ e * x := by rw [pow_add, pow_mul, pow_one]
        _ = (a : 𝓞 K) ^ e * x := by rw [hx]
        _ = x * (a : 𝓞 K) ^ e := mul_comm _ _
    have hdiff : x ^ p - x = x * algebraMap ℤ (𝓞 K) (a ^ e - 1) := by
      calc
        x ^ p - x = x * ((a : 𝓞 K) ^ e - 1) := by rw [hxp]; ring
        _ = x * algebraMap ℤ (𝓞 K) (a ^ e - 1) := by
          rw [map_sub, map_pow]
          simp
    rw [hdiff]
    exact P.mul_mem_left _ hpowCastP
  have hactGeneral (τ : Gal(K/ℚ)) (x : 𝓞 K) :
      (τ • x : 𝓞 K) = RingOfIntegers.mapAlgEquiv τ x := by
    apply RingOfIntegers.ext
    rfl
  have hfixRootMod {τ : Gal(K/ℚ)} {x : 𝓞 K}
      (hx : x ^ q = (a : 𝓞 K))
      (hmod : RingOfIntegers.mapAlgEquiv τ x - x ∈ P) : τ (x : K) = x := by
    have hxField : (x : K) ^ q = (a : K) := RingOfIntegers.ext_iff.mp hx
    have hτRoot : (RingOfIntegers.mapAlgEquiv τ x) ^ q = (a : 𝓞 K) := by
      apply RingOfIntegers.ext
      change (τ (x : K)) ^ q = (a : K)
      calc
        (τ (x : K)) ^ q = τ ((x : K) ^ q) := (map_pow τ (x : K) q).symm
        _ = τ (a : K) := by rw [hxField]
        _ = (a : K) := map_intCast τ a
    have heq := eq_of_pow_eq_mod_prime P hq.pos hqNotP haNotP hτRoot hx hmod
    have hcoeq := RingOfIntegers.ext_iff.mp heq
    change τ (x : K) = (x : K) at hcoeq
    exact hcoeq
  have hfixUnityMod {τ : Gal(K/ℚ)} {x : 𝓞 K}
      (hx : x ^ q = 1)
      (hmod : RingOfIntegers.mapAlgEquiv τ x - x ∈ P) : τ (x : K) = x := by
    have hxField : (x : K) ^ q = 1 := RingOfIntegers.ext_iff.mp hx
    have hτRoot : (RingOfIntegers.mapAlgEquiv τ x) ^ q = 1 := by
      apply RingOfIntegers.ext
      change (τ (x : K)) ^ q = 1
      calc
        (τ (x : K)) ^ q = τ ((x : K) ^ q) := (map_pow τ (x : K) q).symm
        _ = τ 1 := by rw [hxField]
        _ = 1 := map_one τ
    have heq := eq_of_pow_eq_mod_prime P hq.pos hqNotP h1NotP hτRoot hx hmod
    have hcoeq := RingOfIntegers.ext_iff.mp heq
    change τ (x : K) = (x : K) at hcoeq
    exact hcoeq
  have hσFixRoot {x : K} (hx : x ^ q = (a : K)) : σ x = x := by
    have hxInt : IsIntegral ℤ x := by
      apply IsIntegral.of_pow (NeZero.pos q)
      rw [hx]
      exact isIntegral_intCast a
    let xO : 𝓞 K := ⟨x, hxInt⟩
    have hxO : xO ^ q = (a : 𝓞 K) := by
      apply RingOfIntegers.ext
      exact hx
    have hFrobX : σ • xO - xO ^ p ∈ P := by
      simpa [σ, hcard] using hFrob xO
    have hact : (σ • xO : 𝓞 K) = RingOfIntegers.mapAlgEquiv σ xO := by
      apply RingOfIntegers.ext
      rfl
    have hmod : RingOfIntegers.mapAlgEquiv σ xO - xO ∈ P := by
      rw [← hact]
      have heq : σ • xO - xO = (σ • xO - xO ^ p) + (xO ^ p - xO) := by ring
      rw [heq]
      exact P.add_mem hFrobX (hpowAction hxO)
    have hσOroot : (RingOfIntegers.mapAlgEquiv σ xO) ^ q = (a : 𝓞 K) := by
      apply RingOfIntegers.ext
      have hxField : (xO : K) ^ q = (a : K) := hx
      change (σ (xO : K)) ^ q = (a : K)
      calc
        (σ (xO : K)) ^ q = σ ((xO : K) ^ q) := (map_pow σ (xO : K) q).symm
        _ = σ (a : K) := by rw [hxField]
        _ = (a : K) := map_intCast σ a
    have hrootEq := eq_of_pow_eq_mod_prime P hq.pos hqNotP haNotP hσOroot hxO hmod
    have hcoe : (RingOfIntegers.mapAlgEquiv σ xO : K) = (xO : K) :=
      RingOfIntegers.ext_iff.mp hrootEq
    change σ (xO : K) = (xO : K) at hcoe
    change σ x = x at hcoe
    exact hcoe
  have hpowUnity {x : 𝓞 K} (hx : x ^ q = 1) : x ^ p = x := by
    calc
      x ^ p = x ^ (q * e + 1) := by rw [hpEq]
      _ = (x ^ q) ^ e * x := by rw [pow_add, pow_mul, pow_one]
      _ = x := by rw [hx]; simp
  have hσFixUnity {z : K} (hz : z ^ q = 1) : σ z = z := by
    have hzInt : IsIntegral ℤ z := by
      apply IsIntegral.of_pow (NeZero.pos q)
      rw [hz]
      exact isIntegral_one
    let zO : 𝓞 K := ⟨z, hzInt⟩
    have hzO : zO ^ q = 1 := by
      apply RingOfIntegers.ext
      exact hz
    have hFrobZ : σ • zO - zO ^ p ∈ P := by
      simpa [σ, hcard] using hFrob zO
    have hactZ : (σ • zO : 𝓞 K) = RingOfIntegers.mapAlgEquiv σ zO := by
      apply RingOfIntegers.ext
      rfl
    have hmodZ : RingOfIntegers.mapAlgEquiv σ zO - zO ∈ P := by
      rw [← hactZ]
      have heq : σ • zO - zO = (σ • zO - zO ^ p) + (zO ^ p - zO) := by ring
      rw [heq]
      exact P.add_mem hFrobZ (by rw [hpowUnity hzO]; simp)
    have hσOroot : (RingOfIntegers.mapAlgEquiv σ zO) ^ q = 1 := by
      apply RingOfIntegers.ext
      change (σ (zO : K)) ^ q = 1
      have hzField : (zO : K) ^ q = 1 := hz
      calc
        (σ (zO : K)) ^ q = σ ((zO : K) ^ q) := (map_pow σ (zO : K) q).symm
        _ = σ 1 := by rw [hzField]
        _ = 1 := map_one σ
    have hrootEq := eq_of_pow_eq_mod_prime P hq.pos hqNotP h1NotP hσOroot hzO hmodZ
    have hcoe : (RingOfIntegers.mapAlgEquiv σ zO : K) = (zO : K) :=
      RingOfIntegers.ext_iff.mp hrootEq
    change σ (zO : K) = (zO : K) at hcoe
    change σ z = z at hcoe
    exact hcoe
  let E := cyclotomicField q
  haveI : IsCyclotomicExtension {q} ℚ E := CyclotomicField.isCyclotomicExtension q ℚ
  let ζE : E := IsCyclotomicExtension.zeta q ℚ E
  have hζEspec : IsPrimitiveRoot ζE q := IsCyclotomicExtension.zeta_spec q ℚ E
  have hζEgen : Algebra.adjoin ℚ {ζE} = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζEspec
  have hζK : (algebraMap E K ζE) ^ q = 1 := by
    calc
      (algebraMap E K ζE) ^ q = algebraMap E K (ζE ^ q) := (map_pow (algebraMap E K) ζE q).symm
      _ = 1 := by rw [hζEspec.pow_eq_one]; simp
  let iE : E →ₐ[ℚ] K := IsScalarTower.toAlgHom ℚ E K
  have hEhom : (σ.toAlgHom).comp iE = iE := by
    apply AlgHom.ext_of_adjoin_eq_top hζEgen
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    change σ (algebraMap E K ζE) = algebraMap E K ζE
    exact hσFixUnity hζK
  let σE : K →ₐ[E] K := {
    toFun := σ
    map_zero' := map_zero σ
    map_one' := map_one σ
    map_mul' := map_mul σ
    map_add' := map_add σ
    commutes' x := by
      have hx := congrArg (fun f : E →ₐ[ℚ] K => f x) hEhom
      change σ (algebraMap E K x) = algebraMap E K x
      exact hx
  }
  letI : Polynomial.IsSplittingField E K (kummerPolynomial a q) :=
    Polynomial.IsSplittingField.splittingField (kummerPolynomial a q)
  have hKgen : Algebra.adjoin E
      ((kummerPolynomial a q).rootSet K : Set K) = ⊤ :=
    Polynomial.IsSplittingField.adjoin_rootSet K (kummerPolynomial a q)
  have hσEid : σE = AlgHom.id E K := by
    apply AlgHom.ext_of_adjoin_eq_top hKgen
    intro x hx
    have hx' : Polynomial.aeval x (kummerPolynomial a q) = 0 :=
      (Polynomial.mem_rootSet'.mp hx).2
    have hxroot : x ^ q = (a : K) := by
      exact sub_eq_zero.mp (by simpa [kummerPolynomial] using hx')
    change σ x = x
    exact hσFixRoot hxroot
  have hσone : σ = 1 := by
    ext x
    have hx := congrArg (fun f : K →ₐ[E] K => f x) hσEid
    simpa [σE] using hx
  have hglobalId (τ : Gal(K/ℚ))
      (hζ : τ (algebraMap E K ζE) = algebraMap E K ζE)
      (hroots : ∀ x : K, x ∈ (kummerPolynomial a q).rootSet K → τ x = x) : τ = 1 := by
    have hτEhom : (τ.toAlgHom).comp iE = iE := by
      apply AlgHom.ext_of_adjoin_eq_top hζEgen
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      change τ (algebraMap E K ζE) = algebraMap E K ζE
      exact hζ
    let τE : K →ₐ[E] K := {
      toFun := τ
      map_zero' := map_zero τ
      map_one' := map_one τ
      map_mul' := map_mul τ
      map_add' := map_add τ
      commutes' x := by
        have hx := congrArg (fun f : E →ₐ[ℚ] K => f x) hτEhom
        change τ (algebraMap E K x) = algebraMap E K x
        exact hx
    }
    have hτEid : τE = AlgHom.id E K := by
      apply AlgHom.ext_of_adjoin_eq_top hKgen
      intro x hx
      exact hroots x hx
    ext x
    have hx := congrArg (fun f : K →ₐ[E] K => f x) hτEid
    simpa [τE] using hx
  have hτFixRoot (τ : Gal(K/ℚ)) (hτ : τ ∈ P.inertia (Gal(K/ℚ)))
      {x : K} (hx : x ^ q = (a : K)) : τ x = x := by
    have hxInt : IsIntegral ℤ x := by
      apply IsIntegral.of_pow (NeZero.pos q)
      rw [hx]
      exact isIntegral_intCast a
    let xO : 𝓞 K := ⟨x, hxInt⟩
    have hxO : xO ^ q = (a : 𝓞 K) := by
      apply RingOfIntegers.ext
      exact hx
    have hmem : τ • xO - xO ∈ P := (Ideal.mem_inertia.mp hτ) xO
    have hmod : RingOfIntegers.mapAlgEquiv τ xO - xO ∈ P := by
      rw [← hactGeneral]
      exact hmem
    exact hfixRootMod hxO hmod
  have hτFixUnity (τ : Gal(K/ℚ)) (hτ : τ ∈ P.inertia (Gal(K/ℚ)))
      {z : K} (hz : z ^ q = 1) : τ z = z := by
    have hzInt : IsIntegral ℤ z := by
      apply IsIntegral.of_pow (NeZero.pos q)
      rw [hz]
      exact isIntegral_one
    let zO : 𝓞 K := ⟨z, hzInt⟩
    have hzO : zO ^ q = 1 := by
      apply RingOfIntegers.ext
      exact hz
    have hmem : τ • zO - zO ∈ P := (Ideal.mem_inertia.mp hτ) zO
    have hmod : RingOfIntegers.mapAlgEquiv τ zO - zO ∈ P := by
      rw [← hactGeneral]
      exact hmem
    exact hfixUnityMod hzO hmod
  have hInertiaOne (τ : P.inertia (Gal(K/ℚ))) : (τ : Gal(K/ℚ)) = 1 := by
    apply hglobalId (τ : Gal(K/ℚ))
    · apply hτFixUnity (τ : Gal(K/ℚ)) τ.property
      have h := hζEspec.pow_eq_one
      simpa [map_pow] using congrArg (algebraMap E K) h
    · intro x hx
      have hx' : Polynomial.aeval x (kummerPolynomial a q) = 0 :=
        (Polynomial.mem_rootSet'.mp hx).2
      have hxroot : x ^ q = (a : K) := by
        exact sub_eq_zero.mp (by simpa [kummerPolynomial] using hx')
      exact hτFixRoot (τ : Gal(K/ℚ)) τ.property hxroot
  have hInertiaCard : Nat.card (P.inertia (Gal(K/ℚ))) = 1 := by
    letI : Subsingleton (P.inertia (Gal(K/ℚ))) := ⟨fun x y => by
      apply Subtype.ext
      rw [hInertiaOne x, hInertiaOne y]⟩
    exact Nat.card_of_subsingleton (1 : P.inertia (Gal(K/ℚ)))
  have hram : (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 := by
    rw [← Ideal.card_inertia_eq_ramificationIdxIn
      (G := Gal(K/ℚ)) (p := Ideal.span {(p : ℤ)}) (P := P)]
    exact hInertiaCard
  let R₀ := ℤ ⧸ Ideal.span {(p : ℤ)}
  let S₀ := (𝓞 K) ⧸ P
  letI : Field R₀ := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
  letI : Field S₀ := Ideal.Quotient.field P
  let eR : ZMod p ≃+* R₀ := (Int.quotientSpanNatEquivZMod p).symm
  letI : Finite R₀ := Finite.of_equiv (ZMod p) eR.toEquiv
  letI : Fintype R₀ := Fintype.ofFinite R₀
  letI : Finite S₀ := inferInstance
  letI : Fintype S₀ := Fintype.ofFinite S₀
  have hRcard : Fintype.card R₀ = p := by
    calc
      Fintype.card R₀ = Fintype.card (ZMod p) := Fintype.card_congr eR.symm.toEquiv
      _ = p := ZMod.card p
  have hFrobQ (y : S₀) : y ^ (Fintype.card R₀) = y := by
    rw [hRcard]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hmod : σ • x - x ^ p ∈ P := by
      simpa [σ, hcard] using hFrob x
    rw [hσone, one_smul] at hmod
    have heq : Ideal.Quotient.mk P x = Ideal.Quotient.mk P (x ^ p) :=
      Ideal.Quotient.eq.mpr hmod
    calc
      (Ideal.Quotient.mk P x) ^ p = Ideal.Quotient.mk P (x ^ p) := by simp
      _ = Ideal.Quotient.mk P x := heq.symm
  have hFrobId : FiniteField.frobeniusAlgEquivOfAlgebraic R₀ S₀ = 1 := by
    ext y
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    simpa using hFrobQ y
  have hdegree0 : Module.finrank R₀ S₀ = 1 := by
    rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic R₀ S₀, hFrobId, orderOf_one]
  have hdegreeP : P.inertiaDeg ℤ = 1 := by
    calc
      P.inertiaDeg ℤ = Module.finrank R₀ S₀ :=
        Ideal.inertiaDeg_eq_of_isMaximal (R := ℤ) (S := 𝓞 K)
          (p := Ideal.span {(p : ℤ)}) (q := P)
      _ = 1 := hdegree0
  have hinertia : (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg
      (G := Gal(K/ℚ)) (p := Ideal.span {(p : ℤ)}) (P := P)]
    exact hdegreeP
  exact (ext_split_criterion K p).2 ⟨hram, hinertia⟩

private theorem compositum_base_extension (a : ℤ) (q : ℕ) [NeZero q]
    [NeZero (12 * q)] (hq : q.Prime) (ha0 : a ≠ 0) :
    ∃ d : AbelianExtensionData (heckeBaseField q) (compositumField a q),
      Module.finrank (heckeBaseField q) (compositumField a q) ≤ q ∧
      ∀ σ : Gal(compositumField a q / heckeBaseField q), σ ^ q = 1 := by
  let F := heckeBaseField q
  let L := compositumField a q
  let g : Polynomial F := Polynomial.X ^ q - Polynomial.C (a : F)
  let n : ℕ := 12 * q
  haveI : IsCyclotomicExtension {n} ℚ F := CyclotomicField.isCyclotomicExtension n ℚ
  let ζn : F := IsCyclotomicExtension.zeta n ℚ F
  have hζn : IsPrimitiveRoot ζn n := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ : IsPrimitiveRoot (ζn ^ 12) q := by
    have hn : 0 < n := by
      dsimp [n]
      exact Nat.mul_pos (by decide) (NeZero.pos q)
    exact IsPrimitiveRoot.pow hn hζn (by dsimp [n])
  have hζRoots : (primitiveRoots q F).Nonempty :=
    ⟨ζn ^ 12, (mem_primitiveRoots (NeZero.pos q)).2 hζ⟩
  letI : Polynomial.IsSplittingField F L g :=
    Polynomial.IsSplittingField.splittingField g
  have hSep : g.Separable := by
    dsimp [g]
    exact Polynomial.separable_X_pow_sub_C (n := q) (a : F)
      (by exact_mod_cast NeZero.ne q) (by exact_mod_cast ha0)
  have hG : IsGalois F L := IsGalois.of_separable_splitting_field hSep
  have hBranch :
      IsAbelianGalois F L ∧ Module.finrank F L ≤ q ∧
        (∀ σ : Gal(L/F), σ ^ q = 1) := by
    classical
    by_cases hr : ∃ b : F, b ^ q = (a : F)
    · obtain ⟨b, hb⟩ := hr
      have hsplitF : g.Splits := by
        exact X_pow_sub_C_splits_of_isPrimitiveRoot hζ hb
      letI : Polynomial.IsSplittingField F F g := by
        refine ⟨?_, ?_⟩
        · simpa using hsplitF
        · apply top_unique
          intro x hx
          exact (Algebra.adjoin F (g.rootSet F)).algebraMap_mem x
      let eL : L ≃ₐ[F] g.SplittingField := Polynomial.IsSplittingField.algEquiv L g
      let eF : F ≃ₐ[F] g.SplittingField := Polynomial.IsSplittingField.algEquiv F g
      let e : L ≃ₐ[F] F := eL.trans eF.symm
      have hfin : Module.finrank F L = 1 := by
        calc
          Module.finrank F L = Module.finrank F F := e.toLinearEquiv.finrank_eq
          _ = 1 := Module.finrank_self F
      have hcard : Nat.card (Gal(L/F)) = 1 := by
        rw [IsGalois.card_aut_eq_finrank F L, hfin]
      letI : Subsingleton (Gal(L/F)) := (Nat.card_eq_one_iff_unique.mp hcard).1
      letI : IsCyclic (Gal(L/F)) := inferInstance
      refine ⟨IsAbelianGalois.of_isCyclic F L, ?_, ?_⟩
      · rw [hfin]
        exact le_trans (by decide : 1 ≤ 2) hq.two_le
      · intro σ
        exact Subsingleton.elim _ _
    · have hno : ∀ b : F, b ^ q ≠ (a : F) := by
        intro b hb
        exact hr ⟨b, hb⟩
      have hirr : Irreducible g := by
        exact ext_kummer_irreducible hq hno
      letI : IsGalois F L := hG
      letI : IsCyclic (Gal(L/F)) :=
        isCyclic_of_isSplittingField_X_pow_sub_C hζRoots hirr L
      have hfin : Module.finrank F L = q :=
        finrank_of_isSplittingField_X_pow_sub_C hζRoots hirr L
      have hcard : Nat.card (Gal(L/F)) = q := by
        rw [IsGalois.card_aut_eq_finrank F L, hfin]
      refine ⟨IsAbelianGalois.of_isCyclic F L, le_of_eq hfin, ?_⟩
      intro σ
      have horder : orderOf σ ∣ Nat.card (Gal(L/F)) := orderOf_dvd_natCard σ
      obtain ⟨k, hk⟩ := horder
      have horderq : orderOf σ ∣ q := ⟨k, hcard.symm.trans hk⟩
      exact (orderOf_dvd_iff_pow_eq_one).mp horderq
  refine ⟨⟨inferInstance, hBranch.1⟩, hBranch.2.1, hBranch.2.2⟩

set_option maxHeartbeats 1000000 in
/-- **`sp:compositum`**, `07-splitting.tex:70-77`. The chosen top field represents `K_qF_q`.
Its extension over `F_q` is cyclic of degree dividing `q`; over `K_q` it is abelian of exponent
two. All three fields are totally imaginary. -/
theorem sp_compositum (a : ℤ) (ha : 1 < |a|) (q : ℕ) [NeZero q] [NeZero (12 * q)] (hq : q.Prime)
    (hq5 : 5 ≤ q) :
    ∃ dK : AbelianExtensionData (kummerField a q) (compositumField a q),
    ∃ dF : AbelianExtensionData (heckeBaseField q) (compositumField a q),
      letI : AbelianExtensionData (kummerField a q) (compositumField a q) := dK
      letI : AbelianExtensionData (heckeBaseField q) (compositumField a q) := dF
      IsTotallyComplex (kummerField a q) ∧
      IsTotallyComplex (heckeBaseField q) ∧
      IsTotallyComplex (compositumField a q) ∧
      Module.finrank (heckeBaseField q) (compositumField a q) ≤ q ∧
      (∀ σ : Gal(compositumField a q / heckeBaseField q), σ ^ q = 1) ∧
      (∀ σ : Gal(compositumField a q / kummerField a q), σ ^ 2 = 1) ∧
      Nat.card (Gal(compositumField a q / kummerField a q)) ≤ 4 := by
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    simp at ha
  obtain ⟨dF, hFdegree, hFpow⟩ := compositum_base_extension a q hq ha0
  let E := cyclotomicField q
  let F := heckeBaseField q
  let K := kummerField a q
  let L := compositumField a q
  haveI : IsCyclotomicExtension {q} ℚ E := CyclotomicField.isCyclotomicExtension q ℚ
  have hEcomplex : IsTotallyComplex E :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := q) E (by omega)
  have hTC_K : IsTotallyComplex K := isTotallyComplex_of_algebra (F := E) K
  haveI : IsCyclotomicExtension {12 * q} ℚ F :=
    CyclotomicField.isCyclotomicExtension (12 * q) ℚ
  have hTC_F : IsTotallyComplex F :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := 12 * q) F (by omega)
  haveI : AbelianExtensionData F L := dF
  have hTC_L : IsTotallyComplex L := isTotallyComplex_of_algebra (F := F) L
  let n : ℕ := 12 * q
  let ζn : F := IsCyclotomicExtension.zeta n ℚ F
  have hζn : IsPrimitiveRoot ζn n := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζqF : IsPrimitiveRoot (ζn ^ 12) q := by
    have hn : 0 < n := by dsimp [n]; exact Nat.mul_pos (by decide) (NeZero.pos q)
    exact IsPrimitiveRoot.pow hn hζn (by dsimp [n])
  let Cq : IntermediateField ℚ F := IntermediateField.adjoin ℚ {ζn ^ 12}
  haveI : IsCyclotomicExtension {q} ℚ Cq :=
    hζqF.intermediateField_adjoin_isCyclotomicExtension ℚ
  letI : Polynomial.IsSplittingField ℚ E (Polynomial.cyclotomic q ℚ) :=
    Polynomial.IsSplittingField.splittingField (Polynomial.cyclotomic q ℚ)
  let eECq : E ≃ₐ[ℚ] Cq := IsCyclotomicExtension.algEquiv {q} ℚ E Cq
  let eEF : E →ₐ[ℚ] F := Cq.val.comp eECq.toAlgHom
  letI : Algebra E F := eEF.toRingHom.toAlgebra
  have hEFmap : algebraMap E F = (eEF : E →+* F) :=
    RingHom.algebraMap_toAlgebra eEF.toRingHom
  letI : IsScalarTower ℚ E F := IsScalarTower.of_algebraMap_eq' eEF.comp_algebraMap.symm
  letI : IsScalarTower ℚ F L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap ℚ L x = algebraMap F L (algebraMap ℚ F x) :=
        IsScalarTower.algebraMap_apply ℚ F L x
      _ = algebraMap F L (algebraMap E F (algebraMap ℚ E x)) := by
        rw [IsScalarTower.algebraMap_apply ℚ E F]
      _ = algebraMap E L (algebraMap ℚ E x) :=
        (IsScalarTower.algebraMap_apply E F L _).symm
  let gE : Polynomial E := kummerPolynomial a q
  let gF : Polynomial F := Polynomial.X ^ q - Polynomial.C (a : F)
  have hEFcast : algebraMap E F (a : E) = (a : F) := map_intCast eEF a
  letI : Polynomial.IsSplittingField E K gE := Polynomial.IsSplittingField.splittingField gE
  letI : Polynomial.IsSplittingField F L gF := Polynomial.IsSplittingField.splittingField gF
  have hmap : gE.map (algebraMap E L) = gF.map (algebraMap F L) := by
    simp only [gE, gF, kummerPolynomial, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    congr 1
    apply congrArg Polynomial.C
    calc
      algebraMap E L (a : E) = algebraMap F L (algebraMap E F (a : E)) :=
        IsScalarTower.algebraMap_apply E F L _
      _ = algebraMap F L (a : F) := by rw [hEFcast]
  have hsplitgL : (gE.map (algebraMap E L)).Splits := by
    rw [hmap]
    exact Polynomial.IsSplittingField.splits L gF
  let eKL : K →ₐ[E] L := Polynomial.IsSplittingField.lift K gE hsplitgL
  letI : Algebra K L := eKL.toRingHom.toAlgebra
  letI : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq' eKL.comp_algebraMap.symm
  let fQ : Polynomial ℚ := Polynomial.cyclotomic n ℚ
  let gQ : Polynomial ℚ := Polynomial.X ^ q - Polynomial.C (a : ℚ)
  have hfQne : fQ ≠ 0 :=
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)).ne_zero
  have hgQne : gQ ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (NeZero.pos q) (a : ℚ)
  have hmapgQ : gQ.map (algebraMap ℚ F) = gF := by
    dsimp [gQ, gF]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    congr 1
  letI : Polynomial.IsSplittingField ℚ F fQ :=
    Polynomial.IsSplittingField.splittingField fQ
  letI : Polynomial.IsSplittingField F L (gQ.map (algebraMap ℚ F)) := by
    rw [hmapgQ]
    exact Polynomial.IsSplittingField.splittingField gF
  letI : Polynomial.IsSplittingField ℚ L (fQ * gQ) :=
    Polynomial.IsSplittingField.mul (F := ℚ) (K := F) (L := L) fQ gQ hfQne hgQne
  letI : Normal ℚ L := Normal.of_isSplittingField (fQ * gQ)
  letI : Algebra.IsSeparable ℚ L := by infer_instance
  have hGaloisL : IsGalois ℚ L := ⟨⟩
  letI : IsScalarTower ℚ K L := IsScalarTower.of_algHom (eKL.restrictScalars ℚ)
  let eFL : F →ₐ[E] L := IsScalarTower.toAlgHom E F L
  let eFLQ : F →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ F L
  let eKLQ : K →ₐ[ℚ] L := eKL.restrictScalars ℚ
  let KQ : IntermediateField ℚ L := eKLQ.fieldRange
  let FQ : IntermediateField ℚ L := eFLQ.fieldRange
  have hmapgE : gQ.map (algebraMap ℚ E) = gE := by
    simp [gQ, gE, kummerPolynomial]
  have hrootG : gQ.rootSet L = gE.rootSet L := by
    calc
      gQ.rootSet L = (gQ.map (algebraMap ℚ E)).rootSet L :=
        (Polynomial.rootSet_map (T := E) (R := L) gQ).symm
      _ = gE.rootSet L := by rw [hmapgE]
  have hFadjoin : Algebra.adjoin ℚ (fQ.rootSet L) = eFLQ.range :=
    Polynomial.IsSplittingField.adjoin_rootSet_eq_range (K := ℚ) (L := F) fQ eFLQ
  have hKadjoin : Algebra.adjoin E (gE.rootSet L) = eKL.range :=
    Polynomial.IsSplittingField.adjoin_rootSet_eq_range (K := E) (L := K) gE eKL
  have hFroot : ∀ x, x ∈ fQ.rootSet L → x ∈ FQ := by
    intro x hx
    have hxAdj : x ∈ Algebra.adjoin ℚ (fQ.rootSet L) := Algebra.subset_adjoin hx
    have hxRange : x ∈ eFLQ.range := by rw [← hFadjoin]; exact hxAdj
    rcases (AlgHom.mem_range eFLQ).mp hxRange with ⟨y, hy⟩
    change ∃ y : F, eFLQ y = x
    exact ⟨y, hy⟩
  have hKroot : ∀ x, x ∈ gQ.rootSet L → x ∈ KQ := by
    intro x hx
    have hxG : x ∈ gE.rootSet L := by rw [← hrootG]; exact hx
    have hxAdj : x ∈ Algebra.adjoin E (gE.rootSet L) := Algebra.subset_adjoin hxG
    have hxRange : x ∈ eKL.range := by rw [← hKadjoin]; exact hxAdj
    rcases (AlgHom.mem_range eKL).mp hxRange with ⟨y, hy⟩
    change ∃ y : K, eKLQ y = x
    exact ⟨y, by simpa [eKLQ] using hy⟩
  have hrootProd : (fQ * gQ).rootSet L = fQ.rootSet L ∪ gQ.rootSet L := by
    classical
    rw [Polynomial.rootSet, Polynomial.aroots_mul (mul_ne_zero hfQne hgQne),
      Multiset.toFinset_add, Finset.coe_union, ← Polynomial.rootSet, ← Polynomial.rootSet]
  have hrootSubset : (fQ * gQ).rootSet L ⊆ (KQ ⊔ FQ : IntermediateField ℚ L) := by
    intro x hx
    rw [hrootProd] at hx
    rcases hx with hxF | hxK
    · exact mem_of_le_of_mem le_sup_right (hFroot x hxF)
    · exact mem_of_le_of_mem le_sup_left (hKroot x hxK)
  have hrootSubalgebra : (fQ * gQ).rootSet L ⊆ (KQ ⊔ FQ).toSubalgebra := by
    intro x hx
    exact hrootSubset hx
  have hAdjoinLe : Algebra.adjoin ℚ ((fQ * gQ).rootSet L) ≤ (KQ ⊔ FQ).toSubalgebra :=
    Algebra.adjoin_le_iff.mpr hrootSubalgebra
  have hAdjoinTop : Algebra.adjoin ℚ ((fQ * gQ).rootSet L) = ⊤ :=
    Polynomial.IsSplittingField.adjoin_rootSet L (fQ * gQ)
  have hsupQ : KQ ⊔ FQ = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    apply top_unique
    intro x hx
    have hxAdj : x ∈ Algebra.adjoin ℚ ((fQ * gQ).rootSet L) := by
      rw [hAdjoinTop]
      exact hx
    exact hAdjoinLe hxAdj
  let ζnL : L := algebraMap F L ζn
  let ζqL : L := algebraMap F L (ζn ^ 12)
  let ζ12L : L := algebraMap F L (ζn ^ q)
  have hζnL : IsPrimitiveRoot ζnL n :=
    hζn.map_of_injective (FaithfulSMul.algebraMap_injective F L)
  have hζqL : IsPrimitiveRoot ζqL q :=
    hζqF.map_of_injective (FaithfulSMul.algebraMap_injective F L)
  have hζ12F : IsPrimitiveRoot (ζn ^ q) 12 := by
    have hn : 0 < n := by dsimp [n]; exact Nat.mul_pos (by decide) (NeZero.pos q)
    exact IsPrimitiveRoot.pow hn hζn (by dsimp [n]; ring)
  have hζ12L : IsPrimitiveRoot ζ12L 12 :=
    hζ12F.map_of_injective (FaithfulSMul.algebraMap_injective F L)
  let C12 : IntermediateField ℚ L := IntermediateField.adjoin ℚ {ζ12L}
  haveI : IsCyclotomicExtension {12} ℚ C12 :=
    hζ12L.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hζ12mem : ζ12L ∈ C12 := by
    change ζ12L ∈ IntermediateField.adjoin ℚ {ζ12L}
    exact IntermediateField.subset_adjoin ℚ {ζ12L} (Set.mem_singleton_iff.mpr rfl)
  have hζqCq : (ζn ^ 12) ∈ Cq := by
    change (ζn ^ 12) ∈ IntermediateField.adjoin ℚ {ζn ^ 12}
    exact IntermediateField.subset_adjoin ℚ {ζn ^ 12} (Set.mem_singleton_iff.mpr rfl)
  let ζqCq : Cq := ⟨ζn ^ 12, hζqCq⟩
  let xE : E := eECq.symm ζqCq
  have hxEF : eEF xE = ζn ^ 12 := by
    dsimp [eEF, xE]
    rw [AlgEquiv.apply_symm_apply]
  have hxEF' : algebraMap E F xE = ζn ^ 12 := by
    rw [hEFmap]
    exact hxEF
  have hζqK : ζqL ∈ KQ := by
    change ∃ y : K, eKLQ y = ζqL
    refine ⟨algebraMap E K xE, ?_⟩
    calc
      eKLQ (algebraMap E K xE) = eKL (algebraMap E K xE) := rfl
      _ = algebraMap E L xE := by simp
      _ = algebraMap F L (algebraMap E F xE) :=
        IsScalarTower.algebraMap_apply E F L xE
      _ = algebraMap F L (ζn ^ 12) := by rw [hxEF']
  have hgenF : Algebra.adjoin ℚ {ζn} = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζn
  have hFQgen : Algebra.adjoin ℚ {ζnL} = FQ.toSubalgebra := by
    calc
      Algebra.adjoin ℚ {ζnL} = (Algebra.adjoin ℚ {ζn}).map eFLQ := by
        rw [AlgHom.map_adjoin_singleton]
        rfl
      _ = (⊤ : Subalgebra ℚ F).map eFLQ := by rw [hgenF]
      _ = eFLQ.range := Algebra.map_top eFLQ
      _ = FQ.toSubalgebra := by simp [FQ]
  have hFQgenField : FQ = IntermediateField.adjoin ℚ {ζnL} := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_toSubalgebra]
    exact hFQgen.symm
  have hcop : Nat.Coprime 12 q := by
    apply Nat.Coprime.symm
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    rcases hq.dvd_mul.mp (show q ∣ 3 * 4 by simpa using hd) with h3 | h4
    · have hqle : q ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
    · have hqle : q ≤ 4 := Nat.le_of_dvd (by decide : 0 < 4) h4
      omega
  have hLcm : Nat.lcm 12 q = n := by
    dsimp [n]
    exact Nat.Coprime.lcm_eq_mul hcop
  have hζnL_lcm : IsPrimitiveRoot ζnL (Nat.lcm 12 q) := by
    simpa [hLcm] using hζnL
  have hpair : Algebra.adjoin ℚ {ζ12L, ζqL} = Algebra.adjoin ℚ {ζnL} :=
    IsPrimitiveRoot.adjoin_pair_eq ℚ hζ12L hζqL (by norm_num) (NeZero.ne q) hζnL_lcm
  have hpairLe : Algebra.adjoin ℚ {ζ12L, ζqL} ≤ (KQ ⊔ C12).toSubalgebra := by
    apply Algebra.adjoin_le_iff.mpr
    exact Set.pair_subset_iff.mpr
      ⟨mem_of_le_of_mem le_sup_right hζ12mem, mem_of_le_of_mem le_sup_left hζqK⟩
  have hζnSup : ζnL ∈ KQ ⊔ C12 := by
    have hζnAdj : ζnL ∈ Algebra.adjoin ℚ {ζ12L, ζqL} := by
      rw [hpair]
      exact Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)
    exact hpairLe hζnAdj
  have hFQle : FQ ≤ KQ ⊔ C12 := by
    change FQ.toSubalgebra ≤ (KQ ⊔ C12).toSubalgebra
    rw [← hFQgen]
    apply Algebra.adjoin_le_iff.mpr
    exact Set.singleton_subset_iff.mpr hζnSup
  have hsupKC : KQ ⊔ C12 = ⊤ := by
    apply top_unique
    rw [← hsupQ]
    exact sup_le le_sup_left hFQle
  haveI : IsGalois ℚ C12 := IsCyclotomicExtension.isGalois {12} ℚ C12
  have hC12pow : ∀ τ : Gal(C12/ℚ), τ ^ 2 = 1 := by
    have hunitSq : ∀ u : (ZMod 12)ˣ, u ^ 2 = 1 := by decide
    intro τ
    apply (IsCyclotomicExtension.Rat.galEquivZMod 12 C12).injective
    simpa using hunitSq (IsCyclotomicExtension.Rat.galEquivZMod 12 C12 τ)
  have hC12comm : ∀ σ τ : Gal(C12/ℚ), σ * τ = τ * σ := by
    intro σ τ
    apply (IsCyclotomicExtension.Rat.galEquivZMod 12 C12).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hC12card : Nat.card (Gal(C12/ℚ)) = 4 := by
    rw [IsGalois.card_aut_eq_finrank ℚ C12,
      IsCyclotomicExtension.Rat.finrank 12 C12]
    have htotient : Nat.totient 12 = 4 := by
      rw [← ZMod.card_units_eq_totient 12]
      decide
    exact htotient
  let resQ : Gal(L/K) →* Gal(L/ℚ) :=
    MulSemiringAction.toAlgAut Gal(L/K) ℚ L
  let res12 : Gal(L/K) →* Gal(C12/ℚ) :=
    (AlgEquiv.restrictNormalHom C12).comp resQ
  have hfixKQ (σ : Gal(L/K)) {x : L} (hx : x ∈ KQ) : resQ σ x = x := by
    change ∃ y : K, eKLQ y = x at hx
    rcases hx with ⟨y, hy⟩
    rw [← hy]
    change σ (eKL y) = eKL y
    exact σ.commutes y
  have hgenField : IntermediateField.adjoin ℚ ((KQ : Set L) ∪ C12) = ⊤ := by
    apply top_unique
    rw [← hsupKC]
    apply sup_le
    · intro x hx
      exact IntermediateField.subset_adjoin ℚ ((KQ : Set L) ∪ C12) (Or.inl hx)
    · intro x hx
      exact IntermediateField.subset_adjoin ℚ ((KQ : Set L) ∪ C12) (Or.inr hx)
  have hgen : Algebra.adjoin ℚ ((KQ : Set L) ∪ C12) = ⊤ := by
    have h := congrArg (fun F : IntermediateField ℚ L => F.toSubalgebra) hgenField
    simpa [IntermediateField.adjoin_toSubalgebra] using h
  have hresinj : Function.Injective res12 := by
    intro σ τ hστ
    have hEqOn : Set.EqOn (resQ σ) (resQ τ) ((KQ : Set L) ∪ C12) := by
      intro x hx
      rcases hx with hxK | hxC
      · exact (hfixKQ σ hxK).trans (hfixKQ τ hxK).symm
      · have h := congrArg (fun f : Gal(C12/ℚ) => (f ⟨x, hxC⟩ : L)) hστ
        simpa [res12, AlgEquiv.restrictNormalHom_apply] using h
    have hAlg : (resQ σ : L →ₐ[ℚ] L) = (resQ τ : L →ₐ[ℚ] L) :=
      AlgHom.ext_of_adjoin_eq_top hgen hEqOn
    have hσQ : resQ σ = resQ τ := by
      apply AlgEquiv.ext
      intro x
      exact congrArg (fun f : L →ₐ[ℚ] L => f x) hAlg
    exact AlgEquiv.restrictScalars_injective ℚ hσQ
  have hKpow : ∀ σ : Gal(L/K), σ ^ 2 = 1 := by
    intro σ
    have hres : res12 (σ ^ 2) = res12 1 := by
      rw [map_pow]
      simpa using hC12pow (res12 σ)
    exact hresinj hres
  have hKcard : Nat.card (Gal(L/K)) ≤ 4 := by
    calc
      Nat.card (Gal(L/K)) ≤ Nat.card (Gal(C12/ℚ)) :=
        Nat.card_le_card_of_injective res12 hresinj
      _ = 4 := hC12card
  letI : IsGalois ℚ L := hGaloisL
  let hGaloisKL : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  have hKcomm : ∀ σ τ : Gal(L/K), σ * τ = τ * σ := by
    intro σ τ
    apply hresinj
    calc
      res12 (σ * τ) = res12 σ * res12 τ := res12.map_mul σ τ
      _ = res12 τ * res12 σ := hC12comm (res12 σ) (res12 τ)
      _ = res12 (τ * σ) := (res12.map_mul τ σ).symm
  letI : IsGalois K L := hGaloisKL
  letI : IsMulCommutative Gal(L/K) := IsMulCommutative.of_comm hKcomm
  let hKAb : IsAbelianGalois K L := ⟨⟩
  let dK : AbelianExtensionData K L := ⟨inferInstance, hKAb⟩
  refine ⟨dK, dF, hTC_K, hTC_F, hTC_L, hFdegree, hFpow, hKpow, hKcard⟩

end ArtinPrimitiveRoots.Splitting

end
