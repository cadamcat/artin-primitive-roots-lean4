import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Rational coordinates on the completions above a rational prime

For a rational diagonalization `T` of `Tr(a x²)` we build an additive homeomorphism
`Φ : (Fin n → ℚ_[p]) ≃ₜ+ Π_{w | p} F_w`, `y ↦ (Σ yᵢ bᵢ)_w`, using the completion tensor
decomposition, and show that the product of the local additive characters of `a·x²` becomes the
product of the rational characters of `cᵢ yᵢ²`. The local characters are identified with the
trace characters by the lead's `finite_trace_character_comparison`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open scoped TensorProduct

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.weil_trace_opus

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.Proofs.a1_bdata_sol
  ArtinPrimitiveRoots.Proofs.a1_weil_sol

/-- The generic base-field algebra on an absolute-value completion (the instance used by the
completion tensor decomposition; for `K = ℚ` typeclass search would find a different one). -/
@[reducible] def baseCompletionAlgebra {K : Type*} [Field K] (vK : AbsoluteValue K ℝ) :
    Algebra K vK.Completion := inferInstance

scoped instance primesFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

scoped instance extFintype (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fintype (AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) :=
  completionTensorDecomposition_extensionFintype _ (RayClass.adicAbv_isNontrivial v)

/-- An additive map scaling norms by a positive power is continuous. -/
theorem continuous_of_norm_rpow {E G : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup G] (f : E →+ G) (e : ℝ) (he : 0 < e)
    (hf : ∀ x, ‖f x‖ = ‖x‖ ^ e) : Continuous f := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε ^ (1 / e), Real.rpow_pos_of_pos hε _, fun a hab => ?_⟩
  rw [dist_eq_norm, ← map_sub, hf]
  rw [dist_eq_norm] at hab
  calc ‖a - b‖ ^ e < (ε ^ (1 / e)) ^ e := Real.rpow_lt_rpow (norm_nonneg _) hab he
    _ = ε := by rw [← Real.rpow_mul hε.le, one_div_mul_cancel he.ne', Real.rpow_one]

theorem norm_symm_of_norm_rpow {E G : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup G] (f : E ≃+ G) (e : ℝ) (he : 0 < e)
    (hf : ∀ x, ‖f x‖ = ‖x‖ ^ e) (y : G) : ‖f.symm y‖ = ‖y‖ ^ (1 / e) := by
  have h := hf (f.symm y)
  rw [AddEquiv.apply_symm_apply] at h
  rw [h, one_div, Real.rpow_rpow_inv (norm_nonneg _) he.ne']

/-- An additive equivalence scaling norms by a positive power is a homeomorphism. -/
def continuousAddEquivOfNormRpow {E G : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup G] (f : E ≃+ G) (e : ℝ) (he : 0 < e)
    (hf : ∀ x, ‖f x‖ = ‖x‖ ^ e) : E ≃ₜ+ G where
  toAddEquiv := f
  continuous_toFun := continuous_of_norm_rpow f.toAddMonoidHom e he hf
  continuous_invFun := continuous_of_norm_rpow f.symm.toAddMonoidHom (1 / e)
    (one_div_pos.mpr he) (norm_symm_of_norm_rpow f e he hf)

variable {F : Type} [Field F] [NumberField F]

/-- The local factor comparison as an additive homeomorphism. -/
def kappaEquiv (v : HeightOneSpectrum (𝓞 ℚ))
    (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) :
    w.1.Completion ≃ₜ+ (finitePlaceExtensionCentre (K := ℚ) (L := F) v w).adicCompletion F :=
  continuousAddEquivOfNormRpow
    (finitePlaceExtensionAdicCompletionRingEquiv (K := ℚ) (L := F) v w).toAddEquiv
    (finitePlaceExtensionExponent (K := ℚ) (L := F) v w)
    (finitePlaceExtensionExponent_pos (K := ℚ) (L := F) v w)
    (finitePlaceExtensionAdicCompletionRingEquiv_norm (K := ℚ) (L := F) v w)

/-- The comparison of the two models of `ℚ_p` (absolute-value and adic completion). -/
def baseCompletionEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion ≃ₜ+ v.adicCompletion ℚ :=
  continuousAddEquivOfNormRpow (relativeFinitePlaceCompletionRingEquiv v).toAddEquiv 1 one_pos
    (fun x => by
      rw [Real.rpow_one]
      exact relativeFinitePlaceCompletionRingEquiv_norm v x)

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

/-- Mathlib's comparison of the adic completion of `ℚ` with `ℚ_[p]`. -/
def padicHomeo (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletion ℚ ≃ₜ+ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] where
  toAddEquiv := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.toAddEquiv
  continuous_toFun := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous_toFun
  continuous_invFun := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous_invFun

/-- `ℚ_[p]` and the absolute-value completion of `ℚ` at `p`. -/
def padicBaseEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ≃ₜ+
      (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion :=
  (padicHomeo v).symm.trans (baseCompletionEquiv v).symm

/-- Polarize the rational diagonalization: the trace pairing of basis vectors is diagonal. -/
theorem trace_diag_pair {a : Fˣ} (T : QuadraticTraceDiagonal a)
    (i j : Fin (Module.finrank ℚ F)) :
    Algebra.trace ℚ F ((a : F) * (T.basis i * T.basis j)) =
      if i = j then (T.coeff i : ℚ) else 0 := by
  classical
  have hrepr (k l : Fin (Module.finrank ℚ F)) :
      T.basis.repr (T.basis k) l = if k = l then 1 else 0 := by
    rw [T.basis.repr_self, Finsupp.single_apply]
  have hsq (k : Fin (Module.finrank ℚ F)) :
      Algebra.trace ℚ F ((a : F) * T.basis k ^ 2) = T.coeff k := by
    rw [T.diagonal]
    have hpt (l : Fin (Module.finrank ℚ F)) :
        (T.coeff l : ℚ) * (T.basis.repr (T.basis k) l) ^ 2 =
          if k = l then (T.coeff l : ℚ) else 0 := by
      rw [hrepr]
      by_cases h : k = l <;> simp [h]
    rw [Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_ite_eq]
    simp
  have hexp : Algebra.trace ℚ F ((a : F) * (T.basis i + T.basis j) ^ 2) =
      Algebra.trace ℚ F ((a : F) * T.basis i ^ 2) + Algebra.trace ℚ F ((a : F) * T.basis j ^ 2) +
        2 * Algebra.trace ℚ F ((a : F) * (T.basis i * T.basis j)) := by
    have : (a : F) * (T.basis i + T.basis j) ^ 2 =
        (a : F) * T.basis i ^ 2 + (a : F) * T.basis j ^ 2 +
          (2 : ℚ) • ((a : F) * (T.basis i * T.basis j)) := by
      rw [Algebra.smul_def, map_ofNat]
      ring
    rw [this, map_add, map_add, LinearMap.map_smul, smul_eq_mul]
  have hpair : Algebra.trace ℚ F ((a : F) * (T.basis i + T.basis j) ^ 2) =
      (T.coeff i : ℚ) + T.coeff j + if i = j then 2 * (T.coeff i : ℚ) else 0 := by
    rw [T.diagonal]
    have hpt (l : Fin (Module.finrank ℚ F)) :
        (T.coeff l : ℚ) * (T.basis.repr (T.basis i + T.basis j) l) ^ 2 =
          (if i = l then (T.coeff l : ℚ) else 0) + (if j = l then (T.coeff l : ℚ) else 0) +
            (if i = l then (if j = l then 2 * (T.coeff l : ℚ) else 0) else 0) := by
      rw [map_add, Finsupp.add_apply, hrepr, hrepr]
      by_cases hi : i = l <;> by_cases hj : j = l <;> simp [hi, hj] <;> ring
    rw [Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  rw [hsq, hsq, hpair] at hexp
  by_cases h : i = j
  · subst h
    simp only [if_true] at hexp ⊢
    linarith
  · simp only [h, if_false] at hexp ⊢
    linarith

theorem addChar_map_sum {A M ι : Type*} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M)
    (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, ψ.map_add_eq_mul, ih]

/-- Componentwise additive homeomorphisms of finite products. -/
def piCongrRightC {ι : Type*} {G H : ι → Type*} [∀ i, Add (G i)] [∀ i, Add (H i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, TopologicalSpace (H i)] (e : ∀ i, G i ≃ₜ+ H i) :
    (∀ i, G i) ≃ₜ+ (∀ i, H i) where
  toAddEquiv := AddEquiv.piCongrRight (fun i => (e i).toAddEquiv)
  continuous_toFun := continuous_pi fun i => (e i).continuous_toFun.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (e i).continuous_invFun.comp (continuous_apply i)

/-- Coordinates of `Π_w F_w` (absolute-value completions) in a rational basis of `F`. -/
def basisCoordinates (v : HeightOneSpectrum (𝓞 ℚ))
    (b : Module.Basis (Fin (Module.finrank ℚ F)) ℚ F) :
    (Fin (Module.finrank ℚ F) → (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion) ≃ₜ+
      ((w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) →
        w.1.Completion) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv ℚ v
  have hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  letI : Algebra ℚ vK.Completion := baseCompletionAlgebra vK
  letI : ∀ w : AbsoluteValueExtension vK F, Algebra vK.Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField vK hvK
  letI : ∀ w : AbsoluteValueExtension vK F, NormedAlgebra vK.Completion w.1.Completion :=
    fun w => absoluteValueExtension_completionNormedAlgebra vK w
  let dec := completionTensorDecomposition_left (K := ℚ) (L := F) vK hvK
  let B := (Algebra.TensorProduct.basis vK.Completion b).map dec.toLinearEquiv
  let e := B.equivFun.symm.toContinuousLinearEquiv
  exact
    { toAddEquiv := e.toLinearEquiv.toAddEquiv
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }

theorem basisCoordinates_apply (v : HeightOneSpectrum (𝓞 ℚ))
    (b : Module.Basis (Fin (Module.finrank ℚ F)) ℚ F)
    (y : Fin (Module.finrank ℚ F) → (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion)
    (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) :
    basisCoordinates v b y w =
      ∑ i, AbsoluteValue.completionMap _ w.1 w.2 (y i) * AbsoluteValue.toCompletion w.1 (b i) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv ℚ v
  have hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  letI : Algebra ℚ vK.Completion := baseCompletionAlgebra vK
  letI : ∀ w : AbsoluteValueExtension vK F, Algebra vK.Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra vK w.1 w.2
  change ((Algebra.TensorProduct.basis vK.Completion b).map
    (completionTensorDecomposition_left (K := ℚ) (L := F) vK hvK).toLinearEquiv).equivFun.symm
      y w = _
  rw [Module.Basis.equivFun_symm_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.smul_apply, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  change y i • completionTensorDecomposition_left (K := ℚ) (L := F) vK hvK (1 ⊗ₜ[ℚ] b i) w = _
  rw [completionTensorDecomposition_left_tmul_apply, map_one, one_mul, Algebra.smul_def]
  rfl

/-- The local traces of `a x²` in basis coordinates give the rational diagonal form. -/
theorem trace_sum_coordinates (v : HeightOneSpectrum (𝓞 ℚ)) {a : Fˣ}
    (T : QuadraticTraceDiagonal a)
    (y : Fin (Module.finrank ℚ F) → (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion) :
    ∑ w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F,
        traceAtCompletion (NumberField.HeightOneSpectrum.adicAbv ℚ v) w
          (AbsoluteValue.toCompletion w.1 (a : F) *
            (∑ i, AbsoluteValue.completionMap _ w.1 w.2 (y i) *
              AbsoluteValue.toCompletion w.1 (T.basis i)) ^ 2) =
      ∑ i, ((T.coeff i : ℚ) : (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion) * y i ^ 2 := by
  classical
  have hvK : (NumberField.HeightOneSpectrum.adicAbv ℚ v).IsNontrivial := RayClass.adicAbv_isNontrivial v
  letI : Algebra ℚ (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion := baseCompletionAlgebra (NumberField.HeightOneSpectrum.adicAbv ℚ v)
  letI : ∀ w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F, Algebra (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra (NumberField.HeightOneSpectrum.adicAbv ℚ v) w.1 w.2
  have hexpand (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) :
      AbsoluteValue.toCompletion w.1 (a : F) *
          (∑ i, AbsoluteValue.completionMap _ w.1 w.2 (y i) *
            AbsoluteValue.toCompletion w.1 (T.basis i)) ^ 2 =
        ∑ i, ∑ j, (y i * y j) •
          AbsoluteValue.toCompletion w.1 ((a : F) * (T.basis i * T.basis j)) := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def, map_mul, map_mul, map_mul]
    have hal : ∀ z, algebraMap (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion w.1.Completion z =
        AbsoluteValue.completionMap _ w.1 w.2 z := fun z => rfl
    simp only [hal]
    ring
  have htr (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) (x : w.1.Completion) :
      traceAtCompletion (NumberField.HeightOneSpectrum.adicAbv ℚ v) w x = Algebra.trace (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion w.1.Completion x := rfl
  rw [Finset.sum_congr rfl (fun w _ => by rw [hexpand w, htr, map_sum])]
  simp only [map_sum, LinearMap.map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  have hcol (j : Fin (Module.finrank ℚ F)) :
      ∑ w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F, y i * y j *
          Algebra.trace (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion w.1.Completion
            (AbsoluteValue.toCompletion w.1 ((a : F) * (T.basis i * T.basis j))) =
        y i * y j * (((if i = j then (T.coeff i : ℚ) else 0 : ℚ)) : (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion) := by
    rw [← Finset.mul_sum, ← trace_diag_pair T i j]
    congr 1
    have h := completion_trace_compatible (K := ℚ) (L := F) (NumberField.HeightOneSpectrum.adicAbv ℚ v) hvK
      ((a : F) * (T.basis i * T.basis j))
    rw [eq_ratCast] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro w _
    rw [AbsoluteValue.toCompletion_eq_algebraMap]
    rfl
  rw [Finset.sum_congr rfl (fun j _ => hcol j)]
  simp only [apply_ite (fun q : ℚ => (q : (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion)), Rat.cast_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- Rational coordinates on the completions above `p` turn the local Gaussian phases of
`a x²` into the rational phases of the diagonal coefficients. The hypothesis `hcomp` is the
lead's `finite_trace_character_comparison` at the place `v`. -/
theorem trace_coordinates (A : AddCharData F) (v : HeightOneSpectrum (𝓞 ℚ))
    (θv : AddChar (v.adicCompletion ℚ) ℂ)
    (hcomp : ∀ (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F)
      (x : w.1.Completion),
      A.ψ (finitePlaceExtensionCentre (K := ℚ) (L := F) v w)
          (finitePlaceExtensionAdicCompletionRingEquiv (K := ℚ) (L := F) v w x) =
        θv (relativeFinitePlaceCompletionRingEquiv v
          (traceAtCompletion (NumberField.HeightOneSpectrum.adicAbv ℚ v) w x)))
    {a : Fˣ} (T : QuadraticTraceDiagonal a) :
    ∃ Φ : (Fin (Module.finrank ℚ F) → ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) ≃ₜ+
        ((w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) →
          (finitePlaceExtensionCentre (K := ℚ) (L := F) v w).adicCompletion F),
      ∀ y, ∏ w, A.ψ (finitePlaceExtensionCentre (K := ℚ) (L := F) v w)
          (algebraMap F _ (a : F) * Φ y w ^ 2) =
        ∏ i, θv ((padicHomeo v).symm
          (((T.coeff i : ℚ) : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) * y i ^ 2)) := by
  refine ⟨((piCongrRightC (fun _ => padicBaseEquiv v)).trans (basisCoordinates v T.basis)).trans
      (piCongrRightC (fun w => kappaEquiv v w)), fun y => ?_⟩
  let y' : Fin (Module.finrank ℚ F) → (NumberField.HeightOneSpectrum.adicAbv ℚ v).Completion :=
    fun i => padicBaseEquiv v (y i)
  have hfac (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) :
      A.ψ (finitePlaceExtensionCentre (K := ℚ) (L := F) v w)
          (algebraMap F _ (a : F) *
            ((((piCongrRightC (fun _ => padicBaseEquiv v)).trans (basisCoordinates v T.basis)).trans
              (piCongrRightC (fun w => kappaEquiv v w))) y w) ^ 2) =
        θv (relativeFinitePlaceCompletionRingEquiv v
          (traceAtCompletion (NumberField.HeightOneSpectrum.adicAbv ℚ v) w
            (AbsoluteValue.toCompletion w.1 (a : F) *
              (∑ i, AbsoluteValue.completionMap _ w.1 w.2 (y' i) *
                AbsoluteValue.toCompletion w.1 (T.basis i)) ^ 2))) := by
    rw [← hcomp]
    congr 1
    rw [RingEquiv.map_mul, RingEquiv.map_pow,
      finitePlaceExtensionAdicCompletionRingEquiv_toCompletion, ← basisCoordinates_apply]
    rfl
  rw [Finset.prod_congr rfl (fun w _ => hfac w), ← addChar_map_sum, ← map_sum,
    trace_sum_coordinates, ← addChar_map_sum, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hP : ∀ z, (padicHomeo v).symm z =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.symm z :=
    fun z => rfl
  have hy' : relativeFinitePlaceCompletionRingEquiv v (y' i) = (padicHomeo v).symm (y i) := by
    change relativeFinitePlaceCompletionRingEquiv v
      ((relativeFinitePlaceCompletionRingEquiv v).symm ((padicHomeo v).symm (y i))) = _
    rw [RingEquiv.apply_symm_apply]
  rw [map_mul, map_pow, map_ratCast, hy', hP, hP, map_mul, map_pow, map_ratCast]

end ArtinPrimitiveRoots.Proofs.weil_trace_opus
