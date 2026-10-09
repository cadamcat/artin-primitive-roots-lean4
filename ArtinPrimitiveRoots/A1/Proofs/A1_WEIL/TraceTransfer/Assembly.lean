import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer.PadicGaussian
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer.Coordinates
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer.FiberGaussian
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianModulus
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalUnit
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».RationalProduct

/-!
# Assembly of the quadratic trace transfer

The product of the actual normalized local indices over the places above `p` equals the ratio
of the explicit rational phases of two diagonalizations of the trace forms of `a` and of `1`.
Each local index has modulus one (frozen `stable_quadratic_integral_modulus`); the product of
the stabilized Gaussians above `p` is a positive multiple of the rational phase product
(`trace_coordinates`, `fiber_gaussian_eq`, `padic_gaussian_phase`); so all positive constants
cancel.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory AlgebraicNumberTheory.Valuations

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.weil_trace_opus

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.Proofs.a1_bdata_sol
  ArtinPrimitiveRoots.Proofs.a1_weil_sol

attribute [local instance] padicMeasurableSpace padicBorelSpace
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

variable {F : Type} [Field F] [NumberField F]

local instance assemblyMeasurable (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) :=
  borel _
local instance assemblyBorel (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The rational character at `p`, transported to `ℚ_[p]`, has kernel `ℤ_[p]` and the standard
values on `ℤ[1/p]`. -/
theorem padic_transported_char (v : HeightOneSpectrum (𝓞 ℚ))
    (θ : AddChar (v.adicCompletion ℚ) ℂ)
    (hker : ∀ x, θ x = 1 ↔ x ∈ v.adicCompletionIntegers ℚ)
    (hform : ∀ (a : ℤ) (n : ℕ),
      θ (algebraMap ℚ (v.adicCompletion ℚ)
        ((a : ℚ) / ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℚ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) /
        ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℂ) ^ n)) :
    (∀ x : ℚ_[Rat.HeightOneSpectrum.primesEquiv v],
      θ ((padicHomeo v).symm x) = 1 ↔ ‖x‖ ≤ 1) ∧
    (∀ (a : ℤ) (n : ℕ),
      θ ((padicHomeo v).symm ((a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) /
        (((Rat.HeightOneSpectrum.primesEquiv v : ℕ)) : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) /
        ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℂ) ^ n)) := by
  let e := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv
  have hP : ∀ z, (padicHomeo v).symm z = e.symm z := fun z => rfl
  have hbij := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
  refine ⟨fun x => ?_, fun a n => ?_⟩
  · rw [hP, hker, ← PadicInt.mem_subring_iff]
    constructor
    · intro hx
      have h := hbij.mapsTo hx
      have hx' : (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v) (e.symm x) = x :=
        e.apply_symm_apply x
      rw [hx'] at h
      exact h
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
      have : e.symm x = y := by
        rw [← hyx]
        exact e.symm_apply_apply y
      rw [this]
      exact hy
  · rw [hP]
    have := hform a n
    convert this using 2
    rw [map_div₀, map_div₀, map_intCast, map_intCast, map_pow, map_pow, map_natCast, map_natCast]

/-- Places of `F` above `p` correspond to extensions of the `p`-adic absolute value. -/
theorem finitePlaceBelow_eq_iff (v : HeightOneSpectrum (𝓞 ℚ)) (W : HeightOneSpectrum (𝓞 F)) :
    finitePlaceBelow (K := ℚ) W = v ↔
      (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : 𝓞 F)) ∈ W.asIdeal := by
  have hmem (u : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) :
      ((m : 𝓞 ℚ) ∈ u.asIdeal) ↔ (Rat.HeightOneSpectrum.primesEquiv u : ℕ) ∣ m := by
    rw [show (Rat.HeightOneSpectrum.primesEquiv u : ℕ) = Rat.HeightOneSpectrum.natGenerator u
      from rfl, Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    rw [← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]
  have hbelow (m : ℕ) : ((m : 𝓞 ℚ) ∈ (finitePlaceBelow (K := ℚ) W).asIdeal) ↔
      ((m : 𝓞 F) ∈ W.asIdeal) := by
    rw [finitePlaceBelow_asIdeal, Ideal.under, Ideal.mem_comap, map_natCast]
  constructor
  · intro h
    rw [← hbelow, h, hmem]
  · intro h
    rw [← hbelow, hmem] at h
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    apply Subtype.ext
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.primesEquiv _).2
      (Rat.HeightOneSpectrum.primesEquiv v).2).mp h

theorem absFin_nonneg' (v : FinPlace F) (y : v.adicCompletion F) : 0 ≤ absFin v y := by
  unfold absFin
  split_ifs
  · exact NNReal.coe_nonneg _
  · exact le_refl _

/-- The actual normalized local index has modulus one. -/
theorem local_index_norm_one (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (x : (v.adicCompletion F)ˣ) : ‖((W.index v x : ℂˣ) : ℂ)‖ = 1 := by
  have := W.isHaar v
  have hmod := stable_quadratic_integral_modulus A v (W.measure v) (W.isHaar v)
    (local_character_regular D A v) x (W.cutoff v x) (W.cutoff v 1)
    (fun M hM => W.stable v x M hM) (fun M hM => W.stable v 1 M hM)
  have habs : 0 ≤ absFin v (x : v.adicCompletion F) := absFin_nonneg' v _
  have h1 : quadraticIntegral A v (W.measure v) 1 (W.cutoff v 1) ≠ 0 := W.integral_ne_zero v 1
  have h1n : 0 < ‖quadraticIntegral A v (W.measure v) 1 (W.cutoff v 1)‖ := norm_pos_iff.mpr h1
  simp only [LocalGaussianData.index, Units.val_mk0]
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg habs _), div_eq_one_iff_eq h1n.ne']
  have hsq : (absFin v (x : v.adicCompletion F) ^ (1 / 2 : ℝ)) ^ 2 =
      absFin v (x : v.adicCompletion F) := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt habs]
  have hnn : 0 ≤ absFin v (x : v.adicCompletion F) ^ (1 / 2 : ℝ) *
      ‖quadraticIntegral A v (W.measure v) x (W.cutoff v x)‖ :=
    mul_nonneg (Real.rpow_nonneg habs _) (norm_nonneg _)
  have : (absFin v (x : v.adicCompletion F) ^ (1 / 2 : ℝ) *
      ‖quadraticIntegral A v (W.measure v) x (W.cutoff v x)‖) ^ 2 =
      ‖quadraticIntegral A v (W.measure v) 1 (W.cutoff v 1)‖ ^ 2 := by
    rw [mul_pow, hsq, hmod]
  exact (sq_eq_sq₀ hnn (norm_nonneg _)).mp this

/-- Over the places above `p`, the product of stabilized Gaussians of `x` is a positive multiple
of the rational phase of a diagonalization of `Tr(x y²)`. -/
theorem fiber_product_phase (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : Fˣ) (T : QuadraticTraceDiagonal x) :
    ∃ R : ℝ, 0 < R ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      ∏ w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F,
        quadraticIntegral A (finitePlaceExtensionCentre (K := ℚ) (L := F) v w)
          (W.measure (finitePlaceExtensionCentre (K := ℚ) (L := F) v w))
          (toLoc (finitePlaceExtensionCentre (K := ℚ) (L := F) v w) x) N =
        R * tracePrimePhase T (Rat.HeightOneSpectrum.primesEquiv v) := by
  classical
  choose θ hθker hθform using fun u : HeightOneSpectrum (𝓞 ℚ) => rationalCompletionChar_exists u
  have hcompLead := finite_trace_character_comparison A θ (fun u y hy => (hθker u y).mpr hy)
    (fun r => by
      have h := rationalChar_product θ hθker hθform r
      simp only [eq_ratCast] at h ⊢
      exact h)
  obtain ⟨Φ, hΦ⟩ := trace_coordinates A v (θ v) (fun w y => hcompLead v w y) T
  obtain ⟨hker', hform'⟩ := padic_transported_char v (θ v) (hθker v) (hθform v)
  let θ' : AddChar ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ℂ :=
    (θ v).compAddMonoidHom (padicHomeo v).symm.toAddEquiv.toAddMonoidHom
  have hθ' : ∀ y, θ' y = θ v ((padicHomeo v).symm y) := fun _ => rfl
  let lam : Measure ℚ_[Rat.HeightOneSpectrum.primesEquiv v] := Measure.addHaar
  haveI : ∀ w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F,
      (W.measure (finitePlaceExtensionCentre (K := ℚ) (L := F) v w)).IsAddHaarMeasure :=
    fun w => W.isHaar _
  obtain ⟨r, hr, N0, s0, hfib⟩ := fiber_gaussian_eq
    (fun w => finitePlaceExtensionCentre (K := ℚ) (L := F) v w) A
    (fun w => local_character_regular D A _) (fun w => W.measure _) (fun w => toLoc _ x)
    (Rat.HeightOneSpectrum.primesEquiv v : ℕ) lam
    (fun i y => θ' (((T.coeff i : ℚ) : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) * y ^ 2)) Φ
    (fun y => hΦ y)
  choose sI hsI using fun i => padic_gaussian_phase (Rat.HeightOneSpectrum.primesEquiv v) θ'
    (fun y => by rw [hθ']; exact hker' y) (fun a n => by rw [hθ']; exact hform' a n) lam
    (T.coeff i)
  let s : ℤ := |s0| + ∑ i, |sI i|
  have hs0 : s0 ≤ s := (le_abs_self s0).trans (le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => abs_nonneg (sI i)))
  have hsi (i : Fin (Module.finrank ℚ F)) : sI i ≤ s :=
    (le_abs_self (sI i)).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (sI j))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left (abs_nonneg s0)))
  choose rI hrI hrIeq using fun i => hsI i s (hsi i)
  refine ⟨r * ∏ i, rI i, mul_pos hr (Finset.prod_pos fun i _ => hrI i), N0, fun N hN => ?_⟩
  rw [hfib N hN s hs0, Finset.prod_congr rfl (fun i _ => hrIeq i), Finset.prod_mul_distrib]
  unfold tracePrimePhase
  push_cast
  ring

/-- The quadratic trace transfer: the product of the normalized local indices over the places
above `p` is the ratio of the rational phases of the two diagonalizations. -/
theorem quadratic_trace_transfer_proof (D : FieldData F) (A : AddCharData F)
    (W : LocalGaussianData A) (a : Fˣ) (T : QuadraticTraceDiagonal a)
    (T1 : QuadraticTraceDiagonal (1 : Fˣ)) (p : Nat.Primes) :
    primeFiberIndex W p a = tracePrimePhase T p / tracePrimePhase T1 p := by
  classical
  obtain ⟨v, rfl⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective p
  let c : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F → FinPlace F :=
    fun w => finitePlaceExtensionCentre (K := ℚ) (L := F) v w
  let e : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F ≃
      {v' : FinPlace F // (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : 𝓞 F)) ∈ v'.asIdeal} :=
    (finitePlaceExtensionEquivAbove (K := ℚ) (L := F) v).trans
      (Equiv.subtypeEquivRight (fun W => finitePlaceBelow_eq_iff v W))
  have hce (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) :
      (e w).1 = c w := finitePlaceExtensionEquivAbove_coe (K := ℚ) (L := F) v w
  have hidx (v1 v2 : FinPlace F) (h : v1 = v2) :
      ((W.index v1 (toLoc v1 a) : ℂˣ) : ℂ) = ((W.index v2 (toLoc v2 a) : ℂˣ) : ℂ) := by
    subst h
    rfl
  unfold primeFiberIndex
  rw [← finprod_comp_equiv e, finprod_eq_prod_of_fintype]
  rw [Finset.prod_congr rfl (fun w _ => hidx _ _ (hce w))]
  -- Gaussian products for `a` and for `1`
  obtain ⟨Ra, hRa, Na, hNa⟩ := fiber_product_phase D A W v a T
  obtain ⟨R1, hR1, N1, hN1⟩ := fiber_product_phase D A W v 1 T1
  let N : ℕ := Na + N1 + ∑ w, (W.cutoff (c w) (toLoc (c w) a) + W.cutoff (c w) 1)
  have hcut (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F) :
      W.cutoff (c w) (toLoc (c w) a) ≤ N ∧ W.cutoff (c w) 1 ≤ N := by
    have h := Finset.single_le_sum (f := fun w => W.cutoff (c w) (toLoc (c w) a) +
      W.cutoff (c w) 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    constructor <;> simp only [N] at h ⊢ <;> omega
  have hA := hNa N (by simp only [N]; omega)
  have h1 := hN1 N (by simp only [N]; omega)
  simp only [map_one] at h1
  have hIa : ∏ w, quadraticIntegral A (c w) (W.measure (c w)) (toLoc (c w) a)
      (W.cutoff (c w) (toLoc (c w) a)) = Ra * tracePrimePhase T (Rat.HeightOneSpectrum.primesEquiv v) := by
    rw [← hA]
    exact Finset.prod_congr rfl fun w _ => (W.stable (c w) _ N (hcut w).1).symm
  have hI1 : ∏ w, quadraticIntegral A (c w) (W.measure (c w)) 1 (W.cutoff (c w) 1) =
      R1 * tracePrimePhase T1 (Rat.HeightOneSpectrum.primesEquiv v) := by
    rw [← h1]
    exact Finset.prod_congr rfl fun w _ => (W.stable (c w) _ N (hcut w).2).symm
  -- phases have modulus one
  have hPa : ‖tracePrimePhase T (Rat.HeightOneSpectrum.primesEquiv v)‖ = 1 := by
    unfold tracePrimePhase
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => rational_prime_phase_norm _ _
  have hP1 : ‖tracePrimePhase T1 (Rat.HeightOneSpectrum.primesEquiv v)‖ = 1 := by
    unfold tracePrimePhase
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => rational_prime_phase_norm _ _
  have hP1ne : tracePrimePhase T1 (Rat.HeightOneSpectrum.primesEquiv v) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hP1
    exact zero_ne_one hP1
  -- the index product
  let ρ : ℝ := ∏ w, absFin (c w) ((toLoc (c w) a : (c w).adicCompletion F)) ^ (1 / 2 : ℝ)
  have hρ : 0 ≤ ρ := Finset.prod_nonneg fun w _ => Real.rpow_nonneg (absFin_nonneg' _ _) _
  have hprod : (∏ w, ((W.index (c w) (toLoc (c w) a) : ℂˣ) : ℂ)) =
      ((ρ * Ra / R1 : ℝ) : ℂ) * (tracePrimePhase T (Rat.HeightOneSpectrum.primesEquiv v) /
        tracePrimePhase T1 (Rat.HeightOneSpectrum.primesEquiv v)) := by
    simp only [LocalGaussianData.index, Units.val_mk0]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hIa, hI1]
    simp only [ρ]
    push_cast
    field_simp
  have hnorm : ‖∏ w, ((W.index (c w) (toLoc (c w) a) : ℂˣ) : ℂ)‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun w _ => local_index_norm_one D A W _ _
  have ht : ρ * Ra / R1 = 1 := by
    rw [hprod, norm_mul, norm_div, hPa, hP1, div_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hρ hRa.le) hR1.le)] at hnorm
    exact hnorm
  rw [hprod, ht, Complex.ofReal_one, one_mul]

end ArtinPrimitiveRoots.Proofs.weil_trace_opus
