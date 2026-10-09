import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianBinary
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSign
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSquare
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianOne
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.NormCoset
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.NormIndex
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.QuadraticNorm
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.QuadraticSupport
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianFiniteScale
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUniformBound
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianFrequency
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.AdditiveOrthogonality
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSupport
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianFourierSeparation
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianNondegenerate

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem complexRoot_injective (D : FieldData F) :
    Function.Injective (complexRoot D) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply D.σ0.injective
  exact congrArg (fun z : ℂˣ => (z : ℂ)) hxy

private theorem hilbert_pow_left (H : HilbertData F) (v : FinPlace F)
    (a b : (v.adicCompletion F)ˣ) (n : ℕ) :
    H.hilb v (a ^ n) b = H.hilb v a b ^ n := by
  induction n with
  | zero =>
      simpa using H.sixth_power v 1 b ⟨1, by simp⟩
  | succ n ih =>
      rw [pow_succ, H.mul_left, ih, pow_succ]

private theorem quadratic_hilbert_square (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (c b : (v.adicCompletion F)ˣ) :
    complexRoot D (H.hilb v (c ^ 2) b) ^ 3 = 1 := by
  rw [← map_pow, ← hilbert_pow_left, ← pow_mul]
  norm_num only [Nat.reduceMul]
  rw [H.sixth_power v (c ^ 6) b ⟨c, rfl⟩, map_one]

/-- Cubing the sextic Hilbert pairing has exactly the square subgroup as its radical.
This isolates the Hilbert nondegeneracy needed for the Gaussian comparison.
Guide: PROOFS.md:474–475; uses only the frozen Hilbert multiplicativity,
sixth-power vanishing, and nondegeneracy fields. -/
theorem quadratic_hilbert_trivial_iff_square (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    (∀ b, complexRoot D (H.hilb v a b) ^ 3 = 1) ↔
      ∃ c : (v.adicCompletion F)ˣ, a = c ^ 2 := by
  constructor
  · intro ha
    have hcube : ∀ b, H.hilb v (a ^ 3) b = 1 := by
      intro b
      apply complexRoot_injective D
      rw [hilbert_pow_left, map_pow, map_one]
      exact ha b
    obtain ⟨c, hc⟩ := H.nondeg v (a ^ 3) hcube
    refine ⟨a ^ 2 / c ^ 3, ?_⟩
    calc
      a = a ^ 4 / a ^ 3 := by
        rw [show a ^ 4 = a * a ^ 3 from pow_succ' a 3]
        simp
      _ = (a ^ 2 / c ^ 3) ^ 2 := by
        rw [hc]
        simp only [div_pow, ← pow_mul, Nat.reduceMul]
  · rintro ⟨c, rfl⟩ b
    exact quadratic_hilbert_square D H v c b

private def quadraticHilbertLeft (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (b : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun a := complexRoot D (H.hilb v a b) ^ 3
  map_one' := by
    rw [H.sixth_power v 1 b ⟨1, by simp⟩, map_one, one_pow]
  map_mul' a a' := by rw [H.mul_left, map_mul, mul_pow]

private def quadraticHilbertRight (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun b := complexRoot D (H.hilb v a b) ^ 3
  map_one' := by
    have h1 := H.sixth_power v 1 a ⟨1, by simp⟩
    have h2 := H.skew v a 1
    rw [h1, mul_one] at h2
    rw [h2, map_one, one_pow]
  map_mul' b b' := by rw [H.mul_right, map_mul, mul_pow]

private theorem quadratic_hilbert_right_square (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a c : (v.adicCompletion F)ˣ) :
    quadraticHilbertRight D H v a (c ^ 2) = 1 := by
  change complexRoot D (H.hilb v a (c ^ 2)) ^ 3 = 1
  have h := congrArg (fun z : rootsOfUnity 6 F => complexRoot D z ^ 3)
    (H.skew v a (c ^ 2))
  simpa only [map_mul, mul_pow, quadratic_hilbert_square, map_one, one_pow,
    mul_one] using h

private theorem completion_square_neg_one (D : FieldData F) (v : FinPlace F) :
    ∃ i : (v.adicCompletion F)ˣ, (i : v.adicCompletion F) ^ 2 = -1 := by
  have h6 : D.ζ12 ^ 6 = -1 := by
    have hroot : IsPrimitiveRoot (D.ζ12 ^ 6) 2 := by
      simpa using D.hζ12.pow_of_dvd (by norm_num : (6 : ℕ) ≠ 0)
        (by norm_num : 6 ∣ 12)
    exact hroot.eq_neg_one_of_two_right
  have hz : D.ζ12 ^ 3 ≠ 0 :=
    pow_ne_zero 3 (D.hζ12.ne_zero (by norm_num))
  have hzv : algebraMap F (v.adicCompletion F) (D.ζ12 ^ 3) ≠ 0 :=
    (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hz
  refine ⟨Units.mk0 _ hzv, ?_⟩
  change (algebraMap F (v.adicCompletion F) (D.ζ12 ^ 3)) ^ 2 = -1
  rw [← map_pow, ← pow_mul, show 3 * 2 = 6 by rfl, h6, map_neg, map_one]

private theorem quadratic_hilbert_diagonal (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    quadraticHilbertRight D H v a a = 1 := by
  obtain ⟨i, hi⟩ := completion_square_neg_one D v
  let m : (v.adicCompletion F)ˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  have hm : m = i ^ 2 := by
    apply Units.ext
    exact hi.symm
  have hminus : quadraticHilbertRight D H v a m = 1 := by
    rw [hm]
    exact quadratic_hilbert_right_square D H v a i
  by_cases ha : (a : v.adicCompletion F) = 1
  · have hau : a = 1 := Units.ext ha
    rw [hau]
    exact (quadraticHilbertLeft D H v 1).map_one
  · have ht0 : (1 : v.adicCompletion F) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
    let t : (v.adicCompletion F)ˣ := Units.mk0 _ ht0
    have ht : quadraticHilbertRight D H v a t = 1 := by
      change complexRoot D (H.hilb v a (Units.mk0 _ ht0)) ^ 3 = 1
      rw [H.steinberg, map_one, one_pow]
    have htinv0 : (1 : v.adicCompletion F) - (a⁻¹ : (v.adicCompletion F)ˣ) ≠ 0 := by
      intro h
      apply ha
      have hval : (a : v.adicCompletion F)⁻¹ = 1 := by
        simpa only [Units.val_inv_eq_inv_val] using (sub_eq_zero.mp h).symm
      exact inv_eq_one.mp hval
    let ti : (v.adicCompletion F)ˣ := Units.mk0 _ htinv0
    have hti : quadraticHilbertLeft D H v ti (a⁻¹) = 1 := by
      change complexRoot D (H.hilb v (a⁻¹) (Units.mk0 _ htinv0)) ^ 3 = 1
      rw [H.steinberg, map_one, one_pow]
    rw [map_inv] at hti
    have hti' : quadraticHilbertRight D H v a ti = 1 := inv_eq_one.mp hti
    have htiu : ti = m * t / a := by
      apply Units.ext
      simp only [ti, m, t, Units.val_mul, Units.val_div_eq_div_val,
        Units.val_mk0, Units.val_inv_eq_inv_val]
      field_simp [a.ne_zero]
      ring
    rw [htiu, map_div, map_mul, hminus, ht, one_mul, one_div] at hti'
    exact inv_eq_one.mp hti'

/-- The quadratic Hilbert character is trivial on every nonzero binary quadratic norm.
Guide: PROOFS.md:474–475. The proof uses only the supplied Hilbert laws and the square
root of -1 supplied by D; it needs no local norm-index or Gaussian comparison theorem. -/
theorem quadratic_hilbert_binary_norm_eq_one (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a n : (v.adicCompletion F)ˣ) (x y : v.adicCompletion F)
    (hn : (n : v.adicCompletion F) = x ^ 2 - (a : v.adicCompletion F) * y ^ 2) :
    complexRoot D (H.hilb v a n) ^ 3 = 1 := by
  change quadraticHilbertRight D H v a n = 1
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      intro hx
      apply n.ne_zero
      exact hn.trans (by simp [hx, hy])
    have hnu : n = (Units.mk0 x hx) ^ 2 := by
      apply Units.ext
      simpa [hy] using hn
    rw [hnu]
    exact quadratic_hilbert_right_square D H v a _
  · by_cases hx : x = 0
    · obtain ⟨i, hi⟩ := completion_square_neg_one D v
      let yu : (v.adicCompletion F)ˣ := Units.mk0 y hy
      have hnu : n = a * (i * yu) ^ 2 := by
        apply Units.ext
        simp only [yu, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
          mul_pow, hi]
        rw [hn, hx]
        ring
      rw [hnu, map_mul, quadratic_hilbert_right_square, mul_one]
      exact quadratic_hilbert_diagonal D H v a
    · let xu : (v.adicCompletion F)ˣ := Units.mk0 x hx
      let yu : (v.adicCompletion F)ˣ := Units.mk0 y hy
      let t : (v.adicCompletion F)ˣ := a * (yu / xu) ^ 2
      have hdiff : (1 : v.adicCompletion F) - t = (n : v.adicCompletion F) / x ^ 2 := by
        simp only [t, xu, yu, Units.val_mul, Units.val_div_eq_div_val,
          Units.val_pow_eq_pow_val, Units.val_mk0]
        rw [hn]
        field_simp [hx]
      have ht0 : (1 : v.adicCompletion F) - t ≠ 0 := by
        rw [hdiff]
        exact div_ne_zero n.ne_zero (pow_ne_zero 2 hx)
      let r : (v.adicCompletion F)ˣ := Units.mk0 _ ht0
      have hnu : n = xu ^ 2 * r := by
        apply Units.ext
        simp only [xu, r, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
        rw [hdiff]
        field_simp [hx]
      have hstein : quadraticHilbertLeft D H v r t = 1 := by
        change complexRoot D (H.hilb v t (Units.mk0 _ ht0)) ^ 3 = 1
        rw [H.steinberg, map_one, one_pow]
      change quadraticHilbertLeft D H v r (a * (yu / xu) ^ 2) = 1 at hstein
      rw [map_mul] at hstein
      have hsquare : quadraticHilbertLeft D H v r ((yu / xu) ^ 2) = 1 :=
        quadratic_hilbert_square D H v (yu / xu) r
      rw [hsquare, mul_one] at hstein
      rw [hnu, map_mul, quadratic_hilbert_right_square, one_mul]
      exact hstein

private theorem index_two_functions_eq {G T : Type*} [Group G] [One T]
    (N : Subgroup G) (hindex : N.index = 2) (c : T) (f g : G → T)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1)
    (hfvalues : ∀ x, f x = 1 ∨ f x = c) (hgvalues : ∀ x, g x = 1 ∨ g x = c)
    (hfinvariant : ∀ x n, n ∈ N → f (x * n) = f x)
    (hginvariant : ∀ x n, n ∈ N → g (x * n) = g x)
    (hfnontrivial : ¬ ∀ x, f x = 1) (hgnontrivial : ¬ ∀ x, g x = 1)
    (x : G) : f x = g x := by
  classical
  have value (k : G → T) (hk1 : k 1 = 1)
      (hkvalues : ∀ y, k y = 1 ∨ k y = c)
      (hkinvariant : ∀ y n, n ∈ N → k (y * n) = k y)
      (hknontrivial : ¬ ∀ y, k y = 1) (hx : x ∉ N) : k x = c := by
    obtain ⟨t, ht⟩ := not_forall.mp hknontrivial
    have htN : t ∉ N := by
      intro htN
      apply ht
      simpa only [one_mul, hk1] using hkinvariant 1 t htN
    have hn : t⁻¹ * x ∈ N := by
      rw [N.mul_mem_iff_of_index_two hindex]
      simp only [N.inv_mem_iff, htN, hx]
    have hxt : k x = k t := by
      simpa only [mul_inv_cancel_left] using hkinvariant t (t⁻¹ * x) hn
    exact hxt.trans ((hkvalues t).resolve_left ht)
  by_cases hx : x ∈ N
  · have hf : f x = 1 := by
      simpa only [one_mul, hf1] using hfinvariant 1 x hx
    have hg : g x = 1 := by
      simpa only [one_mul, hg1] using hginvariant 1 x hx
    exact hf.trans hg.symm
  · exact (value f hf1 hfvalues hfinvariant hfnontrivial hx).trans
      (value g hg1 hgvalues hginvariant hgnontrivial hx).symm

private theorem quadratic_hilbert_sign (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    quadraticHilbertRight D H v a b = 1 ∨ quadraticHilbertRight D H v a b = -1 := by
  have hroot : H.hilb v a b ^ 6 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 6 _).mp (H.hilb v a b).property
  have hsquare : quadraticHilbertRight D H v a b ^ 2 = 1 := by
    change (complexRoot D (H.hilb v a b) ^ 3) ^ 2 = 1
    rw [← pow_mul, show 3 * 2 = 6 by rfl, ← map_pow, hroot, map_one]
  exact Units.eq_or_eq_neg_of_sq_eq_sq _ 1 (by simpa only [one_pow] using hsquare)

/-- The quadratic Hilbert comparison follows from the Gaussian identities and
nondegeneracy of the actual Gaussian defect. All Gaussian inputs are explicit hypotheses,
so this theorem isolates the analytic step rather than assuming a new index law.
Guide: PROOFS.md:474–475; uses binary norm constancy and the index-two norm subgroup. -/
theorem quadratic_defect_eq_hilbert_of_nondegenerate (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (w : (v.adicCompletion F)ˣ → ℂˣ)
    (hone : w 1 = 1)
    (hsquare : ∀ a c, w (a * c ^ 2) = w a)
    (hsign : ∀ a, w a ^ 2 = 1)
    (hbinary : ∀ (a b : (v.adicCompletion F)ˣ)
      (h : (a : v.adicCompletion F) + (b : v.adicCompletion F) ≠ 0),
      w a * w b = w (Units.mk0 _ h) * w (a * b / Units.mk0 _ h))
    (a b : (v.adicCompletion F)ˣ)
    (hnondegenerate : (∀ t, w a * w t = w (a * t)) →
      ∃ c : (v.adicCompletion F)ˣ, a = c ^ 2) :
    w a * w b = complexRoot D (H.hilb v a b) ^ 3 * w (a * b) := by
  classical
  by_cases ha : ∃ c : (v.adicCompletion F)ˣ, a = c ^ 2
  · obtain ⟨c, rfl⟩ := ha
    have hwc : w (c ^ 2) = 1 := by
      simpa only [one_mul, hone] using hsquare 1 c
    rw [hwc, quadratic_hilbert_square, one_mul, one_mul,
      show c ^ 2 * b = b * c ^ 2 by ac_rfl, hsquare]
  · have haK : ¬ IsSquare (a : v.adicCompletion F) := by
      rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        intro hc0
        apply a.ne_zero
        simpa only [hc0, mul_zero] using hc
      apply ha
      refine ⟨Units.mk0 c hc0, ?_⟩
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, pow_two, Units.val_mul, Units.val_mk0] using hc
    let _ : ValuativeRel (v.adicCompletion F) :=
      a1_hilbert_sol.completionValuativeRel v
    have : IsNonarchimedeanLocalField (v.adicCompletion F) :=
      a1_hilbert_sol.completionIsLocalField v
    obtain ⟨N, hN, hindex⟩ :=
      quadratic_binary_norm_subgroup_index_two (v.adicCompletion F) (a : _) haK
    obtain ⟨i, hi⟩ := completion_square_neg_one D v
    let f (t : (v.adicCompletion F)ˣ) := w a * w t / w (a * t)
    let g : (v.adicCompletion F)ˣ → ℂˣ := quadraticHilbertRight D H v a
    have hf1 : f 1 = 1 := by simp only [f, hone, mul_one, div_self']
    have hg1 : g 1 = 1 := (quadraticHilbertRight D H v a).map_one
    have hfvalues : ∀ t, f t = 1 ∨ f t = -1 := by
      intro t
      have hf2 : f t ^ 2 = 1 := by
        simp only [f, div_pow, mul_pow, hsign, one_mul, div_self']
      exact Units.eq_or_eq_neg_of_sq_eq_sq _ 1 (by simpa only [one_pow] using hf2)
    have hgvalues : ∀ t, g t = 1 ∨ g t = -1 :=
      quadratic_hilbert_sign D H v a
    have hfinvariant : ∀ t n, n ∈ N → f (t * n) = f t := by
      intro t n hn
      obtain ⟨x, y, hxy⟩ := (hN n).mp hn
      exact quadratic_defect_binary_norm_invariant w i hi hsquare hsign hbinary a t n x y hxy
    have hginvariant : ∀ t n, n ∈ N → g (t * n) = g t := by
      intro t n hn
      obtain ⟨x, y, hxy⟩ := (hN n).mp hn
      have hgn : quadraticHilbertRight D H v a n = 1 :=
        quadratic_hilbert_binary_norm_eq_one D H v a n x y hxy
      change quadraticHilbertRight D H v a (t * n) = quadraticHilbertRight D H v a t
      rw [map_mul, hgn, mul_one]
    have hfnontrivial : ¬ ∀ t, f t = 1 := by
      intro ht
      apply ha
      apply hnondegenerate
      intro t
      exact div_eq_one.mp (ht t)
    have hgnontrivial : ¬ ∀ t, g t = 1 := by
      intro ht
      exact ha ((quadratic_hilbert_trivial_iff_square D H v a).mp ht)
    have heq := index_two_functions_eq N hindex (-1 : ℂˣ) f g hf1 hg1 hfvalues hgvalues
      hfinvariant hginvariant hfnontrivial hgnontrivial b
    exact div_eq_iff_eq_mul.mp heq

/-- Identify the Gaussian multiplicative defect with the quadratic Hilbert symbol.
Guide: PROOFS.md:474–475. Uses: local_index_binary; local_index_sign; local_index_square; H.steinberg; H.nondeg; H.tame; H.product_formula. -/
theorem local_index_hilbert_defect (D : FieldData F) (A : AddCharData F) (H : HilbertData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    W.index v a * W.index v b =
      complexRoot D (H.hilb v a b) ^ 3 * W.index v (a * b) := by
  classical
  let : MeasurableSpace (v.adicCompletion F) := borel _
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  have hnorm : ∀ x : v.adicCompletion F, absFin v x = ‖x‖ := by
    intro x
    rw [absFin, dite_eq_left (NumberField.HeightOneSpectrum.absNorm_ne_zero v),
      NumberField.FinitePlace.norm_def]
  have hscale : ∀ c : (v.adicCompletion F)ˣ,
      Measure.map (fun x : v.adicCompletion F => (c : v.adicCompletion F) * x) (W.measure v) =
        (ENNReal.ofReal ‖(c : v.adicCompletion F)‖)⁻¹ • W.measure v := by
    intro c
    simpa only [hnorm] using local_haar_scale v (W.measure v) (W.isHaar v) c
  have hsign : ∀ c : (v.adicCompletion F)ˣ, W.index v c ^ 2 = 1 := by
    intro c
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rcases local_index_sign D A W v c with hc | hc
    · rw [hc]
      norm_num
    · rw [hc]
      norm_num
  exact quadratic_defect_eq_hilbert_of_nondegenerate D H v (W.index v)
    (local_index_one A W v) (local_index_square D A W v) hsign
    (local_index_binary D A W v) a b
    (local_index_defect_nondegenerate A W v (local_character_regular D A v) hscale a)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
