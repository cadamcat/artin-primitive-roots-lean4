import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNEuler
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

/-!
# QS-ANALYTIC, RN-C: the quadratic class field of a quadratic ray character

For a nontrivial quadratic ray character `ψ` of a totally complex field `K`, the class field of
`ker ψ` (ClassFieldTheory's `GlobalClassFieldComparison.rayClassSubgroup_existence`) is a quadratic,
totally complex extension `E/K`, unramified outside the modulus, whose Artin map sends a prime class
to arithmetic Frobenius.  At a place `v` outside the modulus, `v` splits in `E` when `ψ(v) = 1` and
is inert when `ψ(v) = -1`; hence the local Euler factor of `ζ_E` at `v` is
`(1 - N v^{-s})⁻¹ (1 - ψ(v) N v^{-s})⁻¹`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory Polynomial
open scoped NumberField Pointwise

noncomputable section

namespace ArtinPrimitiveRoots.A2

section General

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- RN-C1: the places of `L` over `v` correspond to the primes over `v.asIdeal`. -/
theorem qsa_fiber_card (v : HeightOneSpectrum (𝓞 K)) :
    (qsa_below_fiber_finite K L v).toFinset.card = (v.asIdeal.primesOver (𝓞 L)).ncard := by
  classical
  have himg : v.asIdeal.primesOver (𝓞 L) =
      HeightOneSpectrum.asIdeal '' {w : HeightOneSpectrum (𝓞 L) | qsaBelow K L w = v} := by
    ext Q
    constructor
    · rintro ⟨hQ, hlies⟩
      have hQ0 : Q ≠ ⊥ := by
        rintro rfl
        apply v.ne_bot
        rw [hlies.over]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))
      refine ⟨⟨Q, hQ, hQ0⟩, ?_, rfl⟩
      apply HeightOneSpectrum.ext
      exact hlies.over.symm
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  rw [himg, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h),
    Set.ncard_eq_toFinset_card _ (qsa_below_fiber_finite K L v)]

omit [NumberField L] in
/-- RN-C2: if every residue class is fixed by the `n`-th power map (`n > 1`), the residue field
has at most `n` elements. -/
theorem qsa_card_quot_le_of_pow (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Finite ((𝓞 L) ⧸ Q)] {n : ℕ}
    (hn : 1 < n) (h : ∀ x : 𝓞 L, x - x ^ n ∈ Q) : Nat.card ((𝓞 L) ⧸ Q) ≤ n := by
  classical
  let _ : Fintype ((𝓞 L) ⧸ Q) := Fintype.ofFinite _
  have hdeg : (X ^ n - X : Polynomial ((𝓞 L) ⧸ Q)).natDegree = n := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    omega
  have hP0 : (X ^ n - X : Polynomial ((𝓞 L) ⧸ Q)) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  set P : Polynomial ((𝓞 L) ⧸ Q) := X ^ n - X with hPdef
  have hroots : (Finset.univ : Finset ((𝓞 L) ⧸ Q)) ⊆ P.roots.toFinset := by
    intro y _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [P, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← neg_sub]
    exact Q.neg_mem (h x)
  calc Nat.card ((𝓞 L) ⧸ Q) = (Finset.univ : Finset ((𝓞 L) ⧸ Q)).card := by
        rw [Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = n := hdeg

/-- RN-C3: the local Euler factor of `ζ_L` at an unramified place of `K`, for a quadratic Galois
extension `L/K`, in terms of the sign `ε = ±1` that records whether Frobenius is trivial. -/
theorem qsa_quadratic_local_factor [IsGalois K L] (hG : Nat.card (L ≃ₐ[K] L) = 2)
    (v : HeightOneSpectrum (𝓞 K)) (hunr : Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) (ε : ℂ)
    (hε : ε = 1 ∨ ε = -1)
    (hfrob : ∀ w : HeightOneSpectrum (𝓞 L), qsaBelow K L w = v →
      (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal = 1 ↔ ε = 1)) (s : ℂ) :
    ∏ w ∈ (qsa_below_fiber_finite K L v).toFinset,
        (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ =
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ *
        (1 - ε * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  classical
  set q := Ideal.absNorm v.asIdeal with hqdef
  set g := (v.asIdeal.primesOver (𝓞 L)).ncard with hgdef
  set e := v.asIdeal.ramificationIdxIn (𝓞 L) with hedef
  set f := v.asIdeal.inertiaDegIn (𝓞 L) with hfdef
  have hgef : g * (e * f) = 2 := by
    rw [← hG]
    exact Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 L)
      (L ≃ₐ[K] L)
  have hcard := qsa_fiber_card K L v
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, zero_mul] at hgef
    norm_num at hgef
  obtain ⟨w, hw⟩ : (qsa_below_fiber_finite K L v).toFinset.Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.pos_of_ne_zero hg0
  rw [Set.Finite.mem_toFinset] at hw
  have hw' : qsaBelow K L w = v := hw
  have hlies : w.asIdeal.LiesOver v.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal hw').symm⟩
  have he : e = 1 := by
    rw [hedef, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
      Ideal.ramificationIdx_eq_one_iff]
    exact hunr w.asIdeal w.isPrime hlies
  have hnorm : ∀ w' ∈ (qsa_below_fiber_finite K L v).toFinset,
      Ideal.absNorm w'.asIdeal = q ^ f := by
    intro w' hw'
    rw [Set.Finite.mem_toFinset] at hw'
    have hw'' : qsaBelow K L w' = v := hw'
    have : w'.asIdeal.LiesOver v.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal hw'').symm⟩
    rw [hfdef, Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w'.asIdeal (L ≃ₐ[K] L),
      Ideal.absNorm_pow_inertiaDeg v.asIdeal w'.asIdeal]
  have hprod : ∏ w' ∈ (qsa_below_fiber_finite K L v).toFinset,
        (1 - ((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ =
      ∏ w' ∈ (qsa_below_fiber_finite K L v).toFinset,
        (1 - (((q ^ f : ℕ) : ℕ) : ℂ) ^ (-s))⁻¹ :=
    Finset.prod_congr rfl (fun w' hw' => by rw [hnorm w' hw'])
  rw [hprod, Finset.prod_const, hcard, ← hgdef]
  have hq : 1 < q := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hf0 : f ≠ 0 := Ideal.inertiaDegIn_ne_zero (L ≃ₐ[K] L)
  rw [he, one_mul] at hgef
  rcases hε with rfl | rfl
  · have hfrob1 := (hfrob w hw').mpr rfl
    have hF := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal
    rw [hfrob1] at hF
    have hunder : w.asIdeal.under (𝓞 K) = v.asIdeal := hlies.over.symm
    have hn : Nat.card ((𝓞 K) ⧸ w.asIdeal.under (𝓞 K)) = q := by
      rw [hunder, hqdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hle := qsa_card_quot_le_of_pow L w.asIdeal hq (fun x => by
      have := hF x
      rw [hn] at this
      simpa using this)
    have hcardw : Nat.card ((𝓞 L) ⧸ w.asIdeal) = q ^ f := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      exact hnorm w ((Set.Finite.mem_toFinset _).mpr hw)
    rw [hcardw] at hle
    have hf1 : f = 1 := by
      have hf_le : f ≤ 1 := by
        by_contra hcon
        push_neg at hcon
        have h2 : q ^ 2 ≤ q ^ f := Nat.pow_le_pow_right (by omega) hcon
        have h3 : q < q ^ 2 := by nlinarith
        omega
      omega
    have hg2 : g = 2 := by
      rw [hf1, mul_one] at hgef
      exact hgef
    rw [hf1, hg2, pow_one, one_mul, sq]
  · have hfrob1 : arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal ≠ 1 := fun h => by
      have := (hfrob w hw').mp h
      norm_num at this
    have hmem := (IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal).mem_stabilizer
    have hstab := Ideal.card_stabilizer_eq (G := L ≃ₐ[K] L) v.asIdeal w.asIdeal
    have hf2 : f ≠ 1 := by
      intro hf1
      have h1 : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) = 1 := by
        rw [hstab, ← hedef, ← hfdef, he, hf1]
      have hsub := (Nat.card_eq_one_iff_unique.mp h1).1
      apply hfrob1
      have := hsub.elim ⟨_, hmem⟩ 1
      exact congrArg Subtype.val this
    have hf2' : f = 2 := by
      have hdvd : f ∣ 2 := ⟨g, by rw [← hgef]; ring⟩
      have hle : f ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hg1 : g = 1 := by
      rw [hf2'] at hgef
      omega
    rw [hf2', hg1, pow_one, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
      Complex.cpow_nat_mul]
    set x := ((q : ℕ) : ℂ) ^ (-s)
    rw [← mul_inv]
    congr 1
    ring

end General

variable {K : Type} [Field K] [NumberField K]

/-- RN-C: the quadratic class field of a nontrivial quadratic ray character, with its degree,
signature and the local Euler factors at the places outside the modulus. -/
theorem qsa_quadratic_class_field [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (hsq : ψ⁻¹ = ψ) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      InfinitePlace.nrRealPlaces E = 0 ∧
      InfinitePlace.nrComplexPlaces E = 2 * InfinitePlace.nrComplexPlaces K ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support → ∀ s : ℂ,
        ∏ w ∈ (qsa_below_fiber_finite K E v).toFinset,
            (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ =
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ *
            (1 - Hecke.charValue ψ v.asIdeal *
              ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  classical
  obtain ⟨R⟩ := GlobalClassFieldComparison.rayClassSubgroup_existence K m ψ.ker
  have hsq_c : ∀ c, ψ c = 1 ∨ ψ c = -1 := by
    intro c
    have hinv : (ψ c)⁻¹ = ψ c := by
      have := DFunLike.congr_fun hsq c
      simpa only [MonoidHom.inv_apply] using this
    have h1 : ψ c * ψ c = 1 := by
      calc ψ c * ψ c = ψ c * (ψ c)⁻¹ := by rw [hinv]
        _ = 1 := mul_inv_cancel _
    have h2 : (ψ c : ℂ) * (ψ c : ℂ) = 1 := by rw [← Units.val_mul, h1, Units.val_one]
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simpa using h))
  have hrange : Nat.card ψ.range = 2 := by
    obtain ⟨c, hc⟩ : ∃ c, ψ c ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hψ (MonoidHom.ext hcon)
    have hc' : ψ c = -1 := (hsq_c c).resolve_left hc
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨-1, ⟨c, hc'⟩⟩, ?_, ?_⟩
    · intro h
      have h' := congrArg (fun z : ψ.range => ((z : ℂˣ) : ℂ)) h
      norm_num at h'
    · ext ⟨x, ⟨d, rfl⟩⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases hsq_c d with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  have hG : Nat.card (R.extension ≃ₐ[K] R.extension) = 2 := by
    calc Nat.card (R.extension ≃ₐ[K] R.extension) =
          Nat.card (RayClassGroup m ⧸ R.artin.ker) :=
          (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
            R.artin_surjective).toEquiv).symm
      _ = Nat.card (RayClassGroup m ⧸ ψ.ker) := by rw [R.artin_ker]
      _ = Nat.card ψ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
      _ = 2 := hrange
  have : IsTotallyComplex R.extension := NumberField.isTotallyComplex_of_algebra K R.extension
  have hfinrank : Module.finrank K R.extension = 2 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hG
  refine ⟨R.extension, inferInstance, inferInstance, inferInstance,
    IsTotallyComplex.nrRealPlaces_eq_zero _, ?_, ?_⟩
  · have h1 := IsTotallyComplex.finrank (K := R.extension)
    have h2 := IsTotallyComplex.finrank (K := K)
    have h3 := Module.finrank_mul_finrank ℚ K R.extension
    rw [hfinrank] at h3
    omega
  · intro v hv s
    have hc : Hecke.IsCoprimeTo m v.asIdeal := by
      refine ⟨v.ne_bot, ?_⟩
      intro w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      simpa [Hecke.idealUnit] using FractionalIdeal.count_maximal_coprime K w (Ne.symm hwv)
    have hcv : Hecke.charValue ψ v.asIdeal = (ψ (rayClassOfFinitePrime m v hv) : ℂ) := by
      rw [Hecke.charValue, dif_pos hc]
      rfl
    rw [hcv]
    refine qsa_quadratic_local_factor K R.extension hG v (R.unramifiedOutsideModulus.1 v hv) _
      ?_ ?_ s
    · rcases hsq_c (rayClassOfFinitePrime m v hv) with h | h
      · left; simp [h]
      · right; simp [h]
    · intro w hw
      have hlies : w.asIdeal.LiesOver v.asIdeal :=
        ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩
      have hA : arithFrobAt (𝓞 K) (R.extension ≃ₐ[K] R.extension) w.asIdeal =
          R.artin (rayClassOfFinitePrime m v hv) :=
        (R.artin_frobenius v hv w hlies).symm
      rw [hA]
      constructor
      · intro h1
        have hker : rayClassOfFinitePrime m v hv ∈ R.artin.ker := h1
        rw [R.artin_ker] at hker
        simp [MonoidHom.mem_ker.mp hker]
      · intro h1
        have hψc : ψ (rayClassOfFinitePrime m v hv) = 1 := Units.ext (by simpa using h1)
        have hker : rayClassOfFinitePrime m v hv ∈ R.artin.ker := by
          rw [R.artin_ker]
          exact hψc
        exact hker

end ArtinPrimitiveRoots.A2
