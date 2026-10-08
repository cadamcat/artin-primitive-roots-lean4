import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».Defs
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M0

/-!
# A2-QS-CANCEL, part C0: local signed divisor-pair identity

Guide: `runs/lanes/sol-thin-found/PROOFS.md:435-442`.  Local factor
`(1 + x/√q)(1 − x/√q) = 1 − 1/q` for `x = ψ(P) ∈ {±1}`; compiled algebra
`squarefree_mobius_pair`, `quadratic_local_factor` in
`runs/lanes/sol-thin-found/wt/ArtinPrimitiveRoots/Review/sol-thin-found/SieveAlgebra.lean`.
-/

set_option autoImplicit false

open scoped NumberField
open scoped Classical
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

private def qsPrimeSupport (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (UniqueFactorizationMonoid.normalizedFactors I).toFinset

private theorem qsMemDivisors (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (J : Ideal (𝓞 K)) :
    J ∈ qsDivisors I ↔ J ∣ I := by
  simp only [qsDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro hJI
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI), hJI⟩

private theorem qsSupportPrime {I P : Ideal (𝓞 K)} (hP : P ∈ qsPrimeSupport I) : Prime P :=
  UniqueFactorizationMonoid.prime_of_normalized_factor P
    (Multiset.mem_toFinset.mp hP)

private theorem qsSupportProductFactors {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))}
    (hS : S ⊆ qsPrimeSupport I) :
    UniqueFactorizationMonoid.normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => qsSupportPrime (hS hP)
  simpa using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp

private theorem qsSupportProductSquarefree {I : Ideal (𝓞 K)}
    {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsPrimeSupport I) :
    Squarefree (∏ P ∈ S, P) := by
  have h0 : (∏ P ∈ S, P) ≠ ⊥ := by
    exact Finset.prod_ne_zero_iff.mpr (fun P hP => (qsSupportPrime (hS hP)).ne_zero)
  apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).mpr
  rw [qsSupportProductFactors hS]
  exact S.nodup

private theorem qsSupportProductDvd (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsPrimeSupport I) :
    (∏ P ∈ S, P) ∣ I := by
  have h0 : (∏ P ∈ S, P) ≠ ⊥ := by
    exact Finset.prod_ne_zero_iff.mpr (fun P hP => (qsSupportPrime (hS hP)).ne_zero)
  apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors h0 hI).mpr
  rw [qsSupportProductFactors hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

private theorem qsSupportProductSelf {J : Ideal (𝓞 K)} (hJ : Squarefree J) :
    (∏ P ∈ qsPrimeSupport J, P) = J := by
  have hn : (UniqueFactorizationMonoid.normalizedFactors J).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (qsPrimeSupport J).val = UniqueFactorizationMonoid.normalizedFactors J := by
    simpa only [qsPrimeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (qsPrimeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (UniqueFactorizationMonoid.normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

private theorem qsSupportSquarefreeDivisorsImage (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (qsDivisors I).filter Squarefree =
      (qsPrimeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  classical
  ext J
  simp only [Finset.mem_filter, qsMemDivisors I hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨qsPrimeSupport J,
      (fun P hP => Multiset.mem_toFinset.mpr
        (Multiset.mem_of_le
          ((UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
            hJ.ne_zero hI).mp hJI)
          (Multiset.mem_toFinset.mp hP))),
      qsSupportProductSelf hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨qsSupportProductDvd I hI hS, qsSupportProductSquarefree hS⟩

private theorem qsSupportProductInjective (I : Ideal (𝓞 K))
    {S T : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsPrimeSupport I)
    (hT : T ⊆ qsPrimeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg UniqueFactorizationMonoid.normalizedFactors h
  rw [qsSupportProductFactors hS, qsSupportProductFactors hT] at hf
  exact Finset.val_inj.mp hf

private def qsPrimeValue (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (P : Ideal (𝓞 K)) : ℂ :=
  if hP : P.IsPrime ∧ P ≠ ⊥ then χ.primeValue ⟨P, hP.1, hP.2⟩ else 1

private theorem qsIdealValuePrime (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (P : Ideal (𝓞 K)) (hP : Prime P) : χ.idealValue P = qsPrimeValue χ P := by
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue qsPrimeValue
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible, normalize_eq]
  simp [Ideal.isPrime_of_prime hP, hP.ne_zero]

private theorem qsIdealValueSupportProduct (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsPrimeSupport I) :
    χ.idealValue (∏ P ∈ S, P) = ∏ P ∈ S, qsPrimeValue χ P := by
  classical
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  rw [qsSupportProductFactors hS, Finset.prod_map_val]
  rfl

private theorem qsNormSupportProduct (I : Ideal (𝓞 K)) {S : Finset (Ideal (𝓞 K))}
    (_hS : S ⊆ qsPrimeSupport I) :
    qsN (∏ P ∈ S, P) = ∏ P ∈ S, (Ideal.absNorm P : ℝ) := by
  classical
  have hn : Ideal.absNorm (∏ P ∈ S, P) = ∏ P ∈ S, Ideal.absNorm P :=
    map_prod Ideal.absNorm (fun P => P) S
  simp only [qsN, hn, Nat.cast_prod]

private theorem qsSqrtNormSupportProduct (I : Ideal (𝓞 K))
    {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsPrimeSupport I) :
    Real.sqrt (qsN (∏ P ∈ S, P)) =
      ∏ P ∈ S, Real.sqrt (Ideal.absNorm P : ℝ) := by
  rw [qsNormSupportProduct I hS]
  exact Real.sqrt_prod S (fun P hP => by positivity)

private theorem qsCharacterTermSupportProduct (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsPrimeSupport I) :
    χ.idealValue (∏ P ∈ S, P) /
        (Real.sqrt (qsN (∏ P ∈ S, P)) : ℂ) =
      ∏ P ∈ S, qsPrimeValue χ P /
        (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) := by
  rw [qsIdealValueSupportProduct χ hS, qsSqrtNormSupportProduct I hS]
  have hcast :
      ((∏ P ∈ S, Real.sqrt (Ideal.absNorm P : ℝ) : ℝ) : ℂ) =
        ∏ P ∈ S, (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) := by simp
  rw [hcast, ← Finset.prod_div_distrib]

private theorem qsMuSupportProductComplex (I : Ideal (𝓞 K))
    {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsPrimeSupport I) :
    (qsMu (∏ P ∈ S, P) : ℂ) = (-1 : ℂ) ^ S.card := by
  simp [qsMu, qsSupportProductSquarefree hS, qsSupportProductFactors hS]

private theorem qsMobiusCharacterTermSupportProduct
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) {I : Ideal (𝓞 K)}
    {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsPrimeSupport I) :
    (qsMu (∏ P ∈ S, P) : ℂ) * χ.idealValue (∏ P ∈ S, P) /
        (Real.sqrt (qsN (∏ P ∈ S, P)) : ℂ) =
      ∏ P ∈ S, ((-1 : ℂ) * qsPrimeValue χ P) /
        (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) := by
  rw [qsMuSupportProductComplex I hS, qsIdealValueSupportProduct χ hS,
    qsSqrtNormSupportProduct I hS]
  have hmu : (-1 : ℂ) ^ S.card = ∏ P ∈ S, (-1 : ℂ) := by simp
  rw [hmu]
  have hcast :
      ((∏ P ∈ S, Real.sqrt (Ideal.absNorm P : ℝ) : ℝ) : ℂ) =
        ∏ P ∈ S, (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) := by simp
  rw [hcast, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]

private theorem qsMuSupportProduct (I : Ideal (𝓞 K)) {S : Finset (Ideal (𝓞 K))}
    (hS : S ⊆ qsPrimeSupport I) :
    (qsMu (∏ P ∈ S, P) : ℝ) = (-1 : ℝ) ^ S.card := by
  rw [qsMu, if_pos (qsSupportProductSquarefree hS), qsSupportProductFactors hS]
  simp

private theorem qsPhiRatio_euler (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    qsPhiRatio I = ∏ P ∈ qsPrimeSupport I,
      (1 - 1 / (Ideal.absNorm P : ℝ)) := by
  classical
  unfold qsPhiRatio
  have hfilter :
      (∑ e ∈ qsDivisors I, (qsMu e : ℝ) / (Ideal.absNorm e : ℝ)) =
        ∑ e ∈ (qsDivisors I).filter Squarefree,
          (qsMu e : ℝ) / (Ideal.absNorm e : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e he hnot
    have hnsq : ¬ Squarefree e := by
      intro hs
      exact hnot (Finset.mem_filter.mpr ⟨he, hs⟩)
    simp [qsMu, hnsq]
  have himage :
      (∑ e ∈ (qsDivisors I).filter Squarefree,
        (qsMu e : ℝ) / (Ideal.absNorm e : ℝ)) =
        ∑ S ∈ (qsPrimeSupport I).powerset,
          (qsMu (∏ P ∈ S, P) : ℝ) / (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
    rw [qsSupportSquarefreeDivisorsImage I hI, Finset.sum_image]
    · intro S hS T hT hST
      exact qsSupportProductInjective I
        (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST
  have hsum :
      (∑ S ∈ (qsPrimeSupport I).powerset,
        (qsMu (∏ P ∈ S, P) : ℝ) / (Ideal.absNorm (∏ P ∈ S, P) : ℝ)) =
        ∑ S ∈ (qsPrimeSupport I).powerset,
          ∏ P ∈ S, ((-1 : ℝ) / (Ideal.absNorm P : ℝ)) := by
    apply Finset.sum_congr rfl
    intro S hS
    have hs : S ⊆ qsPrimeSupport I := Finset.mem_powerset.mp hS
    change (qsMu (∏ P ∈ S, P) : ℝ) / qsN (∏ P ∈ S, P) = _
    rw [qsMuSupportProduct I hs, qsNormSupportProduct I hs]
    have hnum : (-1 : ℝ) ^ S.card = ∏ P ∈ S, (-1 : ℝ) := by simp
    rw [hnum, ← Finset.prod_div_distrib]
  calc
    _ = ∑ e ∈ (qsDivisors I).filter Squarefree,
        (qsMu e : ℝ) / (Ideal.absNorm e : ℝ) := hfilter
    _ = ∑ S ∈ (qsPrimeSupport I).powerset,
        (qsMu (∏ P ∈ S, P) : ℝ) / (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := himage
    _ = ∑ S ∈ (qsPrimeSupport I).powerset,
        ∏ P ∈ S, ((-1 : ℝ) / (Ideal.absNorm P : ℝ)) := hsum
    _ = ∏ P ∈ qsPrimeSupport I, (1 + (-1 : ℝ) / (Ideal.absNorm P : ℝ)) :=
      (Finset.prod_one_add (s := qsPrimeSupport I)
        (f := fun P => (-1 : ℝ) / (Ideal.absNorm P : ℝ))).symm
    _ = ∏ P ∈ qsPrimeSupport I, (1 - 1 / (Ideal.absNorm P : ℝ)) := by
      apply Finset.prod_congr rfl
      intro P hP
      ring

/-- C0 (IMPL): for squarefree `𝔮 ≠ ⊥` and a character `ψ` with `ψ(P)² = 1` at every prime
`P ∣ 𝔮` (unramified quadratic there),
`(Σ_{t∣𝔮} ψ(t)/√N t) · (Σ_{e∣𝔮} μ(e) ψ(e)/√N e) = φ(𝔮)/N 𝔮`. -/
theorem qs_local_signed_identity_C0 (ψ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮)
    (hψ : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → P ∣ 𝔮 → ψ.idealValue P ^ 2 = 1) :
    (∑ t ∈ qsDivisors 𝔮, ψ.idealValue t / (Real.sqrt (qsN t) : ℂ)) *
      (∑ e ∈ qsDivisors 𝔮, (qsMu e : ℂ) * ψ.idealValue e / (Real.sqrt (qsN e) : ℂ)) =
        (qsPhiRatio 𝔮 : ℂ) := by
  classical
  have hq0 : 𝔮 ≠ ⊥ := h𝔮.ne_zero
  let x : Ideal (𝓞 K) → ℂ := fun P =>
    qsPrimeValue ψ P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)
  have hfilter : (qsDivisors 𝔮).filter Squarefree = qsDivisors 𝔮 := by
    apply Finset.filter_eq_self.mpr
    intro t ht
    exact Squarefree.squarefree_of_dvd (qsMemDivisors 𝔮 hq0 t |>.mp ht) h𝔮
  have hsumA :
      (∑ t ∈ qsDivisors 𝔮, ψ.idealValue t / (Real.sqrt (qsN t) : ℂ)) =
        ∏ P ∈ qsPrimeSupport 𝔮, (1 + x P) := by
    calc
      _ = ∑ t ∈ (qsDivisors 𝔮).filter Squarefree,
          ψ.idealValue t / (Real.sqrt (qsN t) : ℂ) := by
            exact congrArg (fun s : Finset (Ideal (𝓞 K)) =>
              ∑ t ∈ s, ψ.idealValue t / (Real.sqrt (qsN t) : ℂ)) hfilter.symm
      _ = ∑ S ∈ (qsPrimeSupport 𝔮).powerset,
          ψ.idealValue (∏ P ∈ S, P) /
          (Real.sqrt (qsN (∏ P ∈ S, P)) : ℂ) := by
          rw [qsSupportSquarefreeDivisorsImage 𝔮 hq0, Finset.sum_image]
          · intro S hS T hT hST
            exact qsSupportProductInjective 𝔮
              (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST
      _ = ∑ S ∈ (qsPrimeSupport 𝔮).powerset, ∏ P ∈ S, x P := by
          apply Finset.sum_congr rfl
          intro S hS
          simpa [x] using
            (qsCharacterTermSupportProduct ψ (Finset.mem_powerset.mp hS))
      _ = ∏ P ∈ qsPrimeSupport 𝔮, (1 + x P) := by
          simpa using
            (Finset.prod_one_add (s := qsPrimeSupport 𝔮) (f := x)).symm
  have hfilterB :
      (∑ e ∈ qsDivisors 𝔮,
        (qsMu e : ℂ) * ψ.idealValue e / (Real.sqrt (qsN e) : ℂ)) =
        ∑ e ∈ (qsDivisors 𝔮).filter Squarefree,
          (qsMu e : ℂ) * ψ.idealValue e / (Real.sqrt (qsN e) : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e he hnot
    have hnsq : ¬ Squarefree e := by
      intro hs
      exact hnot (Finset.mem_filter.mpr ⟨he, hs⟩)
    simp [qsMu, hnsq]
  have hsumB :
      (∑ e ∈ qsDivisors 𝔮,
        (qsMu e : ℂ) * ψ.idealValue e / (Real.sqrt (qsN e) : ℂ)) =
        ∏ P ∈ qsPrimeSupport 𝔮, (1 - x P) := by
    calc
      _ = ∑ e ∈ (qsDivisors 𝔮).filter Squarefree,
          (qsMu e : ℂ) * ψ.idealValue e / (Real.sqrt (qsN e) : ℂ) := hfilterB
      _ = ∑ S ∈ (qsPrimeSupport 𝔮).powerset,
          (qsMu (∏ P ∈ S, P) : ℂ) * ψ.idealValue (∏ P ∈ S, P) /
          (Real.sqrt (qsN (∏ P ∈ S, P)) : ℂ) := by
          rw [qsSupportSquarefreeDivisorsImage 𝔮 hq0, Finset.sum_image]
          · intro S hS T hT hST
            exact qsSupportProductInjective 𝔮
              (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST
      _ = ∑ S ∈ (qsPrimeSupport 𝔮).powerset,
          ∏ P ∈ S, (-x P) := by
          apply Finset.sum_congr rfl
          intro S hS
          calc
            _ = ∏ P ∈ S,
                ((-1 : ℂ) * qsPrimeValue ψ P) /
                  (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) :=
                qsMobiusCharacterTermSupportProduct ψ (Finset.mem_powerset.mp hS)
            _ = ∏ P ∈ S, (-x P) := by
                apply Finset.prod_congr rfl
                intro P hP
                dsimp [x]
                ring
      _ = ∏ P ∈ qsPrimeSupport 𝔮, (1 - x P) := by
          calc
            _ = ∏ P ∈ qsPrimeSupport 𝔮, (1 + (-x P)) := by
                simpa using
                  (Finset.prod_one_add (s := qsPrimeSupport 𝔮) (f := fun P => -x P)).symm
            _ = _ := by
                apply Finset.prod_congr rfl
                intro P hP
                ring
  have hpsiSq (P : Ideal (𝓞 K)) (hP : P ∈ qsPrimeSupport 𝔮) :
      (qsPrimeValue ψ P) ^ 2 = 1 := by
    have hp : Prime P := qsSupportPrime hP
    have hPdiv : P ∣ 𝔮 := by
      simpa using qsSupportProductDvd 𝔮 hq0 (Finset.singleton_subset_iff.mpr hP)
    rw [← qsIdealValuePrime ψ P hp]
    exact hψ P (Ideal.isPrime_of_prime hp) hp.ne_zero hPdiv
  have hlocalSq (P : Ideal (𝓞 K)) (hP : P ∈ qsPrimeSupport 𝔮) :
      (x P) ^ 2 = 1 / (Ideal.absNorm P : ℂ) := by
    dsimp [x]
    have hsqrt :
        (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) ^ 2 = (Ideal.absNorm P : ℂ) := by
      have hsqrtR : Real.sqrt (Ideal.absNorm P : ℝ) ^ 2 =
          (Ideal.absNorm P : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
      rw [← Complex.ofReal_pow]
      exact congrArg (fun y : ℝ => (y : ℂ)) hsqrtR
    rw [div_pow, hpsiSq P hP, hsqrt]
  have hphiC : (qsPhiRatio 𝔮 : ℂ) =
      ∏ P ∈ qsPrimeSupport 𝔮, (1 - 1 / (Ideal.absNorm P : ℂ)) := by
    have h := congrArg (fun y : ℝ => (y : ℂ)) (qsPhiRatio_euler 𝔮 hq0)
    calc
      (qsPhiRatio 𝔮 : ℂ) =
          ((∏ P ∈ qsPrimeSupport 𝔮,
            (1 - 1 / (Ideal.absNorm P : ℝ)) : ℝ) : ℂ) := h
      _ = ∏ P ∈ qsPrimeSupport 𝔮, (1 - 1 / (Ideal.absNorm P : ℂ)) := by
        induction qsPrimeSupport 𝔮 using Finset.induction_on with
        | empty => simp
        | @insert P S hP ih =>
            rw [Finset.prod_insert hP, Finset.prod_insert hP]
            rw [Complex.ofReal_mul, ih]
            simp [Complex.ofReal_sub, Complex.ofReal_div]
  calc
    _ = ∏ P ∈ qsPrimeSupport 𝔮, ((1 + x P) * (1 - x P)) := by
      rw [hsumA, hsumB, ← Finset.prod_mul_distrib]
    _ = ∏ P ∈ qsPrimeSupport 𝔮, (1 - 1 / (Ideal.absNorm P : ℂ)) := by
      apply Finset.prod_congr rfl
      intro P hP
      calc
        (1 + x P) * (1 - x P) = 1 - (x P) ^ 2 := by ring
        _ = 1 - 1 / (Ideal.absNorm P : ℂ) := by rw [hlocalSq P hP]
    _ = qsPhiRatio 𝔮 := hphiC.symm

/-- C0 (IMPL): `φ(I J)/N(I J) = (φ(I)/N I)(φ(J)/N J)` for coprime nonzero `I, J`. -/
theorem qs_phiRatio_mul_C0 (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIJ : IsCoprime I J) :
    qsPhiRatio (I * J) = qsPhiRatio I * qsPhiRatio J := by
  classical
  have hdisj : Disjoint (qsPrimeSupport I) (qsPrimeSupport J) := by
    apply Finset.disjoint_left.mpr
    intro P hPI hPJ
    have hp : Prime P := qsSupportPrime hPI
    have hPIdvd : P ∣ I := by
      simpa using qsSupportProductDvd I hI (Finset.singleton_subset_iff.mpr hPI)
    have hPJdvd : P ∣ J := by
      simpa using qsSupportProductDvd J hJ (Finset.singleton_subset_iff.mpr hPJ)
    have hle : I ⊔ J ≤ P :=
      sup_le (Ideal.dvd_iff_le.mp hPIdvd) (Ideal.dvd_iff_le.mp hPJdvd)
    have hPneTop : P ≠ ⊤ := by
      intro heq
      apply hp.not_isUnit
      simpa [heq] using (isUnit_one : IsUnit (1 : Ideal (𝓞 K)))
    exact hPneTop (top_unique (hIJ.sup_eq ▸ hle))
  have hsupp : qsPrimeSupport (I * J) = qsPrimeSupport I ∪ qsPrimeSupport J := by
    dsimp [qsPrimeSupport]
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.toFinset_add]
  rw [qsPhiRatio_euler (I * J) (mul_ne_zero hI hJ), qsPhiRatio_euler I hI,
    qsPhiRatio_euler J hJ, hsupp, Finset.prod_union hdisj]

end ArtinPrimitiveRoots.A2
