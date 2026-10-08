import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C0

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

private def qsC1Support (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (UniqueFactorizationMonoid.normalizedFactors I).toFinset

private def qsC1Prod (S : Finset (Ideal (𝓞 K))) : Ideal (𝓞 K) :=
  ∏ P ∈ S, P

private theorem qsC1SupportPrime {I P : Ideal (𝓞 K)} (hP : P ∈ qsC1Support I) : Prime P :=
  UniqueFactorizationMonoid.prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

private theorem qsC1SupportProdFactors {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))}
    (hS : S ⊆ qsC1Support I) :
    UniqueFactorizationMonoid.normalizedFactors (qsC1Prod S) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => qsC1SupportPrime (hS hP)
  simpa [qsC1Prod] using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp

private theorem qsC1SupportProdSquarefree {I : Ideal (𝓞 K)}
    {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsC1Support I) : Squarefree (qsC1Prod S) := by
  have h0 : qsC1Prod S ≠ ⊥ := by
    exact Finset.prod_ne_zero_iff.mpr (fun P hP => (qsC1SupportPrime (hS hP)).ne_zero)
  apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).mpr
  rw [qsC1SupportProdFactors hS]
  exact S.nodup

private theorem qsC1SupportProdDvd (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {S : Finset (Ideal (𝓞 K))} (hS : S ⊆ qsC1Support I) : qsC1Prod S ∣ I := by
  have h0 : qsC1Prod S ≠ ⊥ := by
    exact Finset.prod_ne_zero_iff.mpr (fun P hP => (qsC1SupportPrime (hS hP)).ne_zero)
  apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors h0 hI).mpr
  rw [qsC1SupportProdFactors hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

private theorem qsC1SupportProdSelf {I : Ideal (𝓞 K)} (hI : Squarefree I) :
    qsC1Prod (qsC1Support I) = I := by
  have hn : (UniqueFactorizationMonoid.normalizedFactors I).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  have hv : (qsC1Support I).val = UniqueFactorizationMonoid.normalizedFactors I := by
    simpa only [qsC1Support, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (qsC1Support I).val.prod := (Finset.prod_val _).symm
    _ = (UniqueFactorizationMonoid.normalizedFactors I).prod := by rw [hv]
    _ = I := Ideal.prod_normalizedFactors_eq_self hI.ne_zero

private theorem qsC1SupportMul {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    qsC1Support (I * J) = qsC1Support I ∪ qsC1Support J := by
  dsimp [qsC1Support]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.toFinset_add]

private theorem qsC1SupportSubsetDvd {I J : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hJI : J ∣ I) :
    qsC1Support J ⊆ qsC1Support I := by
  intro P hP
  have hle := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hJ hI).mp hJI
  exact Multiset.mem_toFinset.mpr
    (Multiset.mem_of_le hle (Multiset.mem_toFinset.mp hP))

private theorem qsC1SupportDisjointOfCoprime {I J : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : IsCoprime I J) :
    Disjoint (qsC1Support I) (qsC1Support J) := by
  apply Finset.disjoint_left.mpr
  intro P hPI hPJ
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime (qsC1SupportPrime hPI)
  have hPIdvd : P ∣ I := by
    exact Ideal.mem_normalizedFactors_iff hI |>.mp
      (Multiset.mem_toFinset.mp hPI) |>.2 |> Ideal.dvd_iff_le.mpr
  have hPJdvd : P ∣ J := by
    exact Ideal.mem_normalizedFactors_iff hJ |>.mp
      (Multiset.mem_toFinset.mp hPJ) |>.2 |> Ideal.dvd_iff_le.mpr
  have hle : I ⊔ J ≤ P := sup_le (Ideal.dvd_iff_le.mp hPIdvd) (Ideal.dvd_iff_le.mp hPJdvd)
  have htop : ⊤ ≤ P := by
    calc
      ⊤ = I ⊔ J := hIJ.sup_eq.symm
      _ ≤ P := hle
  exact hPprime.ne_top (le_antisymm le_top htop)

private theorem qsC1PrimeCoprimeOfNotDvd (P I : Ideal (𝓞 K))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hnot : ¬ P ∣ I) : IsCoprime P I := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hs
  have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
  have hEq : P ⊔ I = P := (hmax.eq_of_le hs le_sup_left).symm
  have hle : I ≤ P := by rw [← hEq]; exact le_sup_right
  exact hnot (Ideal.dvd_iff_le.mpr hle)

private theorem qsC1ProdCoprime (I : Ideal (𝓞 K))
    (S : Finset (Ideal (𝓞 K)))
    (hprime : ∀ P ∈ S, Prime P)
    (hnot : ∀ P ∈ S, ¬ P ∣ I) : IsCoprime (qsC1Prod S) I := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [qsC1Prod, Ideal.isCoprime_iff_sup_eq]
  | @insert P S hPS ih =>
      rw [qsC1Prod, Finset.prod_insert hPS]
      apply IsCoprime.mul_left
      · have hP := hprime P (Finset.mem_insert_self ..)
        exact qsC1PrimeCoprimeOfNotDvd P I (Ideal.isPrime_of_prime hP) hP.ne_zero
          (hnot P (Finset.mem_insert_self ..))
      · apply ih
        · intro Q hQ
          exact hprime Q (Finset.mem_insert_of_mem hQ)
        · intro Q hQ
          exact hnot Q (Finset.mem_insert_of_mem hQ)

/-- Split a squarefree ideal into the factors shared with a fixed squarefree ideal and the
coprime complementary factor. -/
private theorem qsC1_sqf_split (q a : Ideal (𝓞 K)) (hq : Squarefree q) (ha : Squarefree a) :
    ∃ h t : Ideal (𝓞 K), a = h * t ∧ Squarefree h ∧ IsCoprime h q ∧
      t ∣ q ∧ Squarefree t := by
  classical
  let Q := qsC1Support q
  let A := qsC1Support a
  let T := A ∩ Q
  let H := A \ Q
  have hTQ : T ⊆ Q := Finset.inter_subset_right
  have hHA : H ⊆ A := Finset.sdiff_subset
  have hTA : T ⊆ A := Finset.inter_subset_left
  have hdis : Disjoint H T := by
    apply Finset.disjoint_left.mpr
    intro P hPH hPT
    exact (Finset.mem_sdiff.mp hPH).2 (Finset.mem_inter.mp hPT).2
  have hunion : H ∪ T = A := by
    ext P
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, H, T, Q, A]
    constructor
    · rintro (⟨hA, _⟩ | ⟨hA, _⟩) <;> exact hA
    · intro hA
      by_cases hQ : P ∈ qsC1Support q
      · exact Or.inr ⟨hA, hQ⟩
      · exact Or.inl ⟨hA, hQ⟩
  let h := qsC1Prod H
  let t := qsC1Prod T
  have hEq : a = h * t := by
    calc
      a = qsC1Prod A := (qsC1SupportProdSelf ha).symm
      _ = qsC1Prod (H ∪ T) := congrArg qsC1Prod hunion.symm
      _ = h * t := by
        dsimp [h, t, qsC1Prod]
        exact Finset.prod_union hdis
  have hSq : Squarefree h := by
    dsimp [h]
    exact qsC1SupportProdSquarefree (I := a) hHA
  have tSq : Squarefree t := by
    dsimp [t]
    exact qsC1SupportProdSquarefree (I := q) hTQ
  have hcop : IsCoprime h q := by
    dsimp [h, H]
    apply qsC1ProdCoprime q (A \ Q)
    · intro P hP
      exact qsC1SupportPrime (hHA hP)
    · intro P hP
      intro hPq
      have hPQ : P ∈ Q := by
        apply Multiset.mem_toFinset.mpr
        exact Ideal.mem_normalizedFactors_iff hq.ne_zero |>.2
          ⟨Ideal.isPrime_of_prime (qsC1SupportPrime (hHA hP)), Ideal.dvd_iff_le.mp hPq⟩
      exact (Finset.mem_sdiff.mp hP).2 hPQ
  have htdvd : t ∣ q := by
    dsimp [t]
    exact qsC1SupportProdDvd q hq.ne_zero hTQ
  exact ⟨h, t, hEq, hSq, hcop, htdvd, tSq⟩

private theorem qsC1_sqf_split_unique (q h₁ t₁ h₂ t₂ : Ideal (𝓞 K))
    (hq : Squarefree q) (hh₁ : Squarefree h₁) (hh₂ : Squarefree h₂)
    (ht₁ : Squarefree t₁) (ht₂ : Squarefree t₂)
    (hcop₁ : IsCoprime h₁ q) (hcop₂ : IsCoprime h₂ q)
    (htq₁ : t₁ ∣ q) (htq₂ : t₂ ∣ q)
    (heq : h₁ * t₁ = h₂ * t₂) : h₁ = h₂ ∧ t₁ = t₂ := by
  have hprod₁ : h₁ ≠ ⊥ ∧ t₁ ≠ ⊥ := ⟨hh₁.ne_zero, ht₁.ne_zero⟩
  have hprod₂ : h₂ ≠ ⊥ ∧ t₂ ≠ ⊥ := ⟨hh₂.ne_zero, ht₂.ne_zero⟩
  have hsup₁ := qsC1SupportMul hprod₁.1 hprod₁.2
  have hsup₂ := qsC1SupportMul hprod₂.1 hprod₂.2
  have hq0 := hq.ne_zero
  have htq₁s := qsC1SupportSubsetDvd hq0 ht₁.ne_zero htq₁
  have htq₂s := qsC1SupportSubsetDvd hq0 ht₂.ne_zero htq₂
  have hdis₁ := qsC1SupportDisjointOfCoprime hh₁.ne_zero hq0 hcop₁
  have hdis₂ := qsC1SupportDisjointOfCoprime hh₂.ne_zero hq0 hcop₂
  have hsupEq : qsC1Support (h₁ * t₁) = qsC1Support (h₂ * t₂) := congrArg qsC1Support heq
  have hinter₁ : qsC1Support (h₁ * t₁) ∩ qsC1Support q = qsC1Support t₁ := by
    rw [hsup₁]
    ext P
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hP | hP, hQ⟩
      · exact False.elim (Finset.disjoint_left.mp hdis₁ hP hQ)
      · exact hP
    · intro hP
      exact ⟨Or.inr hP, htq₁s hP⟩
  have hinter₂ : qsC1Support (h₂ * t₂) ∩ qsC1Support q = qsC1Support t₂ := by
    rw [hsup₂]
    ext P
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hP | hP, hQ⟩
      · exact False.elim (Finset.disjoint_left.mp hdis₂ hP hQ)
      · exact hP
    · intro hP
      exact ⟨Or.inr hP, htq₂s hP⟩
  have htSupEq : qsC1Support t₁ = qsC1Support t₂ := by
    calc
      qsC1Support t₁ = qsC1Support (h₁ * t₁) ∩ qsC1Support q := hinter₁.symm
      _ = qsC1Support (h₂ * t₂) ∩ qsC1Support q := by rw [hsupEq]
      _ = qsC1Support t₂ := hinter₂
  have htEq : t₁ = t₂ := by
    calc
      t₁ = qsC1Prod (qsC1Support t₁) := (qsC1SupportProdSelf ht₁).symm
      _ = qsC1Prod (qsC1Support t₂) := congrArg qsC1Prod htSupEq
      _ = t₂ := qsC1SupportProdSelf ht₂
  have hdiff₁ : qsC1Support (h₁ * t₁) \ qsC1Support q = qsC1Support h₁ := by
    rw [hsup₁]
    ext P
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hP | hP, hnot⟩
      · exact hP
      · exact False.elim (hnot (htq₁s hP))
    · intro hP
      exact ⟨Or.inl hP, fun hQ => (Finset.disjoint_left.mp hdis₁ hP hQ).elim⟩
  have hdiff₂ : qsC1Support (h₂ * t₂) \ qsC1Support q = qsC1Support h₂ := by
    rw [hsup₂]
    ext P
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hP | hP, hnot⟩
      · exact hP
      · exact False.elim (hnot (htq₂s hP))
    · intro hP
      exact ⟨Or.inl hP, fun hQ => (Finset.disjoint_left.mp hdis₂ hP hQ).elim⟩
  have hhSupEq : qsC1Support h₁ = qsC1Support h₂ := by
    calc
      qsC1Support h₁ = qsC1Support (h₁ * t₁) \ qsC1Support q := hdiff₁.symm
      _ = qsC1Support (h₂ * t₂) \ qsC1Support q := by rw [hsupEq]
      _ = qsC1Support h₂ := hdiff₂
  have hhEq : h₁ = h₂ := by
    calc
      h₁ = qsC1Prod (qsC1Support h₁) := (qsC1SupportProdSelf hh₁).symm
      _ = qsC1Prod (qsC1Support h₂) := congrArg qsC1Prod hhSupEq
      _ = h₂ := qsC1SupportProdSelf hh₂
  exact ⟨hhEq, htEq⟩

private theorem qsC1_normMul (h t : Ideal (𝓞 K)) : qsN (h * t) = qsN h * qsN t := by
  simp [qsN, map_mul]

private theorem qsC1_normPos {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 0 < qsN I := by
  have hN : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr (by
    intro h
    exact hI (Ideal.absNorm_eq_zero_iff.mp h))
  exact_mod_cast hN

private theorem qsC1_normOneLe {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 1 ≤ qsN I := by
  have hN : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (by
    intro h
    exact hI (Ideal.absNorm_eq_zero_iff.mp h))
  exact_mod_cast hN

theorem qsC1_dual_scale (M X Y Z : ℝ)
    (hM : 0 < M) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    M / (X * Real.sqrt Y) * Real.sqrt (X * Y / (M * Z)) =
      Real.sqrt M / (Real.sqrt X * Real.sqrt Z) := by
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY
  have hsZ : 0 < Real.sqrt Z := Real.sqrt_pos.2 hZ
  rw [Real.sqrt_div (by positivity : 0 ≤ X * Y)]
  rw [Real.sqrt_mul (le_of_lt hX) Y]
  rw [Real.sqrt_mul (le_of_lt hM) Z]
  field_simp [ne_of_gt hM, ne_of_gt hX, ne_of_gt hsM, ne_of_gt hsX,
    ne_of_gt hsY, ne_of_gt hsZ]
  have hM2 : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM.le
  have hX2 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX.le
  nlinarith [hM2, hX2]

private theorem qsC1_weightMul (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (h t : Ideal (𝓞 K)) (hh : h ≠ ⊥) (ht : t ≠ ⊥) :
    χ.idealValue (h * t) / (Real.sqrt (qsN (h * t)) : ℂ) =
      (χ.idealValue t / (Real.sqrt (qsN t) : ℂ)) *
        (χ.idealValue h / (Real.sqrt (qsN h) : ℂ)) := by
  rw [qs_idealValue_mul_M0 χ h t hh ht, qsC1_normMul,
    Real.sqrt_mul (le_of_lt (qsC1_normPos hh))]
  have hsh : (Real.sqrt (qsN h) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (qsC1_normPos hh)).ne'
  have hst : (Real.sqrt (qsN t) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (qsC1_normPos ht)).ne'
  field_simp [hsh, hst]
  rw [Complex.ofReal_mul]
  ring

private theorem qsC1_memDivisors {q t : Ideal (𝓞 K)} (hq : q ≠ ⊥) (htq : t ∣ q) :
    t ∈ qsDivisors q := by
  have hn : 0 < Ideal.absNorm q := Nat.pos_iff_ne_zero.mpr (by
    intro h
    exact hq (Ideal.absNorm_eq_zero_iff.mp h))
  simp only [qsDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm htq), htq⟩

private theorem qsC1_sqfOfDvd {q t : Ideal (𝓞 K)} (hq : Squarefree q) (htq : t ∣ q) :
    Squarefree t := Squarefree.squarefree_of_dvd htq hq

private theorem qsC1_coprimeOfDvdRight {h q t : Ideal (𝓞 K)}
    (hcop : IsCoprime h q) (htq : t ∣ q) : IsCoprime h t := by
  rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
  have hqt : q ≤ t := Ideal.dvd_iff_le.mp htq
  apply le_antisymm le_top
  calc
    ⊤ = h ⊔ q := hcop.symm
    _ ≤ h ⊔ t := sup_le le_sup_left (le_trans hqt le_sup_right)

private theorem qsC1_memSqfUpTo {κ : ℝ} {q a : Ideal (𝓞 K)}
    (ha : a ≠ ⊥) (hs : Squarefree a) (hc : IsCoprime a q) (hN : qsN a ≤ κ) :
    a ∈ qsSqfUpTo κ q := by
  simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  refine ⟨Nat.le_floor (by simpa [qsN] using hN), ⟨ha, hs, hc, hN⟩⟩

private def qsC1PairDomain (κ : ℝ) (q : Ideal (𝓞 K)) :
    Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  (qsSqfUpTo κ q ×ˢ qsDivisors q).filter
    (fun p => qsN p.1 * qsN p.2 ≤ κ)

private theorem qsC1_memPairDomain {κ : ℝ} {q h t : Ideal (𝓞 K)}
    (hh : h ∈ qsSqfUpTo κ q) (ht : t ∈ qsDivisors q) (hN : qsN h * qsN t ≤ κ) :
    (h, t) ∈ qsC1PairDomain κ q := by
  simp [qsC1PairDomain, hh, ht, hN]

private theorem qsC1_pairProduct_mem {κ : ℝ} {q h t : Ideal (𝓞 K)}
    (hq : Squarefree q) (hp : (h, t) ∈ qsC1PairDomain κ q) :
    h * t ∈ qsSqfUpTo κ ⊤ := by
  have hp' := Finset.mem_filter.mp hp
  have hprod := Finset.mem_product.mp hp'.1
  rcases hprod with ⟨hh, ht⟩
  have hh' := hh
  simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hh'
  rcases hh' with ⟨_, ⟨hh0, hhsq, hhcop, hhN⟩⟩
  have ht' := ht
  simp only [qsDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ht'
  rcases ht' with ⟨_, htq⟩
  have htsq : Squarefree t := qsC1_sqfOfDvd hq htq
  have ht0 := htsq.ne_zero
  have hcop := qsC1_coprimeOfDvdRight hhcop htq
  have hmulSq : Squarefree (h * t) :=
    (squarefree_mul_iff.mpr ⟨hcop.isRelPrime, hhsq, htsq⟩)
  have hmul0 : h * t ≠ ⊥ := hmulSq.ne_zero
  have htop : IsCoprime (h * t) ⊤ := by
    rw [Ideal.isCoprime_iff_sup_eq]
    simp
  have hN : qsN (h * t) ≤ κ := by
    rw [qsC1_normMul]
    exact hp'.2
  exact qsC1_memSqfUpTo hmul0 hmulSq htop hN

private theorem qsC1_existsPair {κ : ℝ} {q a : Ideal (𝓞 K)}
    (hq : Squarefree q) (ha : a ∈ qsSqfUpTo κ ⊤) :
    ∃ p : Ideal (𝓞 K) × Ideal (𝓞 K),
      p ∈ qsC1PairDomain κ q ∧ a = p.1 * p.2 := by
  have ha' := ha
  simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ha'
  rcases ha' with ⟨_, ⟨ha0, hasq, _, haN⟩⟩
  rcases qsC1_sqf_split q a hq hasq with ⟨h, t, haht, hhsq, hhcop, htq, htsq⟩
  have ht0 := htsq.ne_zero
  have hht := qsC1_memDivisors hq.ne_zero htq
  have hNprod : qsN h * qsN t ≤ κ := by
    rw [← qsC1_normMul, ← haht]
    exact haN
  have hNh : qsN h ≤ κ := by
    have ht1 := qsC1_normOneLe ht0
    have hhpos := qsC1_normPos hhsq.ne_zero
    nlinarith
  have hhsqUp := qsC1_memSqfUpTo hhsq.ne_zero hhsq hhcop hNh
  have hp := qsC1_memPairDomain hhsqUp hht hNprod
  exact ⟨(h, t), hp, haht⟩

private theorem qsC1_mainSum_reindex (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (q : Ideal (𝓞 K)) (κ : ℝ) (hq : Squarefree q) :
    (∑ a ∈ qsSqfUpTo κ ⊤,
        χ.idealValue a / (Real.sqrt (qsN a) : ℂ)) =
      ∑ p ∈ qsC1PairDomain κ q,
        (χ.idealValue p.2 / (Real.sqrt (qsN p.2) : ℂ)) *
          (χ.idealValue p.1 / (Real.sqrt (qsN p.1) : ℂ)) := by
  classical
  let A : Finset (Ideal (𝓞 K)) := qsSqfUpTo κ ⊤
  let D : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) := qsC1PairDomain κ q
  let i : (a : Ideal (𝓞 K)) → a ∈ A → Ideal (𝓞 K) × Ideal (𝓞 K) :=
    fun a ha => Classical.choose (qsC1_existsPair hq ha)
  let j : (p : Ideal (𝓞 K) × Ideal (𝓞 K)) → p ∈ D → Ideal (𝓞 K) :=
    fun p _ => p.1 * p.2
  have hi : ∀ a ha, i a ha ∈ D := by
    intro a ha
    exact (Classical.choose_spec (qsC1_existsPair hq ha)).1
  have hj : ∀ p hp, j p hp ∈ A := by
    intro p hp
    exact qsC1_pairProduct_mem hq hp
  have hleft : ∀ a ha, j (i a ha) (hi a ha) = a := by
    intro a ha
    exact (Classical.choose_spec (qsC1_existsPair hq ha)).2.symm
  have hright : ∀ p hp, i (j p hp) (hj p hp) = p := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    rcases Finset.mem_product.mp hp'.1 with ⟨hh, ht⟩
    have hpairsq : Squarefree p.2 := by
      have htdvd : p.2 ∣ q := (Finset.mem_filter.mp ht).2
      exact qsC1_sqfOfDvd hq htdvd
    let p' := Classical.choose (qsC1_existsPair hq (hj p hp))
    have hchosen := Classical.choose_spec (qsC1_existsPair hq (hj p hp))
    have hp' : p' ∈ D := hchosen.1
    have hprod' : j p hp = p'.1 * p'.2 := hchosen.2
    have hp'' := Finset.mem_filter.mp hp'
    rcases Finset.mem_product.mp hp''.1 with ⟨hh', ht'⟩
    have hpairsq' : Squarefree p'.2 := by
      have htdvd : p'.2 ∣ q := (Finset.mem_filter.mp ht').2
      exact qsC1_sqfOfDvd hq htdvd
    have huniq := qsC1_sqf_split_unique q p.1 p.2 p'.1 p'.2 hq
      (Finset.mem_filter.mp hh).2.2.1 (Finset.mem_filter.mp hh').2.2.1
      hpairsq hpairsq' (Finset.mem_filter.mp hh).2.2.2.1
      (Finset.mem_filter.mp hh').2.2.2.1
      (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp ht').2
      (by simpa [j] using hprod')
    have hcoord : p' = p := Prod.ext huniq.1.symm huniq.2.symm
    simpa [i, j, hcoord]
  have hweight : ∀ a ha,
      χ.idealValue a / (Real.sqrt (qsN a) : ℂ) =
        (χ.idealValue (i a ha).2 / (Real.sqrt (qsN (i a ha).2) : ℂ)) *
          (χ.idealValue (i a ha).1 / (Real.sqrt (qsN (i a ha).1) : ℂ)) := by
    intro a ha
    let p := i a ha
    have hspec := Classical.choose_spec (qsC1_existsPair hq ha)
    have hdom : p ∈ D := hspec.1
    have hprod : a = p.1 * p.2 := hspec.2
    have hp := Finset.mem_filter.mp hdom
    rcases Finset.mem_product.mp hp.1 with ⟨hh, ht⟩
    have hh0 : p.1 ≠ ⊥ := (Finset.mem_filter.mp hh).2.1
    have ht0 : p.2 ≠ ⊥ := by
      have hdvd : p.2 ∣ q := (Finset.mem_filter.mp ht).2
      exact (qsC1_sqfOfDvd hq hdvd).ne_zero
    calc
      χ.idealValue a / (Real.sqrt (qsN a) : ℂ) =
          χ.idealValue (p.1 * p.2) / (Real.sqrt (qsN (p.1 * p.2)) : ℂ) := by
            exact congrArg (fun x => χ.idealValue x / (Real.sqrt (qsN x) : ℂ)) hprod
      _ = (χ.idealValue p.2 / (Real.sqrt (qsN p.2) : ℂ)) *
          (χ.idealValue p.1 / (Real.sqrt (qsN p.1) : ℂ)) :=
            qsC1_weightMul χ p.1 p.2 hh0 ht0
  simpa [A, D, i, j] using
    (Finset.sum_bij' i j hi hj hleft hright hweight)

theorem qsC1_cancelSum (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (q : Ideal (𝓞 K)) (κ : ℝ) (hq : Squarefree q)
    (hχ : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → P ∣ q → χ.idealValue P ^ 2 = 1) :
    (∑ e ∈ qsDivisors q,
        (qsMu e : ℂ) * χ.idealValue e / (Real.sqrt (qsN e) : ℂ)) *
        (∑ a ∈ qsSqfUpTo κ ⊤,
          χ.idealValue a / (Real.sqrt (qsN a) : ℂ)) -
      (qsPhiRatio q : ℂ) *
        (∑ h ∈ qsSqfUpTo κ q,
          χ.idealValue h / (Real.sqrt (qsN h) : ℂ)) =
      - (∑ e ∈ qsDivisors q,
          (qsMu e : ℂ) * χ.idealValue e / (Real.sqrt (qsN e) : ℂ)) *
        ∑ t ∈ qsDivisors q,
          χ.idealValue t / (Real.sqrt (qsN t) : ℂ) *
            ∑ h ∈ (qsSqfUpTo κ q).filter (fun h => κ / qsN t < qsN h),
              χ.idealValue h / (Real.sqrt (qsN h) : ℂ) := by
  classical
  let H : Finset (Ideal (𝓞 K)) := qsSqfUpTo κ q
  let T : Finset (Ideal (𝓞 K)) := qsDivisors q
  let D : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) := qsC1PairDomain κ q
  let wt : Ideal (𝓞 K) → ℂ := fun a => χ.idealValue a / (Real.sqrt (qsN a) : ℂ)
  let pw : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ := fun p => wt p.2 * wt p.1
  let E : ℂ := ∑ e ∈ T,
    (qsMu e : ℂ) * χ.idealValue e / (Real.sqrt (qsN e) : ℂ)
  let U : ℂ := ∑ t ∈ T, wt t
  let V : ℂ := ∑ h ∈ H, wt h
  let B : ℂ := ∑ t ∈ T, wt t *
    ∑ h ∈ H.filter (fun h => κ / qsN t < qsN h), wt h
  have heuler := qs_local_signed_identity_C0 χ q hq hχ
  have heuler' : U * E = (qsPhiRatio q : ℂ) := by
    simpa [U, E, wt, T] using heuler
  have hmain := qsC1_mainSum_reindex χ q κ hq
  have hmain' :
      (∑ a ∈ qsSqfUpTo κ ⊤, wt a) = ∑ p ∈ D, pw p := by
    simpa [D, wt, pw] using hmain
  have hprod : U * V = ∑ p ∈ H ×ˢ T, pw p := by
    calc
      U * V = V * U := mul_comm _ _
      _ = ∑ h ∈ H, wt h * U := by
        simp [U, V, Finset.sum_mul]
      _ = ∑ h ∈ H, ∑ t ∈ T, wt h * wt t := by
        apply Finset.sum_congr rfl
        intro h hh
        simp [U, Finset.mul_sum]
      _ = ∑ p ∈ H ×ˢ T, wt p.1 * wt p.2 := by
        rw [Finset.sum_product]
      _ = ∑ p ∈ H ×ˢ T, pw p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [pw, wt, mul_comm]
  have hpart : ∑ p ∈ H ×ˢ T, pw p =
      (∑ p ∈ D, pw p) +
        ∑ p ∈ (H ×ˢ T).filter (fun p => ¬ qsN p.1 * qsN p.2 ≤ κ), pw p := by
    dsimp [D, qsC1PairDomain, H, T, pw]
    exact (Finset.sum_filter_add_sum_filter_not
      (qsSqfUpTo κ q ×ˢ qsDivisors q)
      (fun p => qsN p.1 * qsN p.2 ≤ κ)
      (fun p => (fun a => χ.idealValue a / (Real.sqrt (qsN a) : ℂ)) p.2 *
        (fun a => χ.idealValue a / (Real.sqrt (qsN a) : ℂ)) p.1)).symm
  have hfilters :
      (H ×ˢ T).filter (fun p => ¬ qsN p.1 * qsN p.2 ≤ κ) =
        (H ×ˢ T).filter (fun p => κ / qsN p.2 < qsN p.1) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hnot⟩
      rcases Finset.mem_product.mp hp with ⟨hh, ht⟩
      have htq : p.2 ∣ q := (Finset.mem_filter.mp ht).2
      have ht0 : p.2 ≠ ⊥ := (qsC1_sqfOfDvd hq htq).ne_zero
      have hpos := qsC1_normPos ht0
      refine ⟨hp, ?_⟩
      apply (div_lt_iff₀ hpos).2
      exact lt_of_not_ge hnot
    · rintro ⟨hp, hlt⟩
      rcases Finset.mem_product.mp hp with ⟨hh, ht⟩
      have htq : p.2 ∣ q := (Finset.mem_filter.mp ht).2
      have ht0 : p.2 ≠ ⊥ := (qsC1_sqfOfDvd hq htq).ne_zero
      have hpos := qsC1_normPos ht0
      have hmul : κ < qsN p.1 * qsN p.2 := (div_lt_iff₀ hpos).1 hlt
      exact ⟨hp, not_le.mpr hmul⟩
  have htail :
      (∑ p ∈ (H ×ˢ T).filter (fun p => κ / qsN p.2 < qsN p.1), pw p) = B := by
    calc
      _ = ∑ p ∈ H ×ˢ T,
          if κ / qsN p.2 < qsN p.1 then pw p else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ t ∈ T, ∑ h ∈ H,
          if κ / qsN t < qsN h then wt t * wt h else 0 := by
            rw [Finset.sum_product, Finset.sum_comm]
      _ = B := by
            dsimp [B, wt, H, T]
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.sum_filter, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro h hh
            by_cases hcut : κ / qsN t < qsN h <;> simp [hcut, mul_comm]
  have hdiff : U * V - (∑ a ∈ qsSqfUpTo κ ⊤, wt a) = B := by
    calc
      U * V - (∑ a ∈ qsSqfUpTo κ ⊤, wt a) =
          (∑ p ∈ H ×ˢ T, pw p) - (∑ p ∈ D, pw p) := by
            rw [hprod, hmain']
      _ = (∑ p ∈ (H ×ˢ T).filter
            (fun p => ¬ qsN p.1 * qsN p.2 ≤ κ), pw p) := by
            rw [hpart]
            ring
      _ = B := by rw [hfilters, htail]
  calc
    E * (∑ a ∈ qsSqfUpTo κ ⊤, wt a) -
        (qsPhiRatio q : ℂ) * V =
      E * (∑ a ∈ qsSqfUpTo κ ⊤, wt a) - E * (U * V) := by
        rw [← heuler']
        ring
    _ = -E * (U * V - (∑ a ∈ qsSqfUpTo κ ⊤, wt a)) := by ring
    _ = -E * B := by rw [hdiff]
    _ = _ := by simp [E, B, U, V, wt, H, T]

private theorem qsC1_primeOfIsPrime (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Prime P := by
  refine ⟨hP0, ?_, ?_⟩
  · intro hunit
    exact hP.ne_top (Ideal.isUnit_iff.mp hunit)
  · intro I J hdiv
    have hle : I * J ≤ P := Ideal.dvd_iff_le.mp hdiv
    rcases hP.mul_le.mp hle with hI | hJ
    · exact Or.inl (Ideal.dvd_iff_le.mpr hI)
    · exact Or.inr (Ideal.dvd_iff_le.mpr hJ)

private theorem qsC1_idealValuePrime (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    χ.idealValue P = χ.primeValue ⟨P, hP, hP0⟩ := by
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
    (qsC1_primeOfIsPrime P hP hP0).irreducible]
  simp [normalize_eq, hP, hP0]

private theorem qsC1_notDvdOfCoprime (P I : Ideal (𝓞 K))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hcop : IsCoprime P I) : ¬ P ∣ I := by
  intro hPI
  have hle : I ≤ P := Ideal.dvd_iff_le.mp hPI
  have htop : ⊤ ≤ P := by
    calc
      ⊤ = P ⊔ I := hcop.sup_eq.symm
      _ ≤ P := sup_le le_rfl hle
  exact hP.ne_top (le_antisymm le_top htop)

private theorem qsC1_unramOutsideConductor (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (f : Ideal (𝓞 K)) (hf0 : f ≠ ⊥) (hcond : χ.ConductorDvd f)
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hnot : ¬ P ∣ f) :
    χ.UnramifiedAt ⟨P, hP, hP0⟩ := by
  let v : ArtinPrimitiveRoots.A1.FinPlace K := ⟨P, hP, hP0⟩
  have hPrime := qsC1_primeOfIsPrime P hP hP0
  have hexp0 : ArtinPrimitiveRoots.A1.idealExp v f = 0 := by
    dsimp [ArtinPrimitiveRoots.A1.idealExp]
    by_contra hne
    exact hnot ((Associates.count_ne_zero_iff_dvd hf0 hPrime.irreducible).mp hne)
  intro u hu huinv
  have hsub : (u : v.adicCompletion K) - 1 ∈ v.adicCompletionIntegers K := by
    exact (v.adicCompletionIntegers K).sub_mem hu (v.adicCompletionIntegers K).one_mem
  have hbound : Valued.v ((u : v.adicCompletion K) - 1) ≤ 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hsub
    exact hsub
  apply hcond v u hu huinv
  simpa [hexp0] using hbound

private theorem qsC1_idealValue_sq_one_of_unramified
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f P : Ideal (𝓞 K))
    (hχsq : χ * χ = 1) (hf0 : f ≠ ⊥) (hcond : χ.ConductorDvd f)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPcop : IsCoprime P f) :
    χ.idealValue P ^ 2 = 1 := by
  let v : ArtinPrimitiveRoots.A1.FinPlace K := ⟨P, hP, hP0⟩
  let u₀ := ArtinPrimitiveRoots.A1.toLoc v
    (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v))
  have hnot := qsC1_notDvdOfCoprime P f hP hP0 hPcop
  have hU := qsC1_unramOutsideConductor χ f hf0 hcond P hP hP0 hnot
  have hloc : χ.loc v u₀ * χ.loc v u₀ = 1 := by
    have hmul : (χ * χ).loc v u₀ = χ.loc v u₀ * χ.loc v u₀ := by
      simp [ArtinPrimitiveRoots.A1.HeckeChar.loc]
    have heq := congrArg (fun θ : ArtinPrimitiveRoots.A1.HeckeChar K => θ.loc v u₀) hχsq
    rw [hmul] at heq
    simpa [ArtinPrimitiveRoots.A1.HeckeChar.loc] using heq
  have hpv : χ.primeValue v = ((χ.loc v u₀ : ℂˣ) : ℂ) := by
    rw [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, if_pos hU]
  have hval : ((χ.loc v u₀ : ℂˣ) : ℂ) ^ 2 = 1 := by
    have h := congrArg (fun x : ℂˣ => (x : ℂ)) hloc
    simpa [pow_two] using h
  calc
    χ.idealValue P ^ 2 = χ.primeValue v ^ 2 := by
      rw [qsC1_idealValuePrime χ P hP hP0]
    _ = 1 := by rw [hpv]; exact hval

variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

private theorem qsC1_pairChar_sq (F : QSFamily m qS)
    (c d : Ideal (𝓞 K)) (hc : QSAdm m qS c) (hd : QSAdm m qS d) :
    qsPairChar F c d * qsPairChar F c d = 1 := by
  let C := F.character c
  let D := F.character d
  have hDinv : D⁻¹ = D := by
    ext x
    have hsqx : D x ^ 2 = 1 := by
      simpa [D] using congrArg (fun ξ : ArtinPrimitiveRoots.A1.HeckeChar K => ξ x)
        (F.character_order_two d hd.1 hd.2.1)
    have hx : (D x)⁻¹ = D x := by
      calc
        (D x)⁻¹ = (D x)⁻¹ * (D x) ^ 2 := by rw [hsqx]; simp
        _ = D x := by group
    exact congrArg (fun u : ℂˣ => (u : ℂ)) hx
  have hC2 : C * C = 1 := by
    simpa [C, pow_two] using F.character_order_two c hc.1 hc.2.1
  have hD2 : D * D = 1 := by
    simpa [D, pow_two] using F.character_order_two d hd.1 hd.2.1
  have hpair : qsPairChar F c d = C * D := by
    simp [qsPairChar, C, D, hDinv]
  have hcomm : C * D = D * C := by
    ext x
    simp [mul_comm]
  rw [hpair]
  calc
    (C * D) * (C * D) = (C * C) * (D * D) := by
      calc
        (C * D) * (C * D) = C * (D * (C * D)) := mul_assoc C D (C * D)
        _ = C * ((D * C) * D) :=
          congrArg (fun x => C * x) (mul_assoc D C D).symm
        _ = C * ((C * D) * D) := congrArg (fun x => C * (x * D)) hcomm.symm
        _ = C * (C * (D * D)) := congrArg (fun x => C * x) (mul_assoc C D D)
        _ = (C * C) * (D * D) := (mul_assoc C C (D * D)).symm
    _ = 1 := by
      calc
        (C * C) * (D * D) = 1 * (D * D) := congrArg (fun x => x * (D * D)) hC2
        _ = D * D := by
          ext x
          simp
        _ = 1 := hD2

private theorem qsC1_notCommonDvd (P I J : Ideal (𝓞 K))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hIJ : IsCoprime I J)
    (hPI : P ∣ I) (hPJ : P ∣ J) : False := by
  have hle : I ⊔ J ≤ P :=
    sup_le (Ideal.dvd_iff_le.mp hPI) (Ideal.dvd_iff_le.mp hPJ)
  have htop : ⊤ ≤ P := by
    calc
      ⊤ = I ⊔ J := hIJ.sup_eq.symm
      _ ≤ P := hle
  exact hP.ne_top (le_antisymm le_top htop)

theorem qsC1_pair_value_sq_one_at_q
    (F : QSFamily m qS) (c d q P : Ideal (𝓞 K))
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hcq : IsCoprime c q) (hdq : IsCoprime d q)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPq : P ∣ q) :
    (qsPairChar F c d).idealValue P ^ 2 = 1 := by
  have hPc : ¬ P ∣ c := by
    intro hPc
    exact qsC1_notCommonDvd P c q hP hP0 hcq hPc hPq
  have hPd : ¬ P ∣ d := by
    intro hPd
    exact qsC1_notCommonDvd P d q hP hP0 hdq hPd hPq
  have hPcd : ¬ P ∣ c * d := by
    intro hPcd
    have hle : c * d ≤ P := Ideal.dvd_iff_le.mp hPcd
    rcases hP.mul_le.mp hle with hc' | hd'
    · exact hPc (Ideal.dvd_iff_le.mpr hc')
    · exact hPd (Ideal.dvd_iff_le.mpr hd')
  rcases hcl with ⟨hc', hd', hclass⟩
  have hprim := F.equalClass_product_conductor c d hc.1 hc' hd.1 hd' hcd hclass
  have hPcop : IsCoprime P (c * d) :=
    qsC1PrimeCoprimeOfNotDvd P (c * d) hP hP0 hPcd
  exact qsC1_idealValue_sq_one_of_unramified (qsPairChar F c d) (c * d) P
    (qsC1_pairChar_sq F c d hc hd) (mul_ne_zero hc.1.ne_zero hd.1.ne_zero)
    hprim.2.1 hP hP0 hPcop

end ArtinPrimitiveRoots.A2
