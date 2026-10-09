import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.c4.RoughPairResidues

namespace ArtinPrimitiveRoots.Construction.Proofs.C_BINS

open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.TypeII

private theorem localSieveDensity_prime_eq (M r p : ℕ) (hp : p.Prime) :
    localSieveDensity M r p =
      if Nat.Coprime p (M * r) then 1 / ((p : ℝ) - 1) else 0 := by
  by_cases hcop : Nat.Coprime p (M * r)
  · simp [localSieveDensity, Nat.totient_prime hp,
      Nat.cast_sub hp.one_le]
  · simp [localSieveDensity, hcop]

theorem localSieveDensity_prime_bounds (M r p : ℕ) (hp : p.Prime)
    (hp3 : 3 ≤ p) :
    0 ≤ localSieveDensity M r p ∧ localSieveDensity M r p ≤ 1 / 2 ∧
      localSieveDensity M r p ≤ 2 / (p : ℝ) := by
  have hpCast : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpMinus : 0 < (p : ℝ) - 1 := by
    have hpCast3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  have hpCast3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hInvHalf : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hpMinus (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  have hInvTwoOver : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
    apply (div_le_div_iff₀ hpMinus hpCast).2
    nlinarith
  by_cases hcop : Nat.Coprime p (M * r)
  · have hEq : localSieveDensity M r p = 1 / ((p : ℝ) - 1) := by
      simp [localSieveDensity, hcop, Nat.totient_prime hp,
        Nat.cast_sub hp.one_le]
    rw [hEq]
    exact ⟨by positivity, hInvHalf, hInvTwoOver⟩
  · rw [localSieveDensity_prime_eq M r p hp]
    simp only [if_neg hcop]
    refine ⟨le_rfl, ?_, ?_⟩
    · norm_num
    · positivity

private theorem prime_dvd_finset_product_iff {p : ℕ} (hp : p.Prime)
    (S : Finset ℕ) :
    p ∣ (∏ q ∈ S, q) ↔ ∃ q ∈ S, p ∣ q := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hp.ne_one
  | @insert q S hq ih =>
    rw [Finset.prod_insert hq, hp.dvd_mul, ih]
    simp

theorem prime_subset_product_injective (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    ∀ D E : Finset ℕ, D ⊆ P → E ⊆ P →
      (∏ p ∈ D, p) = (∏ p ∈ E, p) → D = E := by
  classical
  intro D E hDP hEP hprod
  apply Finset.ext
  intro p
  constructor
  · intro hpD
    have hpP := hDP hpD
    have hpPrim := hprime p hpP
    have hpDivD : p ∣ ∏ q ∈ D, q :=
      (prime_dvd_finset_product_iff hpPrim D).2 ⟨p, hpD, dvd_rfl⟩
    have hpDivE : p ∣ ∏ q ∈ E, q := by
      rw [← hprod]
      exact hpDivD
    obtain ⟨q, hqE, hpq⟩ := (prime_dvd_finset_product_iff hpPrim E).mp hpDivE
    have hqPrim := hprime q (hEP hqE)
    have hpqEq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpPrim hqPrim).mp hpq
    exact hpqEq ▸ hqE
  · intro hpE
    have hpP := hEP hpE
    have hpPrim := hprime p hpP
    have hpDivE : p ∣ ∏ q ∈ E, q :=
      (prime_dvd_finset_product_iff hpPrim E).2 ⟨p, hpE, dvd_rfl⟩
    have hpDivD : p ∣ ∏ q ∈ D, q := by
      rw [hprod]
      exact hpDivE
    obtain ⟨q, hqD, hpq⟩ := (prime_dvd_finset_product_iff hpPrim D).mp hpDivD
    have hqPrim := hprime q (hDP hqD)
    have hpqEq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpPrim hqPrim).mp hpq
    exact hpqEq ▸ hqD

theorem primeSubset_product_dvd_iff (P D : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hD : D ⊆ P) (d : ℕ) :
    (∏ p ∈ D, p) ∣ d ↔ ∀ p ∈ D, p ∣ d := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert p D hpnot ih =>
    have hp := hprime p (hD (Finset.mem_insert_self p D))
    have hprimeD : ∀ q ∈ D, q.Prime := by
      intro q hq
      exact hprime q (hD (Finset.mem_insert_of_mem hq))
    have hDsub : D ⊆ P := fun q hq => hD (Finset.mem_insert_of_mem hq)
    let ell : ℕ := ∏ q ∈ D, q
    have hpnotdiv : ¬ p ∣ ell := by
      dsimp [ell]
      intro hpdiv
      obtain ⟨q, hq, hpqdiv⟩ := (prime_dvd_finset_product_iff hp D).mp hpdiv
      have hpq : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp (hprimeD q hq)).mp hpqdiv
      exact hpnot (hpq ▸ hq)
    have hcop : Nat.Coprime p ell := hp.coprime_iff_not_dvd.mpr hpnotdiv
    rw [Finset.prod_insert hpnot]
    constructor
    · intro hdiv q hq
      rcases Finset.mem_insert.mp hq with rfl | hqD
      · exact (dvd_mul_of_dvd_left (dvd_rfl : q ∣ q) ell).trans hdiv
      · have hEllDiv : ell ∣ d :=
          (dvd_mul_of_dvd_right (dvd_rfl : ell ∣ ell) p).trans hdiv
        exact (ih hDsub).mp hEllDiv q hqD
    · intro hall
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
      · exact hall p (Finset.mem_insert_self p D)
      · apply (ih hDsub).mpr
        intro q hq
        exact hall q (Finset.mem_insert_of_mem hq)

theorem primeProduct_odd_squarefree (D : Finset ℕ)
    (hprime : ∀ p ∈ D, p.Prime ∧ 3 ≤ p) :
    Odd (∏ p ∈ D, p) ∧ Squarefree (∏ p ∈ D, p) := by
  classical
  constructor
  · induction D using Finset.induction_on with
    | empty => simp
    | @insert p D hpnot ih =>
      have hp := (hprime p (Finset.mem_insert_self p D)).1
      have hp3 := (hprime p (Finset.mem_insert_self p D)).2
      have hprimeD : ∀ q ∈ D, q.Prime ∧ 3 ≤ q := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hpnot]
      exact (hp.odd_iff.mpr hp3).mul (ih hprimeD)
  · refine Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => ?_) (fun p hp => (hprime p hp).1.squarefree)
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprime p hp).1 (hprime q hq).1).mpr hpq

theorem localSieveDensity_product_of_primes (M r : ℕ) (D : Finset ℕ)
    (hprime : ∀ p ∈ D, p.Prime ∧ 3 ≤ p) :
    (∏ p ∈ D, localSieveDensity M r p) =
      localSieveDensity M r (∏ p ∈ D, p) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [localSieveDensity]
  | @insert p D hpnot ih =>
    have hp := (hprime p (Finset.mem_insert_self p D)).1
    have hp3 := (hprime p (Finset.mem_insert_self p D)).2
    have hprimeD : ∀ q ∈ D, q.Prime ∧ 3 ≤ q := by
      intro q hq
      exact hprime q (Finset.mem_insert_of_mem hq)
    by_cases hgood : ∀ q ∈ insert p D, Nat.Coprime q (M * r)
    · have hGoodP := hgood p (Finset.mem_insert_self p D)
      have hGoodD : ∀ q ∈ D, Nat.Coprime q (M * r) := by
        intro q hq
        exact hgood q (Finset.mem_insert_of_mem hq)
      let ell : ℕ := ∏ q ∈ D, q
      have hellpos : 0 < ell := by
        dsimp [ell]
        apply Finset.prod_pos
        intro q hq
        exact (hprimeD q hq).1.pos
      have hCopEll : Nat.Coprime ell (M * r) := by
        dsimp [ell]
        exact (Nat.coprime_prod_left_iff).2 hGoodD
      have hpnotdiv : ¬ p ∣ ell := by
        dsimp [ell]
        intro hpdiv
        obtain ⟨q, hq, hpqdiv⟩ := (prime_dvd_finset_product_iff hp D).mp hpdiv
        have hpq : p = q :=
          (Nat.prime_dvd_prime_iff_eq hp (hprimeD q hq).1).mp hpqdiv
        exact hpnot (hpq ▸ hq)
      have hCopPEll : Nat.Coprime p ell := hp.coprime_iff_not_dvd.mpr hpnotdiv
      have hCopProd : Nat.Coprime (p * ell) (M * r) :=
        Nat.Coprime.mul_left hGoodP hCopEll
      have hTotPos : 0 < (Nat.totient ell : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hellpos
      have hpMinusPos : 0 < (p : ℝ) - 1 := by
        have hpCast3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
        linarith
      have hleft : localSieveDensity M r ell =
          1 / (Nat.totient ell : ℝ) := by
        simp [localSieveDensity, hCopEll]
      have hright : localSieveDensity M r (p * ell) =
          1 / (Nat.totient (p * ell) : ℝ) := by
        simp [localSieveDensity, hCopProd]
      have hmulDensity :
          localSieveDensity M r p * localSieveDensity M r ell =
            localSieveDensity M r (p * ell) := by
        rw [localSieveDensity_prime_eq M r p hp]
        simp only [if_pos hGoodP]
        rw [hleft, hright]
        rw [Nat.totient_mul hCopPEll, Nat.totient_prime hp]
        have hcast : (((p - 1) * Nat.totient ell : ℕ) : ℝ) =
            ((p : ℝ) - 1) * (Nat.totient ell : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_sub hp.one_le]
          simp
        rw [hcast]
        field_simp [ne_of_gt hpMinusPos, ne_of_gt hTotPos]
      calc
        (∏ q ∈ insert p D, localSieveDensity M r q) =
            localSieveDensity M r p * ∏ q ∈ D, localSieveDensity M r q :=
              Finset.prod_insert hpnot
        _ = localSieveDensity M r p * localSieveDensity M r ell := by
              rw [ih hprimeD]
        _ = localSieveDensity M r (p * ell) := hmulDensity
        _ = localSieveDensity M r (∏ q ∈ insert p D, q) := by
              rw [Finset.prod_insert hpnot]
    · push_neg at hgood
      obtain ⟨q, hqMem, hqBad⟩ := hgood
      have hqprime := (hprime q hqMem).1
      have hqzero : localSieveDensity M r q = 0 := by
        rw [localSieveDensity_prime_eq M r q hqprime]
        simp [hqBad]
      have hprodZero :
          (∏ q ∈ insert p D, localSieveDensity M r q) = 0 :=
        Finset.prod_eq_zero hqMem hqzero
      have hnotProdCop :
          ¬ Nat.Coprime (∏ q ∈ insert p D, q) (M * r) := by
        intro hcop
        exact hqBad ((Nat.coprime_prod_left_iff.mp hcop) q hqMem)
      have hlocalZero :
          localSieveDensity M r (∏ q ∈ insert p D, q) = 0 := by
        simp [localSieveDensity, hnotProdCop]
      rw [hprodZero, hlocalZero]

theorem primeSubset_absError_sum_le (B : ℝ) (P : Finset ℕ)
    (T : Finset (Finset ℕ))
    (hprime : ∀ p ∈ P, p.Prime) (hsubset : ∀ D ∈ T, D ⊆ P)
    (himage : ∀ D ∈ T, (∏ p ∈ D, p) ∈ oddSquarefreeUpTo B)
    (e : ℕ → ℝ) :
    (∑ D ∈ T, |e (∏ p ∈ D, p)|) ≤
      ∑ ℓ ∈ oddSquarefreeUpTo B, |e ℓ| := by
  classical
  let product : Finset ℕ → ℕ := fun D => ∏ p ∈ D, p
  let image := T.image product
  have hInj : Set.InjOn product T := by
    intro D hD E hE hDE
    exact prime_subset_product_injective P hprime D E (hsubset D hD)
      (hsubset E hE) hDE
  have hImageSub : image ⊆ oddSquarefreeUpTo B := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨D, hD, rfl⟩
    exact himage D hD
  calc
    (∑ D ∈ T, |e (∏ p ∈ D, p)|) =
        ∑ ℓ ∈ image, |e ℓ| := by
          simpa [image, product] using
            (Finset.sum_image (f := fun ℓ : ℕ => |e ℓ|)
              (g := product) hInj).symm
    _ ≤ ∑ ℓ ∈ oddSquarefreeUpTo B, |e ℓ| :=
      Finset.sum_le_sum_of_subset_of_nonneg hImageSub
        (fun ℓ _ _ => abs_nonneg _)

theorem exists_localSieveBlockBound :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
        ∀ v : ℝ, 1 < v →
          ∀ r M : ℕ, (∀ p ∈ P, 3 ≤ p) →
            (∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧
                (p : ℝ) ≤ v ^ 2), localSieveDensity M r p) ≤ C₀ := by
  obtain ⟨C, hC, hBlock⟩ :=
    ArtinPrimitiveRoots.Construction.Proofs.C4.exists_reciprocalPrimeBlockBoundForPrimeSet
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro P hprime v hv r M hp3
  calc
    _ ≤ ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧
          (p : ℝ) ≤ v ^ 2), 2 * (1 / (p : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, ⟨_, _⟩⟩
        have hpprime := hprime p hpP
        have hlocal := localSieveDensity_prime_bounds M r p hpprime (hp3 p hpP)
        have hEq : 2 / (p : ℝ) = 2 * (1 / (p : ℝ)) := by ring
        rw [← hEq]
        exact hlocal.2.2
    _ = 2 * ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧
          (p : ℝ) ≤ v ^ 2), 1 / (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * C := mul_le_mul_of_nonneg_left (hBlock P hprime v hv) (by norm_num)

end ArtinPrimitiveRoots.Construction.Proofs.C_BINS
