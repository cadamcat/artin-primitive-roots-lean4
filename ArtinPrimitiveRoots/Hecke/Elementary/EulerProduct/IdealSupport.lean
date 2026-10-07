/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

The Dedekind-ideal support lemmas below are adapted from
`TauCeti/RingTheory/DedekindDomain/Ideal.lean` (Apache-2.0).
-/
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Basic

public section

open _root_.IsDedekindDomain
open scoped nonZeroDivisors NumberField

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- An ideal is prime to a set of height-one primes if it is nonzero and no prime in the set
divides it. -/
def IsPrimeTo (I : Ideal R) (S : Set (HeightOneSpectrum R)) : Prop :=
  I ≠ ⊥ ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I

variable {I J : Ideal R} {S T : Set (HeightOneSpectrum R)}

theorem isPrimeTo_iff : IsPrimeTo I S ↔ I ≠ ⊥ ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I := Iff.rfl

theorem IsPrimeTo.ne_bot (h : IsPrimeTo I S) : I ≠ ⊥ := h.1

theorem IsPrimeTo.not_dvd (h : IsPrimeTo I S) {𝔭 : HeightOneSpectrum R} (h𝔭 : 𝔭 ∈ S) :
    ¬ 𝔭.asIdeal ∣ I := h.2 𝔭 h𝔭

@[simp]
theorem not_isPrimeTo_bot : ¬ IsPrimeTo (⊥ : Ideal R) S := fun h ↦ h.ne_bot rfl

@[simp]
theorem isPrimeTo_empty : IsPrimeTo I ∅ ↔ I ≠ ⊥ := by
  rw [isPrimeTo_iff]
  simp

@[simp]
theorem isPrimeTo_top : IsPrimeTo (⊤ : Ideal R) S := by
  refine ⟨top_ne_bot, fun 𝔭 _ hdvd ↦ 𝔭.prime.not_isUnit ?_⟩
  exact isUnit_of_dvd_one (by simpa [Ideal.one_eq_top] using hdvd)

theorem IsPrimeTo.mono (hST : S ⊆ T) (h : IsPrimeTo I T) : IsPrimeTo I S :=
  ⟨h.ne_bot, fun _𝔭 h𝔭 ↦ h.not_dvd (hST h𝔭)⟩

@[simp]
theorem isPrimeTo_insert_iff {𝔭 : HeightOneSpectrum R} :
    IsPrimeTo I (insert 𝔭 S) ↔ IsPrimeTo I S ∧ ¬ 𝔭.asIdeal ∣ I := by
  simp only [isPrimeTo_iff, Set.forall_mem_insert]
  tauto

@[simp]
theorem isPrimeTo_mul_iff : IsPrimeTo (I * J) S ↔ IsPrimeTo I S ∧ IsPrimeTo J S := by
  simp only [IsPrimeTo, ne_eq, Ideal.mul_eq_bot, not_or]
  refine ⟨fun ⟨h0, h⟩ ↦ ⟨⟨h0.1, fun 𝔭 h𝔭 hdvd ↦ h 𝔭 h𝔭 (hdvd.mul_right _)⟩,
    ⟨h0.2, fun 𝔭 h𝔭 hdvd ↦ h 𝔭 h𝔭 (hdvd.mul_left _)⟩⟩,
    fun ⟨hI, hJ⟩ ↦ ⟨⟨hI.1, hJ.1⟩, ?_⟩⟩
  intro 𝔭 h𝔭 hdvd
  rcases 𝔭.prime.dvd_mul.mp hdvd with h | h
  · exact hI.2 𝔭 h𝔭 h
  · exact hJ.2 𝔭 h𝔭 h

@[simp]
theorem isPrimeTo_asIdeal_iff {𝔭 : HeightOneSpectrum R} :
    IsPrimeTo 𝔭.asIdeal S ↔ 𝔭 ∉ S := by
  refine ⟨fun h h𝔭 ↦ h.not_dvd h𝔭 dvd_rfl, fun h𝔭 ↦ ⟨𝔭.ne_bot, fun 𝔮 h𝔮 hdvd ↦ h𝔭 ?_⟩⟩
  exact HeightOneSpectrum.asIdeal_injective
    ((prime_dvd_prime_iff_eq 𝔮.prime 𝔭.prime).mp hdvd) ▸ h𝔮

@[elab_as_elim]
theorem IsPrimeTo.induction_on {motive : Ideal R → Prop} (h : IsPrimeTo I S)
    (top : motive ⊤)
    (mul_prime : ∀ (𝔭 : HeightOneSpectrum R) (J : Ideal R), 𝔭 ∉ S →
      IsPrimeTo J S → motive J → motive (𝔭.asIdeal * J)) :
    motive I := by
  revert h
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h ↦ absurd rfl h.ne_bot
  | h₂ x hx => exact fun _ ↦ (Ideal.isUnit_iff.mp hx) ▸ top
  | h₃ J p _ hp ih =>
      intro hprime
      have hJ : IsPrimeTo J S := (isPrimeTo_mul_iff.mp hprime).2
      have hbad : HeightOneSpectrum.ofPrime hp ∉ S :=
        fun h ↦ hprime.2 _ h (dvd_mul_right p J)
      exact mul_prime (HeightOneSpectrum.ofPrime hp) J hbad hJ (ih hJ)

theorem IsPrimeTo.pow (h : IsPrimeTo I S) (n : ℕ) : IsPrimeTo (I ^ n) S := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact isPrimeTo_mul_iff.mpr ⟨ih, h⟩

@[simp]
theorem isPrimeTo_pow_iff {n : ℕ} (hn : n ≠ 0) : IsPrimeTo (I ^ n) S ↔ IsPrimeTo I S := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pow n⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ] at h
  exact (isPrimeTo_mul_iff.mp h).2

@[simp]
theorem isPrimeTo_prod_iff {ι : Type*} {t : Finset ι} {I : ι → Ideal R} :
    IsPrimeTo (∏ i ∈ t, I i) S ↔ ∀ i ∈ t, IsPrimeTo (I i) S := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, isPrimeTo_mul_iff, ih, Finset.forall_mem_insert]

@[simp]
theorem isPrimeTo_univ_iff : IsPrimeTo I Set.univ ↔ I = ⊤ := by
  refine ⟨fun h ↦ h.induction_on rfl fun 𝔭 _ h𝔭 _ _ ↦ absurd (Set.mem_univ 𝔭) h𝔭, ?_⟩
  rintro rfl
  exact isPrimeTo_top

theorem isPrimeTo_compl_singleton_iff {𝔭 : HeightOneSpectrum R} :
    IsPrimeTo I {𝔭}ᶜ ↔ ∃ n : ℕ, I = 𝔭.asIdeal ^ n := by
  constructor
  · intro h
    refine h.induction_on ⟨0, by simp⟩ ?_
    rintro 𝔮 J h𝔮 - ⟨n, rfl⟩
    rw [Set.notMem_compl_iff, Set.mem_singleton_iff] at h𝔮
    exact ⟨n + 1, by rw [h𝔮, pow_succ']⟩
  · rintro ⟨n, rfl⟩
    exact (isPrimeTo_asIdeal_iff.mpr (by simp)).pow n

theorem IsPrimeTo.isRelPrime (hI : IsPrimeTo I S) (hJ : IsPrimeTo J Sᶜ) : IsRelPrime I J := by
  refine (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors
    (by simpa using hI.ne_bot)).mpr fun d hdI hdJ hd ↦ ?_
  have h𝔭 : HeightOneSpectrum.ofPrime hd ∉ Sᶜ := fun h ↦ hJ.not_dvd h hdJ
  exact hI.not_dvd (Set.notMem_compl_iff.mp h𝔭) hdI

/-- Every nonzero ideal is a finite product of powers of height-one primes. -/
theorem exists_eq_prod_pow (hI : I ≠ ⊥) :
    ∃ (S : Finset (HeightOneSpectrum R)) (e : HeightOneSpectrum R → ℕ),
      I = ∏ 𝔭 ∈ S, 𝔭.asIdeal ^ e 𝔭 := by
  classical
  have hI0 : I ≠ 0 := by simpa using hI
  have hfin : (Function.mulSupport fun 𝔭 : HeightOneSpectrum R ↦
      𝔭.asIdeal ^ (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors).Finite :=
    Ideal.hasFiniteMulSupport hI0
  have hprod := finprod_eq_finsetProd_of_mulSupport_subset
    (fun 𝔭 : HeightOneSpectrum R ↦
      𝔭.asIdeal ^ (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors)
    (s := hfin.toFinset) (by simp)
  exact ⟨hfin.toFinset, fun 𝔭 ↦ (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors,
    by rw [← hprod]; exact (Ideal.finprod_heightOneSpectrum_factorization hI0).symm⟩

theorem IsPrimeTo.exists_eq_pow_mul {𝔭 : HeightOneSpectrum R} (h : IsPrimeTo I (insert 𝔭 S)ᶜ) :
    ∃ (n : ℕ) (J : Ideal R), IsPrimeTo J Sᶜ ∧ I = 𝔭.asIdeal ^ n * J := by
  have hmax := 𝔭.isMaximal
  obtain ⟨Q, hQsup, heq⟩ := Ideal.eq_prime_pow_mul_coprime h.ne_bot 𝔭.asIdeal
  refine ⟨_, Q, ⟨fun hQ ↦ h.ne_bot (by rw [heq, hQ, Ideal.mul_bot]),
    fun 𝔮 h𝔮 hdvd ↦ ?_⟩, heq⟩
  refine h.not_dvd ?_ (by rw [heq]; exact hdvd.mul_left _)
  rw [Set.mem_compl_iff, Set.mem_insert_iff]
  rintro (rfl | h𝔮')
  · exact hmax.ne_top (by rwa [sup_eq_left.mpr (Ideal.le_of_dvd hdvd)] at hQsup)
  · exact h𝔮 h𝔮'

private theorem multiplicity_pow_mul {p J : Ideal R} (hp : p ≠ ⊥) (hJ : ¬ p ∣ J) (n : ℕ) :
    multiplicity p (p ^ n * J) = n := by
  refine multiplicity_eq_of_dvd_of_not_dvd (Dvd.intro _ rfl) fun hdvd ↦ hJ ?_
  rw [pow_succ] at hdvd
  exact (mul_dvd_mul_iff_left (pow_ne_zero n (by simpa using hp))).mp hdvd

theorem eq_and_eq_of_pow_mul_eq_pow_mul {p : Ideal R} (hp : p ≠ ⊥) {m n : ℕ}
    {I J : Ideal R} (hI : ¬ p ∣ I) (hJ : ¬ p ∣ J)
    (h : p ^ m * I = p ^ n * J) : m = n ∧ I = J := by
  have hmn : m = n := by
    have hm := multiplicity_pow_mul hp hI m
    rw [h, multiplicity_pow_mul hp hJ n] at hm
    exact hm.symm
  refine ⟨hmn, ?_⟩
  subst hmn
  exact mul_left_cancel₀ (pow_ne_zero _ (by simpa using hp)) h

end Ideal

/-! A finite set containing every prime divisor of an ideal eventually supports that ideal. -/
theorem eventually_isPrimeTo_compl {K : Type*} [Field K] [NumberField K]
    (A : (Ideal (𝓞 K))⁰) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (S : Set (HeightOneSpectrum (𝓞 K)))ᶜ := by
  classical
  let F := Ideal.finite_factors (nonZeroDivisors.coe_ne_zero A)
  let T : Finset (HeightOneSpectrum (𝓞 K)) := F.toFinset
  filter_upwards [Filter.eventually_ge_atTop T] with S hTS
  rw [Ideal.isPrimeTo_iff]
  refine ⟨nonZeroDivisors.coe_ne_zero A, fun P hP hPdvd ↦ hP ?_⟩
  exact hTS (F.mem_toFinset.mpr hPdvd)

end
