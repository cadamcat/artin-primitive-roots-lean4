import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».Defs
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1
import ArtinPrimitiveRoots.Hecke.Elementary.EulerProduct.Algebra

/-!
# A2-QS-MOBIUS, part S0: multiplicativity, class/dyad slicing, gcd expansion and descent

Guide: `runs/lanes/sol-thin-found/PROOFS.md:396-408` (S0) and G1 (found:613-615) specialised to
trivial ray factor.  The family identities are derived prime by prime from `reciprocity`
(trivial factor), `idealValue` multiplicativity (`qs_idealValue_mul_M0`) and ramification at the
primitive conductor (`qs_idealValue_eq_zero_of_conductor_M0`); rows are coprime to `m` and `qS`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate nonZeroDivisors
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

private theorem qs_idealUnit_mul_local (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ArtinPrimitiveRoots.Hecke.idealUnit (I * J) (mul_ne_zero hI hJ) =
      ArtinPrimitiveRoots.Hecke.idealUnit I hI * ArtinPrimitiveRoots.Hecke.idealUnit J hJ := by
  apply Units.ext
  simp [ArtinPrimitiveRoots.Hecke.idealUnit, FractionalIdeal.coeIdeal_mul]

private theorem qs_isCoprimeTo_mul_local (I J : Ideal (𝓞 K))
    (hI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I)
    (hJ : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m J) :
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m (I * J) := by
  rcases hI with ⟨hI0, hI⟩
  rcases hJ with ⟨hJ0, hJ⟩
  refine ⟨mul_ne_zero hI0 hJ0, ?_⟩
  rw [qs_idealUnit_mul_local I J hI0 hJ0]
  exact (rayClassPrimeToIdeals m).mul_mem hI hJ

private theorem qs_multiset_prod_ne_bot_local (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ I ∈ s, I ≠ ⊥) : s.prod ≠ ⊥ := by
  apply Multiset.prod_ne_zero
  intro hmem
  exact hs ⊥ hmem rfl

private theorem qs_idealValue_multiset_product_local
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ I ∈ s, I ≠ ⊥) :
    χ.idealValue s.prod = (s.map χ.idealValue).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      change χ.idealValue (1 : Ideal (𝓞 K)) = 1
      unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
      rw [UniqueFactorizationMonoid.normalizedFactors_of_isUnit isUnit_one]
      rfl
  | cons I s ih =>
      have hI := hs I (by simp)
      have hs' : ∀ J ∈ s, J ≠ ⊥ := by
        intro J hJ
        exact hs J (by simp [hJ])
      have hs0 := qs_multiset_prod_ne_bot_local s hs'
      simp only [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
      rw [qs_idealValue_mul_M0 χ I s.prod hI hs0, ih hs']

private theorem qs_isCoprime_factor_local (a P b : Ideal (𝓞 K))
    (haP : a ≤ P) (hab : IsCoprime a b) : IsCoprime P b := by
  rw [Ideal.isCoprime_iff_sup_eq] at hab ⊢
  apply top_unique
  calc
    ⊤ = a ⊔ b := hab.symm
    _ ≤ P ⊔ b := sup_le_sup haP le_rfl

private theorem qs_coprime_of_not_dvd_prime_local (P c : Ideal (𝓞 K))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPc : ¬ P ∣ c) : IsCoprime P c := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
  have hEq : P = P ⊔ c := hmax.eq_of_le htop le_sup_left
  have hle : c ≤ P := by rw [hEq]; exact le_sup_right
  exact hPc (Ideal.dvd_iff_le.mpr hle)

private theorem qs_coprime_mono_right_local (a b c : Ideal (𝓞 K))
    (hab : IsCoprime a b) (hbc : b ≤ c) : IsCoprime a c := by
  rw [Ideal.isCoprime_iff_sup_eq] at hab ⊢
  apply top_unique
  calc
    ⊤ = a ⊔ b := hab.symm
    _ ≤ a ⊔ c := sup_le_sup le_rfl hbc

private theorem qs_not_dvd_of_prime_coprime_local (P f : Ideal (𝓞 K))
    (hP : P.IsPrime) (hPcop : IsCoprime P f) : ¬ P ∣ f := by
  intro hPf
  have hle : f ≤ P := Ideal.dvd_iff_le.mp hPf
  have hsum := hPcop.sup_eq
  have htop : ⊤ ≤ P := by
    calc
      ⊤ = P ⊔ f := hsum.symm
      _ ≤ P := sup_le le_rfl hle
  exact hP.ne_top (le_antisymm le_top htop)

private theorem qs_prime_ideal_prime_local (P : Ideal (𝓞 K))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) : Prime P := by
  refine ⟨hP0, ?_, ?_⟩
  · intro hunit
    exact hP.ne_top (Ideal.isUnit_iff.mp hunit)
  · intro I J hdiv
    have hle : I * J ≤ P := Ideal.dvd_iff_le.mp hdiv
    rcases hP.mul_le.mp hle with hI | hJ
    · exact Or.inl (Ideal.dvd_iff_le.mpr hI)
    · exact Or.inr (Ideal.dvd_iff_le.mpr hJ)

private theorem qs_prime_ideal_squarefree_local (P : Ideal (𝓞 K))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) : Squarefree P :=
  Prime.squarefree (qs_prime_ideal_prime_local P hP hP0)

private theorem qs_idealValue_prime_local
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (P : Ideal (𝓞 K))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    χ.idealValue P = χ.primeValue ⟨P, hP, hP0⟩ := by
  have hPrime := qs_prime_ideal_prime_local P hP hP0
  rw [ArtinPrimitiveRoots.A1.HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hPrime.irreducible]
  have hnorm : normalize P = P := by simp
  simp [hnorm, hP, hP0]

private theorem qs_unramified_outside_conductor_local
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf0 : f ≠ ⊥) (hcond : χ.ConductorDvd f) (v : ArtinPrimitiveRoots.A1.FinPlace K)
    (hnot : ¬ v.asIdeal ∣ f) : χ.UnramifiedAt v := by
  have hPrime := qs_prime_ideal_prime_local v.asIdeal v.isPrime v.ne_bot
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

private theorem qs_primeValue_mul_of_unramified_local
    (χ ψ : ArtinPrimitiveRoots.A1.HeckeChar K) (v : ArtinPrimitiveRoots.A1.FinPlace K)
    (hχ : χ.UnramifiedAt v) (hψ : ψ.UnramifiedAt v) :
    (χ * ψ).primeValue v = χ.primeValue v * ψ.primeValue v := by
  have hprod : (χ * ψ).UnramifiedAt v := by
    intro u hu huinv
    have hχu := hχ u hu huinv
    have hψu := hψ u hu huinv
    have hloc : (χ * ψ).loc v u = χ.loc v u * ψ.loc v u := by
      simp [ArtinPrimitiveRoots.A1.HeckeChar.loc]
    rw [hloc, hχu, hψu]
    simp
  let u₀ := ArtinPrimitiveRoots.A1.toLoc v
    (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v))
  have hloc : (χ * ψ).loc v u₀ = χ.loc v u₀ * ψ.loc v u₀ := by
    simp [ArtinPrimitiveRoots.A1.HeckeChar.loc]
  simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hprod, hχ, hψ, u₀, hloc]

private theorem qs_not_unramified_mul_of_not_unramified_left_local
    (χ ψ : ArtinPrimitiveRoots.A1.HeckeChar K) (v : ArtinPrimitiveRoots.A1.FinPlace K)
    (hχ : ¬ χ.UnramifiedAt v) (hψ : ψ.UnramifiedAt v) : ¬ (χ * ψ).UnramifiedAt v := by
  intro hprod
  apply hχ
  intro u hu huinv
  have hχψ := hprod u hu huinv
  have hψu := hψ u hu huinv
  have hloc : (χ * ψ).loc v u = χ.loc v u * ψ.loc v u := by
    simp [ArtinPrimitiveRoots.A1.HeckeChar.loc]
  have hmul : χ.loc v u * ψ.loc v u = 1 := by
    simpa only [hloc] using hχψ
  rw [hψu, mul_one] at hmul
  exact hmul

private theorem qs_idealValue_mul_char_local
    (χ ψ : ArtinPrimitiveRoots.A1.HeckeChar K) (a : Ideal (𝓞 K))
    (ha : a ≠ ⊥)
    (hlocal : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors a,
      ∀ hP : P.IsPrime, ∀ hP0 : P ≠ ⊥,
        ((χ * ψ).primeValue ⟨P, hP, hP0⟩) =
          χ.primeValue ⟨P, hP, hP0⟩ * ψ.primeValue ⟨P, hP, hP0⟩) :
    (χ * ψ).idealValue a = χ.idealValue a * ψ.idealValue a := by
  classical
  let fs := UniqueFactorizationMonoid.normalizedFactors a
  have hfactor (P : Ideal (𝓞 K)) (hP : P ∈ fs) :
      (if h : P.IsPrime ∧ P ≠ ⊥ then (χ * ψ).primeValue ⟨P, h.1, h.2⟩ else 1) =
        (if h : P.IsPrime ∧ P ≠ ⊥ then χ.primeValue ⟨P, h.1, h.2⟩ else 1) *
          (if h : P.IsPrime ∧ P ≠ ⊥ then ψ.primeValue ⟨P, h.1, h.2⟩ else 1) := by
    have hP' := (Ideal.mem_normalizedFactors_iff ha).1 hP
    have hP0 : P ≠ ⊥ := by
      intro hbot
      apply ha
      exact bot_unique (by simpa [hbot] using hP'.2)
    have hPpair : P.IsPrime ∧ P ≠ ⊥ := ⟨hP'.1, hP0⟩
    rw [dif_pos hPpair, dif_pos hPpair, dif_pos hPpair]
    exact hlocal P hP hP'.1 hP0
  have hprod := congrArg Multiset.prod
    (Multiset.map_congr rfl (fun P hP => hfactor P hP))
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue at hprod ⊢
  rw [hprod, Multiset.prod_map_mul]

private theorem qs_idealValue_zero_local
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f P : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor χ f) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hPf : P ∣ f) : χ.idealValue P = 0 :=
  qs_idealValue_eq_zero_of_conductor_M0 χ f hf P P hP hP0 hPf hP0 dvd_rfl

private theorem qs_character_ramified_at_index_prime_local
    (F : QSFamily m qS) (c P : Ideal (𝓞 K)) (hc : QSAdm m qS c)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPc : P ∣ c) :
    ¬ (F.character c).UnramifiedAt ⟨P, hP, hP0⟩ := by
  rcases F.indexCondition c hc.1 hc.2.1 with ⟨_, hprim, hsupport⟩
  rcases hsupport with ⟨s, hcond, hs⟩
  have hPf : P ∣ F.conductor c := by
    rw [hcond]
    exact dvd_trans hPc ⟨s, rfl⟩
  have hzero := qs_idealValue_zero_local (F.character c) (F.conductor c) P
    hprim hP hP0 hPf
  have hprime : (F.character c).primeValue ⟨P, hP, hP0⟩ = 0 := by
    rw [← qs_idealValue_prime_local (F.character c) P hP hP0]
    exact hzero
  intro hu
  simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hu] at hprime

private theorem qs_character_unramified_at_index_prime_local
    (F : QSFamily m qS) (c P : Ideal (𝓞 K)) (hc : QSAdm m qS c)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPq : IsCoprime P qS)
    (hPc : ¬ P ∣ c) :
    (F.character c).UnramifiedAt ⟨P, hP, hP0⟩ := by
  rcases F.indexCondition c hc.1 hc.2.1 with ⟨_, hprim, hsupport⟩
  rcases hsupport with ⟨s, hcond, hs⟩
  have hPc' := qs_coprime_of_not_dvd_prime_local P c hP hP0 hPc
  have hPs : IsCoprime P s := qs_coprime_mono_right_local P qS s hPq
    (Ideal.le_of_dvd hs)
  have hPcond' : IsCoprime P (c * s) := IsCoprime.mul_right hPc' hPs
  have hPcond : IsCoprime P (F.conductor c) := by
    rw [hcond]
    exact hPcond'
  have hnot : ¬ P ∣ F.conductor c :=
    qs_not_dvd_of_prime_coprime_local P (F.conductor c) hP hPcond
  exact qs_unramified_outside_conductor_local (F.character c) (F.conductor c)
    hprim.1 hprim.2.1 ⟨P, hP, hP0⟩ hnot

private theorem qs_idealValue_ne_zero_of_coprime_conductor_local
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f a : Ideal (𝓞 K))
    (hf0 : f ≠ ⊥) (hcond : χ.ConductorDvd f) (ha0 : a ≠ ⊥)
    (haf : IsCoprime a f) : χ.idealValue a ≠ 0 := by
  classical
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  apply Multiset.prod_ne_zero
  intro hmem
  rcases Multiset.mem_map.mp hmem with ⟨P, hP, hx⟩
  have hP' := (Ideal.mem_normalizedFactors_iff ha0).1 hP
  have hP0 : P ≠ ⊥ := by
    intro hbot
    apply ha0
    exact bot_unique (by simpa [hbot] using hP'.2)
  have hPpair : P.IsPrime ∧ P ≠ ⊥ := ⟨hP'.1, hP0⟩
  have hPcop := qs_isCoprime_factor_local a P f hP'.2 haf
  have hnot := qs_not_dvd_of_prime_coprime_local P f hP'.1 hPcop
  have hU := qs_unramified_outside_conductor_local χ f hf0 hcond ⟨P, hP'.1, hP0⟩ hnot
  have hprime : χ.primeValue ⟨P, hP'.1, hP0⟩ ≠ 0 := by
    unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
    rw [if_pos hU]
    exact Units.ne_zero _
  rw [dif_pos hPpair] at hx
  exact hprime hx

private theorem qs_complex_sq_eq_one_cases_local (z : ℂ) (hz : z ^ 2 = 1) :
    z = 1 ∨ z = -1 := by
  have hfac : (z - 1) * (z + 1) = 0 := by
    calc
      (z - 1) * (z + 1) = z ^ 2 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hz
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)

set_option maxHeartbeats 500000 in
private theorem qs_coprime_multiset_prod_local (s : Multiset (Ideal (𝓞 K)))
    (g : Ideal (𝓞 K)) (hs : ∀ P ∈ s, IsCoprime P g) : IsCoprime s.prod g := by
  induction s using Multiset.induction_on with
  | empty =>
      apply Ideal.isCoprime_iff_sup_eq.mpr
      simp
  | cons P s ih =>
      have hs' : ∀ Q ∈ s, IsCoprime Q g := by
        intro Q hQ
        exact hs Q (by simp [hQ])
      rw [Multiset.prod_cons]
      change IsCoprime (P * s.prod) g
      exact IsCoprime.mul_left (hs P (by simp)) (ih hs')

private theorem qs_idealValue_zero_of_not_coprime_local
    (F : QSFamily m qS) (g a : Ideal (𝓞 K)) (hg : QSAdm m qS g)
    (ha0 : a ≠ ⊥) (hcop : ¬ IsCoprime a g) : (F.character g).idealValue a = 0 := by
  classical
  let fs := UniqueFactorizationMonoid.normalizedFactors a
  have hbad : ¬ ∀ P ∈ fs, IsCoprime P g := by
    intro hall
    have hcopprod := qs_coprime_multiset_prod_local fs g hall
    have hcopag : IsCoprime a g := by
      rw [← Ideal.prod_normalizedFactors_eq_self ha0]
      exact hcopprod
    exact hcop hcopag
  push_neg at hbad
  rcases hbad with ⟨P, hP, hPnot⟩
  have hP' := (Ideal.mem_normalizedFactors_iff ha0).1 hP
  have hP0 : P ≠ ⊥ := by
    intro hbot
    apply ha0
    exact bot_unique (by simpa [hbot] using hP'.2)
  have hPg : P ∣ g := by
    by_contra hnot
    exact hPnot (qs_coprime_of_not_dvd_prime_local P g hP'.1 hP0 hnot)
  rcases F.indexCondition g hg.1 hg.2.1 with ⟨_, hprim, hsupport⟩
  rcases hsupport with ⟨s, hcond, hs⟩
  have hPf : P ∣ F.conductor g := by
    rw [hcond]
    exact dvd_trans hPg ⟨s, rfl⟩
  have hPa : P ∣ a := Ideal.dvd_iff_le.mpr hP'.2
  exact qs_idealValue_eq_zero_of_conductor_M0 (F.character g) (F.conductor g)
    hprim P a hP'.1 hP0 hPf ha0 hPa

open Classical in
private theorem qs_gcd_diagonal_mask_local
    (F : QSFamily m qS) (g a : Ideal (𝓞 K)) (hg : QSAdm m qS g)
    (ha0 : a ≠ ⊥) (haq : IsCoprime a qS) :
    (F.character g).idealValue a * conj ((F.character g).idealValue a) =
      if IsCoprime a g then 1 else 0 := by
  classical
  by_cases hag : IsCoprime a g
  · rcases F.indexCondition g hg.1 hg.2.1 with ⟨_, hprim, hsupport⟩
    rcases hsupport with ⟨s, hcond, hs⟩
    have has : IsCoprime a s := qs_coprime_mono_right_local a qS s haq
      (Ideal.le_of_dvd hs)
    have hacond : IsCoprime a (F.conductor g) := by
      rw [hcond]
      exact IsCoprime.mul_right hag has
    have hnonzero := qs_idealValue_ne_zero_of_coprime_conductor_local
      (F.character g) (F.conductor g) a hprim.1 hprim.2.1 ha0 hacond
    rcases F.quadraticValues g hg.1 hg.2.1 a with hzero | hsq
    · exact (hnonzero hzero).elim
    · rcases qs_complex_sq_eq_one_cases_local _ hsq with hone | hneg
      · simp [hag, hone]
      · simp [hag, hneg]
  · have hzero := qs_idealValue_zero_of_not_coprime_local F g a hg ha0 hag
    simp [hag, hzero]

private theorem qs_pair_value_eq_conj_product_local
    (F : QSFamily m qS) (c d a : Ideal (𝓞 K))
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (ha0 : a ≠ ⊥) (haq : IsCoprime a qS) :
    (qsPairChar F c d).idealValue a =
      (F.character c).idealValue a * conj ((F.character d).idealValue a) := by
  classical
  have hcdval :
      (F.character c * F.character d).idealValue a =
        (F.character c).idealValue a * (F.character d).idealValue a := by
    apply qs_idealValue_mul_char_local (F.character c) (F.character d) a ha0
    intro P hPmem hP hP0
    have hP' := (Ideal.mem_normalizedFactors_iff ha0).1 hPmem
    have hPq := qs_isCoprime_factor_local a P qS hP'.2 haq
    let vP : ArtinPrimitiveRoots.A1.FinPlace K := ⟨P, hP, hP0⟩
    by_cases hPc : P ∣ c
    · have hPd : ¬ P ∣ d := by
        intro hPd
        have htop : ⊤ ≤ P := by
          calc
            ⊤ = c ⊔ d := hcd.sup_eq.symm
            _ ≤ P := sup_le (Ideal.le_of_dvd hPc) (Ideal.le_of_dvd hPd)
        exact hP.ne_top (le_antisymm le_top htop)
      have hramC := qs_character_ramified_at_index_prime_local F c P hc hP hP0 hPc
      have hunramD := qs_character_unramified_at_index_prime_local F d P hd hP hP0 hPq hPd
      have hramProd := qs_not_unramified_mul_of_not_unramified_left_local
        (F.character c) (F.character d) vP hramC hunramD
      have hzeroC : (F.character c).primeValue vP = 0 := by
        unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
        rw [if_neg hramC]
      have hzeroProd : (F.character c * F.character d).primeValue vP = 0 := by
        unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
        rw [if_neg hramProd]
      rw [hzeroProd, hzeroC]
      simp
    · by_cases hPd : P ∣ d
      · have hPc' : ¬ P ∣ c := hPc
        have hramD := qs_character_ramified_at_index_prime_local F d P hd hP hP0 hPd
        have hunramC := qs_character_unramified_at_index_prime_local F c P hc hP hP0 hPq hPc'
        have hramProd := qs_not_unramified_mul_of_not_unramified_left_local
          (F.character d) (F.character c) vP hramD hunramC
        have hzeroD : (F.character d).primeValue vP = 0 := by
          unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
          rw [if_neg hramD]
        have hzeroProd : (F.character c * F.character d).primeValue vP = 0 := by
          have hswap : F.character c * F.character d = F.character d * F.character c := by
            ext x
            simp [mul_comm]
          rw [hswap]
          unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
          rw [if_neg hramProd]
        rw [hzeroProd, hzeroD]
        simp
      · have hunramC := qs_character_unramified_at_index_prime_local F c P hc hP hP0 hPq hPc
        have hunramD := qs_character_unramified_at_index_prime_local F d P hd hP hP0 hPq hPd
        exact qs_primeValue_mul_of_unramified_local (F.character c) (F.character d)
          vP hunramC hunramD
  have hsqD := F.character_order_two d hd.1 hd.2.1
  have hinvD : (F.character d)⁻¹ = F.character d := by
    ext x
    have hsqx : (F.character d x) ^ 2 = 1 := by
      simpa using congrArg (fun χ : ArtinPrimitiveRoots.A1.HeckeChar K => χ x) hsqD
    have hx : (F.character d x)⁻¹ = F.character d x := by
      calc
        (F.character d x)⁻¹ = (F.character d x)⁻¹ * (F.character d x) ^ 2 := by
          rw [hsqx]
          simp
        _ = F.character d x := by group
    exact congrArg (fun u : ℂˣ => (u : ℂ)) hx
  have hrealD :
      conj ((F.character d).idealValue a) = (F.character d).idealValue a := by
    rcases F.quadraticValues d hd.1 hd.2.1 a with hzero | hsq
    · simp [hzero]
    · rcases qs_complex_sq_eq_one_cases_local _ hsq with hone | hneg
      · simp [hone]
      · simp [hneg]
  calc
    (qsPairChar F c d).idealValue a =
        (F.character c * F.character d).idealValue a := by simp [qsPairChar, hinvD]
    _ = (F.character c).idealValue a * (F.character d).idealValue a := hcdval
    _ = (F.character c).idealValue a * conj ((F.character d).idealValue a) := by
          rw [hrealD]

private theorem qs_family_mul_at_prime_S0
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (c d P : Ideal (𝓞 K)) (hc : QSAdm m qS c) (hd : QSAdm m qS d)
    (hcd : IsCoprime c d) (hcdm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m (c * d))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hPm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m P) :
    (F.character (c * d)).idealValue P =
      (F.character c).idealValue P * (F.character d).idealValue P := by
  classical
  have hcdsq : Squarefree (c * d) :=
    squarefree_mul_iff.mpr ⟨hcd.isRelPrime, hc.1, hd.1⟩
  have hPsq : Squarefree P := qs_prime_ideal_squarefree_local P hP hP0
  by_cases hcp : IsCoprime (c * d) P
  · have hcpC : IsCoprime c P := by
      apply Ideal.isCoprime_iff_sup_eq.mpr
      have hs := (Ideal.isCoprime_iff_sup_eq.mp hcp)
      apply top_unique
      calc
        ⊤ = (c * d) ⊔ P := hs.symm
        _ ≤ c ⊔ P := sup_le_sup Ideal.mul_le_left le_rfl
    have hcpD : IsCoprime d P := by
      apply Ideal.isCoprime_iff_sup_eq.mpr
      have hs := (Ideal.isCoprime_iff_sup_eq.mp hcp)
      apply top_unique
      calc
        ⊤ = (c * d) ⊔ P := hs.symm
        _ ≤ d ⊔ P := sup_le_sup Ideal.mul_le_right le_rfl
    have hcm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c := hc.2.1
    have hdm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d := hd.2.1
    have hrecCD := F.reciprocity (c * d) P hcdsq hcdm hPsq hPm hcp
    have hrecC := F.reciprocity c P hc.1 hcm hPsq hPm hcpC
    have hrecD := F.reciprocity d P hd.1 hdm hPsq hPm hcpD
    have hrecCD' : (F.character (c * d)).idealValue P =
        (F.character P).idealValue (c * d) := by
      calc
        _ = ((F.rayFactor (ArtinPrimitiveRoots.Hecke.rayClass m (c * d) hcdm)
              (ArtinPrimitiveRoots.Hecke.rayClass m P hPm) : ℂˣ) : ℂ) *
              (F.character P).idealValue (c * d) := hrecCD
        _ = _ := by simp [hrf]
    have hrecC' : (F.character c).idealValue P = (F.character P).idealValue c := by
      calc
        _ = ((F.rayFactor (ArtinPrimitiveRoots.Hecke.rayClass m c hcm)
              (ArtinPrimitiveRoots.Hecke.rayClass m P hPm) : ℂˣ) : ℂ) *
              (F.character P).idealValue c := hrecC
        _ = _ := by simp [hrf]
    have hrecD' : (F.character d).idealValue P = (F.character P).idealValue d := by
      calc
        _ = ((F.rayFactor (ArtinPrimitiveRoots.Hecke.rayClass m d hdm)
              (ArtinPrimitiveRoots.Hecke.rayClass m P hPm) : ℂˣ) : ℂ) *
              (F.character P).idealValue d := hrecD
        _ = _ := by simp [hrf]
    have hmul := qs_idealValue_mul_M0 (F.character P) c d hcm.1 hdm.1
    calc
      (F.character (c * d)).idealValue P =
          (F.character P).idealValue c * (F.character P).idealValue d := by
            rw [hrecCD', hmul]
      _ = (F.character c).idealValue P * (F.character d).idealValue P := by
            rw [← hrecC', ← hrecD']
  · have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
    have hsup : c * d ⊔ P ≠ ⊤ := by
      intro heq
      exact hcp (Ideal.isCoprime_iff_sup_eq.mpr heq)
    have hEq : P = c * d ⊔ P := hPmax.eq_of_le hsup le_sup_right
    have hcdle : c * d ≤ P := hEq ▸ le_sup_left
    have hPcd : P ∣ c * d := Ideal.dvd_iff_le.mpr hcdle
    rcases hP.mul_le.mp hcdle with hPc | hPd
    · have hPc' : P ∣ c := Ideal.dvd_iff_le.mpr hPc
      rcases F.indexCondition (c * d) hcdsq hcdm with ⟨_, hprimCD, hcondCD⟩
      rcases hcondCD with ⟨sCD, hEqCD, hdivCD⟩
      rcases F.indexCondition c hc.1 hc.2.1 with ⟨_, hprimC, hcondC⟩
      rcases hcondC with ⟨sC, hEqC, hdivC⟩
      have hPcondCD : P ∣ F.conductor (c * d) := by
        rw [hEqCD]
        exact dvd_trans hPcd ⟨sCD, rfl⟩
      have hPcondC : P ∣ F.conductor c := by
        rw [hEqC]
        exact dvd_trans hPc' ⟨sC, rfl⟩
      rw [qs_idealValue_zero_local (F.character (c * d)) (F.conductor (c * d)) P
          hprimCD hP hP0 hPcondCD,
        qs_idealValue_zero_local (F.character c) (F.conductor c) P
          hprimC hP hP0 hPcondC]
      simp
    · have hPd' : P ∣ d := Ideal.dvd_iff_le.mpr hPd
      rcases F.indexCondition (c * d) hcdsq hcdm with ⟨_, hprimCD, hcondCD⟩
      rcases hcondCD with ⟨sCD, hEqCD, hdivCD⟩
      rcases F.indexCondition d hd.1 hd.2.1 with ⟨_, hprimD, hcondD⟩
      rcases hcondD with ⟨sD, hEqD, hdivD⟩
      have hPcondCD : P ∣ F.conductor (c * d) := by
        rw [hEqCD]
        exact dvd_trans hPcd ⟨sCD, rfl⟩
      have hPcondD : P ∣ F.conductor d := by
        rw [hEqD]
        exact dvd_trans hPd' ⟨sD, rfl⟩
      rw [qs_idealValue_zero_local (F.character (c * d)) (F.conductor (c * d)) P
          hprimCD hP hP0 hPcondCD,
        qs_idealValue_zero_local (F.character d) (F.conductor d) P
          hprimD hP hP0 hPcondD]
      simp

/-- S0 (IMPL): family multiplicativity on rows coprime to `m` and `qS` (trivial ray factor):
`χ_{cd}(a) = χ_c(a) χ_d(a)` for coprime admissible `c, d`.  Prime by prime:
`χ_{cd}(P) = χ_P(cd) = χ_P(c) χ_P(d) = χ_c(P) χ_d(P)` for `P ∤ cd`, and both sides vanish at
`P ∣ cd`. -/
theorem qs_family_mul_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (c d : Ideal (𝓞 K)) (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (a : Ideal (𝓞 K)) (ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a) (haq : IsCoprime a qS) :
    (F.character (c * d)).idealValue a =
      (F.character c).idealValue a * (F.character d).idealValue a := by
  classical
  rcases (qs_isCoprimeTo_iff_M0 (m := m) a).mp ha with ⟨ha0, hamod⟩
  have hcdm := qs_isCoprimeTo_mul_local c d hc.2.1 hd.2.1
  let fs := UniqueFactorizationMonoid.normalizedFactors a
  have hfsne : ∀ P ∈ fs, P ≠ ⊥ := by
    intro P hP
    have hP' := (Ideal.mem_normalizedFactors_iff ha0).1 hP
    intro hPb
    apply ha0
    exact bot_unique (by simpa [hPb] using hP'.2)
  have hloc (P : Ideal (𝓞 K)) (hP : P ∈ fs) :
      (F.character (c * d)).idealValue P =
        (F.character c).idealValue P * (F.character d).idealValue P := by
    have hP' := (Ideal.mem_normalizedFactors_iff ha0).1 hP
    have hP0 := hfsne P hP
    have hPmod := qs_isCoprime_factor_local a P (qsModulusRad m) hP'.2 hamod
    have hPm := (qs_isCoprimeTo_iff_M0 (m := m) P).mpr ⟨hP0, hPmod⟩
    exact qs_family_mul_at_prime_S0 F hrf c d P hc hd hcd hcdm hP'.1 hP0 hPm
  have hprodCD := qs_idealValue_multiset_product_local (F.character (c * d)) fs hfsne
  have hprodC := qs_idealValue_multiset_product_local (F.character c) fs hfsne
  have hprodD := qs_idealValue_multiset_product_local (F.character d) fs hfsne
  calc
    (F.character (c * d)).idealValue a =
        (F.character (c * d)).idealValue fs.prod := by
          rw [← Ideal.prod_normalizedFactors_eq_self ha0]
    _ = (fs.map (F.character (c * d)).idealValue).prod := hprodCD
    _ = (fs.map (fun P => (F.character c).idealValue P *
          (F.character d).idealValue P)).prod := by
          congr 1
          apply Multiset.map_congr rfl
          intro P hP
          exact hloc P hP
    _ = (fs.map (F.character c).idealValue).prod *
          (fs.map (F.character d).idealValue).prod := by
          rw [Multiset.prod_map_mul]
    _ = (F.character c).idealValue fs.prod *
          (F.character d).idealValue fs.prod := by rw [← hprodC, ← hprodD]
    _ = (F.character c).idealValue a * (F.character d).idealValue a := by
          rw [Ideal.prod_normalizedFactors_eq_self ha0]

open Classical in
/-- S0 (IMPL): the gcd identity.  For pairwise coprime admissible `g, c, d` and a row `a`
coprime to `m` and `qS`:
`χ_{gc}(a) conj(χ_{gd}(a)) = 1_{(a,g)=1} · ψ_{c,d}(a)`, `ψ_{c,d} = χ_c χ_d⁻¹`
(ramified × unramified is ramified at `P ∣ cd`; `χ_g(a)² = 1_{(a,g)=1}`). -/
theorem qs_gcd_pair_identity_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (g c d : Ideal (𝓞 K)) (hg : QSAdm m qS g) (hc : QSAdm m qS c) (hd : QSAdm m qS d)
    (hgc : IsCoprime g c) (hgd : IsCoprime g d) (hcd : IsCoprime c d)
    (a : Ideal (𝓞 K)) (ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a) (haq : IsCoprime a qS) :
    (F.character (g * c)).idealValue a * conj ((F.character (g * d)).idealValue a) =
      if IsCoprime a g then (qsPairChar F c d).idealValue a else 0 := by
  classical
  have hgc : IsCoprime g c := hgc
  have hgd : IsCoprime g d := hgd
  have hgcSq : Squarefree (g * c) :=
    squarefree_mul_iff.mpr ⟨hgc.isRelPrime, hg.1, hc.1⟩
  have hgdSq : Squarefree (g * d) :=
    squarefree_mul_iff.mpr ⟨hgd.isRelPrime, hg.1, hd.1⟩
  have hgcM := qs_isCoprimeTo_mul_local g c hg.2.1 hc.2.1
  have hgdM := qs_isCoprimeTo_mul_local g d hg.2.1 hd.2.1
  have hgcQ := IsCoprime.mul_left hg.2.2 hc.2.2
  have hgdQ := IsCoprime.mul_left hg.2.2 hd.2.2
  have hgcAdm : QSAdm m qS (g * c) := ⟨hgcSq, hgcM, hgcQ⟩
  have hgdAdm : QSAdm m qS (g * d) := ⟨hgdSq, hgdM, hgdQ⟩
  have hmulGC := qs_family_mul_S0 F hrf g c hg hc hgc a ha haq
  have hmulGD := qs_family_mul_S0 F hrf g d hg hd hgd a ha haq
  have ha0 := (qs_isCoprimeTo_iff_M0 (m := m) a).mp ha |>.1
  have hmask := qs_gcd_diagonal_mask_local F g a hg ha0 haq
  have hpair := qs_pair_value_eq_conj_product_local F c d a hc hd hcd ha0 haq
  calc
    (F.character (g * c)).idealValue a *
        conj ((F.character (g * d)).idealValue a) =
        ((F.character g).idealValue a * (F.character c).idealValue a) *
          conj ((F.character g).idealValue a * (F.character d).idealValue a) := by
          rw [hmulGC, hmulGD]
    _ = ((F.character g).idealValue a * conj ((F.character g).idealValue a)) *
          ((F.character c).idealValue a * conj ((F.character d).idealValue a)) := by
          simp only [map_mul]
          ring
    _ = (if IsCoprime a g then 1 else 0) * (qsPairChar F c d).idealValue a := by
          rw [hmask, hpair]
    _ = if IsCoprime a g then (qsPairChar F c d).idealValue a else 0 := by
          by_cases h : IsCoprime a g <;> simp [h]

private theorem qs_high_energy_eq_matrix_energy_local
    (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hM : 0 < M) (z : Ideal (𝓞 K) → ℂ) :
    qsHighEnergy F W M κ (qsUpTo m qS N) z =
      ∑ a : qsHighRows m qS M κ,
        ‖∑ c : qsUpTo m qS N,
          qsHighMatrix F W M N κ a c * z c.1‖ ^ 2 := by
  classical
  let rows := qsHighRows m qS M κ
  let cols := qsUpTo m qS N
  let rowCond (I : Ideal (𝓞 K)) :=
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ∧ IsCoprime I qS ∧ κ < (qsSfNorm I : ℝ)
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun a =>
    if rowCond a.1 then
      W (qsN a.1 / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a.1‖ ^ 2
    else 0
  have hrow_nebot (I : Ideal (𝓞 K)) (hI : I ∈ rows) : I ≠ ⊥ := by
    dsimp [rows, qsHighRows] at hI
    exact (Finset.mem_filter.mp hI).2.1.1
  let rowEmbed (r : rows) : {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    ⟨r.1, hrow_nebot r.1 r.2⟩
  have hEmbedInj : Function.Injective rowEmbed := by
    intro r s h
    apply Subtype.ext
    change (rowEmbed r).1 = (rowEmbed s).1
    exact congrArg (fun x : {I : Ideal (𝓞 K) // I ≠ ⊥} => x.1) h
  let rowsNZ : Finset {I : Ideal (𝓞 K) // I ≠ ⊥} := rows.attach.image rowEmbed
  have hzero : ∀ a : {I : Ideal (𝓞 K) // I ≠ ⊥}, a ∉ rowsNZ → f a = 0 := by
    intro a ha
    by_cases hrow : rowCond a.1
    · by_cases hWzero : W (qsN a.1 / M) = 0
      · simp [f, hrow, hWzero]
      · have hlt : qsN a.1 / M < 5 / 2 := by
          apply lt_of_not_ge
          intro hge
          exact hWzero (hW.2.2.2 _ hge)
        have hNbound : (Ideal.absNorm a.1 : ℝ) < 3 * M := by
          dsimp [qsN] at hlt ⊢
          have hlt' := (div_lt_iff₀ hM).mp hlt
          nlinarith
        have hFloor : Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊ := Nat.le_floor hNbound.le
        have hbase : a.1 ∈
            (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset := by
          exact (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).mem_toFinset.mpr hFloor
        have hrowmem : a.1 ∈ rows := by
          dsimp [rows, qsHighRows]
          rw [Finset.mem_filter]
          exact ⟨hbase, hrow⟩
        let r : rows := ⟨a.1, hrowmem⟩
        have hmem : rowEmbed r ∈ rowsNZ :=
          Finset.mem_image.mpr ⟨r, Finset.mem_attach _ _, rfl⟩
        have heq : rowEmbed r = a := by
          apply Subtype.ext
          rfl
        have hmemA : a ∈ rowsNZ := by
          rw [← heq]
          exact hmem
        exact (ha hmemA).elim
    · simp [f, hrow]
  have hfinite :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) = ∑ a ∈ rowsNZ, f a := by
    exact tsum_eq_sum (L := SummationFilter.unconditional _) hzero
  have hrowEnergy (r : rows) :
      f (rowEmbed r) =
        ‖∑ c : cols, qsHighMatrix F W M N κ r c * z c.1‖ ^ 2 := by
    have hr : rowCond r.1 := by
      have hrmem : r.1 ∈ rows := r.2
      change r.1 ∈
        ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset).filter
          (fun I => rowCond I) at hrmem
      exact (Finset.mem_filter.mp hrmem).2
    have hsum :
        ∑ c : cols, qsHighMatrix F W M N κ r c * z c.1 =
          (Real.sqrt (W (qsN r.1 / M)) : ℂ) *
            ∑ c : cols, z c.1 * (F.character c.1).idealValue r.1 := by
      simp only [qsHighMatrix]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    have hcolsSum :
      (∑ c : cols, z c.1 * (F.character c.1).idealValue r.1) =
          ∑ c ∈ cols, z c * (F.character c).idealValue r.1 := by
      rw [Finset.univ_eq_attach cols]
      exact Finset.sum_attach cols (fun c => z c * (F.character c).idealValue r.1)
    have hWnonneg : 0 ≤ W (qsN r.1 / M) := hW.2.1 _
    have hsqrt : 0 ≤ Real.sqrt (W (qsN r.1 / M)) := Real.sqrt_nonneg _
    calc
      f (rowEmbed r) =
          W (qsN r.1 / M) *
            ‖∑ c ∈ cols, z c * (F.character c).idealValue r.1‖ ^ 2 := by
          simp [f, rowCond, rowEmbed, hr]
      _ = ‖∑ c : cols, qsHighMatrix F W M N κ r c * z c.1‖ ^ 2 := by
          rw [hsum, hcolsSum, norm_mul]
          have hnormsqrt :
              ‖(Real.sqrt (W (qsN r.1 / M)) : ℂ)‖ =
                Real.sqrt (W (qsN r.1 / M)) := by
            simp [Complex.norm_real, abs_of_nonneg hsqrt]
          rw [hnormsqrt, mul_pow, Real.sq_sqrt hWnonneg]
  change (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) = _
  rw [hfinite]
  calc
    ∑ a ∈ rowsNZ, f a =
        ∑ r ∈ rows.attach, f (rowEmbed r) := Finset.sum_image hEmbedInj.injOn
    _ = ∑ r : rows, f (rowEmbed r) := by
        rw [← Finset.univ_eq_attach rows]
    _ = ∑ r : rows, ‖∑ c : cols, qsHighMatrix F W M N κ r c * z c.1‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hrowEnergy r

/-- S0 (IMPL): `B₂` is controlled by energies: `qsHighEnergy ≤ qsHighNorm · ‖z‖²` for columns
of norm `≤ N`, and `qsHighNorm` is the least such bound. -/
theorem qs_high_norm_energy_S0 (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hM : 0 < M) :
    (∀ z : Ideal (𝓞 K) → ℂ,
      qsHighEnergy F W M κ (qsUpTo m qS N) z ≤
        qsHighNorm F W M N κ * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2) ∧
    (∀ B : ℝ, 0 ≤ B → (∀ z : Ideal (𝓞 K) → ℂ,
      qsHighEnergy F W M κ (qsUpTo m qS N) z ≤ B * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2) →
        qsHighNorm F W M N κ ≤ B) := by
  classical
  constructor
  · intro z
    calc
      qsHighEnergy F W M κ (qsUpTo m qS N) z =
          ∑ a : qsHighRows m qS M κ,
            ‖∑ c : qsUpTo m qS N,
              qsHighMatrix F W M N κ a c * z c.1‖ ^ 2 :=
            qs_high_energy_eq_matrix_energy_local F W hW M N κ hM z
      _ ≤ ‖OAI.FiniteSieveOperator.operator (qsHighMatrix F W M N κ)‖ ^ 2 *
            ∑ c : qsUpTo m qS N, ‖z c.1‖ ^ 2 :=
            OAI.FiniteSieveOperator.energy_bound (qsHighMatrix F W M N κ)
              (fun c : qsUpTo m qS N => z c.1)
      _ = qsHighNorm F W M N κ * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 := by
            unfold qsHighNorm
            congr 1
            exact Finset.sum_attach (qsUpTo m qS N) (fun c => ‖z c‖ ^ 2)
  · intro B hB hbound
    let cols := qsUpTo m qS N
    let A := qsHighMatrix F W M N κ
    let T := OAI.FiniteSieveOperator.operator A
    have henergy (u : cols → ℂ) :
        (∑ a : qsHighRows m qS M κ,
          ‖∑ c : cols, A a c * u c‖ ^ 2) ≤ B * ∑ c : cols, ‖u c‖ ^ 2 := by
      let zext : Ideal (𝓞 K) → ℂ := fun I => if hI : I ∈ cols then u ⟨I, hI⟩ else 0
      have h := hbound zext
      rw [qs_high_energy_eq_matrix_energy_local F W hW M N κ hM zext] at h
      have hnormSum :
          (∑ c ∈ cols, ‖zext c‖ ^ 2) = ∑ c ∈ cols.attach, ‖u c‖ ^ 2 := by
        rw [← Finset.sum_attach cols (fun I => ‖zext I‖ ^ 2)]
        apply Finset.sum_congr rfl
        intro c hc
        simp [zext]
      rw [hnormSum] at h
      simp [zext, cols, A, Finset.univ_eq_attach] at h
      simpa [cols, A, Finset.univ_eq_attach] using h
    have hnorm : ‖T‖ ≤ Real.sqrt B := by
      apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg B)
      intro x
      have hsquare : ‖T x‖ ^ 2 ≤ B * ‖x‖ ^ 2 := by
        have hu := henergy (fun c => x c)
        simpa [T, A, OAI.FiniteSieveOperator.operator_apply,
          EuclideanSpace.norm_sq_eq] using hu
      have hsqrt : ‖T x‖ ^ 2 ≤ (Real.sqrt B * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hB]
        exact hsquare
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg B) (norm_nonneg _))).mp
        hsqrt
    have hnormSq : ‖T‖ ^ 2 ≤ B := by
      calc
        ‖T‖ ^ 2 ≤ Real.sqrt B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = B := Real.sq_sqrt hB
    simpa [qsHighNorm, T, A] using hnormSq

private theorem qs_dyad_partition_index_spec_S0
    (N : ℝ) (hN : 1 ≤ N) (c : Ideal (𝓞 K)) (hc : QSAdm m qS c)
    (hcn : qsN c ≤ N) :
    ⌊Real.logb 2 (N / qsN c)⌋₊ < Nat.ceil (Real.logb 2 N) + 1 ∧
      N / 2 ^ (⌊Real.logb 2 (N / qsN c)⌋₊ + 1) < qsN c ∧
      qsN c ≤ N / 2 ^ ⌊Real.logb 2 (N / qsN c)⌋₊ := by
  have hc0 : c ≠ ⊥ := hc.2.1.1
  have hnormNat : 0 < Ideal.absNorm c := by
    apply Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
    exact mem_nonZeroDivisors_iff_ne_zero.mpr hc0
  have hnormPos : 0 < qsN c := by exact_mod_cast hnormNat
  have hnormOne : 1 ≤ qsN c := by
    have hn : 1 ≤ Ideal.absNorm c := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnormNat)
    exact_mod_cast hn
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have htpos : 0 < N / qsN c := div_pos hNpos hnormPos
  have htge : 1 ≤ N / qsN c := (le_div_iff₀ hnormPos).2 (by simpa using hcn)
  have htle : N / qsN c ≤ N := div_le_self hNpos.le hnormOne
  let j : ℕ := ⌊Real.logb 2 (N / qsN c)⌋₊
  have hlog0 : 0 ≤ Real.logb 2 (N / qsN c) :=
    Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) htge
  have hjlo : (j : ℝ) ≤ Real.logb 2 (N / qsN c) := Nat.floor_le hlog0
  have hjhi : Real.logb 2 (N / qsN c) < (j : ℝ) + 1 := by
    simpa [j] using Nat.lt_floor_add_one (Real.logb 2 (N / qsN c))
  have hlogN : Real.logb 2 (N / qsN c) ≤ Real.logb 2 N :=
    (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ)) htpos hNpos).2 htle
  have hceil : Real.logb 2 N ≤ (Nat.ceil (Real.logb 2 N) : ℝ) := Nat.le_ceil _
  have hjbound : j ≤ Nat.ceil (Real.logb 2 N) := by
    exact_mod_cast le_trans hjlo (le_trans hlogN hceil)
  have hpowloR : (2 : ℝ) ^ (j : ℝ) ≤ N / qsN c :=
    (Real.le_logb_iff_rpow_le (by norm_num : 1 < (2 : ℝ)) htpos).mp hjlo
  have hpowlo : (2 : ℝ) ^ j ≤ N / qsN c := by
    simpa only [Real.rpow_natCast] using hpowloR
  have hjhi' : Real.logb 2 (N / qsN c) < ((j + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hjhi
  have hpowhiR : N / qsN c < (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num : 1 < (2 : ℝ)) htpos).mp hjhi'
  have hpowhi : N / qsN c < (2 : ℝ) ^ (j + 1) := by
    simpa only [Real.rpow_natCast] using hpowhiR
  have hNlt : N < (2 : ℝ) ^ (j + 1) * qsN c := (div_lt_iff₀ hnormPos).mp hpowhi
  have hlowDen : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hlow : N / (2 : ℝ) ^ (j + 1) < qsN c :=
    (div_lt_iff₀ hlowDen).2 (by simpa [mul_comm] using hNlt)
  have hmul : (2 : ℝ) ^ j * qsN c ≤ N := (le_div_iff₀ hnormPos).mp hpowlo
  have hhighDen : 0 < (2 : ℝ) ^ j := by positivity
  have hhigh : qsN c ≤ N / (2 : ℝ) ^ j :=
    (le_div_iff₀ hhighDen).2 (by simpa [mul_comm] using hmul)
  refine ⟨Nat.lt_succ_of_le hjbound, ?_, ?_⟩
  · simpa [j] using hlow
  · simpa [j] using hhigh

private theorem qs_class_dyad_partition_local
    (F : QSFamily m qS) (N : ℝ) (hN : 1 ≤ N)
    (hcols : ∀ c ∈ qsUpTo m qS N, QSAdm m qS c) :
    ∃ parts : Finset (Finset (Ideal (𝓞 K))),
      ((parts.card : ℕ) : ℝ) ≤
          (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
            ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) ∧
      (∀ P ∈ parts, P ⊆ qsUpTo m qS N) ∧
      (∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) ∧
      (∀ P ∈ parts, ∃ j : ℕ, ∀ c ∈ P,
        N / 2 ^ (j + 1) < qsN c ∧ qsN c ≤ N / 2 ^ j) ∧
      (∀ P ∈ parts, ∀ c ∈ P, ∀ d ∈ P,
        ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
          (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
          ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd) ∧
      (∀ c ∈ qsUpTo m qS N, ∃ P ∈ parts, c ∈ P) := by
  classical
  letI : Finite (ClassFieldTheory.RayClassGroup m) := ClassFieldTheory.rayClassGroup_finite K m
  let G := ClassFieldTheory.RayClassGroup m
  letI : Fintype G := Fintype.ofFinite G
  let cols := qsUpTo m qS N
  let L := Nat.ceil (Real.logb 2 N) + 1
  let rayOf (c : Ideal (𝓞 K)) : G :=
    if hc : c ∈ cols then
      ArtinPrimitiveRoots.Hecke.rayClass m c (hcols c hc).2.1
    else 1
  let dyadOf (c : Ideal (𝓞 K)) : ℕ :=
    if hc : c ∈ cols then ⌊Real.logb 2 (N / qsN c)⌋₊ else 0
  have hdyadLt (c : Ideal (𝓞 K)) (hc : c ∈ cols) : dyadOf c < L := by
    have hcn : qsN c ≤ N := by
      dsimp [cols, qsUpTo] at hc
      exact (Finset.mem_filter.mp hc).2.2
    simpa [dyadOf, hc, L] using
      (qs_dyad_partition_index_spec_S0 N hN c (hcols c hc) hcn).1
  let label (c : Ideal (𝓞 K)) : G × Fin L :=
    (rayOf c, ⟨dyadOf c, by
      by_cases hc : c ∈ cols
      · exact hdyadLt c hc
      · simp [dyadOf, hc, L]⟩)
  let part (i : G × Fin L) : Finset (Ideal (𝓞 K)) :=
    cols.filter (fun c => label c = i)
  let idxAll : Finset (G × Fin L) := Finset.univ
  let idxNZ : Finset (G × Fin L) := idxAll.filter (fun i => (part i).Nonempty)
  let parts : Finset (Finset (Ideal (𝓞 K))) := idxNZ.image part
  have hpartInj : Set.InjOn part (↑idxNZ) := by
    intro i hi j hj hij
    have hNi := (Finset.mem_filter.mp hi).2
    rcases hNi with ⟨c, hc⟩
    have hcJ : c ∈ part j := by rw [← hij]; exact hc
    have hci := (Finset.mem_filter.mp hc).2
    have hcj := (Finset.mem_filter.mp hcJ).2
    exact hci.symm.trans hcj
  have hcardNat : parts.card ≤ Nat.card G * L := by
    calc
      parts.card ≤ idxNZ.card := by
        dsimp [parts]
        exact Finset.card_image_le
      _ ≤ idxAll.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.card G * L := by
        simp [idxAll, L, Nat.card_eq_fintype_card]
  have hcardReal : (parts.card : ℝ) ≤
      (Nat.card G : ℝ) * ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) := by
    simpa [L] using (show (parts.card : ℝ) ≤ (Nat.card G * L : ℕ) by exact_mod_cast hcardNat)
  have hsubset : ∀ P ∈ parts, P ⊆ cols := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨i, hi, rfl⟩
    exact Finset.filter_subset _ _
  have hdisjoint : ∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q := by
    intro P hP Q hQ hPQ
    rcases Finset.mem_image.mp hP with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hQ with ⟨j, hj, rfl⟩
    apply Finset.disjoint_left.mpr
    intro c hcP hcQ
    have hci := (Finset.mem_filter.mp hcP).2
    have hcj := (Finset.mem_filter.mp hcQ).2
    have hij : i = j := hci.symm.trans hcj
    exact hPQ (congrArg part hij)
  have hdyad : ∀ P ∈ parts, ∃ j : ℕ, ∀ c ∈ P,
      N / 2 ^ (j + 1) < qsN c ∧ qsN c ≤ N / 2 ^ j := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨i, hi, rfl⟩
    refine ⟨i.2, ?_⟩
    intro c hc
    have hfilter := (Finset.mem_filter.mp hc).2
    have hlabel := congrArg (fun x : G × Fin L => x.2.val) hfilter
    have hdyadEq : dyadOf c = i.2.val := by simpa [label] using hlabel
    have hcCols := (Finset.mem_filter.mp hc).1
    have hcn : qsN c ≤ N := by
      dsimp [cols, qsUpTo] at hcCols
      exact (Finset.mem_filter.mp hcCols).2.2
    have hspec := qs_dyad_partition_index_spec_S0 N hN c (hcols c hcCols) hcn
    have hfloorEq : ⌊Real.logb 2 (N / qsN c)⌋₊ = i.2.val := by
      simpa [dyadOf, hcCols] using hdyadEq
    simpa [hfloorEq] using hspec.2
  have hray : ∀ P ∈ parts, ∀ c ∈ P, ∀ d ∈ P,
      ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
        (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
        ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd := by
    intro P hP c hcP d hdP
    rcases Finset.mem_image.mp hP with ⟨i, hi, rfl⟩
    have hcFilt := Finset.mem_filter.mp hcP
    have hdFilt := Finset.mem_filter.mp hdP
    rcases hcols c hcFilt.1 with ⟨_, hcRay, _⟩
    rcases hcols d hdFilt.1 with ⟨_, hdRay, _⟩
    have hrc : ArtinPrimitiveRoots.Hecke.rayClass m c hcRay = rayOf c := by
      dsimp [rayOf]
      rw [dif_pos hcFilt.1]
    have hrd : ArtinPrimitiveRoots.Hecke.rayClass m d hdRay = rayOf d := by
      dsimp [rayOf]
      rw [dif_pos hdFilt.1]
    have hci : rayOf c = i.1 := congrArg (fun x : G × Fin L => x.1) hcFilt.2
    have hdi : rayOf d = i.1 := congrArg (fun x : G × Fin L => x.1) hdFilt.2
    refine ⟨hcRay, hdRay, ?_⟩
    calc
      ArtinPrimitiveRoots.Hecke.rayClass m c hcRay = rayOf c := hrc
      _ = i.1 := hci
      _ = rayOf d := hdi.symm
      _ = ArtinPrimitiveRoots.Hecke.rayClass m d hdRay := hrd.symm
  have hcover : ∀ c ∈ cols, ∃ P ∈ parts, c ∈ P := by
    intro c hc
    have hidxNZ : label c ∈ idxNZ := by
      apply Finset.mem_filter.mpr
      have hidxAll : label c ∈ idxAll := by simp [idxAll]
      refine ⟨hidxAll, ?_⟩
      refine ⟨c, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨hc, rfl⟩
    refine ⟨part (label c), Finset.mem_image.mpr ⟨label c, hidxNZ, rfl⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hc, rfl⟩
  exact ⟨parts, hcardReal, hsubset, hdisjoint, hdyad, hray, hcover⟩

private theorem qs_high_energy_finite_sum_local
    (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ : ℝ) (hM : 0 < M) (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) :
    qsHighEnergy F W M κ cols z =
      ∑ a ∈ qsHighRows m qS M κ,
        W (qsN a / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2 := by
  classical
  let rows := qsHighRows m qS M κ
  let rowCond (I : Ideal (𝓞 K)) :=
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ∧ IsCoprime I qS ∧ κ < (qsSfNorm I : ℝ)
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun a =>
    if rowCond a.1 then
      W (qsN a.1 / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a.1‖ ^ 2
    else 0
  have hrow_nebot (I : Ideal (𝓞 K)) (hI : I ∈ rows) : I ≠ ⊥ := by
    dsimp [rows, qsHighRows] at hI
    exact (Finset.mem_filter.mp hI).2.1.1
  let rowEmbed (r : rows) : {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    ⟨r.1, hrow_nebot r.1 r.2⟩
  have hEmbedInj : Function.Injective rowEmbed := by
    intro r s h
    apply Subtype.ext
    change (rowEmbed r).1 = (rowEmbed s).1
    exact congrArg (fun x : {I : Ideal (𝓞 K) // I ≠ ⊥} => x.1) h
  let rowsNZ : Finset {I : Ideal (𝓞 K) // I ≠ ⊥} := rows.attach.image rowEmbed
  have hzero : ∀ a : {I : Ideal (𝓞 K) // I ≠ ⊥}, a ∉ rowsNZ → f a = 0 := by
    intro a ha
    by_cases hrow : rowCond a.1
    · by_cases hWzero : W (qsN a.1 / M) = 0
      · simp [f, hrow, hWzero]
      · have hlt : qsN a.1 / M < 5 / 2 := by
          apply lt_of_not_ge
          intro hge
          exact hWzero (hW.2.2.2 _ hge)
        have hNbound : (Ideal.absNorm a.1 : ℝ) < 3 * M := by
          dsimp [qsN] at hlt ⊢
          have hlt' := (div_lt_iff₀ hM).mp hlt
          nlinarith
        have hFloor : Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊ := Nat.le_floor hNbound.le
        have hbase : a.1 ∈
            (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset := by
          exact (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).mem_toFinset.mpr hFloor
        have hrowmem : a.1 ∈ rows := by
          dsimp [rows, qsHighRows]
          rw [Finset.mem_filter]
          exact ⟨hbase, hrow⟩
        let r : rows := ⟨a.1, hrowmem⟩
        have hmem : rowEmbed r ∈ rowsNZ :=
          Finset.mem_image.mpr ⟨r, Finset.mem_attach _ _, rfl⟩
        have heq : rowEmbed r = a := by
          apply Subtype.ext
          rfl
        have hmemA : a ∈ rowsNZ := by rw [← heq]; exact hmem
        exact (ha hmemA).elim
    · simp [f, hrow]
  have hfinite :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) = ∑ a ∈ rowsNZ, f a := by
    exact tsum_eq_sum (L := SummationFilter.unconditional _) hzero
  have hrowTerm (r : rows) :
      f (rowEmbed r) =
        W (qsN r.1 / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue r.1‖ ^ 2 := by
    have hr : rowCond r.1 := by
      have hrmem : r.1 ∈ rows := r.2
      change r.1 ∈
        ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset).filter
          (fun I => rowCond I) at hrmem
      exact (Finset.mem_filter.mp hrmem).2
    simp [f, rowCond, rowEmbed, hr]
  unfold qsHighEnergy
  change (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) = _
  rw [hfinite]
  calc
    ∑ a ∈ rowsNZ, f a = ∑ r ∈ rows.attach, f (rowEmbed r) :=
      Finset.sum_image hEmbedInj.injOn
    _ = ∑ r ∈ rows.attach,
          W (qsN r.1 / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue r.1‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hrowTerm r
    _ = ∑ a ∈ rows,
          W (qsN a / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2 :=
          Finset.sum_attach rows (fun a =>
            W (qsN a / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2)

private theorem qs_high_pair_finite_sum_local
    (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ : ℝ) (hM : 0 < M) (c d : Ideal (𝓞 K)) :
    qsHighPair F W M κ c d =
      ∑ a ∈ qsHighRows m qS M κ,
        (W (qsN a / M) : ℂ) * (F.character c).idealValue a *
          conj ((F.character d).idealValue a) := by
  classical
  let rows := qsHighRows m qS M κ
  let rowCond (I : Ideal (𝓞 K)) :=
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ∧ IsCoprime I qS ∧ κ < (qsSfNorm I : ℝ)
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if rowCond a.1 then
      (W (qsN a.1 / M) : ℂ) * (F.character c).idealValue a.1 *
        conj ((F.character d).idealValue a.1)
    else 0
  have hrow_nebot (I : Ideal (𝓞 K)) (hI : I ∈ rows) : I ≠ ⊥ := by
    dsimp [rows, qsHighRows] at hI
    exact (Finset.mem_filter.mp hI).2.1.1
  let rowEmbed (r : rows) : {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    ⟨r.1, hrow_nebot r.1 r.2⟩
  have hEmbedInj : Function.Injective rowEmbed := by
    intro r s h
    apply Subtype.ext
    change (rowEmbed r).1 = (rowEmbed s).1
    exact congrArg (fun x : {I : Ideal (𝓞 K) // I ≠ ⊥} => x.1) h
  let rowsNZ : Finset {I : Ideal (𝓞 K) // I ≠ ⊥} := rows.attach.image rowEmbed
  have hzero : ∀ a : {I : Ideal (𝓞 K) // I ≠ ⊥}, a ∉ rowsNZ → f a = 0 := by
    intro a ha
    by_cases hrow : rowCond a.1
    · by_cases hWzero : W (qsN a.1 / M) = 0
      · simp [f, hrow, hWzero]
      · have hlt : qsN a.1 / M < 5 / 2 := by
          apply lt_of_not_ge
          intro hge
          exact hWzero (hW.2.2.2 _ hge)
        have hNbound : (Ideal.absNorm a.1 : ℝ) < 3 * M := by
          dsimp [qsN] at hlt ⊢
          have hlt' := (div_lt_iff₀ hM).mp hlt
          nlinarith
        have hFloor : Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊ := Nat.le_floor hNbound.le
        have hbase : a.1 ∈
            (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset := by
          exact (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).mem_toFinset.mpr hFloor
        have hrowmem : a.1 ∈ rows := by
          dsimp [rows, qsHighRows]
          rw [Finset.mem_filter]
          exact ⟨hbase, hrow⟩
        let r : rows := ⟨a.1, hrowmem⟩
        have hmem : rowEmbed r ∈ rowsNZ :=
          Finset.mem_image.mpr ⟨r, Finset.mem_attach _ _, rfl⟩
        have heq : rowEmbed r = a := by
          apply Subtype.ext
          rfl
        have hmemA : a ∈ rowsNZ := by rw [← heq]; exact hmem
        exact (ha hmemA).elim
    · simp [f, hrow]
  have hfinite :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) = ∑ a ∈ rowsNZ, f a := by
    exact tsum_eq_sum (L := SummationFilter.unconditional _) hzero
  have hrowTerm (r : rows) :
      f (rowEmbed r) =
        (W (qsN r.1 / M) : ℂ) * (F.character c).idealValue r.1 *
          conj ((F.character d).idealValue r.1) := by
    have hr : rowCond r.1 := by
      have hrmem : r.1 ∈ rows := r.2
      change r.1 ∈
        ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset).filter
          (fun I => rowCond I) at hrmem
      exact (Finset.mem_filter.mp hrmem).2
    simp [f, rowCond, rowEmbed, hr]
  unfold qsHighPair
  change (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) = _
  rw [hfinite]
  calc
    ∑ a ∈ rowsNZ, f a = ∑ r ∈ rows.attach, f (rowEmbed r) :=
      Finset.sum_image hEmbedInj.injOn
    _ = ∑ r ∈ rows.attach,
          (W (qsN r.1 / M) : ℂ) * (F.character c).idealValue r.1 *
            conj ((F.character d).idealValue r.1) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hrowTerm r
    _ = ∑ a ∈ rows,
          (W (qsN a / M) : ℂ) * (F.character c).idealValue a *
            conj ((F.character d).idealValue a) :=
          Finset.sum_attach rows (fun a =>
            (W (qsN a / M) : ℂ) * (F.character c).idealValue a *
              conj ((F.character d).idealValue a))

private theorem qs_high_energy_pair_sum_local
    (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ : ℝ) (hM : 0 < M) (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) :
    ((qsHighEnergy F W M κ cols z : ℝ) : ℂ) =
      ∑ c ∈ cols, ∑ d ∈ cols,
        z c * conj (z d) * qsHighPair F W M κ c d := by
  classical
  let rows := qsHighRows m qS M κ
  have henergyFin := qs_high_energy_finite_sum_local F W hW M κ hM cols z
  have hpairFin (c d : Ideal (𝓞 K)) :=
    qs_high_pair_finite_sum_local F W hW M κ hM c d
  have hnorm (a : Ideal (𝓞 K)) :
      ((‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2 : ℝ) : ℂ) =
        (∑ c ∈ cols, z c * (F.character c).idealValue a) *
          conj (∑ c ∈ cols, z c * (F.character c).idealValue a) := by
    calc
      _ = (Complex.normSq (∑ c ∈ cols, z c * (F.character c).idealValue a) : ℂ) := by
            exact congrArg (fun x : ℝ => (x : ℂ))
              (Complex.normSq_eq_norm_sq _).symm
      _ = _ := (Complex.mul_conj _).symm
  have hdouble (a : Ideal (𝓞 K)) :
      (∑ c ∈ cols, z c * (F.character c).idealValue a) *
        conj (∑ d ∈ cols, z d * (F.character d).idealValue a) =
      ∑ c ∈ cols, ∑ d ∈ cols,
        z c * conj (z d) * (F.character c).idealValue a *
          conj ((F.character d).idealValue a) := by
    have hconj :
        conj (∑ d ∈ cols, z d * (F.character d).idealValue a) =
          ∑ d ∈ cols, conj (z d * (F.character d).idealValue a) := by
      simp only [map_sum]
    calc
      _ = (∑ c ∈ cols, z c * (F.character c).idealValue a) *
            (∑ d ∈ cols, conj (z d * (F.character d).idealValue a)) := by rw [hconj]
      _ = ∑ c ∈ cols, ∑ d ∈ cols,
            (z c * (F.character c).idealValue a) *
              conj (z d * (F.character d).idealValue a) := by
            rw [Finset.sum_mul_sum]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro d hd
            simp only [map_mul]
            ring
  have hrowExpand (a : Ideal (𝓞 K)) :
      ((W (qsN a / M) *
          ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2 : ℝ) : ℂ) =
        ∑ c ∈ cols, ∑ d ∈ cols,
          z c * conj (z d) * ((W (qsN a / M) : ℂ) *
            (F.character c).idealValue a * conj ((F.character d).idealValue a)) := by
    calc
      _ = (W (qsN a / M) : ℂ) *
            ((∑ c ∈ cols, z c * (F.character c).idealValue a) *
              conj (∑ d ∈ cols, z d * (F.character d).idealValue a)) := by
            rw [Complex.ofReal_mul, hnorm]
      _ = _ := by
            rw [hdouble]
            simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro d hd
            ring
  have henergyC :
      ((qsHighEnergy F W M κ cols z : ℝ) : ℂ) =
        ∑ a ∈ rows, ∑ c ∈ cols, ∑ d ∈ cols,
          z c * conj (z d) * ((W (qsN a / M) : ℂ) *
            (F.character c).idealValue a * conj ((F.character d).idealValue a)) := by
    rw [henergyFin]
    change algebraMap ℝ ℂ
        (∑ a ∈ rows, W (qsN a / M) *
          ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact hrowExpand a
  have hswap :
      (∑ a ∈ rows, ∑ c ∈ cols, ∑ d ∈ cols,
        z c * conj (z d) * ((W (qsN a / M) : ℂ) *
          (F.character c).idealValue a * conj ((F.character d).idealValue a))) =
      ∑ c ∈ cols, ∑ d ∈ cols, ∑ a ∈ rows,
        z c * conj (z d) * ((W (qsN a / M) : ℂ) *
          (F.character c).idealValue a * conj ((F.character d).idealValue a)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.sum_comm]
  calc
    ((qsHighEnergy F W M κ cols z : ℝ) : ℂ) =
        ∑ c ∈ cols, ∑ d ∈ cols, ∑ a ∈ rows,
          z c * conj (z d) * ((W (qsN a / M) : ℝ) : ℂ) *
            (F.character c).idealValue a * conj ((F.character d).idealValue a) := by
          rw [henergyC, hswap]
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = ∑ c ∈ cols, ∑ d ∈ cols,
          z c * conj (z d) * ∑ a ∈ rows,
            (W (qsN a / M) : ℂ) * (F.character c).idealValue a *
              conj ((F.character d).idealValue a) := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = ∑ c ∈ cols, ∑ d ∈ cols,
          z c * conj (z d) * qsHighPair F W M κ c d := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          rw [hpairFin c d]

open Classical in
/-- S0 (IMPL): exact gcd expansion of the energy of an admissible column set
(`|Σ_c z_c χ_c(a)|² = Σ_{c,d} z_c conj(z_d) χ_c(a) conj(χ_d(a))`, grouped by `g = c ⊔ d`). -/
theorem qs_gcd_expansion_S0 (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ : ℝ) (hM : 0 < M) (cols : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c) (z : Ideal (𝓞 K) → ℂ) :
    ((qsHighEnergy F W M κ cols z : ℝ) : ℂ) =
      ∑ g ∈ (cols ×ˢ cols).image (fun p => p.1 ⊔ p.2), qsGcdBlock F W M κ g cols z := by
  classical
  let pairs := cols ×ˢ cols
  let gcdMap : Ideal (𝓞 K) × Ideal (𝓞 K) → Ideal (𝓞 K) := fun p => p.1 ⊔ p.2
  let pairTerm (p : Ideal (𝓞 K) × Ideal (𝓞 K)) :=
    z p.1 * conj (z p.2) * qsHighPair F W M κ p.1 p.2
  have hblock (g : Ideal (𝓞 K)) :
      qsGcdBlock F W M κ g cols z =
        ∑ p ∈ pairs with gcdMap p = g, pairTerm p := by
    unfold qsGcdBlock
    rw [← Finset.sum_product', ← Finset.sum_filter]
  have hgroup :
      (∑ g ∈ pairs.image gcdMap, qsGcdBlock F W M κ g cols z) =
        ∑ p ∈ pairs, pairTerm p := by
    calc
      _ = ∑ g ∈ pairs.image gcdMap, ∑ p ∈ pairs with gcdMap p = g, pairTerm p := by
            apply Finset.sum_congr rfl
            intro g hg
            exact hblock g
      _ = ∑ p ∈ pairs, pairTerm p :=
            Finset.sum_fiberwise_of_maps_to
              (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) pairTerm
  calc
    ((qsHighEnergy F W M κ cols z : ℝ) : ℂ) =
        ∑ c ∈ cols, ∑ d ∈ cols,
          z c * conj (z d) * qsHighPair F W M κ c d :=
        qs_high_energy_pair_sum_local F W hW M κ hM cols z
    _ = ∑ p ∈ pairs, pairTerm p := by
          simpa [pairs, pairTerm] using
            (Finset.sum_product' cols cols (fun c d =>
              z c * conj (z d) * qsHighPair F W M κ c d)).symm
    _ = ∑ g ∈ (cols ×ˢ cols).image (fun p => p.1 ⊔ p.2),
          qsGcdBlock F W M κ g cols z := by
          simpa [pairs, gcdMap] using hgroup.symm

open Classical in
/-- S0 (IMPL): a gcd block is a residual block for the coprimality ideal `qsBadRad m qS * g`,
with residual columns `c' = c / g` (`c = g c'`) and shifted coefficients `z'(c') = z(g c')`. -/
theorem qs_residual_form_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ : ℝ) (hM : 0 < M)
    (g : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c) (z : Ideal (𝓞 K) → ℂ) :
    ∃ (cols' : Finset (Ideal (𝓞 K))) (z' : Ideal (𝓞 K) → ℂ),
      (∀ c' ∈ cols', QSAdm m qS c' ∧ IsCoprime c' g ∧ g * c' ∈ cols ∧ z' c' = z (g * c')) ∧
      (∀ c ∈ cols, g ∣ c → ∃ c' ∈ cols', c = g * c') ∧
      qsGcdBlock F W M κ g cols z = qsResidualBlock F W M κ (qsBadRad m qS * g) cols' z' := by
  classical
  let divCols := cols.filter (fun c => g ∣ c)
  let quot (c : Ideal (𝓞 K)) := if h : g ∣ c then Classical.choose h else ⊥
  let cols' := divCols.image quot
  have hmul (c : Ideal (𝓞 K)) (hgc : g ∣ c) : c = g * quot c := by
    simpa [quot, hgc] using (Classical.choose_spec hgc)
  have hprops (c : Ideal (𝓞 K)) (hcdiv : c ∈ divCols) :
      QSAdm m qS (quot c) ∧ IsCoprime (quot c) g ∧ g * quot c ∈ cols := by
    have hc : c ∈ cols := (Finset.mem_filter.mp hcdiv).1
    have hgc : g ∣ c := (Finset.mem_filter.mp hcdiv).2
    have hsq : Squarefree (quot c) := by
      apply (hcols c hc).1.squarefree_of_dvd
      exact ⟨g, by calc
        c = g * quot c := hmul c hgc
        _ = quot c * g := mul_comm _ _⟩
    have hcopg : IsCoprime (quot c) g := by
      have hrel : IsRelPrime g (quot c) := by
        have hs : Squarefree (g * quot c) := by
          rw [← hmul c hgc]
          exact (hcols c hc).1
        exact (squarefree_mul_iff.mp hs).1
      rw [Ideal.isCoprime_iff_sup_eq]
      have hunit : IsUnit (quot c ⊔ g) := by
        apply hrel.symm
        · exact Ideal.dvd_iff_le.mpr le_sup_left
        · exact Ideal.dvd_iff_le.mpr le_sup_right
      exact Ideal.isUnit_iff.mp hunit
    have hcopm : IsCoprime (quot c) (qsModulusRad m) := by
      have h := (qs_isCoprimeTo_iff_M0 c).mp (hcols c hc).2.1
      rw [hmul c hgc] at h
      exact h.2.of_mul_left_right
    have hcopq : IsCoprime (quot c) qS := by
      have h := (hcols c hc).2.2
      rw [hmul c hgc] at h
      exact h.of_mul_left_right
    refine ⟨?_, hcopg, ?_⟩
    · refine ⟨hsq, ?_, hcopq⟩
      exact (qs_isCoprimeTo_iff_M0 (quot c)).mpr ⟨hsq.ne_zero, hcopm⟩
    · rw [← hmul c hgc]
      exact hc
  have hmodrad0 : qsModulusRad m ≠ ⊥ := by
    classical
    unfold qsModulusRad
    induction m.finitePart.support using Finset.induction with
    | empty => simp
    | @insert v s hvs ih =>
      rw [Finset.prod_insert hvs]
      intro hp
      rcases Ideal.mul_eq_bot.mp hp with hv | hs
      · exact v.ne_bot hv
      · exact ih hs
  let badBase := qsModulusRad m * qS
  have hbadBase0 : badBase ≠ ⊥ := by
    change qsModulusRad m * qS ≠ ⊥
    intro hp
    rcases Ideal.mul_eq_bot.mp hp with hm | hq
    · exact hmodrad0 hm
    · exact hqS hq
  have hradEq : qsRad badBase = UniqueFactorizationMonoid.radical badBase := by rfl
  have hbadDiv : qsBadRad m qS ∣ badBase := by
    change qsRad badBase ∣ badBase
    rw [hradEq]
    exact UniqueFactorizationMonoid.radical_dvd_self
  obtain ⟨kbad, hbadPow⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow hbadBase0
  have hmodPow : qsModulusRad m ∣ (qsBadRad m qS) ^ kbad := by
    have hmodBase : qsModulusRad m ∣ badBase := ⟨qS, rfl⟩
    have hpow' : badBase ∣ (qsBadRad m qS) ^ kbad := by
      change badBase ∣ (qsRad badBase) ^ kbad
      rw [hradEq]
      exact hbadPow
    exact hmodBase.trans hpow'
  have hqPow : qS ∣ (qsBadRad m qS) ^ kbad := by
    have hqBase : qS ∣ badBase := by
      change qS ∣ qsModulusRad m * qS
      exact ⟨qsModulusRad m, by ac_rfl⟩
    have hpow' : badBase ∣ (qsBadRad m qS) ^ kbad := by
      change badBase ∣ (qsRad badBase) ^ kbad
      rw [hradEq]
      exact hbadPow
    exact hqBase.trans hpow'
  have hbadCoprime (a : Ideal (𝓞 K)) (ha : a ≠ ⊥) :
      (ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a ∧ IsCoprime a qS ∧ IsCoprime a g) ↔
        IsCoprime a (qsBadRad m qS * g) := by
    constructor
    · rintro ⟨hm, hq, hg⟩
      have hmod := ((qs_isCoprimeTo_iff_M0 a).mp hm).2
      have hbase : IsCoprime a badBase := hmod.mul_right hq
      have hbad : IsCoprime a (qsBadRad m qS) :=
        hbase.of_isCoprime_of_dvd_right hbadDiv
      exact hbad.mul_right hg
    · intro h
      have hbad : IsCoprime a (qsBadRad m qS) := h.of_mul_right_left
      have hg : IsCoprime a g := h.of_mul_right_right
      have hpower : IsCoprime a ((qsBadRad m qS) ^ kbad) := hbad.pow_right
      have hmrad : IsCoprime a (qsModulusRad m) :=
        hpower.of_isCoprime_of_dvd_right hmodPow
      have hq : IsCoprime a qS := hpower.of_isCoprime_of_dvd_right hqPow
      exact ⟨(qs_isCoprimeTo_iff_M0 a).mpr ⟨ha, hmrad⟩, hq, hg⟩
  have hdivJoin (c d : Ideal (𝓞 K)) (hjoin : c ⊔ d = g) : g ∣ c ∧ g ∣ d := by
    constructor
    · apply Ideal.dvd_iff_le.mpr
      rw [← hjoin]
      exact le_sup_left
    · apply Ideal.dvd_iff_le.mpr
      rw [← hjoin]
      exact le_sup_right
  have hgNonzeroOfDiv (c : Ideal (𝓞 K)) (hc : c ∈ cols) (hgc : g ∣ c) : g ≠ ⊥ := by
    intro hg0
    have hc0 : c ≠ ⊥ := (hcols c hc).1.ne_zero
    apply hc0
    rw [hmul c hgc, hg0]
    simp
  have hdivisorAdm (c : Ideal (𝓞 K)) (hc : c ∈ cols) (hgc : g ∣ c) : QSAdm m qS g := by
    have hsq := (hcols c hc).1.squarefree_of_dvd hgc
    have hcopm := (((qs_isCoprimeTo_iff_M0 c).mp (hcols c hc).2.1).2
      ).of_isCoprime_of_dvd_left hgc
    have hcopq := (hcols c hc).2.2.of_isCoprime_of_dvd_left hgc
    exact ⟨hsq, (qs_isCoprimeTo_iff_M0 g).mpr ⟨hsq.ne_zero, hcopm⟩, hcopq⟩
  have hquotCoprime (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols)
      (hjoin : c ⊔ d = g) : IsCoprime (quot c) (quot d) := by
    obtain ⟨hgc, hgd⟩ := hdivJoin c d hjoin
    have hg0 := hgNonzeroOfDiv c hc hgc
    have hxy : quot c ⊔ quot d = ⊤ := by
      apply mul_left_cancel₀ hg0
      calc
        g * (quot c ⊔ quot d) = (g * quot c) ⊔ (g * quot d) :=
          Ideal.mul_sup g (quot c) (quot d)
        _ = c ⊔ d := by rw [← hmul c hgc, ← hmul d hgd]
        _ = g := hjoin
        _ = g * ⊤ := by simp
    exact Ideal.isCoprime_iff_sup_eq.mpr hxy
  have hjoinOfQuotCoprime (x y : Ideal (𝓞 K)) (hxy : IsCoprime x y) :
      (g * x) ⊔ (g * y) = g := by
    calc
      (g * x) ⊔ (g * y) = g * (x ⊔ y) := (Ideal.mul_sup g x y).symm
      _ = g * ⊤ := by rw [Ideal.isCoprime_iff_sup_eq.mp hxy]
      _ = g := by simp
  have hkernel (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols)
      (hjoin : c ⊔ d = g) :
      qsHighPair F W M κ c d =
        qsHigh (fun x => (W x : ℂ)) M κ (qsBadRad m qS * g)
          (qsPairChar F (quot c) (quot d)) := by
    obtain ⟨hgc, hgd⟩ := hdivJoin c d hjoin
    have hxc := hprops c (Finset.mem_filter.mpr ⟨hc, hgc⟩)
    have hyd := hprops d (Finset.mem_filter.mpr ⟨hd, hgd⟩)
    have hgam := hdivisorAdm c hc hgc
    have hxy := hquotCoprime c d hc hd hjoin
    have hcopg := hxc.2.1.symm
    have hcopd := hyd.2.1.symm
    have hchar' (a : Ideal (𝓞 K)) (ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a)
        (haq : IsCoprime a qS) :
        (F.character c).idealValue a * conj ((F.character d).idealValue a) =
          if IsCoprime a g then (qsPairChar F (quot c) (quot d)).idealValue a else 0 := by
      have hchar := qs_gcd_pair_identity_S0 F hrf g (quot c) (quot d)
        hgam hxc.1 hyd.1 hcopg hcopd hxy a ha haq
      have hvalc := congrArg (fun I => (F.character I).idealValue a) (hmul c hgc)
      have hvald := congrArg (fun I => conj ((F.character I).idealValue a)) (hmul d hgd)
      calc
        _ = (F.character (g * quot c)).idealValue a *
              conj ((F.character (g * quot d)).idealValue a) := by rw [hvalc, hvald]
        _ = _ := hchar
    have hrow (a : Ideal (𝓞 K)) (ha : a ≠ ⊥) :
        (ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a ∧ IsCoprime a qS ∧ IsCoprime a g) ↔
          IsCoprime a (qsBadRad m qS * g) := hbadCoprime a ha
    rw [qsHighPair, qsHigh]
    apply tsum_congr
    intro a
    by_cases hold : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧
        IsCoprime a.1 qS ∧ κ < (qsSfNorm a.1 : ℝ)
    · have hchar := hchar' a.1 hold.1 hold.2.1
      by_cases hgcop : IsCoprime a.1 g
      · have hnew : IsCoprime a.1 (qsBadRad m qS * g) ∧
            κ < (qsSfNorm a.1 : ℝ) := by
          exact ⟨(hrow a.1 a.2).mp ⟨hold.1, hold.2.1, hgcop⟩, hold.2.2⟩
        simp only [if_pos hold, if_pos hnew]
        calc
          _ = (W (qsN a.1 / M) : ℂ) *
                ((F.character c).idealValue a.1 * conj ((F.character d).idealValue a.1)) := by ring
          _ = (W (qsN a.1 / M) : ℂ) * (qsPairChar F (quot c) (quot d)).idealValue a.1 := by
            rw [hchar]
            simp [hgcop]
          _ = (qsPairChar F (quot c) (quot d)).idealValue a.1 *
                (W (qsN a.1 / M) : ℂ) := by ring
      · have hnew : ¬ (IsCoprime a.1 (qsBadRad m qS * g) ∧
            κ < (qsSfNorm a.1 : ℝ)) := by
          rintro ⟨hbad, _⟩
          exact hgcop ((hrow a.1 a.2).mpr hbad).2.2
        simp only [if_pos hold, if_neg hnew]
        calc
          _ = (W (qsN a.1 / M) : ℂ) *
                ((F.character c).idealValue a.1 * conj ((F.character d).idealValue a.1)) := by ring
          _ = 0 := by rw [hchar]; simp [hgcop]
    · have hnew : ¬ (IsCoprime a.1 (qsBadRad m qS * g) ∧
          κ < (qsSfNorm a.1 : ℝ)) := by
        rintro ⟨hbad, hsf⟩
        exact hold ⟨((hrow a.1 a.2).mpr hbad).1,
          ((hrow a.1 a.2).mpr hbad).2.1, hsf⟩
      simp [hold, hnew]
  refine ⟨cols', fun c' => z (g * c'), ?_, ?_, ?_⟩
  · intro c' hc'
    rcases Finset.mem_image.mp hc' with ⟨c, hcdiv, rfl⟩
    rcases hprops c hcdiv with ⟨hadm, hcopg, hmem⟩
    exact ⟨hadm, hcopg, hmem, rfl⟩
  · intro c hc hgc
    refine ⟨quot c, Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hgc⟩, rfl⟩, ?_⟩
    exact hmul c hgc
  · let sourcePairs := (cols ×ˢ cols).filter (fun p => p.1 ⊔ p.2 = g)
    let targetPairs := (cols' ×ˢ cols').filter (fun p => IsCoprime p.1 p.2)
    let sourceTerm := fun p : Ideal (𝓞 K) × Ideal (𝓞 K) =>
      z p.1 * conj (z p.2) * qsHighPair F W M κ p.1 p.2
    let targetTerm := fun p : Ideal (𝓞 K) × Ideal (𝓞 K) =>
      z (g * p.1) * conj (z (g * p.2)) *
        qsHigh (fun x => (W x : ℂ)) M κ (qsBadRad m qS * g) (qsPairChar F p.1 p.2)
    have hleft : qsGcdBlock F W M κ g cols z =
        ∑ p ∈ sourcePairs, sourceTerm p := by
      unfold qsGcdBlock
      rw [← Finset.sum_product']
      rw [← Finset.sum_filter]
    have hright : qsResidualBlock F W M κ (qsBadRad m qS * g) cols'
        (fun c' => z (g * c')) = ∑ p ∈ targetPairs, targetTerm p := by
      unfold qsResidualBlock qsPairSum
      rw [← Finset.sum_product']
      rw [← Finset.sum_filter]
    have hbij : (∑ p ∈ sourcePairs, sourceTerm p) =
        ∑ p ∈ targetPairs, targetTerm p := by
      apply Finset.sum_bij (fun p _ => (quot p.1, quot p.2))
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hprod, hjoin⟩
        rcases Finset.mem_product.mp hprod with ⟨hc, hd⟩
        obtain ⟨hgc, hgd⟩ := hdivJoin p.1 p.2 hjoin
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
          Finset.mem_image.mpr ⟨p.1, Finset.mem_filter.mpr ⟨hc, hgc⟩, rfl⟩,
          Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨hd, hgd⟩, rfl⟩⟩,
          hquotCoprime p.1 p.2 hc hd hjoin⟩
      · intro p hp q hq hmap
        rcases Finset.mem_filter.mp hp with ⟨hprod, hpjoin⟩
        rcases Finset.mem_product.mp hprod with ⟨hp1, hp2⟩
        rcases Finset.mem_filter.mp hq with ⟨hprod', hqjoin⟩
        rcases Finset.mem_product.mp hprod' with ⟨hq1, hq2⟩
        obtain ⟨hpg1, hpg2⟩ := hdivJoin p.1 p.2 hpjoin
        obtain ⟨hqg1, hqg2⟩ := hdivJoin q.1 q.2 hqjoin
        apply Prod.ext
        · calc
            p.1 = g * quot p.1 := hmul p.1 hpg1
            _ = g * quot q.1 := congrArg (fun x => g * x) (congrArg Prod.fst hmap)
            _ = q.1 := (hmul q.1 hqg1).symm
        · calc
            p.2 = g * quot p.2 := hmul p.2 hpg2
            _ = g * quot q.2 := congrArg (fun x => g * x) (congrArg Prod.snd hmap)
            _ = q.2 := (hmul q.2 hqg2).symm
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hprod, hcop⟩
        rcases Finset.mem_product.mp hprod with ⟨hp1, hp2⟩
        rcases Finset.mem_image.mp hp1 with ⟨c, hcdiv, hcx⟩
        rcases Finset.mem_image.mp hp2 with ⟨d, hddiv, hdy⟩
        have hc : c ∈ cols := (Finset.mem_filter.mp hcdiv).1
        have hd : d ∈ cols := (Finset.mem_filter.mp hddiv).1
        have hgc : g ∣ c := (Finset.mem_filter.mp hcdiv).2
        have hgd : g ∣ d := (Finset.mem_filter.mp hddiv).2
        have hjoin : c ⊔ d = g := by
          calc
            c ⊔ d = (g * quot c) ⊔ (g * quot d) :=
              congrArg₂ (fun x y => x ⊔ y) (hmul c hgc) (hmul d hgd)
            _ = (g * p.1) ⊔ (g * p.2) := by rw [hcx, hdy]
            _ = g := hjoinOfQuotCoprime p.1 p.2 hcop
        refine ⟨(c, d), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hc, hd⟩, hjoin⟩, ?_⟩
        exact Prod.ext hcx hdy
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hprod, hjoin⟩
        rcases Finset.mem_product.mp hprod with ⟨hc, hd⟩
        obtain ⟨hgc, hgd⟩ := hdivJoin p.1 p.2 hjoin
        have hkernel' := hkernel p.1 p.2 hc hd hjoin
        have hz1 := congrArg z (hmul p.1 hgc)
        have hz2 := congrArg (fun x => conj (z x)) (hmul p.2 hgd)
        dsimp [sourceTerm, targetTerm]
        calc
          z p.1 * conj (z p.2) * qsHighPair F W M κ p.1 p.2 =
              z (g * quot p.1) * conj (z (g * quot p.2)) *
                qsHighPair F W M κ p.1 p.2 := by rw [hz1, hz2]
          _ = z (g * quot p.1) * conj (z (g * quot p.2)) *
                qsHigh (fun x => (W x : ℂ)) M κ (qsBadRad m qS * g)
                  (qsPairChar F (quot p.1) (quot p.2)) := by rw [hkernel']
    calc
      qsGcdBlock F W M κ g cols z = ∑ p ∈ sourcePairs, sourceTerm p := hleft
      _ = ∑ p ∈ targetPairs, targetTerm p := hbij
      _ = qsResidualBlock F W M κ (qsBadRad m qS * g) cols'
            (fun c' => z (g * c')) := hright.symm

theorem qsMu_sum_divisors (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    [Fintype {e : Ideal (𝓞 K) // e ∣ I}] :
    (∑ e : {e : Ideal (𝓞 K) // e ∣ I}, (qsMu e.1 : ℤ)) =
      if I = ⊤ then 1 else 0 := by
  classical
  let support := (UniqueFactorizationMonoid.normalizedFactors I).toFinset
  let squarefreeDivs := (Finset.univ : Finset {e : Ideal (𝓞 K) // e ∣ I}).filter
    (fun e => Squarefree e.1)
  have hfiltered :
      (∑ e ∈ squarefreeDivs, (qsMu e.1 : ℤ)) =
        ∑ e : {e : Ideal (𝓞 K) // e ∣ I}, (qsMu e.1 : ℤ) := by
    unfold squarefreeDivs
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hsq : Squarefree e.1 <;> simp [qsMu, hsq]
  have hbij : (∑ e ∈ squarefreeDivs, (qsMu e.1 : ℤ)) =
      ∑ A ∈ support.powerset, (-1 : ℤ) ^ A.card := by
    apply Finset.sum_bij
      (fun e _ => (UniqueFactorizationMonoid.normalizedFactors e.1).toFinset)
    · intro e he
      have hsq : Squarefree e.1 := (Finset.mem_filter.mp he).2
      have hdvd := e.2
      have hfacLe := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
        hsq.ne_zero hI).mp hdvd
      apply Finset.mem_powerset.mpr
      intro p hp
      exact Multiset.mem_toFinset.mpr <| Multiset.mem_of_le hfacLe
        (Multiset.mem_toFinset.mp hp)
    · intro e he d hd heq
      have hsqe : Squarefree e.1 := (Finset.mem_filter.mp he).2
      have hsqd : Squarefree d.1 := (Finset.mem_filter.mp hd).2
      have hfacEq : UniqueFactorizationMonoid.normalizedFactors e.1 =
          UniqueFactorizationMonoid.normalizedFactors d.1 :=
        Multiset.Nodup.toFinset_inj
          ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsqe.ne_zero).mp hsqe)
          ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsqd.ne_zero).mp hsqd) heq
      have hassoc : Associated e.1 d.1 :=
        (UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors
          hsqe.ne_zero hsqd.ne_zero).mpr hfacEq
      exact Subtype.ext (associated_iff_eq.mp hassoc)
    · intro A hA
      let e := A.val.prod
      have hsubset : ∀ p ∈ A.val, p ∈ UniqueFactorizationMonoid.normalizedFactors I := by
        intro p hp
        have hpA : p ∈ A := by simpa using hp
        exact Multiset.mem_toFinset.mp ((Finset.mem_powerset.mp hA) hpA)
      have hfac : UniqueFactorizationMonoid.normalizedFactors e = A.val :=
        UniqueFactorizationMonoid.normalizedFactors_prod_eq_self_of_subset hsubset
      have hradEq : qsRad I = UniqueFactorizationMonoid.radical I := by rfl
      have hradDiv : qsRad I ∣ I := by
        rw [hradEq]
        exact UniqueFactorizationMonoid.radical_dvd_self
      have heRad : e ∣ qsRad I := by
        change A.val.prod ∣ support.prod id
        rw [Finset.prod_val]
        exact Finset.prod_dvd_prod_of_subset A support id (Finset.mem_powerset.mp hA)
      have heDiv : e ∣ I := heRad.trans hradDiv
      have heSq : Squarefree e := by
        have hsqRad : Squarefree (qsRad I) := by
          rw [hradEq]
          exact UniqueFactorizationMonoid.squarefree_radical
        exact hsqRad.squarefree_of_dvd heRad
      refine ⟨⟨e, heDiv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heSq⟩, ?_⟩
      rw [hfac]
      simp
    · intro e he
      have hsq : Squarefree e.1 := (Finset.mem_filter.mp he).2
      have hnd :=
        (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsq.ne_zero).mp hsq
      change (qsMu e.1 : ℤ) =
        (-1 : ℤ) ^ (UniqueFactorizationMonoid.normalizedFactors e.1).toFinset.card
      rw [qsMu, if_pos hsq, Multiset.toFinset_card_of_nodup hnd]
  have hsumPowerset :
      (∑ A ∈ support.powerset, (-1 : ℤ) ^ A.card) =
        ∏ p ∈ support, (1 + (-1 : ℤ)) := by
    simpa [Finset.prod_const] using
      (Finset.prod_one_add (s := support) (f := fun _ : Ideal (𝓞 K) => (-1 : ℤ))).symm
  have hsupportEmpty : support = ∅ ↔ I = ⊤ := by
    constructor
    · intro h
      have hunit : IsUnit I := by
        have hpf : UniqueFactorizationMonoid.primeFactors I = ∅ := by
          change UniqueFactorizationMonoid.primeFactors I = ∅
          exact h
        exact (UniqueFactorizationMonoid.primeFactors_eq_empty_iff hI).mp hpf
      exact Ideal.isUnit_iff.mp hunit
    · intro htop
      unfold support
      rw [htop]
      change UniqueFactorizationMonoid.primeFactors (⊤ : Ideal (𝓞 K)) = ∅
      rw [show (⊤ : Ideal (𝓞 K)) = 1 by simp]
      exact UniqueFactorizationMonoid.primeFactors_one
  have hprodEq : ∏ p ∈ support, (1 + (-1 : ℤ)) = if I = ⊤ then 1 else 0 := by
    by_cases h : support = ∅
    · simp [h, hsupportEmpty.mp h]
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr h
      have hne : I ≠ ⊤ := fun hi => h (hsupportEmpty.mpr hi)
      rw [Finset.prod_eq_zero hp (by norm_num)]
      simp [hne]
  rw [← hfiltered, hbij, hsumPowerset, hprodEq]

private theorem qsMu_sum_antidiagonal (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (∑ p ∈ ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K
      ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, (qsMu p.1.1 : ℤ)) =
        if I = ⊤ then 1 else 0 := by
  classical
  letI : Fintype {e : Ideal (𝓞 K) // e ∣ I} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd I hI
  calc
    _ = ∑ e ∈ (Finset.univ : Finset {e : Ideal (𝓞 K) // e ∣ I}), (qsMu e.1 : ℤ) := by
      refine Finset.sum_bij
        (fun p hp => ⟨p.1.1, ⟨p.2.1, by
          have hprod := congrArg (fun J : (Ideal (𝓞 K))⁰ => J.1)
            ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
          exact hprod.symm⟩⟩)
        ?_ ?_ ?_ ?_
      · intro p hp
        exact Finset.mem_univ _
      · intro p hp q hq heq
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun e : {e : Ideal (𝓞 K) // e ∣ I} => e.1) heq
        · apply Subtype.ext
          have hfirst : p.1.1 = q.1.1 :=
            congrArg (fun e : {e : Ideal (𝓞 K) // e ∣ I} => e.1) heq
          have hp' := congrArg (fun J : (Ideal (𝓞 K))⁰ => J.1)
            ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
          have hq' := congrArg (fun J : (Ideal (𝓞 K))⁰ => J.1)
            ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hq)
          have hmul : p.1.1 * p.2.1 = p.1.1 * q.2.1 := by
            calc
              p.1.1 * p.2.1 = I := hp'
              _ = q.1.1 * q.2.1 := hq'.symm
              _ = p.1.1 * q.2.1 := by rw [hfirst]
          exact mul_left_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp p.1.2) hmul
      · intro e he
        rcases e.2 with ⟨q, hq⟩
        have he0 : e.1 ≠ ⊥ := by
          intro he0
          apply hI
          rw [hq, he0]
          simp
        have hq0 : q ≠ ⊥ := by
          intro hq0
          apply hI
          rw [hq, hq0]
          simp
        let p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ :=
          (⟨e.1, mem_nonZeroDivisors_of_ne_zero he0⟩,
            ⟨q, mem_nonZeroDivisors_of_ne_zero hq0⟩)
        have hp : p ∈ ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K
            ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ := by
          apply (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mpr
          exact Subtype.ext hq.symm
        refine ⟨p, hp, ?_⟩
        apply Subtype.ext
        rfl
      · intro p hp
        rfl
    _ = if I = ⊤ then 1 else 0 := qsMu_sum_divisors I hI

private noncomputable def qsGcdDescentBeta (G : ℝ) (t : (Ideal (𝓞 K))⁰) : ℤ :=
  ∑ p ∈ ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K t,
    if G < qsN p.2.1 then qsMu p.1.1 else 0

private theorem qsGcdDescentBeta_sum (G : ℝ) (I : (Ideal (𝓞 K))⁰) :
    (∑ t ∈ (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K I).image Prod.fst,
      qsGcdDescentBeta G t) = if G < qsN I.1 then 1 else 0 := by
  classical
  let D := ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K
  let divs := (D I).image Prod.fst
  let triples := (divs ×ˢ (divs ×ˢ divs)).filter
    (fun x => x.1.1 * (x.2.1.1 * x.2.2.1) = I.1)
  have memDivsOfProd (a b : (Ideal (𝓞 K))⁰) (hab : a.1 * b.1 = I.1) : a ∈ divs := by
    have hp : (a, b) ∈ D I := by
      apply (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mpr
      exact Subtype.ext hab
    exact Finset.mem_image.mpr ⟨(a, b), hp, rfl⟩
  let src : Finset (Σ p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰,
      (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) :=
    (D I).sigma (fun p => D (p.1))
  let tgt : Finset (Σ p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰,
      (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) :=
    (D I).sigma (fun p => D (p.2))
  let srcTriple := fun x : Σ p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰,
      (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ =>
    (x.2.1, (x.2.2, x.1.2))
  let tgtTriple := fun x : Σ p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰,
      (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ =>
    (x.2.1, (x.1.1, x.2.2))
  have houter : (∑ t ∈ divs, qsGcdDescentBeta G t) =
      ∑ p ∈ D I, qsGcdDescentBeta G p.1 := by
    symm
    apply Finset.sum_bij (fun p _ => p.1)
    · intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · intro p hp q hq heq
      apply Prod.ext
      · exact heq
      · apply Subtype.ext
        have hfirst := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1) heq
        have hp' := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
          ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
        have hq' := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
          ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hq)
        have hmul : p.1.1 * p.2.1 = p.1.1 * q.2.1 := by
          calc
            p.1.1 * p.2.1 = I.1 := hp'
            _ = q.1.1 * q.2.1 := hq'.symm
            _ = p.1.1 * q.2.1 := by rw [hfirst]
        exact mul_left_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp p.1.2) hmul
    · intro t ht
      rcases Finset.mem_image.mp ht with ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · intro p hp
      rfl
  have hsrc : (∑ p ∈ D I, qsGcdDescentBeta G p.1) =
      ∑ x ∈ src, (qsMu x.2.1.1 : ℤ) *
        (if G < qsN x.2.2.1 then 1 else 0) := by
    unfold qsGcdDescentBeta
    simpa [src] using
      (Finset.sum_sigma' (D I) (fun p => D (p.1))
        (fun p q => (qsMu q.1.1 : ℤ) * (if G < qsN q.2.1 then 1 else 0)))
  have hsrcTriple :
      (∑ x ∈ src, (qsMu x.2.1.1 : ℤ) * (if G < qsN x.2.2.1 then 1 else 0)) =
        ∑ x ∈ triples, (qsMu x.1.1 : ℤ) * (if G < qsN x.2.1.1 then 1 else 0) := by
    apply Finset.sum_bij (fun x _ => srcTriple x)
    · intro x hx
      rcases Finset.mem_sigma.mp hx with ⟨hp, hq⟩
      have hpe := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
      have hqe := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hq)
      have hpe' : x.1.1.1 * x.1.2.1 = I.1 := by simpa using hpe
      have hqe' : x.2.1.1 * x.2.2.1 = x.1.1.1 := by simpa using hqe
      have hprod : x.2.1.1 * (x.2.2.1 * x.1.2.1) = I.1 := by
        calc
          x.2.1.1 * (x.2.2.1 * x.1.2.1) =
              (x.2.1.1 * x.2.2.1) * x.1.2.1 := by ac_rfl
          _ = x.1.1.1 * x.1.2.1 := by rw [hqe']
          _ = I.1 := hpe'
      have hgprod : x.2.2.1 * (x.2.1.1 * x.1.2.1) = I.1 := by
        calc
          x.2.2.1 * (x.2.1.1 * x.1.2.1) =
              x.2.1.1 * (x.2.2.1 * x.1.2.1) := by ac_rfl
          _ = I.1 := hprod
      have hhprod : x.1.2.1 * x.1.1.1 = I.1 := by
        calc
          x.1.2.1 * x.1.1.1 = x.1.1.1 * x.1.2.1 := mul_comm _ _
          _ = I.1 := hpe'
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
        memDivsOfProd x.2.1 (x.2.2 * x.1.2) hprod,
        Finset.mem_product.mpr ⟨memDivsOfProd x.2.2 (x.2.1 * x.1.2) hgprod,
          memDivsOfProd x.1.2 x.1.1 hhprod⟩⟩, hprod⟩
    · intro x hx y hy heq
      have he : x.2.1.1 = y.2.1.1 := congrArg (fun z => z.1.1) heq
      have hg : x.2.2.1 = y.2.2.1 := congrArg (fun z => z.2.1.1) heq
      have hh : x.1.2.1 = y.1.2.1 := congrArg (fun z => z.2.2.1) heq
      have hxq := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp
          (Finset.mem_sigma.mp hx).2)
      have hyq := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp
          (Finset.mem_sigma.mp hy).2)
      have ht : x.1.1.1 = y.1.1.1 := by
        calc
          x.1.1.1 = x.2.1.1 * x.2.2.1 := hxq.symm
          _ = y.2.1.1 * y.2.2.1 := by rw [he, hg]
          _ = y.1.1.1 := hyq
      have hpEq : x.1 = y.1 := by
        apply Prod.ext
        · exact Subtype.ext ht
        · exact Subtype.ext hh
      have hqEq : x.2 = y.2 := by
        apply Prod.ext
        · exact Subtype.ext he
        · exact Subtype.ext hg
      exact Sigma.ext hpEq (heq_of_eq hqEq)
    · intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzprod, htotal⟩
      rcases Finset.mem_product.mp hzprod with ⟨he, hgh⟩
      rcases Finset.mem_product.mp hgh with ⟨hg, hh⟩
      let e := z.1
      let g := z.2.1
      let h := z.2.2
      have houterProd : e.1 * g.1 * h.1 = I.1 := by
        simpa [mul_assoc] using htotal
      have hp : (e * g, h) ∈ D I := by
        apply (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mpr
        exact Subtype.ext houterProd
      have hq : (e, g) ∈ D (e * g) := by
        apply (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mpr
        rfl
      refine ⟨⟨(e * g, h), (e, g)⟩, Finset.mem_sigma.mpr ⟨hp, hq⟩, ?_⟩
      rfl
    · intro x hx
      rfl
  have htgtTriple :
      (∑ x ∈ tgt, (qsMu x.2.1.1 : ℤ) * (if G < qsN x.1.1.1 then 1 else 0)) =
        ∑ x ∈ triples, (qsMu x.1.1 : ℤ) * (if G < qsN x.2.1.1 then 1 else 0) := by
    apply Finset.sum_bij (fun x _ => tgtTriple x)
    · intro x hx
      rcases Finset.mem_sigma.mp hx with ⟨hp, hq⟩
      have hpe := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
      have hqe := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hq)
      have hpe' : x.1.1.1 * x.1.2.1 = I.1 := by simpa using hpe
      have hqe' : x.2.1.1 * x.2.2.1 = x.1.2.1 := by simpa using hqe
      have hprod : x.2.1.1 * (x.1.1.1 * x.2.2.1) = I.1 := by
        calc
          x.2.1.1 * (x.1.1.1 * x.2.2.1) =
              x.1.1.1 * (x.2.1.1 * x.2.2.1) := by ac_rfl
          _ = x.1.1.1 * x.1.2.1 := by rw [hqe']
          _ = I.1 := hpe'
      have hhprod : x.2.2.1 * (x.1.1.1 * x.2.1.1) = I.1 := by
        calc
          x.2.2.1 * (x.1.1.1 * x.2.1.1) =
              x.2.1.1 * (x.1.1.1 * x.2.2.1) := by ac_rfl
          _ = I.1 := hprod
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
        memDivsOfProd x.2.1 (x.1.1 * x.2.2) hprod,
        Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x.1, hp, rfl⟩,
          memDivsOfProd x.2.2 (x.1.1 * x.2.1) hhprod⟩⟩, hprod⟩
    · intro x hx y hy heq
      have he : x.2.1.1 = y.2.1.1 := congrArg (fun z => z.1.1) heq
      have hg : x.1.1.1 = y.1.1.1 := congrArg (fun z => z.2.1.1) heq
      have hh : x.2.2.1 = y.2.2.1 := congrArg (fun z => z.2.2.1) heq
      have hxq := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp
          (Finset.mem_sigma.mp hx).2)
      have hyq := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp
          (Finset.mem_sigma.mp hy).2)
      have hu : x.1.2.1 = y.1.2.1 := by
        calc
          x.1.2.1 = x.2.1.1 * x.2.2.1 := hxq.symm
          _ = y.2.1.1 * y.2.2.1 := by rw [he, hh]
          _ = y.1.2.1 := hyq
      have hpEq : x.1 = y.1 := by
        apply Prod.ext
        · exact Subtype.ext hg
        · exact Subtype.ext hu
      have hqEq : x.2 = y.2 := by
        apply Prod.ext
        · exact Subtype.ext he
        · exact Subtype.ext hh
      exact Sigma.ext hpEq (heq_of_eq hqEq)
    · intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzprod, htotal⟩
      rcases Finset.mem_product.mp hzprod with ⟨he, hgh⟩
      rcases Finset.mem_product.mp hgh with ⟨hg, hh⟩
      let e := z.1
      let g := z.2.1
      let h := z.2.2
      have houterProd : g.1 * (e.1 * h.1) = I.1 := by
        simpa [e, g, h, mul_assoc, mul_comm, mul_left_comm] using htotal
      have hp : (g, e * h) ∈ D I := by
        apply (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mpr
        exact Subtype.ext houterProd
      have hq : (e, h) ∈ D (e * h) := by
        apply (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mpr
        rfl
      refine ⟨⟨(g, e * h), (e, h)⟩, Finset.mem_sigma.mpr ⟨hp, hq⟩, ?_⟩
      rfl
    · intro x hx
      rfl
  have hsigmaTgt :
      (∑ x ∈ tgt, (qsMu x.2.1.1 : ℤ) * (if G < qsN x.1.1.1 then 1 else 0)) =
        ∑ p ∈ D I, ∑ q ∈ D p.2,
          (qsMu q.1.1 : ℤ) * (if G < qsN p.1.1 then 1 else 0) := by
    simpa [tgt] using
      (Finset.sum_sigma' (D I) (fun p => D p.2)
        (fun p q => (qsMu q.1.1 : ℤ) * (if G < qsN p.1.1 then 1 else 0))).symm
  have hsum : (∑ p ∈ D I, qsGcdDescentBeta G p.1) =
      ∑ p ∈ D I, (if G < qsN p.1.1 then 1 else 0) *
        (if p.2.1 = ⊤ then 1 else 0) := by
    calc
      _ = ∑ x ∈ src, (qsMu x.2.1.1 : ℤ) *
            (if G < qsN x.2.2.1 then 1 else 0) := hsrc
      _ = ∑ x ∈ triples, (qsMu x.1.1 : ℤ) *
            (if G < qsN x.2.1.1 then 1 else 0) := hsrcTriple
      _ = ∑ x ∈ tgt, (qsMu x.2.1.1 : ℤ) *
            (if G < qsN x.1.1.1 then 1 else 0) := htgtTriple.symm
      _ = ∑ p ∈ D I, ∑ q ∈ D p.2,
            (qsMu q.1.1 : ℤ) * (if G < qsN p.1.1 then 1 else 0) := hsigmaTgt
      _ = ∑ p ∈ D I, (if G < qsN p.1.1 then 1 else 0) *
            (if p.2.1 = ⊤ then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hfactor :
            (∑ q ∈ D p.2, (qsMu q.1.1 : ℤ) * (if G < qsN p.1.1 then 1 else 0)) =
              (if G < qsN p.1.1 then 1 else 0) *
                ∑ q ∈ D p.2, (qsMu q.1.1 : ℤ) := by
          calc
            _ = (∑ q ∈ D p.2, (qsMu q.1.1 : ℤ)) *
                  (if G < qsN p.1.1 then 1 else 0) := by
              rw [Finset.sum_mul]
            _ = _ := by ring
        calc
          _ = (if G < qsN p.1.1 then 1 else 0) *
                (∑ q ∈ D p.2, (qsMu q.1.1 : ℤ)) := hfactor
          _ = (if G < qsN p.1.1 then 1 else 0) *
                (if p.2.1 = ⊤ then 1 else 0) := by
            rw [qsMu_sum_antidiagonal p.2.1
              (mem_nonZeroDivisors_iff_ne_zero.mp p.2.2)]
  have hcollapse : (∑ p ∈ D I, (if G < qsN p.1.1 then (1 : ℤ) else 0) *
        (if p.2.1 = ⊤ then 1 else 0)) = if G < qsN I.1 then (1 : ℤ) else 0 := by
    let p₀ : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ := (I, 1)
    have hp₀ : p₀ ∈ D I := by
      apply (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mpr
      simp [p₀]
    have hfilter : (D I).filter (fun p => p.2.1 = ⊤) = {p₀} := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hp, htop⟩
        have hprod := congrArg (fun t : (Ideal (𝓞 K))⁰ => t.1)
          ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
        have hfst : p.1.1 = I.1 := by
          calc
            p.1.1 = p.1.1 * ⊤ := by simp
            _ = I.1 := by rw [← htop]; exact hprod
        apply Finset.mem_singleton.mpr
        apply Prod.ext
        · exact Subtype.ext hfst
        · apply Subtype.ext
          have htop' : p.2.1 = (1 : Ideal (𝓞 K)) := by
            simpa using htop
          exact htop'
      · intro hp
        have : p = p₀ := Finset.mem_singleton.mp hp
        subst p
        exact Finset.mem_filter.mpr ⟨hp₀, by simp [p₀]⟩
    have hsumFilter :
        (∑ p ∈ D I, (if G < qsN p.1.1 then (1 : ℤ) else 0) *
            (if p.2.1 = ⊤ then 1 else 0)) =
        ∑ p ∈ (D I).filter (fun p => p.2.1 = ⊤),
          (if G < qsN p.1.1 then 1 else 0) := by
      calc
        (∑ p ∈ D I, (if G < qsN p.1.1 then (1 : ℤ) else 0) *
            (if p.2.1 = ⊤ then 1 else 0)) =
            ∑ p ∈ D I, if p.2.1 = ⊤ then
              (if G < qsN p.1.1 then 1 else 0) else 0 := by
          exact Finset.sum_congr (s₁ := D I) (s₂ := D I)
            (f := fun p => (if G < qsN p.1.1 then (1 : ℤ) else 0) *
              (if p.2.1 = ⊤ then 1 else 0))
            (g := fun p => if p.2.1 = ⊤ then (if G < qsN p.1.1 then 1 else 0) else 0)
            rfl (fun p hp => by
              by_cases htop : p.2.1 = ⊤ <;> simp [htop])
        _ = _ :=
          (Finset.sum_filter (s := D I) (fun p => p.2.1 = ⊤)
            (fun p => if G < qsN p.1.1 then 1 else 0)).symm
    calc
      (∑ p ∈ D I, (if G < qsN p.1.1 then (1 : ℤ) else 0) *
          (if p.2.1 = ⊤ then 1 else 0)) =
          ∑ p ∈ (D I).filter (fun p => p.2.1 = ⊤),
            (if G < qsN p.1.1 then 1 else 0) := hsumFilter
      _ = (if G < qsN p₀.1.1 then 1 else 0) := by
        rw [hfilter, Finset.sum_singleton]
      _ = if G < qsN I.1 then 1 else 0 := rfl
  calc
    _ = ∑ p ∈ D I, qsGcdDescentBeta G p.1 := houter
    _ = ∑ p ∈ D I, (if G < qsN p.1.1 then 1 else 0) *
          (if p.2.1 = ⊤ then 1 else 0) := hsum
    _ = if G < qsN I.1 then 1 else 0 := hcollapse

private theorem qs_absNorm_le_of_dvd (a b : Ideal (𝓞 K)) (hb : b ≠ ⊥)
    (hab : a ∣ b) : Ideal.absNorm a ≤ Ideal.absNorm b := by
  have hdiv : Ideal.absNorm a ∣ Ideal.absNorm b :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hab)
  have hbpos : 0 < Ideal.absNorm b :=
    Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero hb)
  exact Nat.le_of_dvd hbpos hdiv

private theorem qsN_le_of_dvd (a b : Ideal (𝓞 K)) (hb : b ≠ ⊥)
    (hab : a ∣ b) : qsN a ≤ qsN b := by
  exact_mod_cast qs_absNorm_le_of_dvd a b hb hab

theorem qs_dvd_mem_qsDivisors (a b : Ideal (𝓞 K)) (hb : b ≠ ⊥)
    (hab : a ∣ b) : a ∈ qsDivisors b := by
  classical
  have hfloor : ⌊qsN b⌋₊ = Ideal.absNorm b := by simp [qsN]
  have hbound := qs_absNorm_le_of_dvd a b hb hab
  unfold qsDivisors
  refine Finset.mem_filter.mpr ⟨?_, hab⟩
  have hset : a ∈ {J : Ideal (𝓞 K) | Ideal.absNorm J ≤ ⌊qsN b⌋₊} := by
    change Ideal.absNorm a ≤ ⌊qsN b⌋₊
    rw [hfloor]
    exact hbound
  simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hfloor] using hset

private theorem qsMu_real_norm_le_one (e : Ideal (𝓞 K)) :
    ‖(qsMu e : ℝ)‖ ≤ 1 := by
  classical
  by_cases hsq : Squarefree e
  · simp [qsMu, hsq]
  · simp [qsMu, hsq]

private theorem qsGcdDescentBeta_norm_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ) (t : (Ideal (𝓞 K))⁰),
      ‖(qsGcdDescentBeta G t : ℂ)‖ ≤ C * (qsN t.1) ^ δ := by
  obtain ⟨C, hC, hdiv⟩ := qs_divisor_bound_M1 (K := K) δ hδ
  refine ⟨C, hC, ?_⟩
  intro G t
  let D := ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K
  have hcard : (D t).card ≤ (qsDivisors t.1).card := by
    apply Finset.card_le_card_of_injOn (fun p => p.1.1)
    · intro p hp
      have hprod := congrArg (fun J : (Ideal (𝓞 K))⁰ => J.1)
        ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
      have hdiv : p.1.1 ∣ t.1 := ⟨p.2.1, hprod.symm⟩
      exact qs_dvd_mem_qsDivisors p.1.1 t.1
        (mem_nonZeroDivisors_iff_ne_zero.mp t.2) hdiv
    · intro p hp q hq heq
      apply Prod.ext
      · exact Subtype.ext heq
      · apply Subtype.ext
        have hp' := congrArg (fun J : (Ideal (𝓞 K))⁰ => J.1)
          ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
        have hq' := congrArg (fun J : (Ideal (𝓞 K))⁰ => J.1)
          ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hq)
        have hfirst : p.1.1 = q.1.1 := by simpa using heq
        have hmul : p.1.1 * p.2.1 = p.1.1 * q.2.1 := by
          calc
            p.1.1 * p.2.1 = t.1 := hp'
            _ = q.1.1 * q.2.1 := hq'.symm
            _ = p.1.1 * q.2.1 := by rw [← hfirst]
        exact mul_left_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp p.1.2) hmul
  have hcast : ((qsGcdDescentBeta G t : ℤ) : ℝ) =
      ∑ p ∈ D t, if G < qsN p.2.1 then (qsMu p.1.1 : ℝ) else 0 := by
    simp [qsGcdDescentBeta, D]
  have hbeta : |((qsGcdDescentBeta G t : ℤ) : ℝ)| ≤ (D t).card := by
    rw [hcast]
    calc
      |∑ p ∈ D t, if G < qsN p.2.1 then (qsMu p.1.1 : ℝ) else 0| ≤
          ∑ p ∈ D t, ‖if G < qsN p.2.1 then (qsMu p.1.1 : ℝ) else 0‖ :=
        (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _p ∈ D t, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hcut : G < qsN p.2.1
        · simpa [hcut] using qsMu_real_norm_le_one p.1.1
        · simp [hcut]
      _ = (D t).card := by simp
  have hcardReal : ((D t).card : ℝ) ≤ ((qsDivisors t.1).card : ℝ) := by
    exact_mod_cast hcard
  have hdivisor := hdiv t.1 (mem_nonZeroDivisors_iff_ne_zero.mp t.2)
  calc
    ‖(qsGcdDescentBeta G t : ℂ)‖ = |((qsGcdDescentBeta G t : ℤ) : ℝ)| := by simp
    _ ≤ (D t).card := hbeta
    _ ≤ (qsDivisors t.1).card := hcardReal
    _ ≤ C * (qsN t.1) ^ δ := by simpa [qsN] using hdivisor

private theorem qsGcdDescentBeta_zero_of_norm_le (G : ℝ) (t : (Ideal (𝓞 K))⁰)
    (hG : qsN t.1 ≤ G) : qsGcdDescentBeta G t = 0 := by
  classical
  unfold qsGcdDescentBeta
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := congrArg (fun J : (Ideal (𝓞 K))⁰ => J.1)
    ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
  have hdiv : p.2.1 ∣ t.1 := by
    refine ⟨p.1.1, ?_⟩
    calc
      t.1 = p.1.1 * p.2.1 := hprod.symm
      _ = p.2.1 * p.1.1 := mul_comm _ _
  have hnorm := qsN_le_of_dvd p.2.1 t.1
    (mem_nonZeroDivisors_iff_ne_zero.mp t.2) hdiv
  have hcut : ¬ G < qsN p.2.1 := not_lt_of_ge (hnorm.trans hG)
  simp [hcut]

private theorem qs_high_energy_subset_bound (F : QSFamily m qS) (W : ℝ → ℝ)
    (hW : IsCapWeight W) (M X κ : ℝ) (hM : 0 < M)
    (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
    (hsub : ∀ c ∈ cols, c ∈ qsUpTo m qS X) :
    qsHighEnergy F W M κ cols z ≤
      qsHighNorm F W M X κ * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let full := qsUpTo m qS X
  let zext : Ideal (𝓞 K) → ℂ := fun c => if c ∈ cols then z c else 0
  have hcols : cols ⊆ full := by
    intro c hc
    exact hsub c hc
  have hinner (a : Ideal (𝓞 K)) :
      (∑ c ∈ cols, z c * (F.character c).idealValue a) =
        ∑ c ∈ full, zext c * (F.character c).idealValue a := by
    calc
      _ = ∑ c ∈ cols, zext c * (F.character c).idealValue a := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [zext, hc]
      _ = ∑ c ∈ full, zext c * (F.character c).idealValue a :=
        Finset.sum_subset hcols (by
          intro c hc hnot
          simp [zext, hnot])
  have henergy : qsHighEnergy F W M κ cols z =
      qsHighEnergy F W M κ full zext := by
    unfold qsHighEnergy
    apply tsum_congr
    intro a
    by_cases ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧
        IsCoprime a.1 qS ∧ κ < (qsSfNorm a.1 : ℝ)
    · simp only [if_pos ha]
      rw [hinner]
    · simp only [if_neg ha]
  have hcoeff : (∑ c ∈ full, ‖zext c‖ ^ 2) =
      ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ = ∑ c ∈ cols, ‖zext c‖ ^ 2 :=
        by
          symm
          exact Finset.sum_subset hcols (by
            intro c hc hnot
            simp [zext, hnot])
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [zext, hc]
  have hbound := (qs_high_norm_energy_S0 F W hW M X κ hM).1 zext
  rw [← henergy, hcoeff] at hbound
  exact hbound

open Classical in
private theorem qs_high_energy_pointwise_le (F : QSFamily m qS) (W : ℝ → ℝ)
    (hW : IsCapWeight W) (M κ : ℝ) (hM : 0 < M)
    (cols₁ cols₂ : Finset (Ideal (𝓞 K))) (z₁ z₂ : Ideal (𝓞 K) → ℂ)
    (hpoint : ∀ a : {I : Ideal (𝓞 K) // I ≠ ⊥},
      (if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
          κ < (qsSfNorm a.1 : ℝ) then
        W (qsN a.1 / M) *
          ‖∑ c ∈ cols₁, z₁ c * (F.character c).idealValue a.1‖ ^ 2 else 0) ≤
      (if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
          κ < (qsSfNorm a.1 : ℝ) then
        W (qsN a.1 / M) *
          ‖∑ c ∈ cols₂, z₂ c * (F.character c).idealValue a.1‖ ^ 2 else 0)) :
    qsHighEnergy F W M κ cols₁ z₁ ≤ qsHighEnergy F W M κ cols₂ z₂ := by
  classical
  let support : Set {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    {a | Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊}
  have hfinite : support.Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).preimage
    intro a ha b hb hab
    exact Subtype.ext hab
  let rows := hfinite.toFinset
  have hrows (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      a ∈ rows ↔ Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊ := by
    simp [rows, support]
  have hweight (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) (ha : a ∉ rows)
      (_hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧
        IsCoprime a.1 qS ∧ κ < (qsSfNorm a.1 : ℝ)) : W (qsN a.1 / M) = 0 := by
    have hnot : ¬ Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊ := by
      intro h
      exact ha ((hrows a).2 h)
    have hnat : ⌊3 * M⌋₊ < Ideal.absNorm a.1 := Nat.lt_of_not_ge hnot
    have hcast : (⌊3 * M⌋₊ : ℝ) + 1 ≤ qsN a.1 := by
      have hnat' : ⌊3 * M⌋₊ + 1 ≤ Ideal.absNorm a.1 := Nat.succ_le_iff.mpr hnat
      exact_mod_cast hnat'
    have hfloor : 3 * M < (⌊3 * M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlarge : 3 * M < qsN a.1 := hfloor.trans_le hcast
    have hratio : (5 / 2 : ℝ) ≤ qsN a.1 / M := by
      apply (le_div_iff₀ hM).2
      nlinarith
    exact hW.2.2.2 _ hratio
  have hsupport (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
      (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) (ha : a ∉ rows) :
      (if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
          κ < (qsSfNorm a.1 : ℝ) then
        W (qsN a.1 / M) *
          ‖∑ c ∈ cols, z c * (F.character c).idealValue a.1‖ ^ 2 else 0) = 0 := by
    by_cases hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧
        IsCoprime a.1 qS ∧ κ < (qsSfNorm a.1 : ℝ)
    · simp [hc, hweight a ha hc]
    · simp [hc]
  have hsum₁ : qsHighEnergy F W M κ cols₁ z₁ =
      ∑ a ∈ rows, if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧
          IsCoprime a.1 qS ∧ κ < (qsSfNorm a.1 : ℝ) then
        W (qsN a.1 / M) *
          ‖∑ c ∈ cols₁, z₁ c * (F.character c).idealValue a.1‖ ^ 2 else 0 := by
    unfold qsHighEnergy
    rw [tsum_eq_sum (hsupport cols₁ z₁)]
  have hsum₂ : qsHighEnergy F W M κ cols₂ z₂ =
      ∑ a ∈ rows, if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧
          IsCoprime a.1 qS ∧ κ < (qsSfNorm a.1 : ℝ) then
        W (qsN a.1 / M) *
          ‖∑ c ∈ cols₂, z₂ c * (F.character c).idealValue a.1‖ ^ 2 else 0 := by
    unfold qsHighEnergy
    rw [tsum_eq_sum (hsupport cols₂ z₂)]
  calc
    qsHighEnergy F W M κ cols₁ z₁ = _ := hsum₁
    _ ≤ _ := Finset.sum_le_sum (fun a ha => hpoint a)
    _ = qsHighEnergy F W M κ cols₂ z₂ := hsum₂.symm

open Classical in
private theorem qs_high_energy_divisor_bound (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N G κ : ℝ) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 1 ≤ G)
    (hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * N)
    (t : Ideal (𝓞 K)) (ht : QSAdm m qS t) (htG : G < qsN t) :
    qsHighEnergy F W M κ (cols.filter (fun c => t ∣ c)) z ≤
      qsHighNorm F W M (2 * N / G) κ *
        ∑ c ∈ cols.filter (fun c => t ∣ c), ‖z c‖ ^ 2 := by
  classical
  let divCols := cols.filter (fun c => t ∣ c)
  let quot (c : Ideal (𝓞 K)) := if h : t ∣ c then Classical.choose h else ⊥
  let qcols := divCols.image quot
  let zq : Ideal (𝓞 K) → ℂ := fun q => z (t * q)
  have ht0 : t ≠ ⊥ := ht.1.ne_zero
  have hmul (c : Ideal (𝓞 K)) (hc : t ∣ c) : c = t * quot c := by
    simpa [quot, hc] using (Classical.choose_spec hc)
  have hprops (c : Ideal (𝓞 K)) (hc : c ∈ divCols) :
      QSAdm m qS (quot c) ∧ IsCoprime (quot c) t ∧
        t * quot c ∈ cols ∧ zq (quot c) = z c := by
    have hc' : c ∈ cols := (Finset.mem_filter.mp hc).1
    have htc : t ∣ c := (Finset.mem_filter.mp hc).2
    have hsq : Squarefree (quot c) := by
      apply (hcols c hc').1.1.squarefree_of_dvd
      exact ⟨t, by
        calc
          c = t * quot c := hmul c htc
          _ = quot c * t := mul_comm _ _⟩
    have hprodSq : Squarefree (t * quot c) := by rw [← hmul c htc]; exact (hcols c hc').1.1
    have hrel : IsRelPrime t (quot c) := (squarefree_mul_iff.mp hprodSq).1
    have hcop : IsCoprime (quot c) t := by
      rw [Ideal.isCoprime_iff_sup_eq]
      have hu : IsUnit (quot c ⊔ t) := by
        apply hrel.symm
        · exact Ideal.dvd_iff_le.mpr le_sup_left
        · exact Ideal.dvd_iff_le.mpr le_sup_right
      exact Ideal.isUnit_iff.mp hu
    have hcopm₀ : IsCoprime c (qsModulusRad m) :=
      ((qs_isCoprimeTo_iff_M0 c).mp (hcols c hc').1.2.1).2
    have hcopm₁ : IsCoprime (t * quot c) (qsModulusRad m) := by
      rw [← hmul c htc]
      exact hcopm₀
    have hcopm := hcopm₁.of_mul_left_right
    have hcopq₀ : IsCoprime c qS := (hcols c hc').1.2.2
    have hcopq₁ : IsCoprime (t * quot c) qS := by
      rw [← hmul c htc]
      exact hcopq₀
    have hcopq := hcopq₁.of_mul_left_right
    have hadm : QSAdm m qS (quot c) := by
      refine ⟨hsq, ?_, hcopq⟩
      exact (qs_isCoprimeTo_iff_M0 (quot c)).mpr ⟨hsq.ne_zero, hcopm⟩
    refine ⟨hadm, hcop, ?_, ?_⟩
    · rw [← hmul c htc]
      exact hc'
    · exact (congrArg z (hmul c htc)).symm
  have hquotNorm (c : Ideal (𝓞 K)) (hc : c ∈ divCols) :
      qsN (quot c) ≤ 2 * N / G := by
    have htc : t ∣ c := (Finset.mem_filter.mp hc).2
    have hnormmul : qsN c = qsN t * qsN (quot c) := by
      calc
        qsN c = qsN (t * quot c) := congrArg qsN (hmul c htc)
        _ = qsN t * qsN (quot c) := by
          simp [qsN, map_mul, Nat.cast_mul]
    have hupper : qsN t * qsN (quot c) ≤ 2 * N := by
      rw [← hnormmul]
      exact (hcols c (Finset.mem_filter.mp hc).1).2
    have hGpos : 0 < G := by linarith
    have hqnonneg : 0 ≤ qsN (quot c) := by positivity
    have hmulbound : qsN (quot c) * G ≤ 2 * N := by
      calc
        qsN (quot c) * G ≤ qsN (quot c) * qsN t :=
          mul_le_mul_of_nonneg_left htG.le hqnonneg
        _ = qsN t * qsN (quot c) := by ring
        _ ≤ 2 * N := hupper
    exact (le_div_iff₀ hGpos).2 hmulbound
  have hqadm (q : Ideal (𝓞 K)) (hq : q ∈ qcols) : QSAdm m qS q := by
    rcases Finset.mem_image.mp hq with ⟨c, hc, rfl⟩
    exact (hprops c hc).1
  have hqnorm (q : Ideal (𝓞 K)) (hq : q ∈ qcols) : qsN q ≤ 2 * N / G := by
    rcases Finset.mem_image.mp hq with ⟨c, hc, rfl⟩
    exact hquotNorm c hc
  have hqsub : ∀ q ∈ qcols, q ∈ qsUpTo m qS (2 * N / G) := by
    intro q hq
    have hqadm' := hqadm q hq
    have hqnorm' := hqnorm q hq
    have hfloor : Ideal.absNorm q ≤ ⌊2 * N / G⌋₊ := by
      exact Nat.le_floor (by exact_mod_cast hqnorm')
    have hbase : q ∈ (Ideal.finite_setOfPred_absNorm_le
        (S := 𝓞 K) ⌊2 * N / G⌋₊).toFinset := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hfloor
    exact Finset.mem_filter.mpr ⟨hbase, ⟨hqadm', hqnorm'⟩⟩
  have hquotInj : ∀ c ∈ divCols, ∀ d ∈ divCols, quot c = quot d → c = d := by
    intro c hc d hd hq
    have htc := (Finset.mem_filter.mp hc).2
    have htd := (Finset.mem_filter.mp hd).2
    calc
      c = t * quot c := hmul c htc
      _ = t * quot d := by rw [hq]
      _ = d := (hmul d htd).symm
  have hsumMap (a : Ideal (𝓞 K))
      (ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a)
      (haq : IsCoprime a qS) :
      (∑ c ∈ divCols, z c * (F.character c).idealValue a) =
        (F.character t).idealValue a *
          ∑ q ∈ qcols, zq q * (F.character q).idealValue a := by
    have hbij : (∑ c ∈ divCols, z c * (F.character c).idealValue a) =
        ∑ q ∈ qcols, z (t * q) * (F.character (t * q)).idealValue a := by
      apply Finset.sum_bij (fun c _ => quot c)
      · intro c hc
        exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
      · intro c hc d hd hq
        exact hquotInj c hc d hd hq
      · intro q hq
        rcases Finset.mem_image.mp hq with ⟨c, hc, rfl⟩
        exact ⟨c, hc, rfl⟩
      · intro c hc
        have htc := (Finset.mem_filter.mp hc).2
        exact congrArg (fun x : Ideal (𝓞 K) => z x * (F.character x).idealValue a)
          (hmul c htc)
    have hfactor :
        (∑ q ∈ qcols, z (t * q) * (F.character (t * q)).idealValue a) =
          (F.character t).idealValue a *
            ∑ q ∈ qcols, zq q * (F.character q).idealValue a := by
      calc
        _ = ∑ q ∈ qcols,
              z (t * q) * ((F.character t).idealValue a *
                (F.character q).idealValue a) := by
          apply Finset.sum_congr rfl
          intro q hq
          rcases Finset.mem_image.mp hq with ⟨c, hc, hqeq⟩
          have hqadm : QSAdm m qS q := by
            simpa [hqeq] using (hprops c hc).1
          have hqcop : IsCoprime t q := by
            simpa [hqeq] using (hprops c hc).2.1.symm
          have hchar := qs_family_mul_S0 F hrf t q ht hqadm hqcop a ha haq
          rw [hchar]
        _ = ∑ q ∈ qcols,
              (F.character t).idealValue a *
                (zq q * (F.character q).idealValue a) := by
          apply Finset.sum_congr rfl
          intro q hq
          simp [zq]
          ring
        _ = _ := by rw [Finset.mul_sum]
    exact hbij.trans hfactor
  have hpoint : ∀ a : {I : Ideal (𝓞 K) // I ≠ ⊥},
      (if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
          κ < (qsSfNorm a.1 : ℝ) then
        W (qsN a.1 / M) *
          ‖∑ c ∈ divCols, z c * (F.character c).idealValue a.1‖ ^ 2 else 0) ≤
      (if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
          κ < (qsSfNorm a.1 : ℝ) then
        W (qsN a.1 / M) *
          ‖∑ q ∈ qcols, zq q * (F.character q).idealValue a.1‖ ^ 2 else 0) := by
    intro a
    by_cases hrow : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧
        IsCoprime a.1 qS ∧ κ < (qsSfNorm a.1 : ℝ)
    · simp only [if_pos hrow]
      rw [hsumMap a.1 hrow.1 hrow.2.1]
      have hchi := F.quadraticValues t ht.1 ht.2.1 a.1
      have hchiNorm : ‖(F.character t).idealValue a.1‖ ^ 2 ≤ 1 := by
        rcases hchi with hzero | hsq
        · simp [hzero]
        · have heq : ‖(F.character t).idealValue a.1‖ ^ 2 = 1 := by
            rw [← norm_pow, hsq]
            norm_num
          linarith
      have hsumNonneg :
          0 ≤ ‖∑ q ∈ qcols, zq q * (F.character q).idealValue a.1‖ ^ 2 := sq_nonneg _
      have hnormMul :
          ‖(F.character t).idealValue a.1 *
              ∑ q ∈ qcols, zq q * (F.character q).idealValue a.1‖ ^ 2 ≤
          ‖∑ q ∈ qcols, zq q * (F.character q).idealValue a.1‖ ^ 2 := by
        rw [norm_mul]
        calc
          (‖(F.character t).idealValue a.1‖ *
              ‖∑ q ∈ qcols, zq q * (F.character q).idealValue a.1‖) ^ 2 =
              ‖(F.character t).idealValue a.1‖ ^ 2 *
                ‖∑ q ∈ qcols, zq q * (F.character q).idealValue a.1‖ ^ 2 := by ring
          _ ≤ 1 * ‖∑ q ∈ qcols, zq q * (F.character q).idealValue a.1‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hchiNorm hsumNonneg
          _ = _ := by ring
      exact mul_le_mul_of_nonneg_left hnormMul (hW.2.1 _)
    · simp [hrow]
  have henergy := qs_high_energy_pointwise_le F W hW M κ hM
    divCols qcols z zq hpoint
  have hcoeff : (∑ q ∈ qcols, ‖zq q‖ ^ 2) =
      ∑ c ∈ divCols, ‖z c‖ ^ 2 := by
    symm
    apply Finset.sum_bij (fun c _ => quot c)
    · intro c hc
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    · intro c hc d hd hq
      exact hquotInj c hc d hd hq
    · intro q hq
      rcases Finset.mem_image.mp hq with ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · intro c hc
      have htc := (Finset.mem_filter.mp hc).2
      exact congrArg (fun x : Ideal (𝓞 K) => ‖z x‖ ^ 2) (hmul c htc)
  have hsubset := qs_high_energy_subset_bound F W hW M (2 * N / G) κ hM
    qcols zq hqsub
  calc
    qsHighEnergy F W M κ divCols z ≤ qsHighEnergy F W M κ qcols zq := henergy
    _ ≤ qsHighNorm F W M (2 * N / G) κ * ∑ q ∈ qcols, ‖zq q‖ ^ 2 := hsubset
    _ = qsHighNorm F W M (2 * N / G) κ * ∑ c ∈ divCols, ‖z c‖ ^ 2 := by rw [hcoeff]

private theorem qs_antidiagonal_fst_mem_iff (I t : (Ideal (𝓞 K))⁰) :
    t ∈ (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K I).image Prod.fst ↔
      t.1 ∣ I.1 := by
  classical
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨p, hp, hfst⟩
    have hprod := congrArg (fun J : (Ideal (𝓞 K))⁰ => J.1)
      ((ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mp hp)
    refine ⟨p.2.1, ?_⟩
    calc
      I.1 = p.1.1 * p.2.1 := hprod.symm
      _ = t.1 * p.2.1 := by rw [congrArg Subtype.val hfst]
  · intro hdiv
    rcases hdiv with ⟨u, hu⟩
    have hu0 : u ≠ ⊥ := by
      intro hu0
      have hI0 : I.1 ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      apply hI0
      rw [hu, hu0]
      simp
    let p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ :=
      (t,
        ⟨u, mem_nonZeroDivisors_of_ne_zero hu0⟩)
    have hp : p ∈ ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K I := by
      apply (ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.mem_divisorsAntidiagonal K).mpr
      exact Subtype.ext hu.symm
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

private theorem qs_dvd_sup_iff (t c d : Ideal (𝓞 K)) :
    t ∣ c ⊔ d ↔ t ∣ c ∧ t ∣ d := by
  rw [Ideal.dvd_iff_le]
  constructor
  · intro h
    exact ⟨Ideal.dvd_iff_le.mpr (le_sup_left.trans h),
      Ideal.dvd_iff_le.mpr (le_sup_right.trans h)⟩
  · rintro ⟨hc, hd⟩
    exact sup_le (Ideal.dvd_iff_le.mp hc) (Ideal.dvd_iff_le.mp hd)

private theorem qs_gcd_blocks_eq_pair_sum (F : QSFamily m qS) (W : ℝ → ℝ)
    (M κ : ℝ) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ) :
    (∑ g ∈ (cols ×ˢ cols).image (fun p => p.1 ⊔ p.2),
        qsGcdBlock F W M κ g cols z) =
      ∑ c ∈ cols, ∑ d ∈ cols,
        z c * conj (z d) * qsHighPair F W M κ c d := by
  classical
  let pairs := cols ×ˢ cols
  let gs := pairs.image (fun p => p.1 ⊔ p.2)
  let term := fun p : Ideal (𝓞 K) × Ideal (𝓞 K) =>
    z p.1 * conj (z p.2) * qsHighPair F W M κ p.1 p.2
  have hblock (g : Ideal (𝓞 K)) :
      qsGcdBlock F W M κ g cols z =
        ∑ p ∈ pairs, if p.1 ⊔ p.2 = g then term p else 0 := by
    unfold qsGcdBlock
    dsimp [pairs, term]
    rw [← Finset.sum_product']
  calc
    _ = ∑ g ∈ gs, ∑ p ∈ pairs, if p.1 ⊔ p.2 = g then term p else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      exact hblock g
    _ = ∑ p ∈ pairs, ∑ g ∈ gs, if p.1 ⊔ p.2 = g then term p else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ pairs, term p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hmem : p.1 ⊔ p.2 ∈ gs := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      simp [hmem]
    _ = ∑ c ∈ cols, ∑ d ∈ cols,
          z c * conj (z d) * qsHighPair F W M κ c d := by
      dsimp [pairs, term]
      symm
      rw [← Finset.sum_product']

private theorem qs_high_energy_nonneg (F : QSFamily m qS) (W : ℝ → ℝ)
    (hW : IsCapWeight W) (M κ : ℝ) (hM : 0 < M)
    (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ) :
    0 ≤ qsHighEnergy F W M κ cols z := by
  have h := qs_high_energy_pointwise_le F W hW M κ hM ∅ cols
    (fun _ => 0) z (by
      intro a
      by_cases ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧
          IsCoprime a.1 qS ∧ κ < (qsSfNorm a.1 : ℝ)
      · simp only [if_pos ha]
        simp only [Finset.sum_empty, norm_zero]
        have hn := mul_nonneg (hW.2.1 (qsN a.1 / M))
          (sq_nonneg ‖∑ c ∈ cols, z c * (F.character c).idealValue a.1‖)
        simpa using hn
      · simp [ha])
  have hzero : qsHighEnergy F W M κ ∅ (fun _ => 0) = 0 := by
    simp [qsHighEnergy]
  rw [hzero] at h
  exact h

open Classical in
/-- S0 (IMPL): gcd descent (found:405-412).  Blocks with `N g > G` recombine, by Möbius
inversion on the divisor lattice and multiplicativity, into high-core energies of shifted
vectors at column length `≤ 2N/G`; the divisor multiplicities cost `N^η`. -/
theorem qs_gcd_descent_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N G κ : ℝ) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
      0 < M → 1 ≤ N → 1 ≤ G →
      (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * N) →
      ‖∑ g ∈ ((cols ×ˢ cols).image (fun p => p.1 ⊔ p.2)).filter (fun g => G < qsN g),
          qsGcdBlock F W M κ g cols z‖ ≤
        C * N ^ η * qsHighNorm F W M (2 * N / G) κ * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let δ : ℝ := η / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨Cβ, hCβ, hβbound⟩ := qsGcdDescentBeta_norm_bound (K := K) δ hδ
  obtain ⟨Cdiv, hCdiv, hdivbound⟩ := qs_divisor_bound_M1 (K := K) δ hδ
  let C : ℝ := Cβ * Cdiv * 2 ^ η
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M N G κ cols z hM hN hG hcols
  have hpowFinal (x : ℝ) (hx : 1 ≤ x) :
      (2 * x) ^ δ * (2 * x) ^ δ = 2 ^ η * x ^ η := by
    have hpos : 0 < 2 * x := by positivity
    calc
      (2 * x) ^ δ * (2 * x) ^ δ = (2 * x) ^ (δ + δ) :=
        (Real.rpow_add hpos δ δ).symm
      _ = (2 * x) ^ η := by congr 1 <;> dsimp [δ] <;> ring
      _ = 2 ^ η * x ^ η := by
        rw [show 2 * x = (2 : ℝ) * x by ring, Real.mul_rpow (by norm_num) (by linarith)]
  let pairs := cols ×ˢ cols
  let gs := pairs.image (fun p => p.1 ⊔ p.2)
  let big := gs.filter (fun g => G < qsN g)
  let term := fun p : Ideal (𝓞 K) × Ideal (𝓞 K) =>
    z p.1 * conj (z p.2) * qsHighPair F W M κ p.1 p.2
  let joinNZ (p : Ideal (𝓞 K) × Ideal (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
    if h : p.1 ⊔ p.2 ≠ ⊥ then ⟨p.1 ⊔ p.2, mem_nonZeroDivisors_of_ne_zero h⟩ else 1
  let D := ArtinPrimitiveRoots.Hecke.EulerProduct.Ideal.divisorsAntidiagonal K
  let T := pairs.biUnion (fun p => (D (joinNZ p)).image Prod.fst)
  have hpairAdmissible (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ pairs) :
      QSAdm m qS p.1 ∧ QSAdm m qS p.2 := by
    rcases Finset.mem_product.mp hp with ⟨h₁, h₂⟩
    exact ⟨(hcols p.1 h₁).1, (hcols p.2 h₂).1⟩
  have hjoinne (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ pairs) :
      p.1 ⊔ p.2 ≠ ⊥ := by
    intro hbot
    have hp₁ := (Finset.mem_product.mp hp).1
    have hc0 : p.1 ≠ ⊥ := (hcols p.1 hp₁).1.1.ne_zero
    apply hc0
    exact le_bot_iff.mp (by simpa [hbot] using (le_sup_left : p.1 ≤ p.1 ⊔ p.2))
  have hjoinVal (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ pairs) :
      (joinNZ p).1 = p.1 ⊔ p.2 := by
    dsimp [joinNZ]
    split
    · rfl
    · rename_i h
      exact False.elim (h (hjoinne p hp))
  have hblocks :
      (∑ g ∈ big, qsGcdBlock F W M κ g cols z) =
        ∑ p ∈ pairs, if G < qsN (p.1 ⊔ p.2) then term p else 0 := by
    have hblock (g : Ideal (𝓞 K)) :
        qsGcdBlock F W M κ g cols z =
          ∑ p ∈ pairs, if p.1 ⊔ p.2 = g then term p else 0 := by
      unfold qsGcdBlock
      dsimp [pairs, term]
      rw [← Finset.sum_product']
    calc
      _ = ∑ g ∈ big, ∑ p ∈ pairs,
            if p.1 ⊔ p.2 = g then term p else 0 := by
        apply Finset.sum_congr rfl
        intro g hg
        exact hblock g
      _ = ∑ p ∈ pairs, ∑ g ∈ big,
            if p.1 ⊔ p.2 = g then term p else 0 := by rw [Finset.sum_comm]
      _ = ∑ p ∈ pairs, if G < qsN (p.1 ⊔ p.2) then term p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hcut : G < qsN (p.1 ⊔ p.2)
        · have hmem : p.1 ⊔ p.2 ∈ big := by
            exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, hcut⟩
          simp [hmem, hcut]
        · have hzero :
              (∑ g ∈ big, if p.1 ⊔ p.2 = g then term p else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro g hg
            by_cases heq : p.1 ⊔ p.2 = g
            · subst g
              exact False.elim (hcut (Finset.mem_filter.mp hg).2)
            · simp [heq]
          simp [hcut, hzero]
      _ = _ := by
        dsimp [pairs, term]
  have hprojFilter (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ pairs) :
      T.filter (fun t => t.1 ∣ p.1 ⊔ p.2) = (D (joinNZ p)).image Prod.fst := by
    ext t
    constructor
    · intro ht
      have hdiv : t.1 ∣ p.1 ⊔ p.2 := (Finset.mem_filter.mp ht).2
      apply (qs_antidiagonal_fst_mem_iff (joinNZ p) t).2
      simpa [hjoinVal p hp] using hdiv
    · intro ht
      have hdiv := (qs_antidiagonal_fst_mem_iff (joinNZ p) t).mp ht
      have hmem : t ∈ T := Finset.mem_biUnion.mpr ⟨p, hp, ht⟩
      exact Finset.mem_filter.mpr ⟨hmem, by simpa [hjoinVal p hp] using hdiv⟩
  have hbetaSum (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ pairs) :
      (∑ t ∈ T, if t.1 ∣ p.1 ⊔ p.2 then
        (qsGcdDescentBeta G t : ℤ) else 0) =
        if G < qsN (p.1 ⊔ p.2) then 1 else 0 := by
    calc
      _ = ∑ t ∈ T.filter (fun t => t.1 ∣ p.1 ⊔ p.2),
            (qsGcdDescentBeta G t : ℤ) := by rw [Finset.sum_filter]
      _ = ∑ t ∈ (D (joinNZ p)).image Prod.fst, qsGcdDescentBeta G t := by
            rw [hprojFilter p hp]
      _ = if G < qsN (joinNZ p).1 then 1 else 0 := qsGcdDescentBeta_sum G (joinNZ p)
      _ = if G < qsN (p.1 ⊔ p.2) then 1 else 0 := by rw [hjoinVal p hp]
  have hpairMobius (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ pairs) :
      (if G < qsN (p.1 ⊔ p.2) then term p else 0) =
        ∑ t ∈ T, if t.1 ∣ p.1 ⊔ p.2 then
          (qsGcdDescentBeta G t : ℂ) * term p else 0 := by
    have hb := hbetaSum p hp
    calc
      _ = term p * (if G < qsN (p.1 ⊔ p.2) then 1 else 0) := by
        by_cases hcut : G < qsN (p.1 ⊔ p.2) <;> simp [hcut] <;> ring
      _ = term p * (∑ t ∈ T, if t.1 ∣ p.1 ⊔ p.2 then
            (qsGcdDescentBeta G t : ℂ) else 0) := by
        have hbC : (∑ t ∈ T, if t.1 ∣ p.1 ⊔ p.2 then
            (qsGcdDescentBeta G t : ℂ) else 0) =
              if G < qsN (p.1 ⊔ p.2) then 1 else 0 := by exact_mod_cast hb
        rw [← hbC]
      _ = ∑ t ∈ T, if t.1 ∣ p.1 ⊔ p.2 then
            (qsGcdDescentBeta G t : ℂ) * term p else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hdiv : t.1 ∣ p.1 ⊔ p.2 <;> simp [hdiv] <;> ring
  have hdecomp :
      (∑ g ∈ big, qsGcdBlock F W M κ g cols z) =
        ∑ t ∈ T, (qsGcdDescentBeta G t : ℂ) *
          (qsHighEnergy F W M κ (cols.filter (fun c => t.1 ∣ c)) z : ℂ) := by
    calc
      _ = ∑ p ∈ pairs, if G < qsN (p.1 ⊔ p.2) then term p else 0 := hblocks
      _ = ∑ p ∈ pairs, ∑ t ∈ T, if t.1 ∣ p.1 ⊔ p.2 then
            (qsGcdDescentBeta G t : ℂ) * term p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpairMobius p hp
      _ = ∑ t ∈ T, ∑ p ∈ pairs, if t.1 ∣ p.1 ⊔ p.2 then
            (qsGcdDescentBeta G t : ℂ) * term p else 0 := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        let divCols := cols.filter (fun c => t.1 ∣ c)
        have hpairSet : pairs.filter (fun p => t.1 ∣ p.1 ⊔ p.2) = divCols ×ˢ divCols := by
          ext p
          simp [pairs, divCols, qs_dvd_sup_iff] <;> tauto
        have hpairSum :
            (∑ p ∈ pairs, if t.1 ∣ p.1 ⊔ p.2 then term p else 0) =
              ∑ c ∈ divCols, ∑ d ∈ divCols,
                z c * conj (z d) * qsHighPair F W M κ c d := by
          calc
            _ = ∑ p ∈ pairs.filter (fun p => t.1 ∣ p.1 ⊔ p.2), term p :=
              by rw [← Finset.sum_filter]
            _ = ∑ p ∈ divCols ×ˢ divCols, term p := by rw [hpairSet]
            _ = _ := by
              dsimp [term]
              symm
              rw [← Finset.sum_product']
        have hdivAdm : ∀ c ∈ divCols, QSAdm m qS c := by
          intro c hc
          exact (hcols c (Finset.mem_filter.mp hc).1).1
        have hpairEnergy :
            (∑ c ∈ divCols, ∑ d ∈ divCols,
              z c * conj (z d) * qsHighPair F W M κ c d) =
              (qsHighEnergy F W M κ divCols z : ℂ) := by
          calc
            _ = ∑ g ∈ (divCols ×ˢ divCols).image (fun p => p.1 ⊔ p.2),
                  qsGcdBlock F W M κ g divCols z :=
                    (qs_gcd_blocks_eq_pair_sum F W M κ divCols z).symm
            _ = (qsHighEnergy F W M κ divCols z : ℝ) :=
                  (qs_gcd_expansion_S0 F W hW M κ hM divCols hdivAdm z).symm
            _ = _ := by norm_cast
        calc
          (∑ p ∈ pairs, if t.1 ∣ p.1 ⊔ p.2 then
              (qsGcdDescentBeta G t : ℂ) * term p else 0) =
              (qsGcdDescentBeta G t : ℂ) *
                ∑ p ∈ pairs, if t.1 ∣ p.1 ⊔ p.2 then term p else 0 := by
            calc
              _ = ∑ p ∈ pairs,
                    (qsGcdDescentBeta G t : ℂ) *
                      (if t.1 ∣ p.1 ⊔ p.2 then term p else 0) := by
                apply Finset.sum_congr rfl
                intro p hp
                by_cases hdiv : t.1 ∣ p.1 ⊔ p.2 <;> simp [hdiv]
              _ = _ := by rw [Finset.mul_sum]
          _ = (qsGcdDescentBeta G t : ℂ) *
                ∑ c ∈ divCols, ∑ d ∈ divCols,
                  z c * conj (z d) * qsHighPair F W M κ c d := by rw [hpairSum]
          _ = _ := by rw [hpairEnergy]
  have hTsource (t : (Ideal (𝓞 K))⁰) (ht : t ∈ T) :
      ∃ p ∈ pairs, t ∈ (D (joinNZ p)).image Prod.fst := by
    exact Finset.mem_biUnion.mp ht
  have hTdiv (t : (Ideal (𝓞 K))⁰) (ht : t ∈ T) (p : Ideal (𝓞 K) × Ideal (𝓞 K))
      (hp : p ∈ pairs) (htp : t ∈ (D (joinNZ p)).image Prod.fst) :
      t.1 ∣ p.1 ∧ t.1 ∣ p.2 := by
    have hdiv := (qs_antidiagonal_fst_mem_iff (joinNZ p) t).mp htp
    rw [hjoinVal p hp] at hdiv
    exact (qs_dvd_sup_iff t.1 p.1 p.2).mp hdiv
  have hTadm (t : (Ideal (𝓞 K))⁰) (ht : t ∈ T) : QSAdm m qS t.1 := by
    obtain ⟨p, hp, htp⟩ := hTsource t ht
    have hdivc := (hTdiv t ht p hp htp).1
    have hc := (Finset.mem_product.mp hp).1
    have hadmc := (hcols p.1 hc).1
    have hsq := hadmc.1.squarefree_of_dvd hdivc
    have hcopm := ((qs_isCoprimeTo_iff_M0 p.1).mp hadmc.2.1).2
      |>.of_isCoprime_of_dvd_left hdivc
    have hcopq := hadmc.2.2.of_isCoprime_of_dvd_left hdivc
    exact ⟨hsq, (qs_isCoprimeTo_iff_M0 t.1).mpr ⟨hsq.ne_zero, hcopm⟩, hcopq⟩
  have hTnorm (t : (Ideal (𝓞 K))⁰) (ht : t ∈ T) : qsN t.1 ≤ 2 * N := by
    obtain ⟨p, hp, htp⟩ := hTsource t ht
    have hdivc := (hTdiv t ht p hp htp).1
    have hc := (Finset.mem_product.mp hp).1
    exact (qsN_le_of_dvd t.1 p.1 (hcols p.1 hc).1.1.ne_zero hdivc).trans
      (hcols p.1 hc).2
  have hdivAdm (c t : Ideal (𝓞 K)) (hc : QSAdm m qS c) (htc : t ∣ c) : QSAdm m qS t := by
    have hsq := hc.1.squarefree_of_dvd htc
    have hcopm := ((qs_isCoprimeTo_iff_M0 c).mp hc.2.1).2
      |>.of_isCoprime_of_dvd_left htc
    have hcopq := hc.2.2.of_isCoprime_of_dvd_left htc
    exact ⟨hsq, (qs_isCoprimeTo_iff_M0 t).mpr ⟨hsq.ne_zero, hcopm⟩, hcopq⟩
  have hmultBound (c : Ideal (𝓞 K)) (hc : c ∈ cols) :
      (((T.filter (fun t => t.1 ∣ c)).card : ℕ) : ℝ) ≤ Cdiv * (2 * N) ^ δ := by
    let ts := T.filter (fun t => t.1 ∣ c)
    have hcard : ts.card ≤ (qsDivisors c).card := by
      apply Finset.card_le_card_of_injOn (fun t => t.1)
      · intro t ht
        have htc := (Finset.mem_filter.mp ht).2
        exact qs_dvd_mem_qsDivisors t.1 c (hcols c hc).1.1.ne_zero htc
      · intro t ht u hu htu
        exact Subtype.ext htu
    have hdiv := hdivbound c (hcols c hc).1.1.ne_zero
    have hpow : qsN c ^ δ ≤ (2 * N) ^ δ :=
      Real.rpow_le_rpow (by positivity) (hcols c hc).2 (by linarith)
    have hcardR : (ts.card : ℝ) ≤ ((qsDivisors c).card : ℝ) := by exact_mod_cast hcard
    calc
      (ts.card : ℝ) ≤ ((qsDivisors c).card : ℝ) := hcardR
      _ ≤ Cdiv * qsN c ^ δ := hdiv
      _ ≤ Cdiv * (2 * N) ^ δ := mul_le_mul_of_nonneg_left hpow hCdiv.le
  have hsumMult :
      (∑ t ∈ T, ∑ c ∈ cols.filter (fun c => t.1 ∣ c), ‖z c‖ ^ 2) ≤
        Cdiv * (2 * N) ^ δ * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ = ∑ t ∈ T, ∑ c ∈ cols,
            if t.1 ∣ c then ‖z c‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.sum_filter]
      _ = ∑ c ∈ cols, ∑ t ∈ T,
            if t.1 ∣ c then ‖z c‖ ^ 2 else 0 := by rw [Finset.sum_comm]
      _ = ∑ c ∈ cols, ((T.filter (fun t => t.1 ∣ c)).card : ℝ) * ‖z c‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [← Finset.sum_filter]
        simp [Finset.sum_const]
      _ ≤ ∑ c ∈ cols, (Cdiv * (2 * N) ^ δ) * ‖z c‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_right (hmultBound c hc) (sq_nonneg ‖z c‖)
      _ = Cdiv * (2 * N) ^ δ * ∑ c ∈ cols, ‖z c‖ ^ 2 := by rw [Finset.mul_sum]
  have hA : 0 ≤ Cβ * (2 * N) ^ δ := by positivity
  have hB : 0 ≤ qsHighNorm F W M (2 * N / G) κ := sq_nonneg _
  have hBigNorm :
      ‖∑ g ∈ big, qsGcdBlock F W M κ g cols z‖ ≤
        Cβ * (2 * N) ^ δ * qsHighNorm F W M (2 * N / G) κ *
          ∑ t ∈ T, ∑ c ∈ cols.filter (fun c => t.1 ∣ c), ‖z c‖ ^ 2 := by
    rw [hdecomp]
    calc
      _ ≤ ∑ t ∈ T, ‖(qsGcdDescentBeta G t : ℂ) *
            (qsHighEnergy F W M κ (cols.filter (fun c => t.1 ∣ c)) z : ℂ)‖ :=
              norm_sum_le _ _
      _ ≤ ∑ t ∈ T, (Cβ * (2 * N) ^ δ) *
            (qsHighNorm F W M (2 * N / G) κ *
              ∑ c ∈ cols.filter (fun c => t.1 ∣ c), ‖z c‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases htG : G < qsN t.1
        · have hEt := qs_high_energy_divisor_bound F hrf W hW M N G κ cols z
            hM hN hG hcols t.1 (hTadm t ht) htG
          have hE0 := qs_high_energy_nonneg F W hW M κ hM
            (cols.filter (fun c => t.1 ∣ c)) z
          have hβ := hβbound G t
          have htpow : (qsN t.1) ^ δ ≤ (2 * N) ^ δ :=
            Real.rpow_le_rpow (by positivity) (hTnorm t ht) (by linarith)
          calc
            ‖(qsGcdDescentBeta G t : ℂ) *
                (qsHighEnergy F W M κ (cols.filter (fun c => t.1 ∣ c)) z : ℂ)‖ =
                ‖(qsGcdDescentBeta G t : ℂ)‖ *
                  qsHighEnergy F W M κ (cols.filter (fun c => t.1 ∣ c)) z := by
                    rw [norm_mul]
                    simp [abs_of_nonneg hE0]
            _ ≤ (Cβ * (qsN t.1) ^ δ) *
                  qsHighEnergy F W M κ (cols.filter (fun c => t.1 ∣ c)) z :=
                    mul_le_mul_of_nonneg_right hβ hE0
            _ ≤ (Cβ * (2 * N) ^ δ) *
                  qsHighEnergy F W M κ (cols.filter (fun c => t.1 ∣ c)) z :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left htpow hCβ.le) hE0
            _ ≤ (Cβ * (2 * N) ^ δ) *
                  (qsHighNorm F W M (2 * N / G) κ *
                    ∑ c ∈ cols.filter (fun c => t.1 ∣ c), ‖z c‖ ^ 2) :=
                    mul_le_mul_of_nonneg_left hEt hA
        · have hβzero : qsGcdDescentBeta G t = 0 :=
            qsGcdDescentBeta_zero_of_norm_le G t (le_of_not_gt htG)
          simp [hβzero]
          positivity
      _ = Cβ * (2 * N) ^ δ * qsHighNorm F W M (2 * N / G) κ *
            ∑ t ∈ T, ∑ c ∈ cols.filter (fun c => t.1 ∣ c), ‖z c‖ ^ 2 := by
        calc
          _ = ∑ t ∈ T,
                (Cβ * (2 * N) ^ δ * qsHighNorm F W M (2 * N / G) κ) *
                  (∑ c ∈ cols.filter (fun c => t.1 ∣ c), ‖z c‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro t ht
            ring
          _ = _ := by rw [Finset.mul_sum]
  calc
    ‖∑ g ∈ big, qsGcdBlock F W M κ g cols z‖ ≤
        Cβ * (2 * N) ^ δ * qsHighNorm F W M (2 * N / G) κ *
          ∑ t ∈ T, ∑ c ∈ cols.filter (fun c => t.1 ∣ c), ‖z c‖ ^ 2 := hBigNorm
    _ ≤ Cβ * (2 * N) ^ δ * qsHighNorm F W M (2 * N / G) κ *
          (Cdiv * (2 * N) ^ δ * ∑ c ∈ cols, ‖z c‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsumMult (by positivity)
    _ = C * N ^ η * qsHighNorm F W M (2 * N / G) κ *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
      calc
        _ = Cβ * Cdiv * ((2 * N) ^ δ * (2 * N) ^ δ) *
              qsHighNorm F W M (2 * N / G) κ * ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
        _ = C * N ^ η * qsHighNorm F W M (2 * N / G) κ *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
          rw [hpowFinal N hN]
          dsimp [C]
          ring

end ArtinPrimitiveRoots.A2
