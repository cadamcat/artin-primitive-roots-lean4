import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».Defs
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1

/-!
# A2-QS-MOBIUS, part S0: multiplicativity, class/dyad slicing, gcd expansion and descent

Guide: `runs/lanes/sol-thin-found/PROOFS.md:396-408` (S0) and G1 (found:613-615) specialised to
trivial ray factor.  The family identities are derived prime by prime from `reciprocity`
(trivial factor), `idealValue` multiplicativity (`qs_idealValue_mul_M0`) and ramification at the
primitive conductor (`qs_idealValue_eq_zero_of_conductor_M0`); rows are coprime to `m` and `qS`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
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

/-- S0 (IMPL): class and dyad slicing (Cauchy–Schwarz over the finite ray class group and over
the `⌈log₂ N⌉₊ + 1` column dyads `N/2^{j+1} < N c ≤ N/2^j`): the up-to columns split into at
most `h_m (⌈log₂ N⌉₊ + 1)` pairwise disjoint parts, each inside one ray class and one dyad
`(n, 2n]`, `n = N/2^{j+1}`, and the high-core energy is at most the number of parts times the
sum of the part energies. -/
theorem qs_class_dyad_slice_S0 (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hN : 1 ≤ N) (z : Ideal (𝓞 K) → ℂ) :
    ∃ parts : Finset (Finset (Ideal (𝓞 K))),
      ((parts.card : ℕ) : ℝ) ≤
          (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
            ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) ∧
      (∀ P ∈ parts, P ⊆ qsUpTo m qS N) ∧
      (∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) ∧
      (∀ P ∈ parts, ∃ j : ℕ, ∀ c ∈ P, N / 2 ^ (j + 1) < qsN c ∧ qsN c ≤ N / 2 ^ j) ∧
      (∀ P ∈ parts, ∀ c ∈ P, ∀ d ∈ P, ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
        (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
        ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd) ∧
      qsHighEnergy F W M κ (qsUpTo m qS N) z ≤
        ((parts.card : ℕ) : ℝ) * ∑ P ∈ parts, qsHighEnergy F W M κ P z := by
  sorry

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
  sorry

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
  sorry

end ArtinPrimitiveRoots.A2
