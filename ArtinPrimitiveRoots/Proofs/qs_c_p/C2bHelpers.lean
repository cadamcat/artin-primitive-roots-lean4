import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C1
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2
import Mathlib.MeasureTheory.Measure.Dirac

/-!
Small arithmetic facts used by the paired boundary estimate.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory
open Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

theorem qs_c2b_char_conj_eq (F : QSFamily m qS) {c : Ideal (𝓞 K)}
    (hc : QSAdm m qS c) (a : Ideal (𝓞 K)) :
    conj ((F.character c).idealValue a) = (F.character c).idealValue a := by
  rcases F.quadraticValues c hc.1 hc.2.1 a with hzero | hsq
  · simp [hzero]
  · rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h]

private theorem qs_c2b_primeOfIsPrime (P : Ideal (𝓞 K)) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) : Prime P := by
  refine ⟨hP0, ?_, ?_⟩
  · intro hunit
    exact hP.ne_top (Ideal.isUnit_iff.mp hunit)
  · intro I J hdiv
    have hle : I * J ≤ P := Ideal.dvd_iff_le.mp hdiv
    rcases hP.mul_le.mp hle with hI | hJ
    · exact Or.inl (Ideal.dvd_iff_le.mpr hI)
    · exact Or.inr (Ideal.dvd_iff_le.mpr hJ)

private def qsC2bLocalUnit (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (P : Ideal (𝓞 K)) : ℂˣ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then
    let v : ArtinPrimitiveRoots.A1.FinPlace K := ⟨P, h.1, h.2⟩
    χ.loc v (ArtinPrimitiveRoots.A1.toLoc v
      (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v)))
  else 1

def qsC2bLocalTwist (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (I : Ideal (𝓞 K)) : ℂ :=
  (UniqueFactorizationMonoid.normalizedFactors I).map
    (fun P => (qsC2bLocalUnit χ P : ℂ)) |>.prod

private theorem qs_c2b_localUnit_sq (F : QSFamily m qS) {c : Ideal (𝓞 K)}
    (hc : QSAdm m qS c) (P : Ideal (𝓞 K)) :
    qsC2bLocalUnit (F.character c) P ^ 2 = 1 := by
  classical
  by_cases hP : P.IsPrime ∧ P ≠ ⊥
  · let v : ArtinPrimitiveRoots.A1.FinPlace K := ⟨P, hP.1, hP.2⟩
    let u := ArtinPrimitiveRoots.A1.toLoc v
      (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v))
    have hchar := F.character_order_two c hc.1 hc.2.1
    have hcharMul : F.character c * F.character c = 1 := by
      simpa [pow_two] using hchar
    have hloc : (F.character c).loc v u * (F.character c).loc v u = 1 := by
      have hmul : ((F.character c) * (F.character c)).loc v u =
          (F.character c).loc v u * (F.character c).loc v u := by
        simp [ArtinPrimitiveRoots.A1.HeckeChar.loc]
      have heq := congrArg (fun θ : ArtinPrimitiveRoots.A1.HeckeChar K => θ.loc v u) hcharMul
      rw [hmul] at heq
      simpa [ArtinPrimitiveRoots.A1.HeckeChar.loc] using heq
    simpa [qsC2bLocalUnit, hP, v, u, pow_two] using hloc
  · simp [qsC2bLocalUnit, hP]

private theorem qs_c2b_localValue_sq (F : QSFamily m qS) {c : Ideal (𝓞 K)}
    (hc : QSAdm m qS c) (P : Ideal (𝓞 K)) :
    ((qsC2bLocalUnit (F.character c) P : ℂˣ) : ℂ) ^ 2 = 1 := by
  have h := congrArg (fun x : ℂˣ => (x : ℂ)) (qs_c2b_localUnit_sq F hc P)
  simpa [pow_two] using h

private theorem qs_c2b_localTwist_sq (F : QSFamily m qS) {c : Ideal (𝓞 K)}
    (hc : QSAdm m qS c) (I : Ideal (𝓞 K)) : qsC2bLocalTwist (F.character c) I ^ 2 = 1 := by
  classical
  unfold qsC2bLocalTwist
  induction UniqueFactorizationMonoid.normalizedFactors I using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, mul_pow]
      rw [qs_c2b_localValue_sq F hc P, ih]
      simp

theorem qs_c2b_localTwist_conj_eq (F : QSFamily m qS) {c : Ideal (𝓞 K)}
    (hc : QSAdm m qS c) (I : Ideal (𝓞 K)) :
    conj (qsC2bLocalTwist (F.character c) I) = qsC2bLocalTwist (F.character c) I := by
  have hsq := qs_c2b_localTwist_sq F hc I
  rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h]

theorem qs_c2b_localTwist_norm_eq_one (F : QSFamily m qS) {c : Ideal (𝓞 K)}
    (hc : QSAdm m qS c) (I : Ideal (𝓞 K)) :
    ‖qsC2bLocalTwist (F.character c) I‖ = 1 := by
  have hsq := qs_c2b_localTwist_sq F hc I
  rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h]

private theorem qs_c2b_idealValue_prime (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    χ.idealValue P = χ.primeValue ⟨P, hP, hP0⟩ := by
  have hPrime := qs_c2b_primeOfIsPrime P hP hP0
  rw [ArtinPrimitiveRoots.A1.HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hPrime.irreducible]
  have hnorm : normalize P = P := by simp
  simp [hnorm, hP, hP0]

private theorem qs_c2b_pair_prime_twist (F : QSFamily m qS) (c d q P : Ideal (𝓞 K))
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hcq : IsCoprime c q) (hdq : IsCoprime d q)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPq : P ∣ q) :
    (qsPairChar F c d).primeValue ⟨P, hP, hP0⟩ =
      ((qsC2bLocalUnit (F.character c) P : ℂˣ) : ℂ) *
        ((qsC2bLocalUnit (F.character d) P : ℂˣ) : ℂ) := by
  let v : ArtinPrimitiveRoots.A1.FinPlace K := ⟨P, hP, hP0⟩
  let u := ArtinPrimitiveRoots.A1.toLoc v
    (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v))
  have hpairSq := qsC1_pair_value_sq_one_at_q F c d q P hc hd hcd hcl hcq hdq hP hP0 hPq
  have hpairIdeal := qs_c2b_idealValue_prime (qsPairChar F c d) P hP hP0
  have hprimeSq : (qsPairChar F c d).primeValue v ^ 2 = 1 := by
    rw [← hpairIdeal]
    exact hpairSq
  have hprimeNe : (qsPairChar F c d).primeValue v ≠ 0 := by
    intro hz
    rw [hz] at hprimeSq
    norm_num at hprimeSq
  have hunr : (qsPairChar F c d).UnramifiedAt v := by
    by_contra hnot
    have hz : (qsPairChar F c d).primeValue v = 0 := by
      simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hnot]
    exact hprimeNe hz
  have hinvD : (F.character d)⁻¹ = F.character d := by
    ext x
    have hsqx : (F.character d x) ^ 2 = 1 := by
      simpa using congrArg (fun χ : ArtinPrimitiveRoots.A1.HeckeChar K => χ x)
        (F.character_order_two d hd.1 hd.2.1)
    have hx : (F.character d x)⁻¹ = F.character d x := by
      calc
        (F.character d x)⁻¹ = (F.character d x)⁻¹ * (F.character d x) ^ 2 := by
          rw [hsqx]
          simp
        _ = F.character d x := by group
    exact congrArg (fun x : ℂˣ => (x : ℂ)) hx
  have hlocPair : (qsPairChar F c d).loc v u =
      (F.character c).loc v u * (F.character d).loc v u := by
    simp [qsPairChar, hinvD, ArtinPrimitiveRoots.A1.HeckeChar.loc]
  have hunitC : qsC2bLocalUnit (F.character c) P = (F.character c).loc v u := by
    rw [qsC2bLocalUnit, dif_pos (show P.IsPrime ∧ P ≠ ⊥ from ⟨hP, hP0⟩)]
  have hunitD : qsC2bLocalUnit (F.character d) P = (F.character d).loc v u := by
    rw [qsC2bLocalUnit, dif_pos (show P.IsPrime ∧ P ≠ ⊥ from ⟨hP, hP0⟩)]
  calc
    (qsPairChar F c d).primeValue v =
        ((qsPairChar F c d).loc v u : ℂˣ) := by
          rw [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, if_pos hunr]
    _ = ((F.character c).loc v u : ℂˣ) *
          ((F.character d).loc v u : ℂˣ) := by
          exact congrArg (fun x : ℂˣ => (x : ℂ)) hlocPair
    _ = _ := by rw [hunitC, hunitD]

theorem qs_c2b_pairValue_localTwist (F : QSFamily m qS) (c d q e : Ideal (𝓞 K))
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hcq : IsCoprime c q) (hdq : IsCoprime d q) (hq : e ∣ q) (he0 : e ≠ ⊥) :
    (qsPairChar F c d).idealValue e =
      qsC2bLocalTwist (F.character c) e * qsC2bLocalTwist (F.character d) e := by
  classical
  let ψ := qsPairChar F c d
  have hterm (P : Ideal (𝓞 K)) (hPmem : P ∈ UniqueFactorizationMonoid.normalizedFactors e) :
      (if h : P.IsPrime ∧ P ≠ ⊥ then ψ.primeValue ⟨P, h.1, h.2⟩ else 1) =
        ((qsC2bLocalUnit (F.character c) P : ℂˣ) : ℂ) *
          ((qsC2bLocalUnit (F.character d) P : ℂˣ) : ℂ) := by
    have hP' := (Ideal.mem_normalizedFactors_iff he0).1 hPmem
    have hP0 : P ≠ ⊥ := by
      intro hbot
      have hprime : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hPmem
      exact hprime.ne_zero (by simpa [Ideal.zero_eq_bot] using hbot)
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime
      (UniqueFactorizationMonoid.prime_of_normalized_factor P hPmem)
    have hPe : P ∣ e := Ideal.dvd_iff_le.mpr hP'.2
    have hPq : P ∣ q := dvd_trans hPe hq
    simp only [dif_pos (show P.IsPrime ∧ P ≠ ⊥ from ⟨hPprime, hP0⟩)]
    exact qs_c2b_pair_prime_twist F c d q P hc hd hcd hcl hcq hdq hPprime hP0 hPq
  have hprod :
      ψ.idealValue e = qsC2bLocalTwist (F.character c) e *
        qsC2bLocalTwist (F.character d) e := by
    have hprod := congrArg Multiset.prod
      (Multiset.map_congr rfl fun P hP => hterm P hP)
    unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue qsC2bLocalTwist
    rw [hprod, Multiset.prod_map_mul]
  calc
    ψ.idealValue e = _ := hprod
    _ = _ := rfl

theorem qs_c2b_phiRatio_norm_le_card {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ‖(qsPhiRatio I : ℂ)‖ ≤ (qsDivisors I).card := by
  have hmu (e : Ideal (𝓞 K)) : ‖(qsMu e : ℝ)‖ ≤ 1 := by
    unfold qsMu
    split_ifs <;> simp
  have hterm (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors I) :
      ‖((qsMu e : ℝ) / (Ideal.absNorm e : ℝ))‖ ≤ 1 := by
    have hdiv := (QSC2.mem_qsDivisors hI).mp he
    have he0 : e ≠ ⊥ := by
      intro hz
      subst e
      have hle : I ≤ ⊥ := Ideal.le_of_dvd hdiv
      exact hI (bot_unique hle)
    have hne : Ideal.absNorm e ≠ 0 := by
      intro hz
      exact he0 (Ideal.absNorm_eq_zero_iff.mp hz)
    have hden : 0 < (Ideal.absNorm e : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hne
    have hden1 : 1 ≤ (Ideal.absNorm e : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hdennorm : ‖(Ideal.absNorm e : ℝ)‖ = (Ideal.absNorm e : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [norm_div, hdennorm]
    have hnumden : ‖(qsMu e : ℝ)‖ ≤ 1 * (Ideal.absNorm e : ℝ) := by
      nlinarith [hmu e, hden1]
    have hquot : ‖(qsMu e : ℝ)‖ / (Ideal.absNorm e : ℝ) ≤ 1 :=
      (div_le_iff₀ hden).2 hnumden
    exact hquot
  have hsum :
      (qsPhiRatio I : ℂ) =
        ∑ e ∈ qsDivisors I, (((qsMu e : ℝ) / (Ideal.absNorm e : ℝ) : ℝ) : ℂ) := by
    simp [qsPhiRatio, map_sum]
  rw [hsum]
  calc
    ‖∑ e ∈ qsDivisors I, (((qsMu e : ℝ) / (Ideal.absNorm e : ℝ) : ℝ) : ℂ)‖
        ≤ ∑ e ∈ qsDivisors I,
            ‖(((qsMu e : ℝ) / (Ideal.absNorm e : ℝ) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ qsDivisors I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      simpa using hterm e he
    _ = (qsDivisors I).card := by simp

private theorem qs_c2b_modulusRad_ne_bot :
    qsModulusRad (K := K) m ≠ ⊥ := by
  unfold qsModulusRad
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  exact v.ne_bot

theorem qs_c2b_mu_top : qsMu (⊤ : Ideal (𝓞 K)) = 1 := by
  rw [show (⊤ : Ideal (𝓞 K)) = 1 by simp]
  unfold qsMu
  have hs : Squarefree (1 : Ideal (𝓞 K)) := by simp
  rw [if_pos hs, UniqueFactorizationMonoid.normalizedFactors_of_isUnit isUnit_one]
  simp

theorem qs_c2b_idealValue_top (χ : ArtinPrimitiveRoots.A1.HeckeChar K) :
    χ.idealValue (⊤ : Ideal (𝓞 K)) = 1 := by
  rw [show (⊤ : Ideal (𝓞 K)) = 1 by simp,
    ArtinPrimitiveRoots.A1.HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_of_isUnit isUnit_one]
  rfl

private theorem qs_c2b_prime_dvd_rad {I P : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hP : P.IsPrime) (hPI : P ∣ I) : P ∣ qsRad I := by
  have hmem : P ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    (Ideal.mem_normalizedFactors_iff hI).2 ⟨hP, Ideal.le_of_dvd hPI⟩
  unfold qsRad
  exact Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.mpr hmem)

private theorem qs_c2b_coprime_factors {a q : Ideal (𝓞 K)}
    (hqS : qS ≠ ⊥) (hbad : qsBadRad m qS ∣ q) (haq : IsCoprime a q) :
    IsCoprime a (qsModulusRad m) ∧ IsCoprime a qS := by
  have hmod0 := qs_c2b_modulusRad_ne_bot (K := K) (m := m)
  have hprod0 : qsModulusRad m * qS ≠ ⊥ := mul_ne_zero hmod0 hqS
  have hbadcop : IsCoprime a (qsBadRad m qS) := by
    rw [Ideal.isCoprime_iff_sup_eq] at haq ⊢
    apply le_antisymm le_top
    calc
      ⊤ = a ⊔ q := haq.symm
      _ ≤ a ⊔ qsBadRad m qS :=
        sup_le_sup_left (Ideal.le_of_dvd hbad) a
  have htarget (X : Ideal (𝓞 K)) (hXI : X ∣ qsModulusRad m * qS) :
      IsCoprime a X := by
    by_contra hcop
    rw [Ideal.isCoprime_iff_sup_eq] at hcop
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hcop
    have hPa : P ∣ a := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
    have hPX : P ∣ X := Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle)
    have hPI : P ∣ qsModulusRad m * qS := dvd_trans hPX hXI
    have hPrad := qs_c2b_prime_dvd_rad hprod0 hP.isPrime hPI
    have hPq : P ∣ q := dvd_trans hPrad hbad
    have hleP : a ⊔ q ≤ P := sup_le (Ideal.le_of_dvd hPa) (Ideal.le_of_dvd hPq)
    have htop : ⊤ ≤ P := by
      rw [Ideal.isCoprime_iff_sup_eq] at haq
      simpa [haq] using hleP
    exact hP.ne_top (top_unique htop)
  constructor
  · apply htarget
    exact ⟨qS, rfl⟩
  · apply htarget
    exact ⟨qsModulusRad m, by rw [mul_comm]⟩

theorem qs_c2b_row_admissible {a q : Ideal (𝓞 K)}
    (hqS : qS ≠ ⊥) (hbad : qsBadRad m qS ∣ q) (ha0 : a ≠ ⊥)
    (hasqf : Squarefree a) (haq : IsCoprime a q) : QSAdm m qS a := by
  rcases qs_c2b_coprime_factors hqS hbad haq with ⟨hamod, haqS⟩
  exact ⟨hasqf,
    (qs_isCoprimeTo_iff_M0 (m := m) a).mpr ⟨ha0, hamod⟩,
    haqS⟩

private theorem qsC2b_sum4_comm {α β γ δ M : Type*} [AddCommMonoid M]
    (s₁ : Finset α) (s₂ : Finset β) (s₃ : Finset γ) (s₄ : Finset δ)
    (f : α → β → γ → δ → M) :
    (∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, f a b c d) =
      ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ a ∈ s₁, ∑ b ∈ s₂, f a b c d := by
  calc
    _ = ∑ a ∈ s₁, ∑ c ∈ s₃, ∑ b ∈ s₂, ∑ d ∈ s₄, f a b c d :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ s₃, ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ d ∈ s₄, f a b c d := Finset.sum_comm
    _ = ∑ c ∈ s₃, ∑ a ∈ s₁, ∑ d ∈ s₄, ∑ b ∈ s₂, f a b c d :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ a ∈ s₁, ∑ b ∈ s₂, f a b c d :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem qs_c2b_pairSum_double_sum {α β : Type*} (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) (s : Finset α) (t : Finset β)
    (f : α → β → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    qsPairSum cols z (fun c d => ∑ x ∈ s, ∑ y ∈ t, f x y c d) =
      ∑ x ∈ s, ∑ y ∈ t, qsPairSum cols z (f x y) := by
  classical
  unfold qsPairSum
  calc
    _ = ∑ c ∈ cols, ∑ d ∈ cols, ∑ x ∈ s, ∑ y ∈ t,
          if IsCoprime c d then z c * conj (z d) * f x y c d else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcd : IsCoprime c d
      · simp only [if_pos hcd, Finset.mul_sum]
      · simp [hcd]
    _ = ∑ x ∈ s, ∑ y ∈ t, ∑ c ∈ cols, ∑ d ∈ cols,
          if IsCoprime c d then z c * conj (z d) * f x y c d else 0 :=
        qsC2b_sum4_comm cols cols s t _
    _ = _ := rfl

theorem qs_c2b_pairSum_const_mul (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) (A : ℂ)
    (f : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    qsPairSum cols z (fun c d => A * f c d) = A * qsPairSum cols z f := by
  classical
  unfold qsPairSum
  calc
    _ = ∑ c ∈ cols, ∑ d ∈ cols,
          A * (if IsCoprime c d then z c * conj (z d) * f c d else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp [mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ c ∈ cols, A * ∑ d ∈ cols,
          if IsCoprime c d then z c * conj (z d) * f c d else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ = A * ∑ c ∈ cols, ∑ d ∈ cols,
          if IsCoprime c d then z c * conj (z d) * f c d else 0 := by
      rw [Finset.mul_sum]

theorem qs_c2b_dirac_constant_mixture (y u x : ℝ) :
    (1 : ℂ) = ∫ t, ((x : ℂ) ^ ((t : ℂ) * Complex.I)) * (1 : ℂ)
      ∂MeasureTheory.Measure.dirac (0 : ℝ) := by
  simp

private theorem qs_c2b_mem_qsUpTo {X : ℝ} {I : Ideal (𝓞 K)}
    (hI : QSAdm m qS I) (hN : qsN I ≤ X) : I ∈ qsUpTo m qS X := by
  classical
  unfold qsUpTo
  apply Finset.mem_filter.mpr
  constructor
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Nat.le_floor hN
  · exact ⟨hI, hN⟩

theorem qs_c2b_top_admissible : QSAdm m qS (⊤ : Ideal (𝓞 K)) := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [qs_isCoprimeTo_iff_M0]
    exact ⟨by simp, by simp [Ideal.isCoprime_iff_sup_eq]⟩
  · simp [Ideal.isCoprime_iff_sup_eq]

theorem qs_c2b_cols_card_le_norm (F : QSFamily m qS) (κ n : ℝ)
    (hκ : 1 ≤ κ) (hn : 1 ≤ n) (cols : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n) :
    (cols.card : ℝ) ≤ qsNorm F κ (2 * n) := by
  classical
  let R := qsUpTo m qS κ
  let C := qsUpTo m qS (2 * n)
  have htopR : (⊤ : Ideal (𝓞 K)) ∈ R := by
    apply qs_c2b_mem_qsUpTo qs_c2b_top_admissible
    simp [qsN, hκ]
  have htopC : (⊤ : Ideal (𝓞 K)) ∈ C := by
    apply qs_c2b_mem_qsUpTo qs_c2b_top_admissible
    have : 1 ≤ 2 * n := by linarith
    simpa [qsN] using this
  have hsubset : cols ⊆ C := by
    intro c hc
    exact qs_c2b_mem_qsUpTo (hcols c hc).1 (hcols c hc).2
  have htopval (c : Ideal (𝓞 K)) : (F.character c).idealValue (⊤ : Ideal (𝓞 K)) = 1 := by
    have htopEq : (⊤ : Ideal (𝓞 K)) = 1 := by simp
    rw [htopEq, ArtinPrimitiveRoots.A1.HeckeChar.idealValue,
      UniqueFactorizationMonoid.normalizedFactors_of_isUnit isUnit_one]
    rfl
  let u : Ideal (𝓞 K) → ℂ := fun _ => 1
  have hsum :
      ∑ c ∈ C, u c * (F.character c).idealValue (⊤ : Ideal (𝓞 K)) = (C.card : ℂ) := by
    calc
      _ = ∑ _c ∈ C, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [u, htopval]
      _ = (C.card : ℂ) := by simp
  have htopSum :
      ‖∑ c ∈ C, u c * (F.character c).idealValue (⊤ : Ideal (𝓞 K))‖ ^ 2 =
        (C.card : ℝ) ^ 2 := by
    rw [hsum]
    simp
  have henergyLower : (C.card : ℝ) ^ 2 ≤
      ∑ a ∈ R, ‖∑ c ∈ C, u c * (F.character c).idealValue a‖ ^ 2 := by
    calc
      _ = ‖∑ c ∈ C, u c * (F.character c).idealValue (⊤ : Ideal (𝓞 K))‖ ^ 2 := htopSum.symm
      _ ≤ ∑ a ∈ R, ‖∑ c ∈ C, u c * (F.character c).idealValue a‖ ^ 2 :=
        Finset.single_le_sum (s := R)
          (f := fun a => ‖∑ c ∈ C, u c * (F.character c).idealValue a‖ ^ 2)
          (fun a _ => sq_nonneg _) htopR
  have henergy := qs_energy_le_norm_M0 F κ (2 * n) u
  have hcoeff : ∑ c ∈ C, ‖u c‖ ^ 2 = (C.card : ℝ) := by simp [u]
  have hle : (C.card : ℝ) ^ 2 ≤ qsNorm F κ (2 * n) * (C.card : ℝ) := by
    calc
      _ ≤ ∑ a ∈ R, ‖∑ c ∈ C, u c * (F.character c).idealValue a‖ ^ 2 := henergyLower
      _ ≤ qsNorm F κ (2 * n) * ∑ c ∈ C, ‖u c‖ ^ 2 := henergy
      _ = qsNorm F κ (2 * n) * (C.card : ℝ) := by rw [hcoeff]
  have hCpos : 0 < (C.card : ℝ) := by
    have hpos : 0 < C.card := Finset.card_pos.mpr ⟨⊤, htopC⟩
    exact_mod_cast hpos
  have hcount : (C.card : ℝ) ≤ qsNorm F κ (2 * n) := by nlinarith
  have hcard : cols.card ≤ C.card := Finset.card_le_card hsubset
  have hcard' : (cols.card : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hcard
  exact hcard'.trans hcount

end ArtinPrimitiveRoots.A2
