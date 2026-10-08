import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2
import ArtinPrimitiveRoots.Proofs.qs_c_p.C2bHelpers

/-!
Local cutoff facts for the C3 remainder estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 20000000

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.qs_c_p

open ArtinPrimitiveRoots.A2

/-- A nonzero divisor inside the dual upper cutoff forces the row-scale bound used
when estimating the dual remainders. -/
theorem qs_c3_dual_cutoff_support (M A E n Λ : ℝ) (hM : 0 < M) (hA : 0 < A)
    (hE : 0 ≤ E) (_hΛ : 0 < Λ)
    (hsupport : 1 ≤ 2 * Λ * Real.sqrt (E * n ^ 2 / (M * A))) :
    M * A ≤ 4 * E * n ^ 2 * Λ ^ 2 := by
  have hden : 0 < M * A := mul_pos hM hA
  have hratio : 0 ≤ E * n ^ 2 / (M * A) :=
    div_nonneg (mul_nonneg hE (sq_nonneg n)) hden.le
  have hsqrt := Real.sq_sqrt hratio
  have hsqrt_nonneg := Real.sqrt_nonneg (E * n ^ 2 / (M * A))
  have hsq : 1 ≤ 4 * Λ ^ 2 * (E * n ^ 2 / (M * A)) := by
    nlinarith [sq_nonneg (2 * Λ * Real.sqrt (E * n ^ 2 / (M * A)) - 1)]
  have hquot : 1 ≤ (4 * Λ ^ 2 * (E * n ^ 2)) / (M * A) := by
    simpa only [mul_div_assoc] using hsq
  have hmul := (le_div_iff₀ hden).mp hquot
  nlinarith

/-- A dyadic C2 norm can be put in the orientation needed by the exponent hypothesis. -/
theorem qs_c3_norm_symm_exp_bound {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε B n D : ℝ) (hε : 0 < ε) (hB : 1 ≤ B) (_hn : 1 ≤ n)
    (hD : 1 ≤ D) (hDn : D ≤ n) (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      qsNorm F (2 * B) (2 * n / D) ≤
        C * ((2 * n / D) * (2 * B)) ^ ε * ((2 * n / D) + (2 * B) ^ α) := by
  obtain ⟨C, hC, hbound⟩ := hexp ε hε
  refine ⟨C, hC, ?_⟩
  have hDpos : 0 < D := by linarith
  have hnD : 1 ≤ n / D := (one_le_div₀ hDpos).2 (by nlinarith)
  have hfirst : 1 ≤ 2 * n / D := by
    rw [show 2 * n / D = 2 * (n / D) by ring]
    nlinarith
  have hsecond : 1 ≤ 2 * B := by nlinarith
  rw [qs_norm_symm_M0 F hrf (2 * B) (2 * n / D)]
  exact hbound (2 * n / D) (2 * B) hfirst hsecond

/-- Rows in an original kernel's squarefree support are admissible when the coprimality
modulus contains the bad radical. -/
theorem qs_c3_orig_row_admissible {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS q a : Ideal (𝓞 K)}
    (hqS : qS ≠ ⊥) (hbad : qsBadRad m qS ∣ q) (κ : ℝ)
    (ha : a ∈ qsSqfUpTo κ q) : QSAdm m qS a ∧ qsN a ≤ κ := by
  have ha' := ha
  simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ha'
  rcases ha' with ⟨_, ⟨ha0, hasqf, haq, hNa⟩⟩
  exact ⟨qs_c2b_row_admissible hqS hbad ha0 hasqf haq, hNa⟩

theorem qs_c3_sqfUpTo_norm_le_nat {K : Type} [Field K] [NumberField K]
    {κ : ℝ} {q a : Ideal (𝓞 K)} (ha : a ∈ qsSqfUpTo κ q) :
    Ideal.absNorm a ≤ ⌊κ⌋₊ := by
  have ha' := ha
  simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq] at ha'
  exact ha'.1

theorem qs_c3_divisor_norm_le_of_col {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    {c e : Ideal (𝓞 K)} (hc : QSAdm m qS c)
    (he : e ∈ qsDivisors c) : qsN e ≤ qsN c := by
  have hc0 := QSC2.ne_bot_of_QSAdm hc
  have hediv := (QSC2.mem_qsDivisors hc0).1 he
  have hcNpos : 0 < Ideal.absNorm c := by
    exact Nat.pos_iff_ne_zero.mpr (fun hz => hc0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hnat := Nat.le_of_dvd hcNpos (map_dvd Ideal.absNorm hediv)
  exact_mod_cast hnat

/-- Every divisor of a product can be represented by a pair of factor divisors. -/
theorem qs_c3_divisor_product_exists {K : Type} [Field K] [NumberField K]
    {I J e : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (he : e ∈ qsDivisors (I * J)) :
    ∃ p : Ideal (𝓞 K) × Ideal (𝓞 K),
      p.1 ∈ qsDivisors I ∧ p.2 ∈ qsDivisors J ∧ e = p.1 * p.2 := by
  have hediv := (QSC2.mem_qsDivisors (mul_ne_zero hI hJ)).1 he
  obtain ⟨eI, eJ, hIdiv, hJdiv, heq⟩ := exists_dvd_and_dvd_of_dvd_mul hediv
  exact ⟨(eI, eJ), (QSC2.mem_qsDivisors hI).2 hIdiv,
    (QSC2.mem_qsDivisors hJ).2 hJdiv, heq⟩

/-- Coprimality makes the divisor product representation unique. -/
theorem qs_c3_divisor_product_unique {K : Type} [Field K] [NumberField K]
    {I J eI eJ fI fJ : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcop : IsCoprime I J)
    (heI : eI ∈ qsDivisors I) (heJ : eJ ∈ qsDivisors J)
    (hfI : fI ∈ qsDivisors I) (hfJ : fJ ∈ qsDivisors J)
    (hprod : eI * eJ = fI * fJ) : eI = fI ∧ eJ = fJ := by
  have heIdiv := (QSC2.mem_qsDivisors hI).1 heI
  have heJdiv := (QSC2.mem_qsDivisors hJ).1 heJ
  have hfIdiv := (QSC2.mem_qsDivisors hI).1 hfI
  have hfJdiv := (QSC2.mem_qsDivisors hJ).1 hfJ
  have hrelE := hcop.isRelPrime.of_dvd_left heIdiv
  have hrelEF := hrelE.of_dvd_right hfJdiv
  have heI_fI : eI ∣ fI := hrelEF.dvd_of_dvd_mul_right (by
    rw [← hprod]
    exact dvd_mul_right eI eJ)
  have hrelF := hcop.isRelPrime.of_dvd_left hfIdiv
  have hrelFE := hrelF.of_dvd_right heJdiv
  have hfI_eI : fI ∣ eI := hrelFE.dvd_of_dvd_mul_right (by
    rw [hprod]
    exact dvd_mul_right fI fJ)
  have heIf : eI = fI := le_antisymm
    (Ideal.dvd_iff_le.mp hfI_eI) (Ideal.dvd_iff_le.mp heI_fI)
  have heI0 : eI ≠ ⊥ := by
    intro hz
    have : I = ⊥ := by
      rw [hz] at heIdiv
      exact bot_unique (Ideal.le_of_dvd heIdiv)
    exact hI this
  have heJfJ : eJ = fJ := by
    apply mul_left_cancel₀ heI0
    simpa [heIf] using hprod
  exact ⟨heIf, heJfJ⟩

/-- Reindex the divisors of a coprime product by the pair of factor divisors. -/
theorem qs_c3_divisor_sum_reindex {K : Type} [Field K] [NumberField K]
    {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcop : IsCoprime I J) {A : Type*} [AddCommMonoid A]
    (f : Ideal (𝓞 K) → A) :
    (∑ e ∈ qsDivisors (I * J), f e) =
      ∑ eI ∈ qsDivisors I, ∑ eJ ∈ qsDivisors J, f (eI * eJ) := by
  classical
  let S : Finset (Ideal (𝓞 K)) := qsDivisors (I * J)
  let T : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) := qsDivisors I ×ˢ qsDivisors J
  let i : (e : Ideal (𝓞 K)) → e ∈ S → Ideal (𝓞 K) × Ideal (𝓞 K) := fun e he =>
    Classical.choose (qs_c3_divisor_product_exists hI hJ (by simpa [S] using he))
  let j : (p : Ideal (𝓞 K) × Ideal (𝓞 K)) → p ∈ T → Ideal (𝓞 K) := fun p _ => p.1 * p.2
  have hi : ∀ e he, i e he ∈ T := by
    intro e he
    have hs := Classical.choose_spec
      (qs_c3_divisor_product_exists hI hJ (by simpa [S] using he))
    exact Finset.mem_product.mpr ⟨hs.1, hs.2.1⟩
  have hj : ∀ p hp, j p hp ∈ S := by
    intro p hp
    rcases Finset.mem_product.mp (show p ∈ T by simpa [T] using hp) with ⟨hpi, hpj⟩
    have hpidiv := (QSC2.mem_qsDivisors hI).1 hpi
    have hpjdiv := (QSC2.mem_qsDivisors hJ).1 hpj
    apply (QSC2.mem_qsDivisors (mul_ne_zero hI hJ)).2
    simpa [j] using mul_dvd_mul hpidiv hpjdiv
  have hleft : ∀ e he, j (i e he) (hi e he) = e := by
    intro e he
    exact (Classical.choose_spec
      (qs_c3_divisor_product_exists hI hJ (by simpa [S] using he))).2.2.symm
  have hright : ∀ p hp, i (j p hp) (hj p hp) = p := by
    intro p hp
    rcases Finset.mem_product.mp (show p ∈ T by simpa [T] using hp) with ⟨hpi, hpj⟩
    let p' := i (j p hp) (hj p hp)
    have hp' : p' ∈ T := hi (j p hp) (hj p hp)
    have hs := Classical.choose_spec
      (qs_c3_divisor_product_exists hI hJ (by simpa [S] using hj p hp))
    rcases Finset.mem_product.mp (show p' ∈ T by exact hp') with ⟨hp'i, hp'j⟩
    have hprod : p.1 * p.2 = p'.1 * p'.2 := by
      simpa [j, p'] using hs.2.2
    have huniq := qs_c3_divisor_product_unique hI hJ hcop hpi hpj hp'i hp'j hprod
    exact Prod.ext huniq.1.symm huniq.2.symm
  have hsum : (∑ e ∈ S, f e) = ∑ p ∈ T, f (p.1 * p.2) := by
    apply Finset.sum_bij' i j hi hj hleft hright
    intro e he
    exact congrArg f (Classical.choose_spec
      (qs_c3_divisor_product_exists hI hJ (by simpa [S] using he))).2.2
  simpa [S, T, Finset.sum_product] using hsum

/-- Möbius multiplicativity for squarefree coprime ideal factors. -/
theorem qs_c3_qsMu_mul_of_squarefree {K : Type} [Field K] [NumberField K]
    {I J : Ideal (𝓞 K)} (hI : Squarefree I) (hJ : Squarefree J)
    (hcop : IsCoprime I J) : qsMu (I * J) = qsMu I * qsMu J := by
  have hIJ : Squarefree (I * J) :=
    squarefree_mul_iff.mpr ⟨hcop.isRelPrime, hI, hJ⟩
  simp only [qsMu, hI, hJ, hIJ, if_pos]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hI.ne_zero hJ.ne_zero,
    Multiset.card_add, pow_add]

theorem qs_c3_isCoprime_of_dvd {K : Type} [Field K] [NumberField K]
    {I J i j : Ideal (𝓞 K)} (hcop : IsCoprime I J) (hi : i ∣ I) (hj : j ∣ J) :
    IsCoprime i j := by
  rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
  apply top_unique
  calc
    ⊤ = I ⊔ J := hcop.symm
    _ ≤ i ⊔ j := sup_le_sup (Ideal.le_of_dvd hi) (Ideal.le_of_dvd hj)

/-- Reindex the divisors of three pairwise-coprime ideals by their three factors. -/
theorem qs_c3_divisor_sum_reindex₃ {K : Type} [Field K] [NumberField K]
    {I J L : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hL : L ≠ ⊥)
    (hIJ : IsCoprime I J) (hIL : IsCoprime I L) (hJL : IsCoprime J L)
    {A : Type*} [AddCommMonoid A] (f : Ideal (𝓞 K) → A) :
    (∑ e ∈ qsDivisors (I * (J * L)), f e) =
      ∑ eI ∈ qsDivisors I, ∑ eJ ∈ qsDivisors J, ∑ eL ∈ qsDivisors L,
        f (eI * (eJ * eL)) := by
  calc
    _ = ∑ eI ∈ qsDivisors I, ∑ eJL ∈ qsDivisors (J * L), f (eI * eJL) :=
      qs_c3_divisor_sum_reindex hI (mul_ne_zero hJ hL)
        (IsCoprime.mul_right hIJ hIL)
        (fun e => f e)
    _ = ∑ eI ∈ qsDivisors I, ∑ eJ ∈ qsDivisors J, ∑ eL ∈ qsDivisors L,
          f (eI * (eJ * eL)) := by
      apply Finset.sum_congr rfl
      intro eI heI
      exact qs_c3_divisor_sum_reindex hJ hL hJL (fun e => f (eI * e))

/-- The ideal Möbius weight splits across the three coprime squarefree factors. -/
theorem qs_c3_qsMu_factor_three {K : Type} [Field K] [NumberField K]
    {q c d eq ec ed : Ideal (𝓞 K)}
    (hq : Squarefree q) (hc : Squarefree c) (hd : Squarefree d)
    (hqc : IsCoprime q c) (hqd : IsCoprime q d) (hcd : IsCoprime c d)
    (heq : eq ∈ qsDivisors q) (hec : ec ∈ qsDivisors c) (hed : ed ∈ qsDivisors d) :
    qsMu (eq * (ec * ed)) = qsMu eq * qsMu (ec * ed) := by
  have heqDvd := (QSC2.mem_qsDivisors hq.ne_zero).1 heq
  have hecDvd := (QSC2.mem_qsDivisors hc.ne_zero).1 hec
  have hedDvd := (QSC2.mem_qsDivisors hd.ne_zero).1 hed
  have heqSq : Squarefree eq := Squarefree.squarefree_of_dvd heqDvd hq
  have hecSq : Squarefree ec := Squarefree.squarefree_of_dvd hecDvd hc
  have hedSq : Squarefree ed := Squarefree.squarefree_of_dvd hedDvd hd
  have heqec : IsCoprime eq ec := qs_c3_isCoprime_of_dvd hqc heqDvd hecDvd
  have heqed : IsCoprime eq ed := qs_c3_isCoprime_of_dvd hqd heqDvd hedDvd
  have heced : IsCoprime ec ed := qs_c3_isCoprime_of_dvd hcd hecDvd hedDvd
  have hec_ed_sq : Squarefree (ec * ed) :=
    squarefree_mul_iff.mpr ⟨heced.isRelPrime, hecSq, hedSq⟩
  have heq_eced : IsCoprime eq (ec * ed) := IsCoprime.mul_right heqec heqed
  exact qs_c3_qsMu_mul_of_squarefree heqSq hec_ed_sq heq_eced

/-- Expand one original zero-residue kernel across the coprime q/c/d divisor factors. -/
theorem qs_c3_orig_res_expand {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] {m : ClassFieldTheory.RayClassModulus K}
    {qS : Ideal (𝓞 K)} (F : QSFamily m qS) (W : ℝ → ℝ)
    (M κ Λ : ℝ) (q c d : Ideal (𝓞 K))
    (hq : Squarefree q) (hc : QSAdm m qS c) (hd : QSAdm m qS d)
    (hqc : IsCoprime c q) (hqd : IsCoprime d q) (hcd : IsCoprime c d)
    (hΛ : 0 < Λ) (hM : 0 < M) :
    qsOrigKernel (qsInnerRes K) F W M κ Λ q c d =
      qsResidueZero K (fun y => (W (y ^ 2) : ℂ)) *
        ∑ a ∈ qsSqfUpTo κ q,
          (qsPairChar F c d).idealValue a *
            ∑ eq ∈ qsDivisors q,
              ∑ ec ∈ qsDivisors c,
                ∑ ed ∈ qsDivisors d,
                  ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
                    (if qsN eq * qsN (ec * ed) ≤
                        Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
  classical
  let Wsq : ℝ → ℂ := fun y => (W (y ^ 2) : ℂ)
  let ψ := qsPairChar F c d
  have hqc' : IsCoprime q c := hqc.symm
  have hq0 : q ≠ ⊥ := hq.ne_zero
  have hc0 : c ≠ ⊥ := QSC2.ne_bot_of_QSAdm hc
  have hd0 : d ≠ ⊥ := QSC2.ne_bot_of_QSAdm hd
  have hcd0 : c * d ≠ ⊥ := mul_ne_zero hc0 hd0
  have hqcd : IsCoprime q (c * d) := IsCoprime.mul_right hqc' hqd.symm
  have hcd' : IsCoprime c d := hcd
  unfold qsOrigKernel
  simp only [qsInnerRes, Wsq]
  have hdivReindex (a : Ideal (𝓞 K)) :
      (∑ e ∈ (qsDivisors (q * (c * d))).filter
          (fun e => qsN e ≤ Λ * Real.sqrt (M / qsN a)), (qsMu e : ℂ)) =
        ∑ eq ∈ qsDivisors q, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
          ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
            (if qsN eq * qsN (ec * ed) ≤
                Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
    rw [Finset.sum_filter]
    rw [qs_c3_divisor_sum_reindex₃ hq0 hc0 hd0 hqc' hqd.symm hcd'
      (fun e => if qsN e ≤ Λ * Real.sqrt (M / qsN a) then (qsMu e : ℂ) else 0)]
    simp_rw [QSC2.qsN_mul]
    apply Finset.sum_congr rfl
    intro eq heq
    apply Finset.sum_congr rfl
    intro ec hec
    apply Finset.sum_congr rfl
    intro ed hed
    have hmu := qs_c3_qsMu_factor_three hq hc.1 hd.1 hqc' hqd.symm hcd' heq hec hed
    simp only [hmu, Int.cast_mul]
    by_cases hcut : qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) <;>
      simp [hcut]
  have hrows :
      (∑ a ∈ qsSqfUpTo κ q,
        ψ.idealValue a *
          ∑ e ∈ (qsDivisors (q * (c * d))).filter
            (fun e => qsN e ≤ Λ * Real.sqrt (M / qsN a)), (qsMu e : ℂ)) =
      ∑ a ∈ qsSqfUpTo κ q,
        ψ.idealValue a *
          ∑ eq ∈ qsDivisors q, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
            ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
              (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hdivReindex a]
  calc
    _ = ∑ a ∈ qsSqfUpTo κ q,
          (qsResidueZero K Wsq) *
            (ψ.idealValue a *
              ∑ e ∈ (qsDivisors (q * (c * d))).filter
                (fun e => qsN e ≤ Λ * Real.sqrt (M / qsN a)), (qsMu e : ℂ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (qsResidueZero K Wsq) *
          ∑ a ∈ qsSqfUpTo κ q,
            ψ.idealValue a *
              ∑ e ∈ (qsDivisors (q * (c * d))).filter
                (fun e => qsN e ≤ Λ * Real.sqrt (M / qsN a)), (qsMu e : ℂ) :=
      (Finset.mul_sum _ _ _).symm
    _ = (qsResidueZero K Wsq) *
          ∑ a ∈ qsSqfUpTo κ q,
            ψ.idealValue a *
              ∑ eq ∈ qsDivisors q, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
                ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
                  (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
      rw [hrows]
    _ = _ := by rfl

/-- Expand the original residue kernel and partition its rows and both column divisors
into dyads. -/

def qsC3RowTwist {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (a : Ideal (𝓞 K)) : ℂ :=
  (F.character ⊤).idealValue a * conj ((F.character ⊤).idealValue a)

/-- On admissible rows, the pair character is the product of the two column characters
multiplied by a bounded diagonal row twist. -/
theorem qs_c3_pairValue_row {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    {a c d : Ideal (𝓞 K)} (ha : QSAdm m qS a) (hc : QSAdm m qS c)
    (hd : QSAdm m qS d) (hcd : IsCoprime c d) :
    (qsPairChar F c d).idealValue a =
      qsC3RowTwist F a * (F.character c).idealValue a * (F.character d).idealValue a := by
  have htop := qs_c2b_top_admissible (m := m) (qS := qS)
  have htc : IsCoprime (⊤ : Ideal (𝓞 K)) c := by
    rw [Ideal.isCoprime_iff_sup_eq]
    simp
  have htd : IsCoprime (⊤ : Ideal (𝓞 K)) d := by
    rw [Ideal.isCoprime_iff_sup_eq]
    simp
  have hmulC := qs_family_mul_S0 F hrf ⊤ c htop hc htc a ha.2.1 ha.2.2
  have hmulD := qs_family_mul_S0 F hrf ⊤ d htop hd htd a ha.2.1 ha.2.2
  have hpair := qs_gcd_pair_identity_S0 F hrf ⊤ c d htop hc hd htc htd hcd a ha.2.1 ha.2.2
  have hacTop : IsCoprime a (⊤ : Ideal (𝓞 K)) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    simp
  have hpair' : (F.character (⊤ * c)).idealValue a *
      conj ((F.character (⊤ * d)).idealValue a) = (qsPairChar F c d).idealValue a := by
    simpa [hacTop] using hpair
  rw [hmulC, hmulD] at hpair'
  dsimp [qsC3RowTwist]
  calc
    (qsPairChar F c d).idealValue a =
        (F.character ⊤).idealValue a * conj ((F.character ⊤).idealValue a) *
          (F.character c).idealValue a * (F.character d).idealValue a := by
          rw [← hpair']
          simp only [map_mul]
          rw [qs_c2b_char_conj_eq F hd a]
          ring
    _ = _ := by ring

theorem qs_c3_rowTwist_norm_le {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) : ∀ a, ‖qsC3RowTwist F a‖ ≤ 1 := by
  intro a
  rw [qsC3RowTwist, norm_mul, Complex.norm_conj]
  have hnorm := QSC2.norm_idealValue_le_one F (qs_c2b_top_admissible (m := m) (qS := qS)) a
  simpa using mul_le_mul hnorm hnorm (norm_nonneg _) zero_le_one

/-- The C2u pair estimate for a coefficient independent of the product of column norms. -/
theorem qs_c3_pair_bound_C2u {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (η : ℝ) (hη : 0 < η)
    (n B D₁ D₂ : ℝ) (p₁ p₂ : Ideal (𝓞 K) → Prop)
    [DecidablePred p₁] [DecidablePred p₂]
    (cols rows : Finset (Ideal (𝓞 K))) (z ρ : Ideal (𝓞 K) → ℂ)
    (w : ℝ → ℝ → ℂ) (R : ℝ)
    (hn : 1 ≤ n) (hB : 1 ≤ B) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hp₁ : ∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁)
    (hp₂ : ∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂)
    (hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n)
    (hrows : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B)
    (hρ : ∀ a, ‖ρ a‖ ≤ 1) (_hR : 0 ≤ R)
    (hw : ∀ y u, ‖w y u‖ ≤ R) :
    ∃ C : ℝ, 0 < C ∧
      ‖qsPairSum cols z (fun c d =>
        ∑ e₁ ∈ (qsDivisors c).filter p₁,
          ∑ e₂ ∈ (qsDivisors d).filter p₂,
            (qsMu (e₁ * e₂) : ℂ) *
              ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                (F.character d).idealValue a * w (qsN a) (qsN (e₁ * e₂)))‖ ≤
        C * (n * B) ^ η * R * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  obtain ⟨C₂, hC₂, hbound⟩ := qs_divisor_pair_cauchy_C2u F hrf η hη
  refine ⟨C₂, hC₂, ?_⟩
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.Measure.dirac (0 : ℝ)
  let φ : ℝ → ℝ → ℝ → ℂ := fun y u _ => w y u
  let Φ : ℝ → ℝ → ℝ → ℂ := fun y u _ => w y u
  let gmaj : ℝ → ℝ := fun _ => R
  letI : MeasureTheory.IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hΦ : ∀ y u x : ℝ,
      Φ y u x = ∫ t, ((x : ℂ) ^ ((t : ℂ) * Complex.I)) * φ y u t ∂μ := by
    intro y u x
    simp [Φ, φ, μ]
  have hgm : MeasureTheory.Integrable gmaj μ := by simp [gmaj, μ]
  have hφ : ∀ y u t, ‖φ y u t‖ ≤ gmaj t := by
    intro y u t
    exact hw y u
  have hmass : ∫ t, gmaj t ∂μ ≤ R := by simp [gmaj, μ]
  exact hbound n B D₁ D₂ R p₁ p₂ cols rows z ρ μ φ Φ gmaj hn hB hD₁ hD₂
    hp₁ hp₂ hcols hrows hρ hΦ hgm hφ hmass

/-- Partition a finite set of positive integer sizes into norm dyads `[2^k,2^(k+1))`. -/
theorem qs_c3_shell_sum {α M : Type*} [AddCommMonoid M]
    (S : Finset α) (size : α → ℕ) (X : ℕ)
    (hsize : ∀ a ∈ S, 1 ≤ size a ∧ size a ≤ X) (f : α → M) :
    (∑ a ∈ S, f a) =
      ∑ k ∈ Finset.range (Nat.log 2 X + 1),
        ∑ a ∈ S.filter (fun a =>
          (2 ^ k : ℝ) ≤ (size a : ℝ) ∧ (size a : ℝ) < 2 ^ (k + 1)), f a := by
  classical
  let L : ℕ := Nat.log 2 X + 1
  let T : Finset (ℕ × α) :=
    ((Finset.range L) ×ˢ S).filter (fun p =>
      (2 ^ p.1 : ℝ) ≤ (size p.2 : ℝ) ∧ (size p.2 : ℝ) < 2 ^ (p.1 + 1))
  let i : (a : α) → a ∈ S → ℕ × α := fun a _ => (Nat.log 2 (size a), a)
  let j : (p : ℕ × α) → p ∈ T → α := fun p _ => p.2
  have hi : ∀ a ha, i a ha ∈ T := by
    intro a ha
    have hpos : size a ≠ 0 := by
      have := hsize a ha
      omega
    have hpowLo := Nat.pow_log_le_self 2 hpos
    have hpowHi := Nat.lt_pow_succ_log_self (Nat.one_lt_two) (size a)
    have hlogX : Nat.log 2 (size a) < L := by
      dsimp [L]
      exact Nat.lt_succ_of_le (Nat.log_mono_right (hsize a ha).2)
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨hlogX, ha⟩, ?_⟩
    constructor
    · exact_mod_cast hpowLo
    · exact_mod_cast hpowHi
  have hj : ∀ p hp, j p hp ∈ S := by
    intro p hp
    have hp' : p ∈ (Finset.range L ×ˢ S).filter (fun p =>
        (2 ^ p.1 : ℝ) ≤ (size p.2 : ℝ) ∧ (size p.2 : ℝ) < 2 ^ (p.1 + 1)) := by
      simpa [T] using hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).2
  have hleft : ∀ a ha, j (i a ha) (hi a ha) = a := by
    intro a ha
    rfl
  have hright : ∀ p hp, i (j p hp) (hj p hp) = p := by
    intro p hp
    have hp' := Finset.mem_filter.mp (show p ∈ (Finset.range L ×ˢ S).filter (fun p =>
      (2 ^ p.1 : ℝ) ≤ (size p.2 : ℝ) ∧ (size p.2 : ℝ) < 2 ^ (p.1 + 1)) by
      simpa [T] using hp)
    rcases Finset.mem_product.mp hp'.1 with ⟨_, hpa⟩
    have hpos : size p.2 ≠ 0 := by
      have := hsize p.2 hpa
      omega
    have hlog : Nat.log 2 (size p.2) = p.1 := by
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · exact_mod_cast hp'.2.1
      · exact_mod_cast hp'.2.2
    apply Prod.ext
    · exact hlog
    · rfl
  have hsum : (∑ a ∈ S, f a) = ∑ p ∈ T, f p.2 := by
    apply Finset.sum_bij' i j hi hj hleft hright
    intro a ha
    rfl
  rw [hsum]
  simp [T, L, Finset.sum_product, Finset.sum_filter]

/-- Simultaneous dyad partition for a finite double sum. -/
theorem qs_c3_shell_sum₂ {α β M : Type*} [AddCommMonoid M]
    (S : Finset α) (sizeS : α → ℕ) (XS : ℕ)
    (hsizeS : ∀ a ∈ S, 1 ≤ sizeS a ∧ sizeS a ≤ XS)
    (T : Finset β) (sizeT : β → ℕ) (XT : ℕ)
    (hsizeT : ∀ b ∈ T, 1 ≤ sizeT b ∧ sizeT b ≤ XT)
    (f : α → β → M) :
    (∑ a ∈ S, ∑ b ∈ T, f a b) =
      ∑ k ∈ Finset.range (Nat.log 2 XS + 1),
        ∑ l ∈ Finset.range (Nat.log 2 XT + 1),
          ∑ a ∈ S.filter (fun a =>
            (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
            ∑ b ∈ T.filter (fun b =>
              (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)), f a b := by
  classical
  calc
    _ = ∑ k ∈ Finset.range (Nat.log 2 XS + 1),
          ∑ a ∈ S.filter (fun a =>
            (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
            ∑ b ∈ T, f a b :=
      qs_c3_shell_sum S sizeS XS hsizeS (fun a => ∑ b ∈ T, f a b)
    _ = ∑ k ∈ Finset.range (Nat.log 2 XS + 1),
          ∑ a ∈ S.filter (fun a =>
            (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
            ∑ l ∈ Finset.range (Nat.log 2 XT + 1),
              ∑ b ∈ T.filter (fun b =>
                (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)), f a b := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      exact qs_c3_shell_sum T sizeT XT hsizeT (fun b => f a b)
    _ = ∑ k ∈ Finset.range (Nat.log 2 XS + 1),
          ∑ l ∈ Finset.range (Nat.log 2 XT + 1),
            ∑ a ∈ S.filter (fun a =>
              (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
              ∑ b ∈ T.filter (fun b =>
                (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)), f a b := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]

/-- Simultaneous dyad partition for a finite triple sum, with the two divisor sums
outside the row sum. -/
theorem qs_c3_shell_sum₃ {α β γ M : Type*} [AddCommMonoid M]
    (S : Finset α) (sizeS : α → ℕ) (XS : ℕ)
    (hsizeS : ∀ a ∈ S, 1 ≤ sizeS a ∧ sizeS a ≤ XS)
    (T : Finset β) (sizeT : β → ℕ) (XT : ℕ)
    (hsizeT : ∀ b ∈ T, 1 ≤ sizeT b ∧ sizeT b ≤ XT)
    (U : Finset γ) (sizeU : γ → ℕ) (XU : ℕ)
    (hsizeU : ∀ c ∈ U, 1 ≤ sizeU c ∧ sizeU c ≤ XU)
    (f : α → β → γ → M) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, f a b c) =
      ∑ k ∈ Finset.range (Nat.log 2 XS + 1),
        ∑ l ∈ Finset.range (Nat.log 2 XT + 1),
          ∑ r ∈ Finset.range (Nat.log 2 XU + 1),
            ∑ b ∈ T.filter (fun b =>
              (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)),
              ∑ c ∈ U.filter (fun c =>
                (2 ^ r : ℝ) ≤ (sizeU c : ℝ) ∧ (sizeU c : ℝ) < 2 ^ (r + 1)),
                ∑ a ∈ S.filter (fun a =>
                  (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)), f a b c := by
  classical
  calc
    _ = ∑ k ∈ Finset.range (Nat.log 2 XS + 1),
          ∑ l ∈ Finset.range (Nat.log 2 XT + 1),
            ∑ a ∈ S.filter (fun a =>
              (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
              ∑ b ∈ T.filter (fun b =>
                (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)),
                ∑ c ∈ U, f a b c :=
      qs_c3_shell_sum₂ S sizeS XS hsizeS T sizeT XT hsizeT
        (fun a b => ∑ c ∈ U, f a b c)
    _ = ∑ k ∈ Finset.range (Nat.log 2 XS + 1),
          ∑ l ∈ Finset.range (Nat.log 2 XT + 1),
            ∑ a ∈ S.filter (fun a =>
              (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
              ∑ b ∈ T.filter (fun b =>
                (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)),
                ∑ r ∈ Finset.range (Nat.log 2 XU + 1),
                  ∑ c ∈ U.filter (fun c =>
                    (2 ^ r : ℝ) ≤ (sizeU c : ℝ) ∧ (sizeU c : ℝ) < 2 ^ (r + 1)),
                    f a b c := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact qs_c3_shell_sum U sizeU XU hsizeU (fun c => f a b c)
    _ = ∑ k ∈ Finset.range (Nat.log 2 XS + 1),
          ∑ l ∈ Finset.range (Nat.log 2 XT + 1),
            ∑ r ∈ Finset.range (Nat.log 2 XU + 1),
              ∑ b ∈ T.filter (fun b =>
                (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)),
                ∑ c ∈ U.filter (fun c =>
                  (2 ^ r : ℝ) ≤ (sizeU c : ℝ) ∧ (sizeU c : ℝ) < 2 ^ (r + 1)),
                  ∑ a ∈ S.filter (fun a =>
                    (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)), f a b c := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      calc
        _ = ∑ a ∈ S.filter (fun a =>
              (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
                ∑ r ∈ Finset.range (Nat.log 2 XU + 1),
                  ∑ b ∈ T.filter (fun b =>
                    (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)),
                    ∑ c ∈ U.filter (fun c =>
                      (2 ^ r : ℝ) ≤ (sizeU c : ℝ) ∧ (sizeU c : ℝ) < 2 ^ (r + 1)), f a b c := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
        _ = ∑ r ∈ Finset.range (Nat.log 2 XU + 1),
              ∑ a ∈ S.filter (fun a =>
                (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
                ∑ b ∈ T.filter (fun b =>
                  (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)),
                  ∑ c ∈ U.filter (fun c =>
                    (2 ^ r : ℝ) ≤ (sizeU c : ℝ) ∧ (sizeU c : ℝ) < 2 ^ (r + 1)), f a b c :=
            Finset.sum_comm
        _ = ∑ r ∈ Finset.range (Nat.log 2 XU + 1),
              ∑ b ∈ T.filter (fun b =>
                (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)),
                ∑ a ∈ S.filter (fun a =>
                  (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)),
                  ∑ c ∈ U.filter (fun c =>
                    (2 ^ r : ℝ) ≤ (sizeU c : ℝ) ∧ (sizeU c : ℝ) < 2 ^ (r + 1)), f a b c := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.sum_comm]
        _ = ∑ r ∈ Finset.range (Nat.log 2 XU + 1),
              ∑ b ∈ T.filter (fun b =>
                (2 ^ l : ℝ) ≤ (sizeT b : ℝ) ∧ (sizeT b : ℝ) < 2 ^ (l + 1)),
                ∑ c ∈ U.filter (fun c =>
                  (2 ^ r : ℝ) ≤ (sizeU c : ℝ) ∧ (sizeU c : ℝ) < 2 ^ (r + 1)),
                  ∑ a ∈ S.filter (fun a =>
                    (2 ^ k : ℝ) ≤ (sizeS a : ℝ) ∧ (sizeS a : ℝ) < 2 ^ (k + 1)), f a b c := by
            apply Finset.sum_congr rfl
            intro r hr
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.sum_comm]

theorem qs_c3_orig_res_shell_expand {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] {m : ClassFieldTheory.RayClassModulus K}
    {qS : Ideal (𝓞 K)} (F : QSFamily m qS) (W : ℝ → ℝ)
    (M κ Λ n : ℝ) (q c d : Ideal (𝓞 K))
    (hq : Squarefree q) (hc : QSAdm m qS c) (hd : QSAdm m qS d)
    (hqc : IsCoprime c q) (hqd : IsCoprime d q) (hcd : IsCoprime c d)
    (hcn : qsN c ≤ 2 * n) (hdn : qsN d ≤ 2 * n)
    (hΛ : 0 < Λ) (hM : 0 < M) :
    qsOrigKernel (qsInnerRes K) F W M κ Λ q c d =
      qsResidueZero K (fun y => (W (y ^ 2) : ℂ)) *
        ∑ eq ∈ qsDivisors q,
          (qsMu eq : ℂ) *
            ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
              ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  ∑ ec ∈ (qsDivisors c).filter (fun ec =>
                    (2 ^ l : ℝ) ≤ qsN ec ∧ qsN ec < 2 ^ (l + 1)),
                    ∑ ed ∈ (qsDivisors d).filter (fun ed =>
                      (2 ^ r : ℝ) ≤ qsN ed ∧ qsN ed < 2 ^ (r + 1)),
                      ∑ a ∈ (qsSqfUpTo κ q).filter (fun a =>
                        (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1)),
                        (qsPairChar F c d).idealValue a * (qsMu (ec * ed) : ℂ) *
                          (if qsN eq * qsN (ec * ed) ≤
                              Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
  classical
  let ψ := qsPairChar F c d
  let rows := qsSqfUpTo κ q
  have hq0 : q ≠ ⊥ := hq.ne_zero
  have hc0 : c ≠ ⊥ := QSC2.ne_bot_of_QSAdm hc
  have hd0 : d ≠ ⊥ := QSC2.ne_bot_of_QSAdm hd
  have hrowSize : ∀ a ∈ rows,
      1 ≤ Ideal.absNorm a ∧ Ideal.absNorm a ≤ ⌊κ⌋₊ := by
    intro a ha
    change a ∈ qsSqfUpTo κ q at ha
    have hnorm : Ideal.absNorm a ≠ 0 := by
      intro hz
      have ha' := ha
      simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq] at ha'
      rcases ha' with ⟨_, ⟨ha0, _, _, _⟩⟩
      exact ha0 (Ideal.absNorm_eq_zero_iff.mp hz)
    exact ⟨Nat.one_le_iff_ne_zero.mpr hnorm,
      qs_c3_sqfUpTo_norm_le_nat ha⟩
  have hdivC : ∀ e ∈ qsDivisors c,
      1 ≤ Ideal.absNorm e ∧ Ideal.absNorm e ≤ ⌊2 * n⌋₊ := by
    intro e he
    have he0 : e ≠ ⊥ := by
      intro hz
      subst e
      have hdiv := (QSC2.mem_qsDivisors hc0).1 he
      exact hc0 (bot_unique (Ideal.le_of_dvd hdiv))
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        exact he0 (Ideal.absNorm_eq_zero_iff.mp hz))
    · apply Nat.le_floor
      exact (qs_c3_divisor_norm_le_of_col hc he).trans hcn
  have hdivD : ∀ e ∈ qsDivisors d,
      1 ≤ Ideal.absNorm e ∧ Ideal.absNorm e ≤ ⌊2 * n⌋₊ := by
    intro e he
    have he0 : e ≠ ⊥ := by
      intro hz
      subst e
      have hdiv := (QSC2.mem_qsDivisors hd0).1 he
      exact hd0 (bot_unique (Ideal.le_of_dvd hdiv))
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        exact he0 (Ideal.absNorm_eq_zero_iff.mp hz))
    · apply Nat.le_floor
      exact (qs_c3_divisor_norm_le_of_col hd he).trans hdn
  have hexp := qs_c3_orig_res_expand F W M κ Λ q c d hq hc hd hqc hqd hcd hΛ hM
  have hcomm :
      (∑ a ∈ rows, ψ.idealValue a *
        ∑ eq ∈ qsDivisors q, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
          ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
            (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0)) =
      ∑ eq ∈ qsDivisors q, ∑ a ∈ rows, ψ.idealValue a *
        ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
          ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
            (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hfixed (eq : Ideal (𝓞 K)) :
      (∑ a ∈ rows, ψ.idealValue a *
        ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
          ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
            (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0)) =
        (qsMu eq : ℂ) *
          ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
            ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
              ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ ec ∈ (qsDivisors c).filter (fun ec =>
                  (2 ^ l : ℝ) ≤ qsN ec ∧ qsN ec < 2 ^ (l + 1)),
                  ∑ ed ∈ (qsDivisors d).filter (fun ed =>
                    (2 ^ r : ℝ) ≤ qsN ed ∧ qsN ed < 2 ^ (r + 1)),
                    ∑ a ∈ rows.filter (fun a =>
                      (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1)),
                      ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                        (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
    have hbase :
        (∑ a ∈ rows, ψ.idealValue a *
          ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
            ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
              (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0)) =
          (qsMu eq : ℂ) *
            ∑ a ∈ rows, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
              ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
      calc
        _ = ∑ a ∈ rows, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
              ψ.idealValue a *
                ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ) *
                  (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0)) := by
              simp_rw [Finset.mul_sum]
        _ = ∑ a ∈ rows, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
              (qsMu eq : ℂ) *
                (ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                  (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro ec hec
              apply Finset.sum_congr rfl
              intro ed hed
              ring
        _ = ∑ a ∈ rows, ∑ ec ∈ qsDivisors c,
              (qsMu eq : ℂ) *
                ∑ ed ∈ qsDivisors d,
                  ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                    (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro ec hec
              exact (Finset.mul_sum _ _ _).symm
        _ = ∑ a ∈ rows,
              (qsMu eq : ℂ) *
                ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
                  ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                    (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro a ha
              exact (Finset.mul_sum _ _ _).symm
        _ = (qsMu eq : ℂ) *
              ∑ a ∈ rows, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
                ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                  (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) :=
              (Finset.mul_sum _ _ _).symm
    calc
      _ = (qsMu eq : ℂ) *
            ∑ a ∈ rows, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
              ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := hbase
      _ = (qsMu eq : ℂ) *
            ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
              ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  ∑ ec ∈ (qsDivisors c).filter (fun ec =>
                    (2 ^ l : ℝ) ≤ qsN ec ∧ qsN ec < 2 ^ (l + 1)),
                    ∑ ed ∈ (qsDivisors d).filter (fun ed =>
                      (2 ^ r : ℝ) ≤ qsN ed ∧ qsN ed < 2 ^ (r + 1)),
                      ∑ a ∈ rows.filter (fun a =>
                        (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1)),
                        ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                          (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
            congr 1
            simpa [qsN] using qs_c3_shell_sum₃ rows Ideal.absNorm ⌊κ⌋₊ hrowSize
              (qsDivisors c) Ideal.absNorm ⌊2 * n⌋₊ hdivC
              (qsDivisors d) Ideal.absNorm ⌊2 * n⌋₊ hdivD
              (fun a ec ed => ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0))
  rw [hexp]
  congr 1
  calc
    _ = ∑ eq ∈ qsDivisors q, ∑ a ∈ rows, ψ.idealValue a *
          ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
            ((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) *
              (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := hcomm
    _ = ∑ eq ∈ qsDivisors q, (qsMu eq : ℂ) *
          ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
            ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
              ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ ec ∈ (qsDivisors c).filter (fun ec =>
                  (2 ^ l : ℝ) ≤ qsN ec ∧ qsN ec < 2 ^ (l + 1)),
                  ∑ ed ∈ (qsDivisors d).filter (fun ed =>
                    (2 ^ r : ℝ) ≤ qsN ed ∧ qsN ed < 2 ^ (r + 1)),
                    ∑ a ∈ rows.filter (fun a =>
                      (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1)),
                      ψ.idealValue a * (qsMu (ec * ed) : ℂ) *
                        (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro eq heq
      exact hfixed eq

/-- Rewrite the row characters in one original residue dyad into the C2u quadratic form. -/
theorem qs_c3_res_shell_row_rewrite {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (q : Ideal (𝓞 K)) (hqS : qS ≠ ⊥) (hbad : qsBadRad m qS ∣ q)
    (c d eq : Ideal (𝓞 K)) (κ Λ M : ℝ)
    (rows : Finset (Ideal (𝓞 K))) (p₁ p₂ : Ideal (𝓞 K) → Prop)
    [DecidablePred p₁] [DecidablePred p₂]
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hqc : IsCoprime c q) (hqd : IsCoprime d q)
    (hrow : ∀ a ∈ rows, a ∈ qsSqfUpTo κ q) :
    (∑ ec ∈ (qsDivisors c).filter p₁,
      ∑ ed ∈ (qsDivisors d).filter p₂,
        (qsMu (ec * ed) : ℂ) *
          ∑ a ∈ rows, qsC3RowTwist F a * (F.character c).idealValue a *
            (F.character d).idealValue a *
            (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0)) =
    ∑ ec ∈ (qsDivisors c).filter p₁,
      ∑ ed ∈ (qsDivisors d).filter p₂,
        ∑ a ∈ rows,
          (qsPairChar F c d).idealValue a * (qsMu (ec * ed) : ℂ) *
            (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro ec hec
  apply Finset.sum_congr rfl
  intro ed hed
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have haAdm := qs_c3_orig_row_admissible (qS := qS) (q := q)
    hqS hbad κ (hrow a ha)
  rw [← qs_c3_pairValue_row F hrf haAdm.1 hc hd hcd]
  ring

def qsC3ResidueShellPairKernel {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (q eq : Ideal (𝓞 K)) (κ Λ M : ℝ)
    (k l r : ℕ) : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun c d =>
  ∑ ec ∈ (qsDivisors c).filter (fun ec =>
      (2 ^ l : ℝ) ≤ qsN ec ∧ qsN ec < 2 ^ (l + 1)),
    ∑ ed ∈ (qsDivisors d).filter (fun ed =>
      (2 ^ r : ℝ) ≤ qsN ed ∧ qsN ed < 2 ^ (r + 1)),
      (qsMu (ec * ed) : ℂ) *
        ∑ a ∈ (qsSqfUpTo κ q).filter (fun a =>
          (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1)),
          qsC3RowTwist F a * (F.character c).idealValue a *
            (F.character d).idealValue a *
            (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0)

/-- The pair-summed original residue kernel is a finite sum of C2u-compatible dyad kernels. -/
theorem qs_c3_pairSum_sum {K : Type} [Field K] [NumberField K]
    (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
    {ι : Type*} (s : Finset ι) (f : ι → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    qsPairSum cols z (fun c d => ∑ i ∈ s, f i c d) =
      ∑ i ∈ s, qsPairSum cols z (f i) := by
  classical
  simpa using qs_c2b_pairSum_double_sum cols z s (Finset.univ : Finset Unit)
    (fun i (_ : Unit) => f i)

theorem qs_c3_shell_scale_le (x : ℝ) (hx : 1 ≤ x) (k : ℕ)
    (hk : k ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1)) :
    (2 ^ k : ℝ) ≤ x := by
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hklog : k ≤ Nat.log 2 ⌊x⌋₊ := by
    have := Finset.mem_range.mp hk
    omega
  have hpow : 2 ^ k ≤ 2 ^ Nat.log 2 ⌊x⌋₊ :=
    Nat.pow_le_pow_right (by norm_num) hklog
  have hpowX : 2 ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ :=
    Nat.pow_log_le_self 2 (by omega)
  have hnat : 2 ^ k ≤ ⌊x⌋₊ := hpow.trans hpowX
  have hcast : (2 ^ k : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le (le_trans (by norm_num) hx))

theorem qs_c3_shell_count_cube (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      ((Nat.log 2 ⌊x⌋₊ + 1 : ℕ) : ℝ) ^ 3 ≤ C * x ^ δ := by
  classical
  have hσ : 0 < δ / 3 := by positivity
  have hlittle := isLittleO_log_rpow_rpow_atTop (1 : ℝ) hσ
  have hsmall := hlittle.bound (show 0 < (1 : ℝ) by norm_num)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 hsmall
  let Xbar : ℝ := max 2 X₀
  let c₀ : ℝ := 2 / Real.log 2
  let C : ℝ := c₀ ^ 3 + (Xbar + 1) ^ 3 / (2 ^ δ) + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro x hx
    have hxpos : 0 < x := by linarith
    let N : ℕ := ⌊x⌋₊
    have hN1 : 1 ≤ N := by
      dsimp [N]
      exact Nat.le_floor (by exact_mod_cast (show (1 : ℝ) ≤ x by linarith))
    have hN0 : N ≠ 0 := by omega
    have hpowNat := Nat.pow_log_le_self 2 hN0
    have hpowCast : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hpowNat
    have hpow : (2 : ℝ) ^ Nat.log 2 N ≤ x := by
      calc
        _ = ((2 ^ Nat.log 2 N : ℕ) : ℝ) := by norm_cast
        _ ≤ (N : ℝ) := hpowCast
        _ ≤ x := Nat.floor_le (by linarith)
    have hlogpow := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 N) hpow
    have hlogpow' : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log x := by
      simpa [Real.log_pow] using hlogpow
    have hj : (Nat.log 2 N : ℝ) ≤ Real.log x / Real.log 2 := by
      apply (le_div_iff₀ hlog2).2
      nlinarith [hlogpow']
    have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hL : (Nat.log 2 N + 1 : ℝ) ≤ c₀ * Real.log x := by
      dsimp [c₀]
      have hratio : 1 ≤ Real.log x / Real.log 2 :=
        (le_div_iff₀ hlog2).2 (by simpa only [one_mul] using hlog2x)
      calc
        _ ≤ 2 * (Real.log x / Real.log 2) := by nlinarith [hj, hratio]
        _ = 2 / Real.log 2 * Real.log x := by ring
    have hlogx : 0 ≤ Real.log x := le_trans (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hlog2x
    have hLcube : (Nat.log 2 N + 1 : ℝ) ^ 3 ≤ c₀ ^ 3 * (Real.log x) ^ 3 := by
      calc
        _ ≤ (c₀ * Real.log x) ^ 3 := by gcongr
        _ = c₀ ^ 3 * (Real.log x) ^ 3 := by ring
    by_cases hlarge : Xbar ≤ x
    · have hx₀ : X₀ ≤ x := le_trans (le_max_right 2 X₀) hlarge
      have hlittleX := hX₀ x hx₀
      have hlogsmall : Real.log x ≤ x ^ (δ / 3) := by
        have hbound : |Real.log x| ≤ |x ^ (δ / 3)| := by simpa using hlittleX
        simpa [abs_of_nonneg hlogx,
          abs_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hbound
      have hlogCube : (Real.log x) ^ 3 ≤ x ^ δ := by
        have hcube : (Real.log x) ^ 3 ≤ (x ^ (δ / 3)) ^ 3 := by gcongr
        have hpowEq : (x ^ (δ / 3)) ^ 3 = x ^ δ := by
          calc
            (x ^ (δ / 3)) ^ 3 = (x ^ (δ / 3)) ^ (3 : ℝ) := by
              exact (Real.rpow_natCast (x ^ (δ / 3)) 3).symm
            _ = x ^ ((δ / 3) * 3) := (Real.rpow_mul hxpos.le _ _).symm
            _ = x ^ δ := by congr 1 <;> ring
        simpa [hpowEq] using hcube
      have hc₀cube : c₀ ^ 3 ≤ C := by
        dsimp [C]
        have hterm : 0 ≤ (Xbar + 1) ^ 3 / 2 ^ δ := by positivity
        linarith
      calc
        _ = (Nat.log 2 N + 1 : ℝ) ^ 3 := by simp [N]
        _ ≤ c₀ ^ 3 * (Real.log x) ^ 3 := hLcube
        _ ≤ c₀ ^ 3 * x ^ δ := mul_le_mul_of_nonneg_left hlogCube (by positivity)
        _ ≤ C * x ^ δ := mul_le_mul_of_nonneg_right hc₀cube (Real.rpow_nonneg hxpos.le _)
    · have hxbar : x ≤ Xbar := le_of_not_ge hlarge
      have hlogNat : Nat.log 2 N ≤ N := Nat.log_le_self 2 N
      have hLsmall : (Nat.log 2 N + 1 : ℝ) ≤ Xbar + 1 := by
        have hcast : (Nat.log 2 N + 1 : ℝ) ≤ (N : ℝ) + 1 := by
          exact_mod_cast Nat.add_le_add_right hlogNat 1
        have hNle : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
        linarith
      have hden : 0 < (2 : ℝ) ^ δ := by positivity
      have hCsmall : (Xbar + 1) ^ 3 ≤ C * (2 : ℝ) ^ δ := by
        have hquot : (Xbar + 1) ^ 3 / (2 : ℝ) ^ δ ≤ C := by
          dsimp [C]
          have hterm : 0 ≤ c₀ ^ 3 := by positivity
          linarith
        calc
          (Xbar + 1) ^ 3 = ((Xbar + 1) ^ 3 / (2 : ℝ) ^ δ) * (2 : ℝ) ^ δ := by
            field_simp [hden.ne']
          _ ≤ C * (2 : ℝ) ^ δ := mul_le_mul_of_nonneg_right hquot hden.le
      have h2pow : (2 : ℝ) ^ δ ≤ x ^ δ := Real.rpow_le_rpow (by norm_num) hx (by linarith)
      calc
        _ = (Nat.log 2 N + 1 : ℝ) ^ 3 := by simp [N]
        _ ≤ (Xbar + 1) ^ 3 := by gcongr
        _ ≤ C * (2 : ℝ) ^ δ := hCsmall
        _ ≤ C * x ^ δ := mul_le_mul_of_nonneg_left h2pow (by positivity)

theorem qs_c3_norm_sum4_bound {α β γ ι : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (V : Finset ι)
    (f : α → β → γ → ι → ℂ) (A : ℝ)
    (hf : ∀ a ∈ S, ∀ b ∈ T, ∀ c ∈ U, ∀ d ∈ V, ‖f a b c d‖ ≤ A) :
    ‖∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d‖ ≤
      (S.card : ℝ) * (T.card : ℝ) * (U.card : ℝ) * (V.card : ℝ) * A := by
  classical
  have hV : ∀ a ∈ S, ∀ b ∈ T, ∀ c ∈ U,
      ‖∑ d ∈ V, f a b c d‖ ≤ (V.card : ℝ) * A := by
    intro a ha b hb c hc
    calc
      _ ≤ ∑ d ∈ V, ‖f a b c d‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ V, A := Finset.sum_le_sum fun d hd => hf a ha b hb c hc d hd
      _ = (V.card : ℝ) * A := by simp
  have hU : ∀ a ∈ S, ∀ b ∈ T,
      ‖∑ c ∈ U, ∑ d ∈ V, f a b c d‖ ≤
        (U.card : ℝ) * (V.card : ℝ) * A := by
    intro a ha b hb
    calc
      _ ≤ ∑ c ∈ U, ‖∑ d ∈ V, f a b c d‖ := norm_sum_le _ _
      _ ≤ ∑ c ∈ U, (V.card : ℝ) * A :=
        Finset.sum_le_sum fun c hc => hV a ha b hb c hc
      _ = (U.card : ℝ) * (V.card : ℝ) * A := by simp [mul_assoc]
  have hT : ∀ a ∈ S,
      ‖∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d‖ ≤
        (T.card : ℝ) * (U.card : ℝ) * (V.card : ℝ) * A := by
    intro a ha
    calc
      _ ≤ ∑ b ∈ T, ‖∑ c ∈ U, ∑ d ∈ V, f a b c d‖ := norm_sum_le _ _
      _ ≤ ∑ b ∈ T, (U.card : ℝ) * (V.card : ℝ) * A :=
        Finset.sum_le_sum fun b hb => hU a ha b hb
      _ = (T.card : ℝ) * (U.card : ℝ) * (V.card : ℝ) * A := by simp [mul_assoc]
  calc
    _ ≤ ∑ a ∈ S, ‖∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ S, (T.card : ℝ) * (U.card : ℝ) * (V.card : ℝ) * A :=
      Finset.sum_le_sum fun a ha => hT a ha
    _ = (S.card : ℝ) * (T.card : ℝ) * (U.card : ℝ) * (V.card : ℝ) * A := by
      simp [mul_assoc]

/-- Arithmetic bound for one original residue dyad. -/

theorem qs_c3_orig_res_pairShell_expand {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] {m : ClassFieldTheory.RayClassModulus K}
    {qS : Ideal (𝓞 K)} (F : QSFamily m qS) (W : ℝ → ℝ)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (M κ Λ n : ℝ) (q : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) (hblock : QSBlockCols m qS q n cols)
    (hM : 0 < M) (hΛ : 0 < Λ) :
    qsPairSum cols z (qsOrigKernel (qsInnerRes K) F W M κ Λ q) =
      (qsResidueZero K (fun y => (W (y ^ 2) : ℂ))) *
        ∑ eq ∈ qsDivisors q,
          (qsMu eq : ℂ) *
            ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
              ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  qsPairSum cols z (qsC3ResidueShellPairKernel F q eq κ Λ M k l r) := by
  classical
  rcases hblock with ⟨hq, hbad, hcol, hclass⟩
  have hker : ∀ c ∈ cols, ∀ d ∈ cols, IsCoprime c d →
      qsOrigKernel (qsInnerRes K) F W M κ Λ q c d =
        (qsResidueZero K (fun y => (W (y ^ 2) : ℂ))) *
          ∑ eq ∈ qsDivisors q,
            (qsMu eq : ℂ) *
            ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
              ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  qsC3ResidueShellPairKernel F q eq κ Λ M k l r c d := by
    intro c hc d hd hcd
    have hc' := hcol c hc
    have hd' := hcol d hd
    have hExpanded := qs_c3_orig_res_shell_expand F W M κ Λ n q c d hq hc'.1 hd'.1
      hc'.2.1 hd'.2.1 hcd hc'.2.2.2 hd'.2.2.2 hΛ hM
    calc
      _ = (qsResidueZero K (fun y => (W (y ^ 2) : ℂ))) *
            ∑ eq ∈ qsDivisors q,
              (qsMu eq : ℂ) *
              ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
                ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                    ∑ ec ∈ (qsDivisors c).filter (fun ec =>
                        (2 ^ l : ℝ) ≤ qsN ec ∧ qsN ec < 2 ^ (l + 1)),
                        ∑ ed ∈ (qsDivisors d).filter (fun ed =>
                          (2 ^ r : ℝ) ≤ qsN ed ∧ qsN ed < 2 ^ (r + 1)),
                          ∑ a ∈ (qsSqfUpTo κ q).filter (fun a =>
                            (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1)),
                            (qsPairChar F c d).idealValue a * (qsMu (ec * ed) : ℂ) *
                            (if qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) then 1 else 0) :=
        hExpanded
      _ = (qsResidueZero K (fun y => (W (y ^ 2) : ℂ))) *
            ∑ eq ∈ qsDivisors q,
              (qsMu eq : ℂ) *
              ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
                ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                  ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                    qsC3ResidueShellPairKernel F q eq κ Λ M k l r c d := by
        congr 1
        apply Finset.sum_congr rfl
        intro eq heq
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro r hr
        let rowShell := (qsSqfUpTo κ q).filter (fun a =>
          (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1))
        let p₁ : Ideal (𝓞 K) → Prop := fun e =>
          (2 ^ l : ℝ) ≤ qsN e ∧ qsN e < 2 ^ (l + 1)
        let p₂ : Ideal (𝓞 K) → Prop := fun e =>
          (2 ^ r : ℝ) ≤ qsN e ∧ qsN e < 2 ^ (r + 1)
        have hrowShell : ∀ a ∈ rowShell, a ∈ qsSqfUpTo κ q := by
          intro a ha
          exact (Finset.mem_filter.mp ha).1
        have hrowrewrite := qs_c3_res_shell_row_rewrite F hrf q hqS hbad
          c d eq κ Λ M rowShell p₁ p₂ hc'.1 hd'.1 hcd hc'.2.1 hd'.2.1 hrowShell
        simpa [qsC3ResidueShellPairKernel, rowShell, p₁, p₂] using hrowrewrite.symm
  have hPair :
      qsPairSum cols z (qsOrigKernel (qsInnerRes K) F W M κ Λ q) =
        qsPairSum cols z (fun c d =>
          (qsResidueZero K (fun y => (W (y ^ 2) : ℂ))) *
            ∑ eq ∈ qsDivisors q,
              (qsMu eq : ℂ) *
                ∑ k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1),
                  ∑ l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                    ∑ r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1),
                      qsC3ResidueShellPairKernel F q eq κ Λ M k l r c d) := by
    unfold qsPairSum
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hcd : IsCoprime c d
    · simp only [if_pos hcd]
      rw [hker c hc d hd hcd]
    · simp [hcd]
  rw [hPair]
  rw [qs_c2b_pairSum_const_mul cols z (qsResidueZero K (fun y => (W (y ^ 2) : ℂ)))]
  congr 1
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro eq heq
  rw [qs_c2b_pairSum_const_mul cols z (qsMu eq : ℂ)]
  congr 1
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [qs_c3_pairSum_sum]
  apply Finset.sum_congr rfl
  intro l hl
  exact qs_c3_pairSum_sum cols z
    (Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1))
    (fun r => qsC3ResidueShellPairKernel F q eq κ Λ M k l r)

theorem qs_c3_residue_shell_arith (M n κ B D₁ D₂ Λ α : ℝ)
    (hM : 0 < M) (hn : 1 ≤ n) (hB : 1 ≤ B)
    (hBκ : B ≤ κ) (hκM : 2 * κ ≤ M)
    (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hΛ : 1 ≤ Λ)
    (hD : D₁ * D₂ ≤ Λ * Real.sqrt (M / B)) :
    Real.sqrt (D₁ * D₂) *
        (n / Real.sqrt (D₁ * D₂) +
          Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) ≤
      4 * Real.sqrt Λ * (n + B ^ α * Real.sqrt (M / B)) := by
  have hBpos : 0 < B := by linarith
  have hD₁pos : 0 < D₁ := by linarith
  have hD₂pos : 0 < D₂ := by linarith
  have hDpos : 0 < D₁ * D₂ := mul_pos hD₁pos hD₂pos
  have hDroot : 0 < Real.sqrt (D₁ * D₂) := Real.sqrt_pos.2 hDpos
  have hD₁root : 0 < Real.sqrt D₁ := Real.sqrt_pos.2 hD₁pos
  have hD₂root : 0 < Real.sqrt D₂ := Real.sqrt_pos.2 hD₂pos
  have h2B : 2 * B ≤ M := by
    exact (mul_le_mul_of_nonneg_left hBκ (by norm_num)).trans hκM
  have hMB : 1 ≤ M / B := (one_le_div₀ hBpos).2 (by nlinarith)
  have hrootMB : 1 ≤ Real.sqrt (M / B) := (Real.one_le_sqrt).2 hMB
  have hrootMul : Real.sqrt (D₁ * D₂) = Real.sqrt D₁ * Real.sqrt D₂ :=
    Real.sqrt_mul hD₁pos.le D₂
  have hD₁factor : Real.sqrt (D₁ * D₂) / Real.sqrt D₁ = Real.sqrt D₂ := by
    rw [hrootMul]
    field_simp [hD₁root.ne']
  have hD₂factor : Real.sqrt (D₁ * D₂) / Real.sqrt D₂ = Real.sqrt D₁ := by
    rw [hrootMul]
    field_simp [hD₂root.ne']
  let H : ℝ := B ^ α * Real.sqrt (M / B)
  let T₁ : ℝ := Real.sqrt n * B ^ (α / 2) * Real.sqrt D₂
  let T₂ : ℝ := Real.sqrt n * B ^ (α / 2) * Real.sqrt D₁
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hT₁ : 0 ≤ T₁ := by dsimp [T₁]; positivity
  have hT₂ : 0 ≤ T₂ := by dsimp [T₂]; positivity
  have hBpow : (B ^ (α / 2)) ^ 2 = B ^ α := by
    calc
      (B ^ (α / 2)) ^ 2 = (B ^ (α / 2)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (B ^ (α / 2)) 2).symm
      _ = B ^ ((α / 2) * 2) := (Real.rpow_mul hBpos.le (α / 2) 2).symm
      _ = B ^ α := by congr 1 <;> ring
  have hT₁sq : T₁ ^ 2 = n * B ^ α * D₂ := by
    dsimp [T₁]
    calc
      _ = (Real.sqrt n) ^ 2 * (B ^ (α / 2)) ^ 2 * (Real.sqrt D₂) ^ 2 := by ring
      _ = n * B ^ α * D₂ := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ n), hBpow,
          Real.sq_sqrt hD₂pos.le]
  have hT₂sq : T₂ ^ 2 = n * B ^ α * D₁ := by
    dsimp [T₂]
    calc
      _ = (Real.sqrt n) ^ 2 * (B ^ (α / 2)) ^ 2 * (Real.sqrt D₁) ^ 2 := by ring
      _ = n * B ^ α * D₁ := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ n), hBpow,
          Real.sq_sqrt hD₁pos.le]
  have hD₁le : D₁ ≤ D₁ * D₂ := by
    have := mul_le_mul_of_nonneg_left hD₂ (le_of_lt hD₁pos)
    nlinarith
  have hD₂le : D₂ ≤ D₁ * D₂ := by
    have := mul_le_mul_of_nonneg_right hD₁ (le_of_lt hD₂pos)
    nlinarith
  have hD₁upper : D₁ ≤ Λ * Real.sqrt (M / B) := hD₁le.trans hD
  have hD₂upper : D₂ ≤ Λ * Real.sqrt (M / B) := hD₂le.trans hD
  have hT₁boundSq : T₁ ^ 2 ≤ (Real.sqrt Λ * (n + H)) ^ 2 := by
    have hcross : T₁ ^ 2 ≤ Λ * (n * H) := by
      dsimp [H] at hD₂upper ⊢
      calc
        T₁ ^ 2 = n * B ^ α * D₂ := hT₁sq
        _ ≤ n * B ^ α * (Λ * Real.sqrt (M / B)) :=
          mul_le_mul_of_nonneg_left hD₂upper (by positivity)
        _ = Λ * (n * H) := by ring
    have hYoung : n * H ≤ (n + H) ^ 2 := by nlinarith [sq_nonneg (n - H)]
    calc
      T₁ ^ 2 ≤ Λ * (n * H) := hcross
      _ ≤ Λ * (n + H) ^ 2 := mul_le_mul_of_nonneg_left hYoung (by linarith)
      _ = (Real.sqrt Λ * (n + H)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ Λ)]
  have hT₂boundSq : T₂ ^ 2 ≤ (Real.sqrt Λ * (n + H)) ^ 2 := by
    have hcross : T₂ ^ 2 ≤ Λ * (n * H) := by
      dsimp [H] at hD₁upper ⊢
      calc
        T₂ ^ 2 = n * B ^ α * D₁ := hT₂sq
        _ ≤ n * B ^ α * (Λ * Real.sqrt (M / B)) :=
          mul_le_mul_of_nonneg_left hD₁upper (by positivity)
        _ = Λ * (n * H) := by ring
    have hYoung : n * H ≤ (n + H) ^ 2 := by nlinarith [sq_nonneg (n - H)]
    calc
      T₂ ^ 2 ≤ Λ * (n * H) := hcross
      _ ≤ Λ * (n + H) ^ 2 := mul_le_mul_of_nonneg_left hYoung (by linarith)
      _ = (Real.sqrt Λ * (n + H)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ Λ)]
  have hA : 0 ≤ Real.sqrt Λ * (n + H) := by positivity
  have hT₁bound : T₁ ≤ Real.sqrt Λ * (n + H) :=
    (sq_le_sq₀ hT₁ hA).mp hT₁boundSq
  have hT₂bound : T₂ ≤ Real.sqrt Λ * (n + H) :=
    (sq_le_sq₀ hT₂ hA).mp hT₂boundSq
  have hLastSq : (B ^ α * Real.sqrt (D₁ * D₂)) ^ 2 ≤
      (Real.sqrt Λ * H) ^ 2 := by
    have hsqrtMB : Real.sqrt (M / B) ≤ M / B :=
      (Real.sqrt_le_self_iff).2 (Or.inr hMB)
    have hDupper' : D₁ * D₂ ≤ Λ * (M / B) := by
      exact hD.trans (mul_le_mul_of_nonneg_left hsqrtMB (by linarith))
    have hHsq : H ^ 2 = (B ^ α) ^ 2 * (M / B) := by
      dsimp [H]
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ M / B)]
    calc
      (B ^ α * Real.sqrt (D₁ * D₂)) ^ 2 = (B ^ α) ^ 2 * (D₁ * D₂) := by
        rw [mul_pow, Real.sq_sqrt hDpos.le]
      _ ≤ (B ^ α) ^ 2 * (Λ * (M / B)) :=
        mul_le_mul_of_nonneg_left hDupper' (sq_nonneg _)
      _ = (Real.sqrt Λ * H) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ Λ), hHsq]
        ring
  have hLast : B ^ α * Real.sqrt (D₁ * D₂) ≤ Real.sqrt Λ * H :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hLastSq
  have hfirst : Real.sqrt (D₁ * D₂) * (n / Real.sqrt (D₁ * D₂)) = n := by
    field_simp [hDroot.ne']
  have hcrossTerms :
      Real.sqrt (D₁ * D₂) *
          (Real.sqrt n * B ^ (α / 2) *
            (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂)) = T₁ + T₂ := by
    let X₀ : ℝ := Real.sqrt n * B ^ (α / 2)
    have hterm₁ : Real.sqrt (D₁ * D₂) * (X₀ / Real.sqrt D₁) = T₁ := by
      dsimp [X₀, T₁]
      calc
        _ = Real.sqrt n * B ^ (α / 2) *
              (Real.sqrt (D₁ * D₂) / Real.sqrt D₁) := by ring
        _ = _ := by rw [hD₁factor]
    have hterm₂ : Real.sqrt (D₁ * D₂) * (X₀ / Real.sqrt D₂) = T₂ := by
      dsimp [X₀, T₂]
      calc
        _ = Real.sqrt n * B ^ (α / 2) *
              (Real.sqrt (D₁ * D₂) / Real.sqrt D₂) := by ring
        _ = _ := by rw [hD₂factor]
    calc
      _ = Real.sqrt (D₁ * D₂) *
            (X₀ / Real.sqrt D₁ + X₀ / Real.sqrt D₂) := by
              dsimp [X₀]
              congr 1 <;> ring
      _ = Real.sqrt (D₁ * D₂) * (X₀ / Real.sqrt D₁) +
            Real.sqrt (D₁ * D₂) * (X₀ / Real.sqrt D₂) := by rw [mul_add]
      _ = T₁ + T₂ := by rw [hterm₁, hterm₂]
  have hmain :
      Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) =
        n + T₁ + T₂ + B ^ α * Real.sqrt (D₁ * D₂) := by
    calc
      _ = Real.sqrt (D₁ * D₂) * (n / Real.sqrt (D₁ * D₂)) +
            Real.sqrt (D₁ * D₂) *
              (Real.sqrt n * B ^ (α / 2) *
                (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂)) +
            Real.sqrt (D₁ * D₂) * B ^ α := by ring
      _ = n + T₁ + T₂ + B ^ α * Real.sqrt (D₁ * D₂) := by
        rw [hfirst, hcrossTerms]
        ring
  have hYoungB : 1 ≤ Real.sqrt Λ := (Real.one_le_sqrt).2 hΛ
  have hTotal : n + T₁ + T₂ + B ^ α * Real.sqrt (D₁ * D₂) ≤
      4 * Real.sqrt Λ * (n + H) := by
    have h₁ := hT₁bound
    have h₂ := hT₂bound
    have h₃ := hLast
    have hN : n ≤ Real.sqrt Λ * (n + H) := by nlinarith [hA, hYoungB]
    nlinarith
  calc
    _ = n + T₁ + T₂ + B ^ α * Real.sqrt (D₁ * D₂) := hmain
    _ ≤ 4 * Real.sqrt Λ * (n + H) := hTotal

theorem qs_c3_residue_scale_mono (M B κ α : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hBκ : B ≤ κ) (hα : 1 < α) :
    B ^ α * Real.sqrt (M / B) ≤ Real.sqrt M * κ ^ (α - 1 / 2) := by
  have hpow : 0 < α - 1 / 2 := by linarith
  have hκpos : 0 < κ := lt_of_lt_of_le hB hBκ
  have hsqrtM : Real.sqrt (M / B) = Real.sqrt M / Real.sqrt B :=
    Real.sqrt_div hM.le B
  have hsqrtB : Real.sqrt B = B ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow B
  have hscale : B ^ α * Real.sqrt (M / B) = Real.sqrt M * B ^ (α - 1 / 2) := by
    rw [hsqrtM, hsqrtB]
    calc
      B ^ α * (Real.sqrt M / B ^ (1 / 2 : ℝ)) =
          Real.sqrt M * (B ^ α / B ^ (1 / 2 : ℝ)) := by ring
      _ = Real.sqrt M * B ^ (α - 1 / 2) := by
          rw [← Real.rpow_sub hB α (1 / 2)]
  rw [hscale]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hB.le hBκ hpow.le) (Real.sqrt_nonneg M)


theorem qs_c3_sum3_comm {α β γ M : Type*} [AddCommMonoid M]
    (S : Finset α) (T : Finset β) (U : Finset γ)
    (f : α → β → γ → M) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, f a b c) =
      ∑ b ∈ T, ∑ c ∈ U, ∑ a ∈ S, f a b c := by
  classical
  calc
    _ = ∑ b ∈ T, ∑ a ∈ S, ∑ c ∈ U, f a b c := Finset.sum_comm
    _ = ∑ b ∈ T, ∑ c ∈ U, ∑ a ∈ S, f a b c := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm


/-- The exponent hypothesis bounds every C2u matrix norm by the dyadic length envelope. -/
theorem qs_c3_norm_exp_envelope {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε : ℝ) (hε : 0 < ε) (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B n D : ℝ), 1 ≤ B → 1 ≤ n → 1 ≤ D → D ≤ 2 * n →
        qsNorm F (2 * B) (2 * n / D) ≤
          C * (n * B) ^ ε * (n / D + B ^ α) := by
  obtain ⟨C₀, hC₀, hbound⟩ := hexp ε hε
  let C : ℝ := C₀ * 4 ^ ε * (2 + 2 ^ α)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro B n D hB hn hD hD₂n
  have hDpos : 0 < D := by linarith
  have hnD : 1 ≤ 2 * n / D := (one_le_div₀ hDpos).2 hD₂n
  have htwoB : 1 ≤ 2 * B := by linarith
  have hscale : (2 * n / D) * (2 * B) ≤ 4 * (n * B) := by
    have hDmul : 4 * (n * B) ≤ 4 * (n * B) * D := by
      have := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 4 * (n * B))
      nlinarith
    have hdiv := (div_le_iff₀ hDpos).2 hDmul
    calc
      (2 * n / D) * (2 * B) = (4 * (n * B)) / D := by field_simp; ring
      _ ≤ 4 * (n * B) := hdiv
  have hscalePow : ((2 * n / D) * (2 * B)) ^ ε ≤ 4 ^ ε * (n * B) ^ ε := by
    calc
      ((2 * n / D) * (2 * B)) ^ ε ≤ (4 * (n * B)) ^ ε :=
        Real.rpow_le_rpow (by positivity) hscale hε.le
      _ = 4 ^ ε * (n * B) ^ ε := by
        rw [show 4 * (n * B) = 4 * (n * B) by rfl, Real.mul_rpow (by norm_num) (by positivity)]
  have hsum : (2 * n / D) + (2 * B) ^ α ≤ (2 + 2 ^ α) * (n / D + B ^ α) := by
    have hpow : (2 * B) ^ α = 2 ^ α * B ^ α :=
      Real.mul_rpow (by norm_num) (by positivity)
    have hdiv0 : 0 ≤ n / D := div_nonneg (by positivity) (by positivity)
    have hBpow0 : 0 ≤ B ^ α := Real.rpow_nonneg (by linarith) α
    have htwoPow0 : 0 ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
    rw [hpow, show 2 * n / D = 2 * (n / D) by ring]
    nlinarith
  rw [qs_norm_symm_M0 F hrf (2 * B) (2 * n / D)]
  calc
    qsNorm F (2 * n / D) (2 * B) ≤
        C₀ * ((2 * n / D) * (2 * B)) ^ ε *
          ((2 * n / D) + (2 * B) ^ α) :=
      hbound (2 * n / D) (2 * B) hnD htwoB
    _ ≤ C₀ * (4 ^ ε * (n * B) ^ ε) *
          ((2 + 2 ^ α) * (n / D + B ^ α)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hscalePow hC₀.le) hsum
        (by positivity) (by positivity)
    _ = C * (n * B) ^ ε * (n / D + B ^ α) := by
      dsimp [C]
      ring

/-- The product of two C2u matrix norms expands into the three standard dyadic terms. -/
theorem qs_c3_sqrt_norm_product_envelope {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε : ℝ) (hε : 0 < ε) (_hα : 1 < α)
    (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B n D₁ D₂ : ℝ), 1 ≤ B → 1 ≤ n → 1 ≤ D₁ → 1 ≤ D₂ →
        D₁ ≤ 2 * n → D₂ ≤ 2 * n →
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) ≤
            C * (n * B) ^ ε *
              (n / Real.sqrt (D₁ * D₂) +
                Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) := by
  obtain ⟨C, hC, hEnv⟩ := qs_c3_norm_exp_envelope F hrf α ε hε hexp
  refine ⟨C, hC, ?_⟩
  intro B n D₁ D₂ hB hn hD₁ hD₂ hD₁n hD₂n
  have hEnv₁ := hEnv B n D₁ hB hn hD₁ hD₁n
  have hEnv₂ := hEnv B n D₂ hB hn hD₂ hD₂n
  let X : ℝ := n / D₁
  let Y : ℝ := n / D₂
  let A : ℝ := B ^ α
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hN₁ : 0 ≤ qsNorm F (2 * B) (2 * n / D₁) := sq_nonneg _
  have hN₂ : 0 ≤ qsNorm F (2 * B) (2 * n / D₂) := sq_nonneg _
  have hN₁' : qsNorm F (2 * B) (2 * n / D₁) ≤ C * (n * B) ^ ε * (X + A) := by
    dsimp [X, A]
    exact hEnv₁
  have hN₂' : qsNorm F (2 * B) (2 * n / D₂) ≤ C * (n * B) ^ ε * (Y + A) := by
    dsimp [Y, A]
    exact hEnv₂
  have hprod :
      qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂) ≤
        (C * (n * B) ^ ε) ^ 2 * ((X + A) * (Y + A)) := by
    have hcoeff : 0 ≤ C * (n * B) ^ ε := by positivity
    calc
      _ ≤ (C * (n * B) ^ ε * (X + A)) * (C * (n * B) ^ ε * (Y + A)) :=
        mul_le_mul hN₁' hN₂' hN₂ (by positivity)
      _ = _ := by ring
  have hcross :
      Real.sqrt ((X + A) * (Y + A)) ≤
        Real.sqrt (X * Y) + Real.sqrt (X * A) + Real.sqrt (A * Y) + A := by
    have hXsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX
    have hYsq : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY
    have hAsq : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA
    have hxy : Real.sqrt (X * Y) = Real.sqrt X * Real.sqrt Y :=
      Real.sqrt_mul hX Y
    have hxa : Real.sqrt (X * A) = Real.sqrt X * Real.sqrt A :=
      Real.sqrt_mul hX A
    have hay : Real.sqrt (A * Y) = Real.sqrt A * Real.sqrt Y :=
      Real.sqrt_mul hA Y
    have hRnonneg : 0 ≤ Real.sqrt (X * Y) + Real.sqrt (X * A) +
        Real.sqrt (A * Y) + A := by positivity
    have hcompX : X + A ≤ (Real.sqrt X + Real.sqrt A) ^ 2 := by
      have hXsq' : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX
      have hAsq' : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
      rw [add_sq]
      nlinarith [mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg A), hXsq', hAsq']
    have hcompY : Y + A ≤ (Real.sqrt Y + Real.sqrt A) ^ 2 := by
      have hYsq' : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hY
      have hAsq' : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
      rw [add_sq]
      nlinarith [mul_nonneg (Real.sqrt_nonneg Y) (Real.sqrt_nonneg A), hYsq', hAsq']
    have hcomp : (X + A) * (Y + A) ≤
        (Real.sqrt X + Real.sqrt A) ^ 2 * (Real.sqrt Y + Real.sqrt A) ^ 2 :=
      mul_le_mul hcompX hcompY (by positivity) (by positivity)
    have hsumLinear :
        Real.sqrt (X * Y) + Real.sqrt (X * A) + Real.sqrt (A * Y) + A =
          (Real.sqrt X + Real.sqrt A) * (Real.sqrt Y + Real.sqrt A) := by
      rw [hxy, hxa, hay]
      nlinarith [hAsq]
    have hsum : (X + A) * (Y + A) ≤
        (Real.sqrt (X * Y) + Real.sqrt (X * A) + Real.sqrt (A * Y) + A) ^ 2 := by
      calc
        _ ≤ (Real.sqrt X + Real.sqrt A) ^ 2 * (Real.sqrt Y + Real.sqrt A) ^ 2 := hcomp
        _ = ((Real.sqrt X + Real.sqrt A) * (Real.sqrt Y + Real.sqrt A)) ^ 2 := by ring
        _ = (Real.sqrt (X * Y) + Real.sqrt (X * A) + Real.sqrt (A * Y) + A) ^ 2 :=
          congrArg (fun t : ℝ => t ^ 2) hsumLinear.symm
    exact Real.sqrt_le_iff.mpr ⟨hRnonneg, hsum⟩
  have hfirst : Real.sqrt (X * Y) = n / Real.sqrt (D₁ * D₂) := by
    dsimp [X, Y]
    have hn0 : 0 ≤ n := by positivity
    have hD₁0 : 0 ≤ D₁ := by linarith
    have hD₂0 : 0 ≤ D₂ := by linarith
    have hD₁pos : 0 < D₁ := by linarith
    have hD₂pos : 0 < D₂ := by linarith
    rw [Real.sqrt_mul (div_nonneg hn0 hD₁0) (n / D₂),
      Real.sqrt_div hn0 D₁, Real.sqrt_div hn0 D₂,
      Real.sqrt_mul hD₁0 D₂]
    have hsqrtN : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
    have hsqrtD₁ : Real.sqrt D₁ ≠ 0 := (Real.sqrt_pos.2 hD₁pos).ne'
    have hsqrtD₂ : Real.sqrt D₂ ≠ 0 := (Real.sqrt_pos.2 hD₂pos).ne'
    field_simp [hsqrtD₁, hsqrtD₂]
    rw [sq, hsqrtN]
  have hBpow : Real.sqrt (B ^ α) = B ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ B) α (1 / 2)]
    congr 1 <;> ring
  have hcross₁ : Real.sqrt (X * A) =
      Real.sqrt n * B ^ (α / 2) / Real.sqrt D₁ := by
    dsimp [X, A]
    have hn0 : 0 ≤ n := by positivity
    calc
      Real.sqrt (n / D₁ * B ^ α) = Real.sqrt (n / D₁) * Real.sqrt (B ^ α) :=
        Real.sqrt_mul (div_nonneg hn0 (by positivity)) (B ^ α)
      _ = (Real.sqrt n / Real.sqrt D₁) * B ^ (α / 2) := by
        rw [Real.sqrt_div hn0 D₁, hBpow]
      _ = Real.sqrt n * B ^ (α / 2) / Real.sqrt D₁ := by ring
  have hcross₂ : Real.sqrt (A * Y) =
      Real.sqrt n * B ^ (α / 2) / Real.sqrt D₂ := by
    dsimp [Y, A]
    have hn0 : 0 ≤ n := by positivity
    calc
      Real.sqrt (B ^ α * (n / D₂)) = Real.sqrt (B ^ α) * Real.sqrt (n / D₂) :=
        Real.sqrt_mul (Real.rpow_nonneg (by positivity : 0 ≤ B) α) (n / D₂)
      _ = B ^ (α / 2) * (Real.sqrt n / Real.sqrt D₂) := by
        rw [hBpow, Real.sqrt_div hn0 D₂]
      _ = Real.sqrt n * B ^ (α / 2) / Real.sqrt D₂ := by ring
  have hmain :
      Real.sqrt (X + A) * Real.sqrt (Y + A) ≤
        Real.sqrt (X * Y) + Real.sqrt (X * A) + Real.sqrt (A * Y) + A := by
    calc
      _ = Real.sqrt ((X + A) * (Y + A)) :=
        (Real.sqrt_mul (add_nonneg hX hA) (Y + A)).symm
      _ ≤ _ := hcross
  calc
    _ ≤ Real.sqrt ((C * (n * B) ^ ε) ^ 2 * ((X + A) * (Y + A))) :=
      Real.sqrt_le_sqrt hprod
    _ = C * (n * B) ^ ε * Real.sqrt ((X + A) * (Y + A)) := by
      rw [Real.sqrt_mul (sq_nonneg (C * (n * B) ^ ε)) ((X + A) * (Y + A)),
        Real.sqrt_sq (by positivity)]
    _ ≤ C * (n * B) ^ ε *
        (Real.sqrt (X * Y) + Real.sqrt (X * A) + Real.sqrt (A * Y) + A) :=
      mul_le_mul_of_nonneg_left hcross (by positivity)
    _ = C * (n * B) ^ ε *
        (n / Real.sqrt (D₁ * D₂) +
          Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) := by
      rw [hfirst, hcross₁, hcross₂]
      dsimp [A]
      ring

/-- Combine C2u and the exponent hypothesis on one row/divisor dyad. -/
theorem qs_c3_shell_pair_bound {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε : ℝ) (hε : 0 < ε) (hα : 1 < α) (hexp : QSHasExponent F α)
    (n B D₁ D₂ : ℝ) (p₁ p₂ : Ideal (𝓞 K) → Prop)
    [DecidablePred p₁] [DecidablePred p₂]
    (cols rows : Finset (Ideal (𝓞 K))) (z ρ : Ideal (𝓞 K) → ℂ)
    (w : ℝ → ℝ → ℂ) (R : ℝ)
    (hn : 1 ≤ n) (hB : 1 ≤ B) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hD₁n : D₁ ≤ 2 * n) (hD₂n : D₂ ≤ 2 * n)
    (hp₁ : ∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁)
    (hp₂ : ∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂)
    (hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n)
    (hrows : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B)
    (hρ : ∀ a, ‖ρ a‖ ≤ 1) (hR : 0 ≤ R)
    (hw : ∀ y u, ‖w y u‖ ≤ R) :
    ∃ C : ℝ, 0 < C ∧
      ‖qsPairSum cols z (fun c d =>
        ∑ e₁ ∈ (qsDivisors c).filter p₁,
          ∑ e₂ ∈ (qsDivisors d).filter p₂,
            (qsMu (e₁ * e₂) : ℂ) *
              ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                (F.character d).idealValue a * w (qsN a) (qsN (e₁ * e₂)))‖ ≤
        C * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  obtain ⟨C₂, hC₂, hC₂bound⟩ :=
    qs_c3_pair_bound_C2u F hrf ε hε n B D₁ D₂ p₁ p₂ cols rows z ρ w R
      hn hB hD₁ hD₂ hp₁ hp₂ hcols hrows hρ hR hw
  obtain ⟨C₁, hC₁, hNormFor⟩ :=
    qs_c3_sqrt_norm_product_envelope F hrf α ε hε hα hexp
  have hNorm := hNormFor B n D₁ D₂ hB hn hD₁ hD₂ hD₁n hD₂n
  let C : ℝ := C₂ * C₁
  refine ⟨C, mul_pos hC₂ hC₁, ?_⟩
  have henergy : 0 ≤ ∑ c ∈ cols, ‖z c‖ ^ 2 := by positivity
  have hDroot : 0 ≤ Real.sqrt (D₁ * D₂) := Real.sqrt_nonneg _
  calc
    _ ≤ C₂ * (n * B) ^ ε * R * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := hC₂bound
    _ ≤ C₂ * (n * B) ^ ε * R * Real.sqrt (D₁ * D₂) *
          (C₁ * (n * B) ^ ε *
            (n / Real.sqrt (D₁ * D₂) +
              Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α)) *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
        gcongr
    _ = C * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
        calc
          _ = C₂ * C₁ * ((n * B) ^ ε * (n * B) ^ ε) * R * Real.sqrt (D₁ * D₂) *
                (n / Real.sqrt (D₁ * D₂) +
                  Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
                  ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
          _ = C * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
                (n / Real.sqrt (D₁ * D₂) +
                  Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
                  ∑ c ∈ cols, ‖z c‖ ^ 2 := by
                rw [← Real.rpow_add (by positivity : 0 < n * B)]
                dsimp [C]
                ring

theorem qs_c3_shell_pair_bound_uniform {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (α ε : ℝ) (hε : 0 < ε) (hα : 1 < α) (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n B D₁ D₂ : ℝ) (p₁ p₂ : Ideal (𝓞 K) → Prop)
        [DecidablePred p₁] [DecidablePred p₂]
        (cols rows : Finset (Ideal (𝓞 K))) (z ρ : Ideal (𝓞 K) → ℂ)
        (w : ℝ → ℝ → ℂ) (R : ℝ),
        1 ≤ n → 1 ≤ B → 1 ≤ D₁ → 1 ≤ D₂ →
        D₁ ≤ 2 * n → D₂ ≤ 2 * n →
        (∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁) →
        (∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂) →
        (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n) →
        (∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B) →
        (∀ a, ‖ρ a‖ ≤ 1) → 0 ≤ R → (∀ y u, ‖w y u‖ ≤ R) →
        ‖qsPairSum cols z (fun c d =>
          ∑ e₁ ∈ (qsDivisors c).filter p₁,
            ∑ e₂ ∈ (qsDivisors d).filter p₂,
              (qsMu (e₁ * e₂) : ℂ) *
                ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                  (F.character d).idealValue a * w (qsN a) (qsN (e₁ * e₂)))‖ ≤
          C * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
            (n / Real.sqrt (D₁ * D₂) +
              Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  obtain ⟨C₂, hC₂, hC₂bound⟩ := qs_divisor_pair_cauchy_C2u F hrf ε hε
  obtain ⟨C₁, hC₁, hNormFor⟩ :=
    qs_c3_sqrt_norm_product_envelope F hrf α ε hε hα hexp
  let C : ℝ := C₂ * C₁
  refine ⟨C, mul_pos hC₂ hC₁, ?_⟩
  intro n B D₁ D₂ p₁ p₂ _ _ cols rows z ρ w R hn hB hD₁ hD₂ hD₁n hD₂n
    hp₁ hp₂ hcols hrows hρ hR hw
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.Measure.dirac (0 : ℝ)
  let φ : ℝ → ℝ → ℝ → ℂ := fun y u _ => w y u
  let Φ : ℝ → ℝ → ℝ → ℂ := fun y u _ => w y u
  let gmaj : ℝ → ℝ := fun _ => R
  letI : MeasureTheory.IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hΦ : ∀ y u x : ℝ,
      Φ y u x = ∫ t, ((x : ℂ) ^ ((t : ℂ) * Complex.I)) * φ y u t ∂μ := by
    intro y u x
    simp [Φ, φ, μ]
  have hgm : MeasureTheory.Integrable gmaj μ := by simp [gmaj, μ]
  have hφ : ∀ y u t, ‖φ y u t‖ ≤ gmaj t := by
    intro y u t
    exact hw y u
  have hmass : ∫ t, gmaj t ∂μ ≤ R := by simp [gmaj, μ]
  have hpair := hC₂bound n B D₁ D₂ R p₁ p₂ cols rows z ρ μ φ Φ gmaj
    hn hB hD₁ hD₂ hp₁ hp₂ hcols hrows hρ hΦ hgm hφ hmass
  have hNorm := hNormFor B n D₁ D₂ hB hn hD₁ hD₂ hD₁n hD₂n
  have henergy : 0 ≤ ∑ c ∈ cols, ‖z c‖ ^ 2 := by positivity
  calc
    _ ≤ C₂ * (n * B) ^ ε * R * Real.sqrt (D₁ * D₂) *
          Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := hpair
    _ ≤ C₂ * (n * B) ^ ε * R * Real.sqrt (D₁ * D₂) *
          (C₁ * (n * B) ^ ε *
            (n / Real.sqrt (D₁ * D₂) +
              Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α)) *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by gcongr
    _ = C * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
        calc
          _ = C₂ * C₁ * ((n * B) ^ ε * (n * B) ^ ε) * R * Real.sqrt (D₁ * D₂) *
                (n / Real.sqrt (D₁ * D₂) +
                  Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
                  ∑ c ∈ cols, ‖z c‖ ^ 2 := by ring
          _ = C * (n * B) ^ (2 * ε) * R * Real.sqrt (D₁ * D₂) *
                (n / Real.sqrt (D₁ * D₂) +
                  Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
                  ∑ c ∈ cols, ‖z c‖ ^ 2 := by
                rw [← Real.rpow_add (by positivity : 0 < n * B)]
                dsimp [C]
                ring

theorem qs_c3_residue_shell_bound {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (hqS : qS ≠ ⊥) (α ε : ℝ) (hε : 0 < ε) (hα : 1 < α)
    (hexp : QSHasExponent F α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ Λ : ℝ), 0 < M → 1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → 1 ≤ Λ →
        ∀ (q : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
          (z : Ideal (𝓞 K) → ℂ), QSBlockCols m qS q n cols →
          ∀ (eq : Ideal (𝓞 K)) (heq : eq ∈ qsDivisors q) (k l r : ℕ),
            k ∈ Finset.range (Nat.log 2 ⌊κ⌋₊ + 1) →
            l ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1) →
            r ∈ Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1) →
            ‖qsPairSum cols z
              (qsC3ResidueShellPairKernel F q eq κ Λ M k l r)‖ ≤
              C * (n * (2 ^ k : ℝ)) ^ (2 * ε) * 4 * Real.sqrt Λ *
                (n + (2 ^ k : ℝ) ^ α * Real.sqrt (M / (2 ^ k : ℝ))) *
                ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  obtain ⟨C₂, hC₂, hC₂bound⟩ :=
    qs_c3_shell_pair_bound_uniform F hrf α ε hε hα hexp
  refine ⟨C₂, hC₂, ?_⟩
  intro M n κ Λ hM hn hκ hκM hΛ q cols z hblock eq heq k l r hk hl hr
  rcases hblock with ⟨hq, hbad, hcol, hclass⟩
  let B : ℝ := 2 ^ k
  let D₁ : ℝ := 2 ^ l
  let D₂ : ℝ := 2 ^ r
  let rows : Finset (Ideal (𝓞 K)) :=
    (qsSqfUpTo κ q).filter (fun a =>
      (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1))
  let p₁ : Ideal (𝓞 K) → Prop := fun e =>
    (2 ^ l : ℝ) ≤ qsN e ∧ qsN e < 2 ^ (l + 1)
  let p₂ : Ideal (𝓞 K) → Prop := fun e =>
    (2 ^ r : ℝ) ≤ qsN e ∧ qsN e < 2 ^ (r + 1)
  let ρ : Ideal (𝓞 K) → ℂ := qsC3RowTwist F
  let w : ℝ → ℝ → ℂ := fun y u =>
    if qsN eq * u ≤ Λ * Real.sqrt (M / y) then 1 else 0
  have hB : 1 ≤ B := by dsimp [B]; exact one_le_pow₀ (by norm_num)
  have hD₁ : 1 ≤ D₁ := by dsimp [D₁]; exact one_le_pow₀ (by norm_num)
  have hD₂ : 1 ≤ D₂ := by dsimp [D₂]; exact one_le_pow₀ (by norm_num)
  have hBκ : B ≤ κ := by
    dsimp [B]
    exact qs_c3_shell_scale_le κ hκ k hk
  have hD₁n : D₁ ≤ 2 * n := by
    dsimp [D₁]
    exact qs_c3_shell_scale_le (2 * n) (by nlinarith) l hl
  have hD₂n : D₂ ≤ 2 * n := by
    dsimp [D₂]
    exact qs_c3_shell_scale_le (2 * n) (by nlinarith) r hr
  have hp₁ : ∀ e, p₁ e → D₁ ≤ qsN e ∧ qsN e ≤ 2 * D₁ := by
    intro e he
    dsimp [p₁, D₁] at he ⊢
    refine ⟨he.1, ?_⟩
    calc
      qsN e ≤ (2 ^ (l + 1) : ℝ) := le_of_lt he.2
      _ = 2 * (2 ^ l : ℝ) := by rw [pow_succ]; ring
  have hp₂ : ∀ e, p₂ e → D₂ ≤ qsN e ∧ qsN e ≤ 2 * D₂ := by
    intro e he
    dsimp [p₂, D₂] at he ⊢
    refine ⟨he.1, ?_⟩
    calc
      qsN e ≤ (2 ^ (r + 1) : ℝ) := le_of_lt he.2
      _ = 2 * (2 ^ r : ℝ) := by rw [pow_succ]; ring
  have hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n := by
    intro c hc
    exact ⟨(hcol c hc).1, (hcol c hc).2.2.2⟩
  have hrows : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have haAdm := qs_c3_orig_row_admissible hqS hbad κ ha'.1
    refine ⟨haAdm.1, ?_⟩
    dsimp [B]
    exact le_of_lt (calc
      qsN a < (2 ^ (k + 1) : ℝ) := ha'.2.2
      _ = 2 * (2 ^ k : ℝ) := by rw [pow_succ]; ring)
  have hρ : ∀ a, ‖ρ a‖ ≤ 1 := by
    intro a
    exact qs_c3_rowTwist_norm_le F a
  have hw : ∀ y u, ‖w y u‖ ≤ 1 := by
    intro y u
    dsimp [w]
    split_ifs <;> norm_num
  have hpairzero_of_hnot : ¬ D₁ * D₂ ≤ Λ * Real.sqrt (M / B) →
      qsPairSum cols z (qsC3ResidueShellPairKernel F q eq κ Λ M k l r) = 0 := by
    intro hnot'
    have hq0 : q ≠ ⊥ := hq.ne_zero
    have heq0 : eq ≠ ⊥ := by
      intro heqbot
      subst eq
      have heqdiv := (QSC2.mem_qsDivisors hq0).1 heq
      exact hq0 (bot_unique (Ideal.le_of_dvd heqdiv))
    have hEqNat : 1 ≤ Ideal.absNorm eq := Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      exact heq0 (Ideal.absNorm_eq_zero_iff.mp hzero))
    have hEq : 1 ≤ qsN eq := by exact_mod_cast hEqNat
    have hcut_implies : ∀ ec ed a, p₁ ec → p₂ ed → a ∈ rows →
        qsN eq * qsN (ec * ed) ≤ Λ * Real.sqrt (M / qsN a) →
        D₁ * D₂ ≤ Λ * Real.sqrt (M / B) := by
      intro ec ed a hec hed ha hcut
      have hp₁' := hec
      have hp₂' := hed
      have ha' := Finset.mem_filter.mp ha
      have hmulLower : D₁ * D₂ ≤ qsN ec * qsN ed := by
        exact mul_le_mul hp₁'.1 hp₂'.1 (by positivity) (by positivity)
      have hmulEq : qsN ec * qsN ed ≤ qsN eq * (qsN ec * qsN ed) := by
        calc
          qsN ec * qsN ed = 1 * (qsN ec * qsN ed) := by ring
          _ ≤ qsN eq * (qsN ec * qsN ed) :=
            mul_le_mul_of_nonneg_right hEq (by positivity)
      have hcut' : qsN eq * (qsN ec * qsN ed) ≤ Λ * Real.sqrt (M / qsN a) := by
        simpa only [QSC2.qsN_mul] using hcut
      have hNa : 0 < qsN a := by
        have haAdm := qs_c3_orig_row_admissible hqS hbad κ ha'.1
        have ha0 := QSC2.ne_bot_of_QSAdm haAdm.1
        have hNaNat : 0 < Ideal.absNorm a := Nat.pos_iff_ne_zero.mpr (by
          intro hzero
          exact ha0 (Ideal.absNorm_eq_zero_iff.mp hzero))
        exact_mod_cast hNaNat
      have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
      have hBNa : B ≤ qsN a := ha'.2.1
      have hdiv : M / qsN a ≤ M / B := by
        rw [div_le_div_iff₀ hNa hBpos]
        nlinarith [mul_le_mul_of_nonneg_left hBNa hM.le]
      have hroot := Real.sqrt_le_sqrt hdiv
      have hpre : D₁ * D₂ ≤ Λ * Real.sqrt (M / qsN a) :=
        (hmulLower.trans hmulEq).trans hcut'
      exact hpre.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
    have hkernel_zero : ∀ c d, qsC3ResidueShellPairKernel F q eq κ Λ M k l r c d = 0 := by
      intro c d
      simp only [qsC3ResidueShellPairKernel]
      apply Finset.sum_eq_zero
      intro ec hec
      apply Finset.sum_eq_zero
      intro ed hed
      have hrowsum : ∑ a ∈ (qsSqfUpTo κ q).filter (fun a =>
          (2 ^ k : ℝ) ≤ qsN a ∧ qsN a < 2 ^ (k + 1)),
          (if qsN eq * qsN (ec * ed) ≤ Λ *
              (Real.sqrt M / Real.sqrt (qsN a)) then
            qsC3RowTwist F a * (F.character c).idealValue a *
              (F.character d).idealValue a
          else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have hcutfalse : ¬ qsN eq * qsN (ec * ed) ≤
            Λ * (Real.sqrt M / Real.sqrt (qsN a)) := by
          intro hcut
          have hcut' : qsN eq * qsN (ec * ed) ≤
              Λ * Real.sqrt (M / qsN a) := by
            simpa only [Real.sqrt_div hM.le (qsN a)] using hcut
          exact hnot' (hcut_implies ec ed a (Finset.mem_filter.mp hec).2
            (Finset.mem_filter.mp hed).2 (by simpa [rows] using ha) hcut')
        simp [hcutfalse]
      simp [hrowsum]
    have hpairzero : qsPairSum cols z
        (qsC3ResidueShellPairKernel F q eq κ Λ M k l r) = 0 := by
      unfold qsPairSum
      apply Finset.sum_eq_zero
      intro c hc
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hcd : IsCoprime c d
      · simp only [if_pos hcd]
        rw [hkernel_zero c d]
        simp
      · simp [hcd]
    exact hpairzero
  have hbase := hC₂bound n B D₁ D₂ p₁ p₂ cols rows z ρ w 1
    hn hB hD₁ hD₂ hD₁n hD₂n hp₁ hp₂ hcols hrows hρ (by norm_num) hw
  have hsqrt_div (a : Ideal (𝓞 K)) :
      Real.sqrt (M / qsN a) = Real.sqrt M / Real.sqrt (qsN a) :=
    Real.sqrt_div hM.le (qsN a)
  have hFun : (fun c d =>
      ∑ ec ∈ (qsDivisors c).filter p₁,
        ∑ ed ∈ (qsDivisors d).filter p₂,
          (qsMu (ec * ed) : ℂ) *
            ∑ a ∈ rows,
              (if qsN eq * qsN (ec * ed) ≤
                  Λ * (Real.sqrt M / Real.sqrt (qsN a)) then
                ρ a * (F.character c).idealValue a * (F.character d).idealValue a
              else 0)) = qsC3ResidueShellPairKernel F q eq κ Λ M k l r := by
    funext c d
    simp [qsC3ResidueShellPairKernel, rows, p₁, p₂, ρ, w, hsqrt_div]
  have hbase' :
      ‖qsPairSum cols z (qsC3ResidueShellPairKernel F q eq κ Λ M k l r)‖ ≤
      C₂ * (n * B) ^ (2 * ε) * 1 * Real.sqrt (D₁ * D₂) *
          (n / Real.sqrt (D₁ * D₂) +
            Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    rw [← hFun]
    simpa [w, hsqrt_div] using hbase
  by_cases hDcut : D₁ * D₂ ≤ Λ * Real.sqrt (M / B)
  · have hArith := qs_c3_residue_shell_arith M n κ B D₁ D₂ Λ α hM hn hB hBκ hκM
      hD₁ hD₂ hΛ hDcut
    have hEnergy : 0 ≤ ∑ c ∈ cols, ‖z c‖ ^ 2 := by positivity
    have hcoef : 0 ≤ C₂ * (n * B) ^ (2 * ε) := by positivity
    have hArith' := mul_le_mul_of_nonneg_left hArith hcoef
    calc
      _ ≤ C₂ * (n * B) ^ (2 * ε) * 1 * Real.sqrt (D₁ * D₂) *
            (n / Real.sqrt (D₁ * D₂) +
              Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := hbase'
      _ = (C₂ * (n * B) ^ (2 * ε) *
            (Real.sqrt (D₁ * D₂) *
              (n / Real.sqrt (D₁ * D₂) +
                Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α))) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
          simp only [mul_one]
          ac_rfl
      _ ≤ (C₂ * (n * B) ^ (2 * ε) *
            (4 * Real.sqrt Λ * (n + B ^ α * Real.sqrt (M / B)))) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hArith' hEnergy
      _ = C₂ * (n * B) ^ (2 * ε) * 4 * Real.sqrt Λ *
            (n + B ^ α * Real.sqrt (M / B)) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by ac_rfl
      _ = C₂ * (n * (2 ^ k : ℝ)) ^ (2 * ε) * 4 * Real.sqrt Λ *
            (n + (2 ^ k : ℝ) ^ α * Real.sqrt (M / (2 ^ k : ℝ))) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by simp [B]
  · have hzero := hpairzero_of_hnot hDcut
    have hRhs : 0 ≤ C₂ * (n * (2 ^ k : ℝ)) ^ (2 * ε) * 4 * Real.sqrt Λ *
        (n + (2 ^ k : ℝ) ^ α * Real.sqrt (M / (2 ^ k : ℝ))) *
        ∑ c ∈ cols, ‖z c‖ ^ 2 := by positivity
    simpa [hzero] using hRhs

theorem qs_c3_orig_residue_shell_aggregate {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] {m : ClassFieldTheory.RayClassModulus K}
    {qS : Ideal (𝓞 K)} (F : QSFamily m qS) (W : ℝ → ℝ)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (α ε : ℝ) (hε : 0 < ε) (hα : 1 < α) (hexp : QSHasExponent F α)
    :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ Λ : ℝ), 0 < M → 1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → 1 ≤ Λ →
        ∀ (q : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
          (z : Ideal (𝓞 K) → ℂ), QSBlockCols m qS q n cols →
          ‖qsPairSum cols z (qsOrigKernel (qsInnerRes K) F W M κ Λ q)‖ ≤
            ‖qsResidueZero K (fun y => (W (y ^ 2) : ℂ))‖ *
              (qsDivisors q).card *
              (Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card *
              (Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card ^ 2 *
              C * (M * n) ^ (2 * ε) * 4 * Real.sqrt Λ *
                (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
                ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  obtain ⟨C₂, hC₂, hShell⟩ :=
    qs_c3_residue_shell_bound F hrf hqS α ε hε hα hexp
  refine ⟨C₂, hC₂, ?_⟩
  intro M n κ Λ hM hn hκ hκM hΛ q cols z hblock
  let S₀ := qsDivisors q
  let S₁ := Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)
  let S₂ := Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)
  let S₃ := Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)
  let X : ℝ := M * n
  let E : ℝ := ∑ c ∈ cols, ‖z c‖ ^ 2
  let A : ℝ := C₂ * X ^ (2 * ε) * 4 * Real.sqrt Λ *
    (n + Real.sqrt M * κ ^ (α - 1 / 2)) * E
  have hX1 : 1 ≤ X := by dsimp [X]; nlinarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hκM' : κ ≤ M := by linarith
  have hterm : ∀ eq ∈ S₀, ∀ k ∈ S₁, ∀ l ∈ S₂, ∀ r ∈ S₃,
      ‖(qsMu eq : ℂ) * qsPairSum cols z
          (qsC3ResidueShellPairKernel F q eq κ Λ M k l r)‖ ≤ A := by
    intro eq heq k hk l hl r hr
    have hmu : ‖(qsMu eq : ℂ)‖ ≤ 1 := QSC2.norm_qsMu_le eq
    have hBnd := hShell M n κ Λ hM hn hκ hκM hΛ q cols z hblock eq heq k l r hk hl hr
    let B : ℝ := 2 ^ k
    have hB1 : 1 ≤ B := by dsimp [B]; exact one_le_pow₀ (by norm_num)
    have hBκ : B ≤ κ := by dsimp [B]; exact qs_c3_shell_scale_le κ hκ k hk
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
    have hBn : n * B ≤ X := by
      dsimp [X]
      calc
        n * B ≤ n * κ := mul_le_mul_of_nonneg_left hBκ (by linarith)
        _ ≤ M * n := by nlinarith
    have hpow : (n * B) ^ (2 * ε) ≤ X ^ (2 * ε) :=
      Real.rpow_le_rpow (by positivity) hBn (by positivity)
    have hscale := qs_c3_residue_scale_mono M B κ α hM hBpos hBκ hα
    have hshape : n + B ^ α * Real.sqrt (M / B) ≤
        n + Real.sqrt M * κ ^ (α - 1 / 2) := by linarith
    have hEnergy : ∑ c ∈ cols, ‖z c‖ ^ 2 = E := rfl
    calc
      _ ≤ ‖(qsMu eq : ℂ)‖ *
          ‖qsPairSum cols z (qsC3ResidueShellPairKernel F q eq κ Λ M k l r)‖ := norm_mul_le _ _
      _ ≤ 1 * (C₂ * (n * B) ^ (2 * ε) * 4 * Real.sqrt Λ *
          (n + B ^ α * Real.sqrt (M / B)) * E) := by gcongr
      _ ≤ A := by
        dsimp [A, X]
        have hprod : (n * B) ^ (2 * ε) *
            (n + B ^ α * Real.sqrt (M / B)) ≤
            (M * n) ^ (2 * ε) * (n + Real.sqrt M * κ ^ (α - 1 / 2)) :=
          mul_le_mul hpow hshape (by positivity) (by positivity)
        have hcoef : 0 ≤ C₂ * 4 * Real.sqrt Λ * E := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hprod hcoef]
  have hsum := qs_c3_norm_sum4_bound S₀ S₁ S₂ S₃
    (fun eq k l r => (qsMu eq : ℂ) * qsPairSum cols z
      (qsC3ResidueShellPairKernel F q eq κ Λ M k l r)) A hterm
  have hExpand := qs_c3_orig_res_pairShell_expand F W hrf hqS M κ Λ n q cols z
    hblock hM (by linarith)
  have hdist :
      (∑ eq ∈ S₀, (qsMu eq : ℂ) *
        ∑ k ∈ S₁, ∑ l ∈ S₂, ∑ r ∈ S₃,
          qsPairSum cols z (qsC3ResidueShellPairKernel F q eq κ Λ M k l r)) =
      ∑ eq ∈ S₀, ∑ k ∈ S₁, ∑ l ∈ S₂, ∑ r ∈ S₃,
        (qsMu eq : ℂ) * qsPairSum cols z
          (qsC3ResidueShellPairKernel F q eq κ Λ M k l r) := by
    apply Finset.sum_congr rfl
    intro eq heq
    simp_rw [Finset.mul_sum]
  have hnorm :
      ‖∑ eq ∈ S₀, (qsMu eq : ℂ) *
        ∑ k ∈ S₁, ∑ l ∈ S₂, ∑ r ∈ S₃,
          qsPairSum cols z (qsC3ResidueShellPairKernel F q eq κ Λ M k l r)‖ ≤
      (S₀.card : ℝ) * (S₁.card : ℝ) * (S₂.card : ℝ) * (S₃.card : ℝ) * A := by
    rw [hdist]
    exact hsum
  rw [hExpand]
  calc
    _ = ‖qsResidueZero K (fun y => (W (y ^ 2) : ℂ))‖ *
          ‖∑ eq ∈ S₀, (qsMu eq : ℂ) *
            ∑ k ∈ S₁, ∑ l ∈ S₂, ∑ r ∈ S₃,
              qsPairSum cols z (qsC3ResidueShellPairKernel F q eq κ Λ M k l r)‖ := by
        rw [norm_mul]
    _ ≤ ‖qsResidueZero K (fun y => (W (y ^ 2) : ℂ))‖ *
          ((S₀.card : ℝ) * (S₁.card : ℝ) * (S₂.card : ℝ) * (S₃.card : ℝ) * A) :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := by dsimp [A, E, S₀, S₁, S₂, S₃, X]; ring

theorem qs_c3_orig_residue_C3a_bound {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] {m : ClassFieldTheory.RayClassModulus K}
    {qS : Ideal (𝓞 K)} (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (M n κ : ℝ) (q : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
          (z : Ideal (𝓞 K) → ℂ),
          1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS q n cols →
          ‖qsPairSum cols z (qsOrigKernel (qsInnerRes K) F W M κ ((M * n) ^ η) q)‖ ≤
            C * qsN q ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let ε : ℝ := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Cshell, hCshell, hAggregate⟩ :=
    qs_c3_orig_residue_shell_aggregate F W hrf hqS α ε hε hα1 hexp
  obtain ⟨Cdiv, hCdiv, hDiv⟩ := qs_divisor_bound_M1 (K := K) (1 : ℝ) (by norm_num)
  obtain ⟨Ccount, hCcount, hCount⟩ := qs_c3_shell_count_cube (δ / 2) (by positivity)
  refine ⟨δ / 4, by positivity, ?_⟩
  intro η hη hη₀
  let R₀ : ℂ := qsResidueZero K (fun y => (W (y ^ 2) : ℂ))
  let C : ℝ := 1 + ‖R₀‖ * Cdiv * Ccount * Cshell * 4
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M n κ q cols z hn hκ hκM hblock
  rcases hblock with ⟨hq, hbad, hcol, hclass⟩
  have hq0 : q ≠ ⊥ := hq.ne_zero
  have hqN : 1 ≤ qsN q := by
    dsimp [qsN]
    have hnat : 1 ≤ Ideal.absNorm q := Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      exact hq0 (Ideal.absNorm_eq_zero_iff.mp hzero))
    exact_mod_cast hnat
  have hM : 0 < M := by linarith
  let X : ℝ := M * n
  have hX2 : 2 ≤ X := by dsimp [X]; nlinarith
  have hXpos : 0 < X := by linarith
  have hX1 : 1 ≤ X := le_trans (by norm_num) hX2
  let Λ : ℝ := X ^ η
  have hΛ : 1 ≤ Λ := by dsimp [Λ]; exact Real.one_le_rpow hX1 hη.le
  have hκX : κ ≤ X := by
    have hκM' : κ ≤ M := by linarith
    dsimp [X]
    nlinarith
  have h2nX : 2 * n ≤ X := by
    have hM2 : 2 ≤ M := by nlinarith
    dsimp [X]
    nlinarith
  have hfloorκ : ⌊κ⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hκX
  have hfloor2n : ⌊2 * n⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono h2nX
  have hlogκ : Nat.log 2 ⌊κ⌋₊ ≤ Nat.log 2 ⌊X⌋₊ := Nat.log_mono_right hfloorκ
  have hlog2n : Nat.log 2 ⌊2 * n⌋₊ ≤ Nat.log 2 ⌊X⌋₊ := Nat.log_mono_right hfloor2n
  have hcardκ :
      ((Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card : ℝ) ≤
        (Nat.log 2 ⌊X⌋₊ + 1 : ℝ) := by
    have hnat : (Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card ≤ Nat.log 2 ⌊X⌋₊ + 1 := by
      simp only [Finset.card_range]
      omega
    exact_mod_cast hnat
  have hcard2n :
      ((Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card : ℝ) ≤
        (Nat.log 2 ⌊X⌋₊ + 1 : ℝ) := by
    have hnat : (Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card ≤ Nat.log 2 ⌊X⌋₊ + 1 := by
      simp only [Finset.card_range]
      omega
    exact_mod_cast hnat
  have hcardShells :
      ((Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card : ℝ) *
        ((Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card : ℝ) ^ 2 ≤
        Ccount * X ^ (δ / 2) := by
    have hprod :
        ((Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card : ℝ) *
          ((Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card : ℝ) ^ 2 ≤
          (Nat.log 2 ⌊X⌋₊ + 1 : ℝ) ^ 3 := by
      calc
        _ ≤ (Nat.log 2 ⌊X⌋₊ + 1 : ℝ) *
              (Nat.log 2 ⌊X⌋₊ + 1 : ℝ) ^ 2 := by gcongr
        _ = (Nat.log 2 ⌊X⌋₊ + 1 : ℝ) ^ 3 := by ring
    have hcount : (Nat.log 2 ⌊X⌋₊ + 1 : ℝ) ^ 3 ≤ Ccount * X ^ (δ / 2) := by
      have htmp := hCount X hX2
      norm_num at htmp
      exact htmp
    exact hprod.trans hcount
  have hqdiv : ((qsDivisors q).card : ℝ) ≤ Cdiv * qsN q := by
    have h := hDiv q hq0
    simpa [qsN, Real.rpow_one] using h
  have hqpow : qsN q ≤ qsN q ^ 8 := by
    calc
      qsN q = qsN q * 1 := by ring
      _ ≤ qsN q * qsN q ^ 7 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hqN) (by positivity)
      _ = qsN q ^ (7 + 1) := by
        calc
          qsN q * qsN q ^ 7 = qsN q ^ 7 * qsN q := by ring
          _ = qsN q ^ (7 + 1) := (pow_succ (qsN q) 7).symm
      _ = qsN q ^ 8 := by norm_num
  have hrootEq : Real.sqrt Λ = X ^ (η / 2) := by
    dsimp [Λ]
    rw [Real.sqrt_eq_rpow]
    calc
      (X ^ η) ^ (1 / 2 : ℝ) = X ^ (η * (1 / 2 : ℝ)) :=
        (Real.rpow_mul hXpos.le η (1 / 2 : ℝ)).symm
      _ = X ^ (η / 2) := by congr 1 <;> ring
  have hroot : Real.sqrt Λ ≤ X ^ (δ / 8) := by
    rw [hrootEq]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    linarith
  have hpowEq : X ^ (δ / 4) * X ^ (δ / 2) * X ^ (δ / 8) = X ^ (7 * δ / 8) := by
    rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
    congr 1 <;> ring
  have hpowLe : X ^ (7 * δ / 8) ≤ X ^ δ := by
    apply Real.rpow_le_rpow_of_exponent_le hX1
    linarith
  have hshape : n + Real.sqrt M * κ ^ (α - 1 / 2) ≤ qsBlockShape M n κ α := by
    dsimp [qsBlockShape]
    have hMnonneg : 0 ≤ M := hM.le
    have hκnonneg : 0 ≤ κ := by linarith
    have hterm : 0 ≤ n * Real.sqrt (M / κ) := by positivity
    linarith
  have hεpow : 2 * ε = δ / 4 := by dsimp [ε]; ring
  have hεpow' : ε * 2 = δ / 4 := by
    calc
      ε * 2 = 2 * ε := by ring
      _ = δ / 4 := hεpow
  have hAggregateRaw := hAggregate M n κ Λ hM hn hκ hκM hΛ q cols z
    ⟨hq, hbad, hcol, hclass⟩
  have hAggregate :
      ‖qsPairSum cols z (qsOrigKernel (qsInnerRes K) F W M κ Λ q)‖ ≤
        ‖R₀‖ * (qsDivisors q).card *
          (Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card *
          (Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card ^ 2 *
          Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ *
          (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    simpa [hεpow, hεpow', R₀, X] using hAggregateRaw
  have hCmain : ‖R₀‖ * Cdiv * Ccount * Cshell * 4 ≤ C := by
    dsimp [C]
    have hnonneg : 0 ≤ ‖R₀‖ * Cdiv * Ccount * Cshell * 4 := by positivity
    linarith
  have hcards : ((qsDivisors q).card : ℝ) *
        ((Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card : ℝ) *
        ((Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card : ℝ) ^ 2 ≤
      (Cdiv * qsN q) * (Ccount * X ^ (δ / 2)) := by
    calc
      _ ≤ (Cdiv * qsN q) *
            ((Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card : ℝ) *
            ((Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card : ℝ) ^ 2 := by
          gcongr
      _ = (Cdiv * qsN q) *
            (((Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card : ℝ) *
              ((Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card : ℝ) ^ 2) := by ac_rfl
      _ ≤ (Cdiv * qsN q) * (Ccount * X ^ (δ / 2)) := by
          have hfac : 0 ≤ Cdiv * qsN q := by positivity
          exact mul_le_mul_of_nonneg_left hcardShells hfac
  have hrest : 0 ≤ Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ *
      (n + Real.sqrt M * κ ^ (α - 1 / 2)) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by positivity
  let C₀ : ℝ := ‖R₀‖ * Cdiv * Ccount * Cshell * 4
  have hRegroup :
      ‖R₀‖ * (Cdiv * qsN q) * (Ccount * X ^ (δ / 2)) *
        Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ =
      C₀ * qsN q * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ) := by
    dsimp [C₀]
    ring
  have hCmain : C₀ ≤ C := by
    dsimp [C₀, C]
    linarith
  have hReduce :
      ‖qsPairSum cols z (qsOrigKernel (qsInnerRes K) F W M κ Λ q)‖ ≤
        C₀ * qsN q * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ) *
          (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ ≤ ‖R₀‖ * (qsDivisors q).card *
            (Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card *
            (Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card ^ 2 *
            Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ *
            (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := hAggregate
      _ ≤ ‖R₀‖ * (Cdiv * qsN q) *
            (Ccount * X ^ (δ / 2)) * Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ *
            (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
        calc
          _ = ‖R₀‖ * (((qsDivisors q).card : ℝ) *
                ((Finset.range (Nat.log 2 ⌊κ⌋₊ + 1)).card : ℝ) *
                ((Finset.range (Nat.log 2 ⌊2 * n⌋₊ + 1)).card : ℝ) ^ 2) *
                (Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ *
                  (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
                  ∑ c ∈ cols, ‖z c‖ ^ 2) := by ac_rfl
          _ ≤ ‖R₀‖ * ((Cdiv * qsN q) * (Ccount * X ^ (δ / 2))) *
                (Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ *
                  (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
                  ∑ c ∈ cols, ‖z c‖ ^ 2) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcards (norm_nonneg _)) hrest
          _ = ‖R₀‖ * (Cdiv * qsN q) * (Ccount * X ^ (δ / 2)) *
                Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ *
                (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
                ∑ c ∈ cols, ‖z c‖ ^ 2 := by ac_rfl
      _ = (‖R₀‖ * (Cdiv * qsN q) * (Ccount * X ^ (δ / 2)) *
            Cshell * X ^ (δ / 4) * 4 * Real.sqrt Λ) *
            ((n + Real.sqrt M * κ ^ (α - 1 / 2)) *
              ∑ c ∈ cols, ‖z c‖ ^ 2) := by ac_rfl
      _ = (C₀ * qsN q * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ)) *
            ((n + Real.sqrt M * κ ^ (α - 1 / 2)) *
              ∑ c ∈ cols, ‖z c‖ ^ 2) := by rw [hRegroup]
      _ = C₀ * qsN q * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ) *
            (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by ac_rfl
  have hpower : X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ ≤ X ^ δ := by
    calc
      _ ≤ X ^ (δ / 4) * X ^ (δ / 2) * X ^ (δ / 8) := by gcongr
      _ = X ^ (7 * δ / 8) := by rw [hpowEq]
      _ ≤ X ^ δ := hpowLe
  have hP : 0 ≤ X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ := by positivity
  have hmix : C₀ * qsN q * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ) ≤
      C * qsN q ^ 8 * X ^ δ := by
    calc
      _ = C₀ * (qsN q * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ)) := by ac_rfl
      _ ≤ C₀ * (qsN q ^ 8 * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hqpow hP) (by positivity)
      _ ≤ C * (qsN q ^ 8 * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ)) :=
        mul_le_mul_of_nonneg_right hCmain (by positivity)
      _ ≤ C * (qsN q ^ 8 * X ^ δ) := by
        have hqpower : qsN q ^ 8 *
            (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ) ≤ qsN q ^ 8 * X ^ δ :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        exact mul_le_mul_of_nonneg_left hqpower (by positivity)
      _ = C * qsN q ^ 8 * X ^ δ := by ring
  have henergy : 0 ≤ ∑ c ∈ cols, ‖z c‖ ^ 2 := by positivity
  calc
    _ ≤ C₀ * qsN q * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ) *
          (n + Real.sqrt M * κ ^ (α - 1 / 2)) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := hReduce
    _ = (C₀ * qsN q * (X ^ (δ / 4) * X ^ (δ / 2) * Real.sqrt Λ)) *
          ((n + Real.sqrt M * κ ^ (α - 1 / 2)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2) := by ac_rfl
    _ ≤ (C * qsN q ^ 8 * X ^ δ) *
          ((n + Real.sqrt M * κ ^ (α - 1 / 2)) *
            ∑ c ∈ cols, ‖z c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hmix (by positivity)
    _ ≤ (C * qsN q ^ 8 * X ^ δ) *
          (qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hshape henergy) (by positivity)
    _ = C * qsN q ^ 8 * X ^ δ * qsBlockShape M n κ α *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by ac_rfl

private theorem qs_c3_transform_pointwise_bound {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdecay : ∀ x : ℝ, 0 < x →
      (x ≤ 1 → ‖iteratedDeriv 0 (qsTransform K h) x‖ ≤ C₀ * x ^ (-1 : ℝ)) ∧
      (1 ≤ x → ‖iteratedDeriv 0 (qsTransform K h) x‖ ≤ C₀ * x ^ (-4 : ℝ)))
    (Λ X : ℝ) (hΛ : 1 ≤ Λ) (hX : 1 / Λ ≤ X) :
    ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥},
      ‖qsTransform K h (X * qsN b.1)‖ ≤
        C₀ * Λ ^ 4 * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1 := by
  have hΛpos : 0 < Λ := by linarith
  have hXpos : 0 < X := lt_of_lt_of_le (one_div_pos.mpr hΛpos) hX
  intro b
  let N : ℝ := qsN b.1
  have hNpos : 0 < N := by
    dsimp [N, qsN]
    have hnat : 0 < Ideal.absNorm b.1 := Nat.pos_iff_ne_zero.mpr (by
      intro hz
      exact b.2 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact_mod_cast hnat
  have hN1 : 1 ≤ N := by
    dsimp [N, qsN]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro hz
      exact b.2 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hxpos : 0 < X * N := mul_pos hXpos hNpos
  have hlow : N / Λ ≤ X * N := by
    have hh := mul_le_mul_of_nonneg_right hX (le_of_lt hNpos)
    simpa [div_eq_mul_inv, mul_comm] using hh
  have hsmall (hx : X * N ≤ 1) :
      ‖qsTransform K h (X * N)‖ ≤ C₀ * (X * N) ^ (-1 : ℝ) := by
    have hb := (hdecay (X * N) hxpos).1 hx
    simpa [iteratedDeriv_zero] using hb
  have hlarge (hx : 1 ≤ X * N) :
      ‖qsTransform K h (X * N)‖ ≤ C₀ * (X * N) ^ (-4 : ℝ) := by
    have hb := (hdecay (X * N) hxpos).2 hx
    simpa [iteratedDeriv_zero] using hb
  have htermEq : ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1 = N ^ (-2 : ℝ) := by
    simp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm, N, qsN,
      Ideal.absNorm_eq_zero_iff, b.2]
  by_cases hx : X * N ≤ 1
  · have hNΛ : N ≤ Λ := by
      have htmp : N / Λ ≤ 1 := le_trans hlow hx
      simpa using (div_le_iff₀ hΛpos).mp htmp
    have hinv : (X * N) ^ (-1 : ℝ) ≤ Λ / N := by
      have hmono := Real.rpow_le_rpow_of_nonpos (div_pos hNpos hΛpos) hlow
        (by norm_num : (-1 : ℝ) ≤ 0)
      have hEq : (N / Λ) ^ (-1 : ℝ) = Λ / N := by
        rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
        field_simp
      exact hmono.trans_eq hEq
    have hlargePow : Λ / N ≤ Λ ^ 4 * N ^ (-2 : ℝ) := by
      have hNpow : N ^ (-2 : ℝ) = 1 / N ^ 2 := by
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hNpos.le]
        simp [one_div]
      rw [hNpow]
      have hΛ3 : Λ ≤ Λ ^ 3 := by
        calc
          Λ = Λ * 1 := by ring
          _ ≤ Λ * Λ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hΛ]) hΛpos.le
          _ = Λ ^ 3 := by ring
      have hNΛ3 : N ≤ Λ ^ 3 := hNΛ.trans hΛ3
      have hcross : Λ * N ^ 2 ≤ Λ ^ 4 * N := by
        have hmul := mul_le_mul_of_nonneg_right hNΛ3
          (mul_nonneg hΛpos.le hNpos.le)
        nlinarith [hmul]
      have hfrac : Λ / N ≤ Λ ^ 4 / N ^ 2 :=
        (div_le_div_iff₀ hNpos (by positivity : 0 < N ^ 2)).2 hcross
      simpa [div_eq_mul_inv] using hfrac
    have hpoint : ‖qsTransform K h (X * N)‖ ≤ C₀ * (Λ / N) :=
      (hsmall hx).trans (mul_le_mul_of_nonneg_left hinv hC₀.le)
    calc
      _ ≤ C₀ * (Λ / N) := hpoint
      _ ≤ C₀ * (Λ ^ 4 * N ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlargePow hC₀.le
      _ = C₀ * Λ ^ 4 * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1 := by
        rw [← htermEq]
        ring
  · have hx' : 1 ≤ X * N := le_of_not_ge hx
    have hlowInv : (X * N) ^ (-4 : ℝ) ≤ (N / Λ) ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hNpos hΛpos) hlow
        (by norm_num : (-4 : ℝ) ≤ 0)
    have hscale : (N / Λ) ^ (-4 : ℝ) = Λ ^ 4 * N ^ (-4 : ℝ) := by
      rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num,
        Real.div_rpow hNpos.le hΛpos.le, Real.rpow_neg hNpos.le,
        Real.rpow_neg hΛpos.le]
      field_simp [hNpos.ne', hΛpos.ne']
      exact Real.rpow_natCast Λ 4
    have hNpow : N ^ (-4 : ℝ) ≤ N ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have hpoint : ‖qsTransform K h (X * N)‖ ≤ C₀ * (Λ ^ 4 * N ^ (-4 : ℝ)) := by
      calc
        _ ≤ C₀ * (X * N) ^ (-4 : ℝ) := hlarge hx'
        _ ≤ C₀ * (N / Λ) ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_left hlowInv hC₀.le
        _ = C₀ * (Λ ^ 4 * N ^ (-4 : ℝ)) := by rw [hscale]
    calc
      _ ≤ C₀ * (Λ ^ 4 * N ^ (-4 : ℝ)) := hpoint
      _ ≤ C₀ * Λ ^ 4 * N ^ (-2 : ℝ) := by
        calc
          _ = (C₀ * Λ ^ 4) * N ^ (-4 : ℝ) := by ring
          _ ≤ (C₀ * Λ ^ 4) * N ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left hNpow (by positivity)
          _ = C₀ * Λ ^ 4 * N ^ (-2 : ℝ) := by ring
      _ = C₀ * Λ ^ 4 * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm 2 b.1 := by
        rw [← htermEq]


end ArtinPrimitiveRoots.Proofs.qs_c_p

namespace ArtinPrimitiveRoots.Proofs.qs_c_p

open ArtinPrimitiveRoots.A2

/-- Reindex the original high-divisor coefficient over the coprime q/c/d factors. -/
theorem qs_c3_highdiv_divisor_sum_reindex {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    {q c d : Ideal (𝓞 K)} (hq : Squarefree q) (hc : QSAdm (m := m) (qS := qS) c)
    (hd : QSAdm (m := m) (qS := qS) d)
    (hqc : IsCoprime q c) (hqd : IsCoprime q d) (hcd : IsCoprime c d)
    (T : ℝ) :
    (∑ e ∈ (qsDivisors (q * (c * d))).filter (fun e => T < qsN e),
        ((qsMu e : ℂ) / (qsN e : ℂ))) =
      ∑ eq ∈ qsDivisors q, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
        (((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) /
          ((qsN eq : ℂ) * (qsN (ec * ed) : ℂ))) *
          (if T < qsN eq * qsN (ec * ed) then 1 else 0) := by
  classical
  have hq0 : q ≠ ⊥ := hq.ne_zero
  have hc0 : c ≠ ⊥ := QSC2.ne_bot_of_QSAdm hc
  have hd0 : d ≠ ⊥ := QSC2.ne_bot_of_QSAdm hd
  rw [Finset.sum_filter]
  rw [qs_c3_divisor_sum_reindex₃ hq0 hc0 hd0 hqc hqd hcd
    (fun e => if T < qsN e then ((qsMu e : ℂ) / (qsN e : ℂ)) else 0)]
  simp_rw [QSC2.qsN_mul]
  apply Finset.sum_congr rfl
  intro eq heq
  apply Finset.sum_congr rfl
  intro ec hec
  apply Finset.sum_congr rfl
  intro ed hed
  have hmu := qs_c3_qsMu_factor_three hq hc.1 hd.1 hqc hqd hcd heq hec hed
  simp only [hmu, Int.cast_mul]
  by_cases hcut : T < qsN eq * qsN (ec * ed) <;> simp [hcut]

/-- Expand one original high-divisor kernel using the q/c/d divisor factors. -/
theorem qs_c3_orig_highdiv_expand {K : Type} [Field K] [NumberField K]
    {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}
    (F : QSFamily m qS) (W : ℝ → ℝ) (M κ Λ : ℝ)
    (q c d : Ideal (𝓞 K)) (hq : Squarefree q)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d)
    (hqc : IsCoprime q c) (hqd : IsCoprime q d) (hcd : IsCoprime c d) :
    qsOrigKernel (qsInnerHighDiv K) F W M κ Λ q c d =
      ∑ a ∈ qsSqfUpTo κ q,
        (qsPairChar F c d).idealValue a *
          ((qsResidueOne K : ℂ) * (Real.sqrt (M / qsN a) : ℂ) *
            mellin (fun y => (W (y ^ 2) : ℂ)) 1 *
            ∑ eq ∈ qsDivisors q, ∑ ec ∈ qsDivisors c, ∑ ed ∈ qsDivisors d,
              (((qsMu eq : ℂ) * (qsMu (ec * ed) : ℂ)) /
                ((qsN eq : ℂ) * (qsN (ec * ed) : ℂ))) *
                (if Λ * Real.sqrt (M / qsN a) < qsN eq * qsN (ec * ed)
                  then 1 else 0)) := by
  classical
  unfold qsOrigKernel
  simp only [qsInnerHighDiv]
  apply Finset.sum_congr rfl
  intro a ha
  rw [qs_c3_highdiv_divisor_sum_reindex hq hc hd hqc hqd hcd
    (Λ * Real.sqrt (M / qsN a))]

/-- Arithmetic envelope for one original high-divisor row and divisor shell. -/
theorem qs_c3_highdiv_shell_arith (M n B D₁ D₂ Λ Q α : ℝ)
    (hM : 0 < M) (hn : 1 ≤ n) (hB : 1 ≤ B) (hΛ : 1 ≤ Λ) (hQ : 1 ≤ Q)
    (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (h2B : 2 * B ≤ M)
    (hcut : Λ * Real.sqrt (M / (2 * B)) < Q * D₁ * D₂) :
    Real.sqrt (M / B) / (Q * (D₁ * D₂)) * Real.sqrt (D₁ * D₂) *
        (n / Real.sqrt (D₁ * D₂) +
          Real.sqrt n * B ^ (α / 2) * (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂) + B ^ α) ≤
      4 * (n + B ^ α * Real.sqrt (M / B)) := by
  have hBpos : 0 < B := by linarith
  have hQpos : 0 < Q := by linarith
  have hD₁pos : 0 < D₁ := by linarith
  have hD₂pos : 0 < D₂ := by linarith
  have hDpos : 0 < D₁ * D₂ := mul_pos hD₁pos hD₂pos
  have hMB : 0 < M / B := div_pos hM hBpos
  have hMB2 : 0 < M / (2 * B) := by positivity
  let D : ℝ := D₁ * D₂
  let S : ℝ := Real.sqrt (M / B)
  let H : ℝ := B ^ α * S
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg (D₁ - 1), sq_nonneg (D₂ - 1)]
  have hS : 0 < S := Real.sqrt_pos.2 hMB
  have hSsq : S ^ 2 = M / B := Real.sq_sqrt hMB.le
  have hrootSq : (Real.sqrt (M / (2 * B))) ^ 2 = M / (2 * B) :=
    Real.sq_sqrt hMB2.le
  have hrootCut : Real.sqrt (M / (2 * B)) ≤ Q * D := by
    have hrootnon : 0 ≤ Real.sqrt (M / (2 * B)) := Real.sqrt_nonneg _
    have hle : Real.sqrt (M / (2 * B)) ≤ Λ * Real.sqrt (M / (2 * B)) := by
      simpa using mul_le_mul_of_nonneg_right hΛ hrootnon
    have hcut' : Λ * Real.sqrt (M / (2 * B)) < Q * (D₁ * D₂) := by
      simpa [mul_assoc] using hcut
    dsimp [D]
    exact hle.trans (le_of_lt hcut')
  have hrootSqle : (Real.sqrt (M / (2 * B))) ^ 2 ≤ (Q * D) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hrootCut 2
  have hMsplit : M / B = 2 * (M / (2 * B)) := by field_simp [hBpos.ne']
  have hSbound : S ^ 2 ≤ 2 * (Q * D) ^ 2 := by
    rw [hSsq, hMsplit, ← hrootSq]
    nlinarith [hrootSqle]
  have hSle : S ≤ Real.sqrt 2 * (Q * D) := by
    apply (sq_le_sq₀ hS.le (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    exact hSbound
  have hQD : 0 < Q * D := mul_pos hQpos (by dsimp [D]; exact hDpos)
  have hratio : S / (Q * D) ≤ Real.sqrt 2 :=
    (div_le_iff₀ hQD).2 hSle
  have hD₁sq : D₁ ≤ D₁ ^ 2 := by nlinarith [sq_nonneg (D₁ - 1)]
  have hD₂sq : D₂ ≤ D₂ ^ 2 := by nlinarith [sq_nonneg (D₂ - 1)]
  have hQsq : Q ≤ Q ^ 2 := by nlinarith [sq_nonneg (Q - 1)]
  have hden₁ : Q * D ≤ Q ^ 2 * D₁ ^ 2 * D₂ := by
    dsimp [D]
    calc
      Q * (D₁ * D₂) ≤ Q * (D₁ ^ 2 * D₂) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hD₁sq (by positivity)
        · exact hQpos.le
      _ ≤ Q ^ 2 * (D₁ ^ 2 * D₂) :=
        mul_le_mul_of_nonneg_right hQsq (by positivity)
      _ = Q ^ 2 * D₁ ^ 2 * D₂ := by ring
  have hden₂ : Q * D ≤ Q ^ 2 * D₁ * D₂ ^ 2 := by
    dsimp [D]
    calc
      Q * (D₁ * D₂) ≤ Q * (D₁ * D₂ ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hD₂sq (by positivity)
        · exact hQpos.le
      _ ≤ Q ^ 2 * (D₁ * D₂ ^ 2) :=
        mul_le_mul_of_nonneg_right hQsq (by positivity)
      _ = Q ^ 2 * D₁ * D₂ ^ 2 := by ring
  have hcrossRatio₁ : S / (Q ^ 2 * D₁ ^ 2 * D₂) ≤ Real.sqrt 2 := by
    calc
      _ ≤ S / (Q * D) := by
        rw [div_le_div_iff₀ (by positivity) hQD]
        exact mul_le_mul_of_nonneg_left hden₁ hS.le
      _ ≤ Real.sqrt 2 := hratio
  have hcrossRatio₂ : S / (Q ^ 2 * D₁ * D₂ ^ 2) ≤ Real.sqrt 2 := by
    calc
      _ ≤ S / (Q * D) := by
        rw [div_le_div_iff₀ (by positivity) hQD]
        exact mul_le_mul_of_nonneg_left hden₂ hS.le
      _ ≤ Real.sqrt 2 := hratio
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hpow : (B ^ (α / 2)) ^ 2 = B ^ α := by
    calc
      (B ^ (α / 2)) ^ 2 = (B ^ (α / 2)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (B ^ (α / 2)) 2).symm
      _ = B ^ ((α / 2) * 2) := (Real.rpow_mul hBpos.le (α / 2) 2).symm
      _ = B ^ α := by congr 1 <;> ring
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hHdef : H = B ^ α * S := rfl
  let T₁ : ℝ := S / (Q * D) * Real.sqrt D * Real.sqrt n * B ^ (α / 2) / Real.sqrt D₁
  let T₂ : ℝ := S / (Q * D) * Real.sqrt D * Real.sqrt n * B ^ (α / 2) / Real.sqrt D₂
  have hDroot : Real.sqrt D = Real.sqrt D₁ * Real.sqrt D₂ := by
    dsimp [D]
    exact Real.sqrt_mul hD₁pos.le D₂
  have hT₁sq : T₁ ^ 2 = n * H * (S / (Q ^ 2 * D₁ ^ 2 * D₂)) := by
    dsimp [T₁, H]
    rw [hDroot]
    simp only [div_pow, mul_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ n), hpow,
      Real.sq_sqrt hD₁pos.le, Real.sq_sqrt hD₂pos.le]
    field_simp [hQpos.ne', hD₁pos.ne', hD₂pos.ne', hBpos.ne']
    dsimp [D]
    <;> ring
  have hT₂sq : T₂ ^ 2 = n * H * (S / (Q ^ 2 * D₁ * D₂ ^ 2)) := by
    dsimp [T₂, H]
    rw [hDroot]
    simp only [div_pow, mul_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ n), hpow,
      Real.sq_sqrt hD₁pos.le, Real.sq_sqrt hD₂pos.le]
    field_simp [hQpos.ne', hD₁pos.ne', hD₂pos.ne', hBpos.ne']
    dsimp [D]
    <;> ring
  have hT₁non : 0 ≤ T₁ := by dsimp [T₁]; positivity
  have hT₂non : 0 ≤ T₂ := by dsimp [T₂]; positivity
  have hYoung : 2 * n * H ≤ (n + H) ^ 2 := by
    nlinarith [sq_nonneg (n - H)]
  have hT₁le : T₁ ≤ n + H := by
    apply (sq_le_sq₀ hT₁non (by positivity)).mp
    calc
      T₁ ^ 2 = n * H * (S / (Q ^ 2 * D₁ ^ 2 * D₂)) := hT₁sq
      _ ≤ 2 * n * H := by
        calc
          _ ≤ n * H * 2 := mul_le_mul_of_nonneg_left
            (hcrossRatio₁.trans hsqrt2) (mul_nonneg (by positivity) hH)
          _ = 2 * n * H := by ring
      _ ≤ (n + H) ^ 2 := hYoung
  have hT₂le : T₂ ≤ n + H := by
    apply (sq_le_sq₀ hT₂non (by positivity)).mp
    calc
      T₂ ^ 2 = n * H * (S / (Q ^ 2 * D₁ * D₂ ^ 2)) := hT₂sq
      _ ≤ 2 * n * H := by
        calc
          _ ≤ n * H * 2 := mul_le_mul_of_nonneg_left
            (hcrossRatio₂.trans hsqrt2) (mul_nonneg (by positivity) hH)
          _ = 2 * n * H := by ring
      _ ≤ (n + H) ^ 2 := hYoung
  have hfirst :
      S / (Q * D) * Real.sqrt D * (n / Real.sqrt D) = n * (S / (Q * D)) := by
    field_simp [Real.sqrt_ne_zero'.mpr hDpos]
    <;> ring
  have hlastCoeff : S / (Q * D) * Real.sqrt D ≤ S := by
    have hsimp : S / (Q * D) * Real.sqrt D = S / (Q * Real.sqrt D) := by
      rw [hDroot]
      field_simp [hQpos.ne', hD₁pos.ne', hD₂pos.ne']
      rw [Real.sq_sqrt hD₁pos.le, Real.sq_sqrt hD₂pos.le]
    rw [hsimp]
    have hroot1 : 1 ≤ Real.sqrt D := (Real.one_le_sqrt).2 hD1
    apply (div_le_iff₀ (mul_pos hQpos (Real.sqrt_pos.2 hDpos))).2
    calc
      S = S * 1 := by ring
      _ ≤ S * (Q * Real.sqrt D) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hS.le
  have hlast : S / (Q * D) * Real.sqrt D * B ^ α ≤ H := by
    have hBp : 0 ≤ B ^ α := Real.rpow_nonneg hBpos.le _
    calc
      _ ≤ S * B ^ α := mul_le_mul_of_nonneg_right hlastCoeff hBp
      _ = H := by rw [hHdef]; ring
  have hcross :
      S / (Q * D) * Real.sqrt D *
          (Real.sqrt n * B ^ (α / 2) *
            (1 / Real.sqrt D₁ + 1 / Real.sqrt D₂)) = T₁ + T₂ := by
    dsimp [T₁, T₂]
    ring
  calc
    _ = n * (S / (Q * D)) + T₁ + T₂ +
          S / (Q * D) * Real.sqrt D * B ^ α := by
      rw [mul_add, mul_add, hfirst, hcross]
      <;> ring
    _ ≤ 2 * n + (n + H) + (n + H) + H := by
      have hratio2 : S / (Q * D) ≤ 2 := hratio.trans hsqrt2
      have hn0 : 0 ≤ n := by linarith
      have hfirstle : n * (S / (Q * D)) ≤ 2 * n := by
        calc
          _ ≤ n * 2 := mul_le_mul_of_nonneg_left hratio2 hn0
          _ = 2 * n := by ring
      nlinarith [hT₁le, hT₂le, hlast, hfirstle]
    _ ≤ 4 * (n + H) := by nlinarith

end ArtinPrimitiveRoots.Proofs.qs_c_p
