import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».Defs
import ArtinPrimitiveRoots.A2.ZeroFree.Nodes
import ArtinPrimitiveRoots.Hecke.Theta.IdealNormSummability

/-!
# A2-QS-MATRIX, part M1: uniform ideal counts, divisor bounds, squarefree parts, tails

Guide: `runs/lanes/sol-thin-found/PROOFS.md:307-326`.  Hints: Mathlib
`Ideal.finite_setOfPred_absNorm_le`, the ideal-count asymptotic
`NumberField.Ideal.tendsto_norm_le_div_atTop` (`M/NumberTheory/NumberField/Ideal/Asymptotics.lean`)
may replace the Euler-factor comparison for `qs_ideal_count_M1`; divisor bound by
`τ(I) = ∏(e_P + 1)` with finitely many small primes.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- M1 (IMPL): `#{I : N I ≤ X} ≪_η X^{1+η}` for `X ≥ 1` (found:309-310). -/
theorem qs_ideal_count_M1 (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      (((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset.card : ℕ) : ℝ) ≤
        C * X ^ (1 + η) := by
  obtain ⟨C, hC, hcount⟩ := ArtinPrimitiveRoots.A2.ext_ideal_count (F := K)
  refine ⟨C, hC, ?_⟩
  intro X hX
  have hpow : X ≤ X ^ (1 + η) := by
    rw [show (1 + η : ℝ) = η + 1 by ring,
      Real.rpow_add_one (ne_of_gt (by linarith : 0 < X)) η]
    have hp := mul_le_mul_of_nonneg_right (Real.one_le_rpow hX hη.le)
      (le_of_lt (show 0 < X by linarith))
    simpa only [one_mul] using hp
  exact (hcount X hX).trans (mul_le_mul_of_nonneg_left hpow hC.le)

/-- M1 (IMPL): divisor bound `τ(I) ≪_η (N I)^η` (found:311-313). -/
theorem qs_divisor_bound_M1 (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      (((qsDivisors I).card : ℕ) : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ η := by
  obtain ⟨C, hC, hdiv⟩ :=
    ArtinPrimitiveRoots.A2.Proofs.A2Z1.ideal_divisor_count_small_power (F := K) η hη
  refine ⟨C, hC, ?_⟩
  intro I hI
  have hnorm : 0 < Ideal.absNorm I := by
    apply Nat.pos_iff_ne_zero.mpr
    intro hn
    exact hI (Ideal.absNorm_eq_zero_iff.mp hn)
  have hfinite : ({J : Ideal (𝓞 K) | J ∣ I} : Set (Ideal (𝓞 K))).Finite := by
    refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).subset ?_
    intro J hJ
    exact Nat.le_of_dvd hnorm (map_dvd Ideal.absNorm hJ)
  have hfinset : hfinite.toFinset = qsDivisors I := by
    ext J
    simp only [Set.Finite.mem_toFinset, qsDivisors, Finset.mem_filter,
      Set.mem_ofPred_eq]
    constructor
    · intro hJ
      exact ⟨Nat.le_of_dvd hnorm (map_dvd Ideal.absNorm hJ), hJ⟩
    · intro hJ
      exact hJ.2
  have hcard : Set.ncard {J : Ideal (𝓞 K) | J ∣ I} = (qsDivisors I).card := by
    rw [Set.ncard_eq_toFinset_card _ hfinite, hfinset]
  simpa only [hcard] using hdiv I hI

private theorem qs_squarefree_decomposition_unique_aux
    (I a b c d : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (ha : Squarefree a) (hc : Squarefree c)
    (hab : I = a * b ^ 2) (hcd : I = c * d ^ 2) : a = c ∧ b = d := by
  classical
  have ha0 : a ≠ ⊥ := by
    intro hz
    apply hI
    simpa [hz] using hab
  have hb0 : b ≠ ⊥ := by
    intro hz
    apply hI
    simpa [hz] using hab
  have hc0 : c ≠ ⊥ := by
    intro hz
    apply hI
    simpa [hz] using hcd
  have hd0 : d ≠ ⊥ := by
    intro hz
    apply hI
    simpa [hz] using hcd
  have hfa : (normalizedFactors a).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors ha0).mp ha
  have hfc : (normalizedFactors c).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hc0).mp hc
  have hca (P : Ideal (𝓞 K)) :
      (normalizedFactors a).count P ≤ 1 :=
    (Multiset.nodup_iff_count_le_one.mp hfa) P
  have hcc (P : Ideal (𝓞 K)) :
      (normalizedFactors c).count P ≤ 1 :=
    (Multiset.nodup_iff_count_le_one.mp hfc) P
  have hcountA (P : Ideal (𝓞 K)) :
      (normalizedFactors I).count P =
        (normalizedFactors a).count P + 2 * (normalizedFactors b).count P := by
    rw [hab, UniqueFactorizationMonoid.normalizedFactors_mul ha0 (pow_ne_zero 2 hb0),
      UniqueFactorizationMonoid.normalizedFactors_pow]
    simp
  have hcountC (P : Ideal (𝓞 K)) :
      (normalizedFactors I).count P =
        (normalizedFactors c).count P + 2 * (normalizedFactors d).count P := by
    rw [hcd, UniqueFactorizationMonoid.normalizedFactors_mul hc0 (pow_ne_zero 2 hd0),
      UniqueFactorizationMonoid.normalizedFactors_pow]
    simp
  have hcounts (P : Ideal (𝓞 K)) :
      (normalizedFactors a).count P = (normalizedFactors c).count P ∧
        (normalizedFactors b).count P = (normalizedFactors d).count P := by
    have h1 := hcountA P
    have h2 := hcountC P
    have hkA := hca P
    have hkC := hcc P
    omega
  have hfa_eq : normalizedFactors a = normalizedFactors c := by
    ext P
    exact (hcounts P).1
  have hfb_eq : normalizedFactors b = normalizedFactors d := by
    ext P
    exact (hcounts P).2
  constructor
  · calc
      a = (normalizedFactors a).prod := (Ideal.prod_normalizedFactors_eq_self ha0).symm
      _ = (normalizedFactors c).prod := congrArg Multiset.prod hfa_eq
      _ = c := Ideal.prod_normalizedFactors_eq_self hc0
  · calc
      b = (normalizedFactors b).prod := (Ideal.prod_normalizedFactors_eq_self hb0).symm
      _ = (normalizedFactors d).prod := congrArg Multiset.prod hfb_eq
      _ = d := Ideal.prod_normalizedFactors_eq_self hd0

/-- M1 (IMPL): unique squarefree decomposition `I = a₀ b²` (found:314-316). -/
theorem qs_squarefree_decomposition_M1 (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃! p : Ideal (𝓞 K) × Ideal (𝓞 K), Squarefree p.1 ∧ I = p.1 * p.2 ^ 2 := by
  classical
  obtain ⟨b, a₀, hfac, ha₀⟩ := exists_sq_mul_squarefree I
  refine ⟨(a₀, b), ?_, ?_⟩
  · refine ⟨ha₀, ?_⟩
    calc
      I = b ^ 2 * a₀ := hfac.symm
      _ = a₀ * b ^ 2 := by ac_rfl
  · rintro ⟨a₁, b₁⟩ ⟨ha₁, hfac₁⟩
    obtain ⟨rfl, rfl⟩ := qs_squarefree_decomposition_unique_aux
      I a₀ b a₁ b₁ hI ha₀ ha₁
      (by calc I = a₀ * b ^ 2 := by
                calc I = b ^ 2 * a₀ := hfac.symm
                     _ = a₀ * b ^ 2 := by ac_rfl)
      hfac₁
    rfl

/-- M1 (IMPL): `qsSfNorm` is the norm of the squarefree part (consistency with
`qs_squarefree_decomposition_M1`). -/
theorem qs_sfNorm_eq_M1 (a₀ b : Ideal (𝓞 K)) (ha₀ : Squarefree a₀) (hb : b ≠ ⊥) :
    qsSfNorm (a₀ * b ^ 2) = Ideal.absNorm a₀ := by
  classical
  have ha₀0 : a₀ ≠ ⊥ := ha₀.ne_zero
  have hfac (P : Ideal (𝓞 K)) :
      (normalizedFactors (a₀ * b ^ 2)).count P =
        (normalizedFactors a₀).count P + 2 * (normalizedFactors b).count P := by
    rw [normalizedFactors_mul ha₀0 (pow_ne_zero 2 hb), normalizedFactors_pow]
    simp
  have hnodup : (normalizedFactors a₀).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors ha₀0).mp ha₀
  have hselect :
      (normalizedFactors (a₀ * b ^ 2)).toFinset.filter
          (fun P => Odd ((normalizedFactors (a₀ * b ^ 2)).count P)) =
        (normalizedFactors a₀).toFinset := by
    ext P
    simp only [Finset.mem_filter, Multiset.mem_toFinset]
    constructor
    · rintro ⟨_, hodd⟩
      rcases hodd with ⟨k, hk⟩
      by_contra hnot
      have hzero := Multiset.count_eq_zero_of_notMem hnot
      have hc := hfac P
      omega
    · intro hP
      have hone := Multiset.count_eq_one_of_mem hnodup hP
      have hc := hfac P
      have hpos : 0 < (normalizedFactors (a₀ * b ^ 2)).count P := by omega
      refine ⟨Multiset.count_pos.mp hpos, ?_⟩
      change ∃ k,
        (normalizedFactors (a₀ * b ^ 2)).count P = 2 * k + 1
      exact ⟨(normalizedFactors b).count P, by omega⟩
  have hprod :
      (∏ P ∈ (normalizedFactors a₀).toFinset, P) =
        (normalizedFactors a₀).prod := by
    rw [Finset.prod_multiset_count]
    refine Finset.prod_congr rfl ?_
    intro P hP
    rw [Multiset.count_eq_one_of_mem hnodup (Multiset.mem_toFinset.mp hP), pow_one]
  unfold qsSfNorm
  rw [hselect]
  calc
    Ideal.absNorm (∏ P ∈ (normalizedFactors a₀).toFinset, P) =
        Ideal.absNorm (normalizedFactors a₀).prod := congrArg Ideal.absNorm hprod
    _ = Ideal.absNorm a₀ := by rw [Ideal.prod_normalizedFactors_eq_self ha₀0]

/-- M1 (IMPL): rapid-decay tails over ideals (found:320-324): if `‖h x‖ ≤ C_A x^{-A}` for
`x ≥ 1` and `A > 1 + η`, then `Σ_{N I > T} ‖h(N I / X)‖ ≪ C_A X^A T^{1+η-A}` for
`T ≥ max 1 X`; the constant depends only on `K, η, A`. -/
theorem qs_tail_bound_M1 (η A : ℝ) (hη : 0 < η) (hA : 1 + η < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℂ) (CA X T : ℝ), 0 ≤ CA → 0 < X → max 1 X ≤ T →
      (∀ x : ℝ, 1 ≤ x → ‖h x‖ ≤ CA * x ^ (-A)) →
        Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ T < (Ideal.absNorm I : ℝ)} =>
          ‖h ((Ideal.absNorm I.1 : ℝ) / X)‖) ∧
        ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ T < (Ideal.absNorm I : ℝ)},
            ‖h ((Ideal.absNorm I.1 : ℝ) / X)‖ ≤
          C * CA * X ^ A * T ^ (1 + η - A) := by
  have hσ : 1 < 1 + η := by linarith
  have hbase₀ : Summable
      (fun I : Ideal (𝓞 K) =>
        ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + η) I) :=
    ArtinPrimitiveRoots.Hecke.summable_idealNormRpow (K := K) hσ
  let S : ℝ := ∑' I : Ideal (𝓞 K),
    ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + η) I
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun I => by
      dsimp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
      split_ifs <;> positivity
  let C : ℝ := 1 + S
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    linarith
  · intro h CA X T hCA hX hT hh
    have hT1 : 1 ≤ T := (max_le_iff.mp hT).1
    have hXT : X ≤ T := (max_le_iff.mp hT).2
    let tail : Set (Ideal (𝓞 K)) :=
      {I | I ≠ ⊥ ∧ T < (Ideal.absNorm I : ℝ)}
    let factor : ℝ := CA * X ^ A * T ^ (1 + η - A)
    have hfactor : 0 ≤ factor := by
      dsimp [factor]
      positivity
    have hbaseTail : Summable
        (fun I : tail => (Ideal.absNorm I.1 : ℝ) ^ (-(1 + η))) := by
      refine (hbase₀.subtype tail).congr ?_
      intro I
      have hnorm : 0 < Ideal.absNorm I.1 := by
        apply Nat.pos_iff_ne_zero.mpr
        intro hzero
        exact I.2.1 (Ideal.absNorm_eq_zero_iff.mp hzero)
      simp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm, hnorm.ne']
    have hmajor : Summable
        (fun I : tail => factor * (Ideal.absNorm I.1 : ℝ) ^ (-(1 + η))) :=
      hbaseTail.mul_left factor
    have hpoint : ∀ I : tail,
        ‖h ((Ideal.absNorm I.1 : ℝ) / X)‖ ≤
          factor * (Ideal.absNorm I.1 : ℝ) ^ (-(1 + η)) := by
      intro I
      let n : ℝ := Ideal.absNorm I.1
      have hnT : T < n := by simpa [n] using I.2.2
      have hnX : X ≤ n := le_trans hXT hnT.le
      have hn1 : 1 ≤ n := le_trans hT1 hnT.le
      have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
      have hratio : 1 ≤ n / X := (one_le_div₀ hX).2 hnX
      have hscale : (n / X) ^ (-A) = X ^ A * n ^ (-A) := by
        calc
          (n / X) ^ (-A) = (n / X)⁻¹ ^ A := Real.rpow_neg_eq_inv_rpow _ _
          _ = (X / n) ^ A := by congr 1 <;> field_simp
          _ = X ^ A / n ^ A := Real.div_rpow (by positivity) (by positivity) A
          _ = X ^ A * n ^ (-A) := by
            rw [Real.rpow_neg hnpos.le]
            ring
      let q : ℝ := A - (1 + η)
      have hq : 0 < q := by dsimp [q]; linarith
      have hsplit : n ^ (-A) = n ^ (-(1 + η)) * n ^ (-q) := by
        calc
          n ^ (-A) = n ^ (-(1 + η) + -q) := by congr 1 <;> dsimp [q] <;> ring
          _ = n ^ (-(1 + η)) * n ^ (-q) :=
            Real.rpow_add hnpos (-(1 + η)) (-q)
      have hnq : n ^ (-q) ≤ T ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hT1)
          hnT.le (neg_nonpos.mpr hq.le)
      have hpower : n ^ (-A) ≤ T ^ (1 + η - A) * n ^ (-(1 + η)) := by
        calc
          n ^ (-A) = n ^ (-(1 + η)) * n ^ (-q) := hsplit
          _ ≤ n ^ (-(1 + η)) * T ^ (-q) :=
            mul_le_mul_of_nonneg_left hnq (Real.rpow_nonneg hnpos.le _)
          _ = T ^ (1 + η - A) * n ^ (-(1 + η)) := by
            have he : -q = 1 + η - A := by dsimp [q]; ring
            rw [he]
            ring
      calc
        ‖h (n / X)‖ ≤ CA * (n / X) ^ (-A) := hh (n / X) hratio
        _ = (CA * X ^ A) * n ^ (-A) := by rw [hscale]; ring
        _ ≤ (CA * X ^ A) *
              (T ^ (1 + η - A) * n ^ (-(1 + η))) :=
            mul_le_mul_of_nonneg_left hpower (mul_nonneg hCA (Real.rpow_nonneg (le_of_lt hX) _))
        _ = factor * n ^ (-(1 + η)) := by dsimp [factor]; ring
    have htarget : Summable
        (fun I : tail => ‖h ((Ideal.absNorm I.1 : ℝ) / X)‖) :=
      hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
    have hbaseTail_le :
        (∑' I : tail, (Ideal.absNorm I.1 : ℝ) ^ (-(1 + η))) ≤ S := by
      calc
        _ = ∑' I : tail,
              ArtinPrimitiveRoots.Hecke.idealNormRpowTerm (1 + η) I.1 := by
          apply tsum_congr
          intro I
          have hnorm : 0 < Ideal.absNorm I.1 := by
            apply Nat.pos_iff_ne_zero.mpr
            intro hzero
            exact I.2.1 (Ideal.absNorm_eq_zero_iff.mp hzero)
          simp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm, hnorm.ne']
        _ ≤ S := hbase₀.tsum_subtype_le _ tail (fun I => by
          dsimp [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm]
          split_ifs <;> positivity)
    have hsum :
        (∑' I : tail, ‖h ((Ideal.absNorm I.1 : ℝ) / X)‖) ≤ factor * S := by
      calc
        _ ≤ ∑' I : tail, factor * (Ideal.absNorm I.1 : ℝ) ^ (-(1 + η)) :=
          htarget.tsum_le_tsum hpoint hmajor
        _ = factor * ∑' I : tail, (Ideal.absNorm I.1 : ℝ) ^ (-(1 + η)) :=
          hbaseTail.tsum_mul_left factor
        _ ≤ factor * S := mul_le_mul_of_nonneg_left hbaseTail_le hfactor
    have hfinal : factor * S ≤ C * CA * X ^ A * T ^ (1 + η - A) := by
      dsimp [factor, C]
      nlinarith [hS, hCA, Real.rpow_nonneg (le_of_lt hX) A,
        Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hT1)) (1 + η - A)]
    exact ⟨htarget, hsum.trans hfinal⟩

end ArtinPrimitiveRoots.A2
