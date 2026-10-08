import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P1
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0

/-!
# A2-QS-MATRIX, part M2: the initial exponent `HasExponent 2`

Guide: `runs/lanes/sol-thin-found/PROOFS.md:327-328`.  Smooth Gram expansion of
`Σ_a W(N a/M) |Σ_c z_c χ_c(a)|²` (rows coprime to `m`, `qS`; `W ≥ 1` on `[0,1]` dominates the
squarefree rows of norm `≤ M`), class slicing, gcd grouping (`qs_gcd_pair_identity_S0`):
diagonal pairs cost `≪ M ‖z‖²`; a nonprincipal residual pair kernel is `≪ √N f (N𝔮 N f)^η`
(`qs_pair_kernel_bound_M2`: Möbius over `e ∣ 𝔮`, P1, decay of `T W`, ideal counts), and
Cauchy–Schwarz over the `≪ N^{1+η}` columns gives `N^{2+O(η)} ‖z‖²`.  No use of the quadratic
bound being proved or of the A2 zero-free theorem.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

private theorem qs_norm_multiset_prod_le_one {α : Type*} (s : Multiset α) (f : α → ℂ)
    (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) (ih fun x hx =>
        hf x (Multiset.mem_cons_of_mem hx))

private theorem qs_primeValue_norm_le_one (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (hsq : χ ^ 2 = 1) (v : ArtinPrimitiveRoots.A1.FinPlace K) :
    ‖ArtinPrimitiveRoots.A1.HeckeChar.primeValue χ v‖ ≤ 1 := by
  by_cases hu : ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt χ v
  · simp only [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hu, ↓reduceDIte]
    let u : (v.adicCompletion K)ˣ :=
      ArtinPrimitiveRoots.A1.toLoc v (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
        (ArtinPrimitiveRoots.A1.unif_ne_zero v))
    have hloc : (ArtinPrimitiveRoots.A1.HeckeChar.loc χ v u) ^ 2 = 1 := by
      let x := IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u
      have h := congrArg (fun ψ : ArtinPrimitiveRoots.A1.HeckeChar K => ψ x) hsq
      simpa [pow_two, x, ArtinPrimitiveRoots.A1.HeckeChar.loc] using h
    have hpow : ((ArtinPrimitiveRoots.A1.HeckeChar.loc χ v u : ℂˣ) : ℂ) ^ 2 = 1 := by
      simpa only [pow_two, Units.val_mul, Units.val_one] using
        congrArg (fun z : ℂˣ => (z : ℂ)) hloc
    have hnorm : ‖((ArtinPrimitiveRoots.A1.HeckeChar.loc χ v u : ℂˣ) : ℂ)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hpow (by norm_num)
    simpa using le_of_eq hnorm
  · simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hu]

private theorem qs_idealValue_norm_le_one (χ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (hsq : χ ^ 2 = 1) (I : Ideal (𝓞 K)) :
    ‖ArtinPrimitiveRoots.A1.HeckeChar.idealValue χ I‖ ≤ 1 := by
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  apply qs_norm_multiset_prod_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using qs_primeValue_norm_le_one χ hsq ⟨P, h.1, h.2⟩
  · simp [h]

private theorem qs_sum_neg_one_powerset {α : Type*} [DecidableEq α] (S : Finset α) :
    (∑ s ∈ S.powerset, (-1 : ℂ) ^ s.card) = if S = ∅ then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hinj : Set.InjOn (insert a) (S.powerset : Set (Finset α)) := by
        intro s hs t ht hst
        have hsa : a ∉ s := fun hs' => ha (Finset.mem_powerset.mp hs hs')
        have hta : a ∉ t := fun ht' => ha (Finset.mem_powerset.mp ht ht')
        apply Finset.ext
        intro x
        by_cases hxa : x = a
        · subst x
          simp [hsa, hta]
        · have hmem := congrArg (fun u : Finset α => x ∈ u) hst
          simpa [hxa] using hmem
      have hdisj : Disjoint S.powerset (S.powerset.image (insert a)) := by
        apply Finset.disjoint_left.mpr
        intro t ht hti
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hti
        have hsub := Finset.mem_powerset.mp ht
        exact ha (hsub (Finset.mem_insert_self a u))
      have hneg :
          (∑ t ∈ S.powerset, (-1 : ℂ) ^ (insert a t).card) =
            -∑ t ∈ S.powerset, (-1 : ℂ) ^ t.card := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        have hnot : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
        rw [Finset.card_insert_of_notMem hnot, pow_succ]
        ring
      rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj, hneg]
      simp

open Classical in
private theorem qs_coprime_iff_no_common_factor_M2 (q a : Ideal (𝓞 K))
    (hq : q ≠ ⊥) (ha : a ≠ ⊥) :
    IsCoprime a q ↔
      ((UniqueFactorizationMonoid.normalizedFactors q).toFinset.filter
        (fun p => p ∣ a)) = ∅ := by
  classical
  let common := (UniqueFactorizationMonoid.normalizedFactors q).toFinset.filter
    (fun p => p ∣ a)
  constructor
  · intro hcop
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpq, hpa⟩
    have hqf := (Ideal.mem_normalizedFactors_iff hq).mp
      (Multiset.mem_toFinset.mp hpq)
    have hcop' : q ⊔ a = ⊤ := by
      simpa [sup_comm] using (Ideal.isCoprime_iff_sup_eq.mp hcop)
    have hle : q ⊔ a ≤ p := sup_le hqf.2 (Ideal.dvd_iff_le.mp hpa)
    have htop : ⊤ ≤ p := by simpa [hcop'] using hle
    exact hqf.1.ne_top (top_unique htop)
  · intro hcommon
    have htop : q ⊔ a = ⊤ := by
      by_contra htop
      have hsumne : q ⊔ a ≠ ⊥ := by
        intro hbot
        have hqle : q ≤ ⊥ := by simpa [hbot] using (le_sup_left : q ≤ q ⊔ a)
        exact hq (le_bot_iff.mp hqle)
      have hnotunit : ¬ IsUnit (q ⊔ a) := by
        intro hu
        exact htop (Ideal.isUnit_iff.mp hu)
      obtain ⟨p, hp⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hsumne hnotunit
      have hpspec := (Ideal.mem_normalizedFactors_iff hsumne).mp hp
      have hpq : p ∈ UniqueFactorizationMonoid.normalizedFactors q :=
        (Ideal.mem_normalizedFactors_iff hq).mpr
          ⟨hpspec.1, le_trans le_sup_left hpspec.2⟩
      have hpa : p ∣ a := Ideal.dvd_iff_le.mpr (le_trans le_sup_right hpspec.2)
      have hpmem : p ∈ common := Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr hpq, hpa⟩
      simp [common, hcommon] at hpmem
    exact (Ideal.isCoprime_iff_sup_eq).mpr (by simpa [sup_comm] using htop)

open Classical in
private theorem qs_coprime_factor_sum_M2 (q a : Ideal (𝓞 K))
    (hq : q ≠ ⊥) (ha : a ≠ ⊥) :
    (if IsCoprime a q then (1 : ℂ) else 0) =
      ∑ s ∈ (UniqueFactorizationMonoid.normalizedFactors q).toFinset.powerset,
        if ∀ p ∈ s, p ∣ a then (-1 : ℂ) ^ s.card else 0 := by
  classical
  let P := (UniqueFactorizationMonoid.normalizedFactors q).toFinset
  let common := P.filter (fun p => p ∣ a)
  have hsubset : common ⊆ P := Finset.filter_subset _ _
  have hcommon : IsCoprime a q ↔ common = ∅ := by
    simpa [P, common] using qs_coprime_iff_no_common_factor_M2 q a hq ha
  have hfilter : P.powerset.filter (fun s => s ⊆ common) = common.powerset := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hsP, hsC⟩
      exact hsC
    · intro hsC
      exact ⟨hsC.trans hsubset, hsC⟩
  have hsum :
      (∑ s ∈ P.powerset, if s ⊆ common then (-1 : ℂ) ^ s.card else 0) =
        ∑ s ∈ common.powerset, (-1 : ℂ) ^ s.card := by
    rw [← Finset.sum_filter, hfilter]
  have hterm (s : Finset (Ideal (𝓞 K))) (hs : s ∈ P.powerset) :
      (∀ p ∈ s, p ∣ a) ↔ s ⊆ common := by
    simp only [Finset.mem_powerset] at hs
    constructor
    · intro h p hp
      exact Finset.mem_filter.mpr ⟨hs hp, h p hp⟩
    · intro h p hp
      exact (Finset.mem_filter.mp (h hp)).2
  have hsum' :
      (∑ s ∈ P.powerset,
        if ∀ p ∈ s, p ∣ a then (-1 : ℂ) ^ s.card else 0) =
        ∑ s ∈ P.powerset, if s ⊆ common then (-1 : ℂ) ^ s.card else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    by_cases h : ∀ p ∈ s, p ∣ a
    · have h' := (hterm s hs).mp h
      simp only [if_pos h, if_pos h']
    · have h' : ¬ s ⊆ common := fun hs' => h ((hterm s hs).mpr hs')
      simp only [if_neg h, if_neg h']
  rw [hsum']
  rw [hcommon]
  rw [hsum]
  rw [qs_sum_neg_one_powerset]
  by_cases h : common = ∅ <;> simp [h]

private theorem qs_factor_subset_product_inj_M2 (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    Set.InjOn (fun s : Finset (Ideal (𝓞 K)) => ∏ p ∈ s, p)
      ((UniqueFactorizationMonoid.normalizedFactors q).toFinset.powerset :
        Set (Finset (Ideal (𝓞 K)))) := by
  classical
  intro s hs t ht hst
  have hprodNorm (u : Finset (Ideal (𝓞 K))) (hu : u ⊆
      (UniqueFactorizationMonoid.normalizedFactors q).toFinset) :
      UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ u, p) = u.1 := by
    have hprime : ∀ p ∈ u.1, Prime p := by
      intro p hp
      have hpU : p ∈ u := by simpa using hp
      have hpQ : p ∈ UniqueFactorizationMonoid.normalizedFactors q :=
        Multiset.mem_toFinset.mp (hu hpU)
      exact UniqueFactorizationMonoid.prime_of_normalized_factor p hpQ
    rw [Finset.prod_eq_multiset_prod]
    simpa using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprime
  have hs' := hprodNorm s (Finset.mem_powerset.mp hs)
  have ht' := hprodNorm t (Finset.mem_powerset.mp ht)
  have hmult : s.1 = t.1 := by
    have h := congrArg UniqueFactorizationMonoid.normalizedFactors hst
    simpa [hs', ht'] using h
  exact Finset.val_injective hmult

private theorem qs_factor_subset_product_dvd_M2 (q : Ideal (𝓞 K)) (hq : q ≠ ⊥)
    (s : Finset (Ideal (𝓞 K)))
    (hs : s ⊆ (UniqueFactorizationMonoid.normalizedFactors q).toFinset) :
    (∏ p ∈ s, p) ∣ q := by
  classical
  have hPval :
      ((UniqueFactorizationMonoid.normalizedFactors q).toFinset).1 =
        (UniqueFactorizationMonoid.normalizedFactors q).dedup := by
    exact Multiset.toFinset_val _
  have hsval : s.1 ≤ UniqueFactorizationMonoid.normalizedFactors q := by
    calc
      s.1 ≤ (UniqueFactorizationMonoid.normalizedFactors q).toFinset.1 :=
        Finset.val_le_iff.mpr hs
      _ = (UniqueFactorizationMonoid.normalizedFactors q).dedup := hPval
      _ ≤ UniqueFactorizationMonoid.normalizedFactors q := Multiset.dedup_le _
  have hprod : (∏ p ∈ s, p) = s.1.prod := by
    rw [Finset.prod_eq_multiset_prod]
    simp
  rw [hprod]
  exact (Multiset.prod_dvd_prod_of_le hsval).trans
    (by rw [Ideal.prod_normalizedFactors_eq_self hq])

private theorem qs_factor_subset_product_mem_divisors_M2 (q : Ideal (𝓞 K))
    (hq : q ≠ ⊥) (s : Finset (Ideal (𝓞 K)))
    (hs : s ⊆ (UniqueFactorizationMonoid.normalizedFactors q).toFinset) :
    (∏ p ∈ s, p) ∈ qsDivisors q := by
  classical
  have hdiv := qs_factor_subset_product_dvd_M2 q hq s hs
  have he : (∏ p ∈ s, p) ≠ ⊥ := by
    intro hebot
    have hbotdiv : (⊥ : Ideal (𝓞 K)) ∣ q := by simpa [hebot] using hdiv
    exact hq (le_bot_iff.mp (Ideal.dvd_iff_le.mp hbotdiv))
  have hnorm : Ideal.absNorm (∏ p ∈ s, p) ≤ Ideal.absNorm q := by
    have hqND : q ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using hq)
    apply Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors ⟨q, hqND⟩)
    exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdiv)
  change (∏ p ∈ s, p) ∈
    ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm q)).toFinset).filter
      (fun e => e ∣ q)
  exact Finset.mem_filter.mpr
    ⟨(Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm q)).mem_toFinset.mpr hnorm,
      hdiv⟩

private theorem qs_factor_subset_count_bound_M2 (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (( ((UniqueFactorizationMonoid.normalizedFactors q).toFinset.powerset.card : ℕ) : ℝ)) ≤
      ((qsDivisors q).card : ℝ) := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun s : Finset (Ideal (𝓞 K)) => ∏ p ∈ s, p)
  · intro s hs
    exact qs_factor_subset_product_mem_divisors_M2 q hq s
      (Finset.mem_powerset.mp hs)
  · exact qs_factor_subset_product_inj_M2 q hq

private theorem qs_factor_product_normalizedFactors_M2 (q : Ideal (𝓞 K)) (hq : q ≠ ⊥)
    (s : Finset (Ideal (𝓞 K)))
    (hs : s ⊆ (UniqueFactorizationMonoid.normalizedFactors q).toFinset) :
    UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.1 := by
  classical
  have hprime : ∀ p ∈ s.1, Prime p := by
    intro p hp
    have hpS : p ∈ s := by simpa using hp
    have hpq : p ∈ UniqueFactorizationMonoid.normalizedFactors q :=
      Multiset.mem_toFinset.mp (hs hpS)
    exact UniqueFactorizationMonoid.prime_of_normalized_factor p hpq
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprime

private theorem qs_factor_product_divides_iff_M2 (q a : Ideal (𝓞 K))
    (hq : q ≠ ⊥) (ha : a ≠ ⊥) (s : Finset (Ideal (𝓞 K)))
    (hs : s ⊆ (UniqueFactorizationMonoid.normalizedFactors q).toFinset) :
    (∏ p ∈ s, p) ∣ a ↔ ∀ p ∈ s, p ∣ a := by
  classical
  have heDivQ := qs_factor_subset_product_dvd_M2 q hq s hs
  have he0 : (∏ p ∈ s, p) ≠ ⊥ := by
    intro hebot
    have hbotdiv : (⊥ : Ideal (𝓞 K)) ∣ q := by simpa [hebot] using heDivQ
    exact hq (le_bot_iff.mp (Ideal.dvd_iff_le.mp hbotdiv))
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors he0 ha,
    qs_factor_product_normalizedFactors_M2 q hq s hs,
    Multiset.le_iff_subset s.nodup]
  constructor
  · intro h p hp
    have hpA : p ∈ UniqueFactorizationMonoid.normalizedFactors a := h hp
    exact Ideal.dvd_iff_le.mpr ((Ideal.mem_normalizedFactors_iff ha).mp hpA).2
  · intro h p hp
    have hpq : p ∈ UniqueFactorizationMonoid.normalizedFactors q :=
      Multiset.mem_toFinset.mp (hs (by simpa using hp))
    have hpqSpec := (Ideal.mem_normalizedFactors_iff hq).mp hpq
    exact (Ideal.mem_normalizedFactors_iff ha).mpr
      ⟨hpqSpec.1, Ideal.dvd_iff_le.mp (h p (by simpa using hp))⟩

private theorem qs_series_supported_norm_summable_M2
    (X : ℝ) (hX : 0 < X) (g : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ)
    (hg : ∀ I, 5 / 2 ≤ (Ideal.absNorm I.1 : ℝ) / X → g I = 0) : Summable g := by
  classical
  let T : ℕ := Nat.ceil (3 * X)
  let B : Set {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    (fun I => I.1) ⁻¹' {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ T}
  have hB : B.Finite := by
    let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → Ideal (𝓞 K) := Subtype.val
    let S : Set (Ideal (𝓞 K)) := {I | Ideal.absNorm I ≤ T}
    have hS : S.Finite := by simpa [S] using
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) T)
    have hpre : (f ⁻¹' S).Finite :=
      Set.Finite.preimage (f := f) (s := S) Subtype.val_injective.injOn hS
    simpa [B, f, S] using hpre
  have hsupport : Function.support g ⊆ B := by
    intro I hI
    by_contra hnot
    have hnorm : T < Ideal.absNorm I.1 := lt_of_not_ge hnot
    have hnormR : (T : ℝ) < (Ideal.absNorm I.1 : ℝ) := by exact_mod_cast hnorm
    have hTX : 3 * X ≤ (T : ℝ) := by
      dsimp [T]
      exact Nat.le_ceil _
    have harg : 5 / 2 ≤ (Ideal.absNorm I.1 : ℝ) / X := by
      apply (le_div_iff₀ hX).2
      exact (calc
        (5 / 2 : ℝ) * X ≤ 3 * X := by gcongr; norm_num
        _ ≤ (T : ℝ) := hTX
        _ < (Ideal.absNorm I.1 : ℝ) := hnormR).le
    exact (Function.mem_support.mp hI) (hg I harg)
  have hfin : (Function.support g).Finite := hB.subset hsupport
  exact summable_of_hasFiniteSupport hfin

private noncomputable def qs_divisible_ideal_equiv_M2 (e : Ideal (𝓞 K)) (he : e ≠ ⊥) :
    {b : Ideal (𝓞 K) // b ≠ ⊥} ≃
      {a : {a : Ideal (𝓞 K) // a ≠ ⊥} // e ∣ a.1} where
  toFun b := ⟨⟨e * b.1, by simpa using mul_ne_zero he b.2⟩, ⟨b.1, rfl⟩⟩
  invFun a := ⟨Classical.choose a.2, by
    intro hzero
    apply a.1.2
    rw [Classical.choose_spec a.2, hzero]
    simp⟩
  left_inv b := by
    apply Subtype.ext
    apply mul_left_cancel₀ he
    exact (Classical.choose_spec (show e ∣ e * b.1 from ⟨b.1, rfl⟩)).symm
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec a.2).symm

open Classical in
private theorem qs_divisible_smooth_reindex_M2
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (W : ℝ → ℝ) (e : Ideal (𝓞 K))
    (he : e ≠ ⊥) (M : ℝ) (hM : 0 < M) :
    (∑' a : {a : Ideal (𝓞 K) // a ≠ ⊥},
      if e ∣ a.1 then χ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0) =
      χ.idealValue e *
        ∑' b : {b : Ideal (𝓞 K) // b ≠ ⊥},
          χ.idealValue b.1 * (W (qsN b.1 / (M / qsN e)) : ℂ) := by
  classical
  let N := {a : Ideal (𝓞 K) // a ≠ ⊥}
  let s : Set N := {a | e ∣ a.1}
  let D := {a : N // a ∈ s}
  let E := qs_divisible_ideal_equiv_M2 e he
  have heNorm : 0 < qsN e := by
    have he' : e ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa [Ideal.zero_eq_bot] using he)
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors ⟨e, he'⟩
  have hX : 0 < M / qsN e := div_pos hM heNorm
  let f : N → ℂ := fun a => χ.idealValue a.1 * (W (qsN a.1 / M) : ℂ)
  have hsumSub :
      (∑' a : D, χ.idealValue a.1.1 * (W (qsN a.1.1 / M) : ℂ)) =
        ∑' a : {a : Ideal (𝓞 K) // a ≠ ⊥},
          if e ∣ a.1 then χ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0 := by
    calc
      _ = ∑' a : N, s.indicator f a := tsum_subtype s f
      _ = _ := by
        apply tsum_congr
        intro a
        simp [s, f, Set.indicator_apply]
  have hreindex :
      (∑' a : D, χ.idealValue a.1.1 * (W (qsN a.1.1 / M) : ℂ)) =
        ∑' b : {b : Ideal (𝓞 K) // b ≠ ⊥},
          χ.idealValue (e * b.1) * (W (qsN (e * b.1) / M) : ℂ) := by
    change (∑' a : {a : N // e ∣ a.1}, χ.idealValue a.1.1 *
      (W (qsN a.1.1 / M) : ℂ)) = _
    simpa [E, qs_divisible_ideal_equiv_M2] using
      (E.tsum_eq (fun a : D => χ.idealValue a.1.1 * (W (qsN a.1.1 / M) : ℂ))).symm
  rw [← hsumSub, hreindex]
  have hmulN (b : {b : Ideal (𝓞 K) // b ≠ ⊥}) :
      qsN (e * b.1) = qsN e * qsN b.1 := by
    simp [qsN, map_mul]
  have hscale (b : {b : Ideal (𝓞 K) // b ≠ ⊥}) :
      qsN (e * b.1) / M = qsN b.1 / (M / qsN e) := by
    rw [hmulN]
    field_simp [ne_of_gt hM, ne_of_gt heNorm] <;> ring
  have hterm (b : {b : Ideal (𝓞 K) // b ≠ ⊥}) :
      χ.idealValue (e * b.1) * (W (qsN (e * b.1) / M) : ℂ) =
        χ.idealValue e * (χ.idealValue b.1 * (W (qsN b.1 / (M / qsN e)) : ℂ)) := by
    rw [qs_idealValue_mul_M0 χ e b.1 he b.2, hscale]
    ring
  simp_rw [hterm]
  rw [← tsum_mul_left]

set_option maxHeartbeats 1000000 in
private theorem qs_transform_sum_bound_M2 [IsTotallyComplex K] (W : ℝ → ℝ)
    (hW : IsCapWeight W) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 0 < Y →
      Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ‖qsTransform K (fun x => (W x : ℂ)) ((Ideal.absNorm I.1 : ℝ) / Y)‖) ∧
      (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ‖qsTransform K (fun x => (W x : ℂ)) ((Ideal.absNorm I.1 : ℝ) / Y)‖) ≤
          C * Y * (1 + Y) ^ η := by
  classical
  let η₀ : ℝ := min (η / 4) (1 / 4)
  have hη₀ : 0 < η₀ := by
    dsimp [η₀]
    exact lt_min (by positivity) (by norm_num)
  have hη₀η : η₀ ≤ η / 4 := min_le_left _ _
  have hη₀small : η₀ ≤ 1 / 4 := min_le_right _ _
  let H : ℝ → ℂ := qsTransform K (fun x => (W x : ℂ))
  obtain ⟨_, ⟨Cw, hCwpos, hCw⟩⟩ :=
    qs_transform_bounds_P0 (K := K) (fun x => (W x : ℂ)) hW.1 2 0 η₀ hη₀
  obtain ⟨Ccnt, hCcntpos, hCcnt⟩ := qs_ideal_count_M1 (K := K) η₀ hη₀
  obtain ⟨Ctail, hCtailpos, hCtail⟩ :=
    qs_tail_bound_M1 (K := K) η₀ 2 hη₀ (by nlinarith [hη₀small])
  let C : ℝ := 2 * (Cw * Ccnt * (2 : ℝ) ^ (1 + η₀) + Ctail * Cw) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Y hY
  let z : ℝ := max 1 Y
  let n : ℕ := Nat.ceil z
  let T : ℝ := (n : ℝ)
  have hTlow : z ≤ T := by
    dsimp [T, n, z]
    exact Nat.le_ceil _
  have hTup : T < z + 1 := by
    dsimp [T, n, z]
    exact Nat.ceil_lt_add_one (by positivity)
  have hTpos : 0 < T := by linarith [show 1 ≤ z from le_max_left 1 Y]
  have hTge1 : 1 ≤ T := by linarith [show 1 ≤ z from le_max_left 1 Y]
  have hcntT :
      (((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n).toFinset.card : ℕ) : ℝ) ≤
        Ccnt * T ^ (1 + η₀) := by
    have h := hCcnt T hTge1
    simpa [T] using h
  let low : Finset (Ideal (𝓞 K)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n).toFinset
  have hlowmem (I : Ideal (𝓞 K)) : I ∈ low ↔ (Ideal.absNorm I : ℝ) ≤ T := by
    simp [low, T]
  have hlowCard : (low.card : ℝ) ≤ Ccnt * T ^ (1 + η₀) := hcntT
  have hHsmall (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
      ‖H x‖ ≤ Cw * x ^ (-η₀) := by
    have h := (hCw x hx).1 hx1
    simpa [H, iteratedDeriv_zero] using h
  have hHlarge (x : ℝ) (hx : 0 < x) (hx1 : 1 ≤ x) :
      ‖H x‖ ≤ Cw * x ^ (-(2 : ℝ)) := by
    have h := (hCw x hx).2 hx1
    simpa [H, iteratedDeriv_zero] using h
  have hdecay : ∀ x : ℝ, 1 ≤ x → ‖H x‖ ≤ Cw * x ^ (-(2 : ℝ)) := by
    intro x hx
    exact hHlarge x (by linarith) hx
  have htail := hCtail H Cw Y T (by positivity) hY (by
    rw [max_le_iff]
    exact ⟨hTge1, le_trans (le_max_right 1 Y) hTlow⟩) hdecay
  let Tail₀ := {I : Ideal (𝓞 K) // I ∉ low}
  let Tail₁ := {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ T < (Ideal.absNorm I : ℝ)}
  have hbotLow : (⊥ : Ideal (𝓞 K)) ∈ low :=
    (hlowmem ⊥).2 (by simp [T])
  have hTail_ne (I : Tail₀) : I.1 ≠ ⊥ := by
    intro hbot
    exact I.2 (by simpa [hbot] using hbotLow)
  let e : Tail₀ ≃ Tail₁ := {
    toFun := fun I => ⟨I.1, ⟨hTail_ne I, by
      apply lt_of_not_ge
      intro hle
      exact I.2 ((hlowmem I.1).mpr hle)⟩⟩
    invFun := fun I => ⟨I.1, by
      intro hmem
      have hle := (hlowmem I.1).mp hmem
      exact (not_lt_of_ge hle) I.2.2⟩
    left_inv := by intro I; apply Subtype.ext; rfl
    right_inv := by intro I; apply Subtype.ext; rfl
  }
  let g : Ideal (𝓞 K) → ℝ := fun I =>
    if I = ⊥ then 0 else ‖H ((Ideal.absNorm I : ℝ) / Y)‖
  have htailComp : Summable (fun I : Tail₀ => g I.1) := by
    have hc := htail.1.comp_injective e.injective
    have hcomp : Summable (fun I : Tail₀ => ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖) := by
      convert hc using 1
      funext I
      rfl
    convert hcomp using 1
    funext I
    simp [g, hTail_ne I]
  have hlowSum : Summable (fun I : {I : Ideal (𝓞 K) // I ∈ low} => g I.1) := Summable.of_finite
  have hsumAll : Summable g := Summable.add_compl hlowSum htailComp
  have htailEq :
      (∑' I : Tail₀, g I.1) =
        ∑' I : Tail₁, ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖ := by
    simpa [g, e, hTail_ne] using e.tsum_eq (fun I : Tail₁ => ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖)
  have hnormPos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : 1 ≤ (Ideal.absNorm I : ℝ) := by
    have hn : Ideal.absNorm I ≠ 0 := by
      intro h
      exact hI ((Ideal.absNorm_eq_zero_iff.mp h))
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hlowPoint : ∀ I ∈ low,
      g I ≤
        Cw * (if 1 ≤ Y then (1 + Y) ^ η₀ else Y ^ (2 : ℝ)) := by
    intro I hI
    by_cases hIbot : I = ⊥
    · simp [g, hIbot]
      split_ifs <;> positivity
    have hIpos := hnormPos I hIbot
    have hYpos : 0 < (Ideal.absNorm I : ℝ) / Y := div_pos (by positivity) hY
    by_cases hY1 : 1 ≤ Y
    · let x := (Ideal.absNorm I : ℝ) / Y
      by_cases hx1 : x ≤ 1
      · have hxinv : x⁻¹ ≤ Y := by
          dsimp [x]
          rw [inv_div]
          -- the inverse scale is at most Y because the ideal norm is at least one
          have : Y ≤ Y * (Ideal.absNorm I : ℝ) := by nlinarith [hY, hIpos]
          exact (div_le_iff₀ (by positivity : 0 < (Ideal.absNorm I : ℝ))).2 this
        have hrpow : x ^ (-η₀) ≤ Y ^ η₀ := by
          rw [Real.rpow_neg_eq_inv_rpow]
          exact Real.rpow_le_rpow (by positivity) hxinv hη₀.le
        have hsmall := hHsmall x hYpos hx1
        have hYpow : Y ^ η₀ ≤ (1 + Y) ^ η₀ :=
          Real.rpow_le_rpow (by positivity) (by linarith) hη₀.le
        have := hsmall.trans (mul_le_mul_of_nonneg_left (hrpow.trans hYpow) hCwpos.le)
        simpa [g, x, hIbot, hY1] using this
      · have hx : 1 ≤ x := le_of_not_ge hx1
        have hlarge := hHlarge x (by linarith [hx]) hx
        have hdec : x ^ (-(2 : ℝ)) ≤ 1 := by
          simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : 0 < (1 : ℝ)) hx
            (by norm_num : (-(2 : ℝ)) ≤ 0)
        have hone : 1 ≤ (1 + Y) ^ η₀ := Real.one_le_rpow (by linarith) hη₀.le
        have hle : Cw * x ^ (-(2 : ℝ)) ≤ Cw * (1 + Y) ^ η₀ :=
          mul_le_mul_of_nonneg_left (hdec.trans hone) hCwpos.le
        simpa [g, x, hIbot, hY1] using hlarge.trans hle
    · have hYlt : Y < 1 := lt_of_not_ge hY1
      let x := (Ideal.absNorm I : ℝ) / Y
      have hx : 1 ≤ x := by
        dsimp [x]
        exact (le_div_iff₀ hY).2 (by linarith [hIpos])
      have hlarge := hHlarge x (by linarith [hx]) hx
      have hxinv : x⁻¹ ≤ Y := by
        dsimp [x]
        rw [inv_div]
        have : Y ≤ Y * (Ideal.absNorm I : ℝ) := by nlinarith [hY, hIpos]
        exact (div_le_iff₀ (by positivity : 0 < (Ideal.absNorm I : ℝ))).2 this
      have hdec : x ^ (-(2 : ℝ)) ≤ Y ^ (2 : ℝ) := by
        rw [Real.rpow_neg_eq_inv_rpow]
        exact Real.rpow_le_rpow (by positivity) hxinv (by norm_num)
      simpa [g, x, hIbot, hY1] using
        hlarge.trans (mul_le_mul_of_nonneg_left hdec hCwpos.le)
  have hlowTotal :
      (∑ I ∈ low, g I) ≤
        (low.card : ℝ) *
          (Cw * (if 1 ≤ Y then (1 + Y) ^ η₀ else Y ^ (2 : ℝ))) := by
    calc
      _ ≤ low.card •
          (Cw * (if 1 ≤ Y then (1 + Y) ^ η₀ else Y ^ (2 : ℝ))) :=
        Finset.sum_le_card_nsmul low _ _ hlowPoint
      _ = _ := by simp [nsmul_eq_mul, mul_comm]
  have hsplit := hsumAll.sum_add_tsum_subtype_compl low
  have htailBound := htail.2
  have hsum : Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖) := by
    have hs := hsumAll.subtype (fun I : Ideal (𝓞 K) => I ≠ ⊥)
    convert hs using 1
    funext I
    simp [g, I.2]
  refine ⟨hsum, ?_⟩
  have htsum :
      (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖) = ∑' I : Ideal (𝓞 K), g I := by
    calc
      _ = ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, g I.1 := by
        congr 1
        funext I
        simp [g, I.2]
      _ = ∑' I : Ideal (𝓞 K), ({I : Ideal (𝓞 K) | I ≠ ⊥}.indicator g) I := by
        change (∑' I : {I : Ideal (𝓞 K) // I ∈ {I : Ideal (𝓞 K) | I ≠ ⊥}}, g I.1) = _
        exact tsum_subtype {I : Ideal (𝓞 K) | I ≠ ⊥} g
      _ = _ := by
        apply tsum_congr
        intro I
        by_cases hI : I = ⊥ <;> simp [g, hI]
  rw [htsum, ← hsplit, htailEq]
  by_cases hY1 : 1 ≤ Y
  · have hz : z = Y := max_eq_right hY1
    have hTle : T ≤ 2 * Y := by
      dsimp [T, n]
      rw [hz]
      exact (Nat.ceil_lt_add_one hY.le).le.trans (by nlinarith)
    have hpow : T ^ (1 + η₀) ≤ (2 * Y) ^ (1 + η₀) := by
      apply Real.rpow_le_rpow (by positivity) hTle
      positivity
    have hmul : (2 * Y) ^ (1 + η₀) = 2 ^ (1 + η₀) * Y ^ (1 + η₀) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    have hYPow : Y ^ (1 + η₀) ≤ Y * (1 + Y) ^ η₀ := by
      rw [Real.rpow_add hY]
      simp only [Real.rpow_one]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) hη₀.le) (by positivity)
    have hEtaPow : (1 + Y) ^ (2 * η₀) ≤ (1 + Y) ^ η := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      nlinarith [hη₀η]
    have hlow :
        (∑ I ∈ low, g I) ≤
          Cw * Ccnt * 2 ^ (1 + η₀) * (Y * (1 + Y) ^ η) := by
      calc
        _ ≤ (Ccnt * T ^ (1 + η₀)) * (Cw * (1 + Y) ^ η₀) := by
          have hL := hlowTotal
          simp [hY1] at hL
          exact hL.trans (mul_le_mul_of_nonneg_right hlowCard
            (by positivity : 0 ≤ Cw * (1 + Y) ^ η₀))
        _ ≤ Ccnt * ((2 * Y) ^ (1 + η₀)) * (Cw * (1 + Y) ^ η₀) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ Ccnt))
            (by positivity : 0 ≤ Cw * (1 + Y) ^ η₀)
        _ = Cw * Ccnt * 2 ^ (1 + η₀) * Y ^ (1 + η₀) * (1 + Y) ^ η₀ := by
          rw [hmul]
          ring
        _ ≤ Cw * Ccnt * 2 ^ (1 + η₀) *
              (Y * (1 + Y) ^ η₀) * (1 + Y) ^ η₀ := by
          have hmid :
              Cw * Ccnt * 2 ^ (1 + η₀) * Y ^ (1 + η₀) * (1 + Y) ^ η₀ ≤
                Cw * Ccnt * 2 ^ (1 + η₀) *
                  (Y * (1 + Y) ^ η₀) * (1 + Y) ^ η₀ := by
            calc
              _ = (Cw * Ccnt * 2 ^ (1 + η₀) * (1 + Y) ^ η₀) * Y ^ (1 + η₀) := by ring
              _ ≤ (Cw * Ccnt * 2 ^ (1 + η₀) * (1 + Y) ^ η₀) *
                    (Y * (1 + Y) ^ η₀) :=
                mul_le_mul_of_nonneg_left hYPow (by positivity)
              _ = _ := by ring
          exact hmid
        _ ≤ Cw * Ccnt * 2 ^ (1 + η₀) *
              (Y * (1 + Y) ^ (2 * η₀)) := by
          have hpowSquare :
              (1 + Y) ^ η₀ * (1 + Y) ^ η₀ = (1 + Y) ^ (2 * η₀) := by
            rw [← Real.rpow_add (by positivity : 0 < 1 + Y)]
            ring
          calc
            _ = Cw * Ccnt * 2 ^ (1 + η₀) *
                (Y * ((1 + Y) ^ η₀ * (1 + Y) ^ η₀)) := by ring
            _ ≤ _ := by
              apply le_of_eq
              rw [hpowSquare]
        _ ≤ _ := by
          have hcoef : 0 ≤ Cw * Ccnt * 2 ^ (1 + η₀) * Y := by positivity
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hEtaPow hcoef
    have htail' :
        (∑' I : Tail₁, ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖) ≤
          Ctail * Cw * (Y * (1 + Y) ^ η) := by
      calc
        _ ≤ Ctail * Cw * Y ^ (2 : ℝ) * T ^ (1 + η₀ - 2) := htailBound
        _ ≤ Ctail * Cw * Y ^ (2 : ℝ) * Y ^ (1 + η₀ - 2) := by
          have hTy : Y ≤ T := by
            exact (le_trans (le_max_right 1 Y) hTlow)
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hY hTy (by nlinarith [hη₀small]))
            (by positivity : 0 ≤ Ctail * Cw * Y ^ (2 : ℝ))
        _ = Ctail * Cw * (Y ^ (1 + η₀)) := by
          have hpow : Y ^ (2 : ℝ) * Y ^ (1 + η₀ - 2) = Y ^ (1 + η₀) := by
            rw [← Real.rpow_add hY]
            congr 1 <;> ring
          calc
            _ = Ctail * Cw * (Y ^ (2 : ℝ) * Y ^ (1 + η₀ - 2)) := by ring
            _ = _ := by rw [hpow]
        _ ≤ Ctail * Cw * (Y * (1 + Y) ^ η) := by
          have hpowEta : η₀ ≤ η := by nlinarith [hη₀η, hη]
          have hpowScale : Y ^ (1 + η₀) ≤ Y * (1 + Y) ^ η := by
            rw [Real.rpow_add hY]
            simp only [Real.rpow_one]
            have hYpow : Y ^ η₀ ≤ (1 + Y) ^ η₀ :=
              Real.rpow_le_rpow (by positivity) (by linarith) hη₀.le
            have hbase : (1 : ℝ) ≤ 1 + Y := by linarith [hY]
            have hpowBase : (1 + Y) ^ η₀ ≤ (1 + Y) ^ η :=
              Real.rpow_le_rpow_of_exponent_le hbase hpowEta
            exact mul_le_mul_of_nonneg_left
              (hYpow.trans hpowBase) (by positivity)
          exact mul_le_mul_of_nonneg_left hpowScale
            (by positivity : 0 ≤ Ctail * Cw)
    have hsumBound :
        (∑ I ∈ low, g I) +
          ∑' I : Tail₁, ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖ ≤
            C * Y * (1 + Y) ^ η := by
      have hcoef : Cw * Ccnt * 2 ^ (1 + η₀) + Ctail * Cw ≤ C := by
        dsimp [C]
        nlinarith [show 0 ≤ Cw * Ccnt * 2 ^ (1 + η₀) + Ctail * Cw by positivity]
      have hbase : 0 ≤ Y * (1 + Y) ^ η := by positivity
      calc
        _ ≤ (Cw * Ccnt * 2 ^ (1 + η₀) + Ctail * Cw) *
              (Y * (1 + Y) ^ η) := by
          exact (add_le_add hlow htail').trans_eq (by ring)
        _ ≤ C * (Y * (1 + Y) ^ η) := mul_le_mul_of_nonneg_right hcoef hbase
        _ = C * Y * (1 + Y) ^ η := by ring
    exact hsumBound
  · have hYlt : Y < 1 := lt_of_not_ge hY1
    have hz : z = 1 := max_eq_left (le_of_lt hYlt)
    have hTle : T ≤ 2 := by
      dsimp [T, n]
      rw [hz]
      norm_num [Nat.ceil]
    have hTneg : T ^ (1 + η₀ - 2) ≤ 1 := by
      calc
        _ ≤ (1 : ℝ) ^ (1 + η₀ - 2) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hTge1 (by nlinarith [hη₀small])
        _ = 1 := by simp
    have hlow :
        (∑ I ∈ low, g I) ≤
          Ccnt * 2 ^ (1 + η₀) * Cw * Y ^ (2 : ℝ) := by
      have hL := hlowTotal
      simp only [if_neg hY1] at hL
      calc
        _ ≤ (Ccnt * T ^ (1 + η₀)) * (Cw * Y ^ (2 : ℝ)) := by
          exact hL.trans (mul_le_mul_of_nonneg_right hlowCard
            (by positivity : 0 ≤ Cw * Y ^ (2 : ℝ)))
        _ ≤ Ccnt * 2 ^ (1 + η₀) * (Cw * Y ^ (2 : ℝ)) := by
          gcongr
        _ = _ := by ring
    have htail' :
        (∑' I : Tail₁, ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖) ≤
          Ctail * Cw * Y ^ (2 : ℝ) := by
      calc
        _ ≤ Ctail * Cw * Y ^ (2 : ℝ) * T ^ (1 + η₀ - 2) := htailBound
        _ ≤ Ctail * Cw * Y ^ (2 : ℝ) := by
          simpa using mul_le_mul_of_nonneg_left hTneg
            (by positivity : 0 ≤ Ctail * Cw * Y ^ (2 : ℝ))
    have hsumBound :
        (∑ I ∈ low, g I) +
          ∑' I : Tail₁, ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖ ≤
            C * Y * (1 + Y) ^ η := by
      have hY2 : Y ^ (2 : ℝ) ≤ Y := by
        have hYle1 : Y ≤ 1 := le_of_not_ge hY1
        have hpow : Y ^ (2 : ℝ) ≤ Y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (x := Y) (y := (2 : ℝ)) (z := (1 : ℝ))
            hY hYle1 (by norm_num)
        simpa using hpow
      have hone : 1 ≤ (1 + Y) ^ η := Real.one_le_rpow (by linarith) hη.le
      have hlowY :
          (∑ I ∈ low, g I) ≤ Ccnt * 2 ^ (1 + η₀) * Cw * Y := by
        calc
          _ ≤ Ccnt * 2 ^ (1 + η₀) * Cw * Y ^ (2 : ℝ) := hlow
          _ ≤ Ccnt * 2 ^ (1 + η₀) * Cw * Y := by
            exact mul_le_mul_of_nonneg_left hY2 (by positivity)
      have htailY :
          (∑' I : Tail₁, ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖) ≤ Ctail * Cw * Y := by
        calc
          _ ≤ Ctail * Cw * Y ^ (2 : ℝ) := htail'
          _ ≤ Ctail * Cw * Y :=
            mul_le_mul_of_nonneg_left hY2 (by positivity : 0 ≤ Ctail * Cw)
      have hcoef : Ccnt * 2 ^ (1 + η₀) * Cw + Ctail * Cw ≤ C := by
        dsimp [C]
        nlinarith [show 0 ≤ Ccnt * 2 ^ (1 + η₀) * Cw + Ctail * Cw by positivity]
      have hsumY :
          (∑ I ∈ low, g I) + ∑' I : Tail₁,
            ‖H ((Ideal.absNorm I.1 : ℝ) / Y)‖ ≤
            (Ccnt * 2 ^ (1 + η₀) * Cw + Ctail * Cw) * Y := by
        calc
          _ ≤ Ccnt * 2 ^ (1 + η₀) * Cw * Y + Ctail * Cw * Y :=
            add_le_add hlowY htailY
          _ = _ := by ring
      calc
        _ ≤ (Ccnt * 2 ^ (1 + η₀) * Cw + Ctail * Cw) * Y := hsumY
        _ ≤ C * Y := mul_le_mul_of_nonneg_right hcoef (le_of_lt hY)
        _ ≤ C * Y * (1 + Y) ^ η := by
          simpa using mul_le_mul_of_nonneg_left hone (by positivity : 0 ≤ C * Y)
    exact hsumBound

private theorem qs_primitive_smooth_sum_bound_M2 [IsTotallyComplex K]
    (W : ℝ → ℝ) (hW : IsCapWeight W) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
      (X : ℝ), IsPrimitiveConductor χ f → χ ^ 2 = 1 → χ ≠ 1 →
      (∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1) → 0 < X →
      ‖∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
          χ.idealValue a.1 * (W ((Ideal.absNorm a.1 : ℝ) / X) : ℂ)‖ ≤
        C * Real.sqrt (qsN f) * (1 + qsN f / X) ^ η := by
  classical
  obtain ⟨Csum, hCsumpos, hCsum⟩ := qs_transform_sum_bound_M2 (K := K) W hW η hη
  refine ⟨Csum, hCsumpos, ?_⟩
  intro χ f X hf hsq hne hinf hX
  have hf0 : f ≠ ⊥ := hf.1
  have hnfNat : 0 < Ideal.absNorm f := by
    have hfnz : Ideal.absNorm f ≠ 0 := by
      intro h
      exact hf0 (Ideal.absNorm_eq_zero_iff.mp h)
    exact Nat.pos_of_ne_zero hfnz
  have hnf : 0 < qsN f := by exact_mod_cast hnfNat
  let Y : ℝ := qsN f / X
  have hY : 0 < Y := div_pos hnf hX
  let h : ℝ → ℂ := fun x => (W x : ℂ)
  have hh : IsQSWeight h := hW.1
  obtain ⟨hdual, hpoisson⟩ :=
    qs_primitive_smooth_poisson_P1 (K := K) χ f hf hsq hne hinf h hh X hX
  have htrans := hCsum Y hY
  have htrans' :
      Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ‖qsTransform K h ((Ideal.absNorm I.1 : ℝ) / Y)‖) ∧
      (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ‖qsTransform K h ((Ideal.absNorm I.1 : ℝ) / Y)‖) ≤
          Csum * Y * (1 + Y) ^ η := by simpa [h] using htrans
  have harg (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      X * (Ideal.absNorm a.1 : ℝ) / qsN f =
        (Ideal.absNorm a.1 : ℝ) / Y := by
    dsimp [Y]
    field_simp [ne_of_gt hnf, ne_of_gt hX] <;> ring
  have hdualBound :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ‖χ.idealValue a.1 *
          qsTransform K h (X * (Ideal.absNorm a.1 : ℝ) / qsN f)‖) ≤
        Csum * Y * (1 + Y) ^ η := by
    calc
      _ ≤ ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ‖qsTransform K h ((Ideal.absNorm a.1 : ℝ) / Y)‖ := by
        apply hdual.tsum_le_tsum ?_ htrans'.1
        intro a
        rw [norm_mul, harg a]
        have hχ := qs_idealValue_norm_le_one χ hsq a.1
        calc
          ‖χ.idealValue a.1‖ * ‖qsTransform K h ((Ideal.absNorm a.1 : ℝ) / Y)‖ ≤
              1 * ‖qsTransform K h ((Ideal.absNorm a.1 : ℝ) / Y)‖ :=
            mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
          _ = _ := by ring
      _ ≤ Csum * Y * (1 + Y) ^ η := htrans'.2
  have hdualC : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      χ.idealValue a.1 * qsTransform K h
        (X * (Ideal.absNorm a.1 : ℝ) / qsN f)) := by
    apply Summable.of_norm
    simpa only [harg] using hdual
  have hscalePos : 0 < X / Real.sqrt (qsN f) := div_pos hX (Real.sqrt_pos.2 hnf)
  have hnormScale : ‖((X / Real.sqrt (qsN f) : ℝ) : ℂ)‖ = X / Real.sqrt (qsN f) := by
    rw [Complex.norm_real]
    exact abs_of_pos hscalePos
  have hcancel :
      X / Real.sqrt (qsN f) * (Csum * Y * (1 + Y) ^ η) =
        Csum * Real.sqrt (qsN f) * (1 + Y) ^ η := by
    dsimp [Y]
    field_simp [ne_of_gt hX, ne_of_gt hnf, (Real.sqrt_pos.2 hnf).ne'] <;>
      rw [Real.sq_sqrt hnf.le] <;> ring
  calc
    _ = ‖((X / Real.sqrt (qsN f) : ℝ) : ℂ) *
          ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
            χ.idealValue a.1 * qsTransform K h
              (X * (Ideal.absNorm a.1 : ℝ) / qsN f)‖ := by rw [hpoisson]
    _ = (X / Real.sqrt (qsN f)) *
          ‖∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
            χ.idealValue a.1 * qsTransform K h
              (X * (Ideal.absNorm a.1 : ℝ) / qsN f)‖ := by rw [norm_mul, hnormScale]
    _ ≤ (X / Real.sqrt (qsN f)) * (Csum * Y * (1 + Y) ^ η) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hscalePos)
      exact (norm_tsum_le_tsum_norm hdual).trans hdualBound
    _ = Csum * Real.sqrt (qsN f) * (1 + Y) ^ η := hcancel

private theorem qsTot_factor_decomposition_M2 (W : ℝ → ℝ) (hW : IsCapWeight W)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (q : Ideal (𝓞 K))
    (hq : q ≠ ⊥) (M : ℝ) (hM : 0 < M) :
    qsTot (fun x => (W x : ℂ)) M q χ =
      ∑ s ∈ (UniqueFactorizationMonoid.normalizedFactors q).toFinset.powerset,
        (-1 : ℂ) ^ s.card * χ.idealValue (∏ p ∈ s, p) *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            χ.idealValue b.1 *
              (W ((Ideal.absNorm b.1 : ℝ) / (M / qsN (∏ p ∈ s, p))) : ℂ) := by
  classical
  let P := (UniqueFactorizationMonoid.normalizedFactors q).toFinset
  let F : Finset (Ideal (𝓞 K)) → {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun s a =>
    if (∏ p ∈ s, p) ∣ a.1 then
      (-1 : ℂ) ^ s.card *
        (χ.idealValue a.1 * (W ((Ideal.absNorm a.1 : ℝ) / M) : ℂ)) else 0
  have hpoint (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      (if IsCoprime a.1 q then
        χ.idealValue a.1 * (W ((Ideal.absNorm a.1 : ℝ) / M) : ℂ) else 0) =
      ∑ s ∈ P.powerset, F s a := by
    let term := χ.idealValue a.1 * (W ((Ideal.absNorm a.1 : ℝ) / M) : ℂ)
    have hcoef := qs_coprime_factor_sum_M2 q a.1 hq a.2
    have hcoefDiv :
        (if IsCoprime a.1 q then (1 : ℂ) else 0) =
          ∑ s ∈ P.powerset,
            if (∏ p ∈ s, p) ∣ a.1 then (-1 : ℂ) ^ s.card else 0 := by
      calc
        _ = ∑ s ∈ P.powerset,
              if ∀ p ∈ s, p ∣ a.1 then (-1 : ℂ) ^ s.card else 0 := by
          simpa [P] using hcoef
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s hs
          have hdiv := qs_factor_product_divides_iff_M2 q a.1 hq a.2 s
            (Finset.mem_powerset.mp hs)
          by_cases hd : (∏ p ∈ s, p) ∣ a.1
          · have hall := hdiv.mp hd
            simp only [if_pos hd, if_pos hall]
          · have hnall : ¬ ∀ p ∈ s, p ∣ a.1 := fun hall => hd (hdiv.mpr hall)
            simp only [if_neg hd, if_neg hnall]
    have hscale :
        term * (if IsCoprime a.1 q then (1 : ℂ) else 0) =
          ∑ s ∈ P.powerset, F s a := by
      calc
        _ = term * (∑ s ∈ P.powerset,
              if (∏ p ∈ s, p) ∣ a.1 then (-1 : ℂ) ^ s.card else 0) := by rw [hcoefDiv]
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hd : (∏ p ∈ s, p) ∣ a.1 <;> simp [F, term, hd, mul_assoc, mul_comm, mul_left_comm]
    calc
      _ = term * (if IsCoprime a.1 q then (1 : ℂ) else 0) := by
        by_cases hc : IsCoprime a.1 q <;> simp [term, hc]
      _ = _ := hscale
  have hseries (s : Finset (Ideal (𝓞 K))) (hs : s ∈ P.powerset) :
      Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} => F s a) := by
    apply qs_series_supported_norm_summable_M2 M hM
    intro a ha
    have hW0 := hW.2.2.2 ((Ideal.absNorm a.1 : ℝ) / M) ha
    simp [F, hW0]
  have hswap := Summable.tsum_finsetSum (s := P.powerset) hseries
  unfold qsTot
  calc
    _ = ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, ∑ s ∈ P.powerset, F s a := by
      apply tsum_congr
      intro a
      exact hpoint a
    _ = ∑ s ∈ P.powerset, ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, F s a := hswap
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      let e := ∏ p ∈ s, p
      have hdivQ := qs_factor_subset_product_dvd_M2 q hq s (Finset.mem_powerset.mp hs)
      have he : e ≠ ⊥ := by
        intro hebot
        have hbotdiv : (⊥ : Ideal (𝓞 K)) ∣ q := by simpa [e, hebot] using hdivQ
        exact hq (le_bot_iff.mp (Ideal.dvd_iff_le.mp hbotdiv))
      have hsumEq :
          (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, F s a) =
            (-1 : ℂ) ^ s.card *
              ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
                if e ∣ a.1 then χ.idealValue a.1 *
                  (W ((Ideal.absNorm a.1 : ℝ) / M) : ℂ) else 0 := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro a
        simp [F, e]
      rw [hsumEq, qs_divisible_smooth_reindex_M2 χ W e he M hM]
      simp [e, mul_assoc]

/-- M2a (IMPL over P1): the smooth kernel of a nonprincipal primitive quadratic character,
`|Σ'_{(a,𝔮)=1} W(N a/M) χ(a)| ≪_η (N𝔮 · N f)^η √(N f)`, uniformly in `M ≥ 1`. -/
theorem qs_pair_kernel_bound_M2 [IsTotallyComplex K] (W : ℝ → ℝ) (hW : IsCapWeight W)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f 𝔮 : Ideal (𝓞 K)) (M : ℝ),
      IsPrimitiveConductor χ f → χ ^ 2 = 1 → χ ≠ 1 →
      (∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1) →
      Squarefree 𝔮 → IsCoprime 𝔮 f → 1 ≤ M →
      ‖qsTot (fun x => (W x : ℂ)) M 𝔮 χ‖ ≤
        C * (qsN 𝔮 * qsN f) ^ η * Real.sqrt (qsN f) := by
  classical
  let β : ℝ := η / 4
  let γ : ℝ := η / 4
  have hβ : 0 < β := by dsimp [β]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨Cprim, hCprimpos, hprim⟩ := qs_primitive_smooth_sum_bound_M2 (K := K) W hW β hβ
  obtain ⟨Cdiv, hCdivpos, hdivisor⟩ := qs_divisor_bound_M1 (K := K) γ hγ
  let C : ℝ := Cprim * Cdiv * (2 : ℝ) ^ β
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro χ f 𝔮 M hf hsq hne hinf hqsf hqf hM
  have hq0 : 𝔮 ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using hqsf.ne_zero
  have hf0 : f ≠ ⊥ := hf.1
  have hqNat : Ideal.absNorm 𝔮 ≠ 0 := by
    intro h
    exact hq0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hfNat : Ideal.absNorm f ≠ 0 := by
    intro h
    exact hf0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hqN : 1 ≤ qsN 𝔮 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hqNat)
  have hfN : 1 ≤ qsN f := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hfNat)
  have hqPos : 0 < qsN 𝔮 := by exact_mod_cast Nat.pos_of_ne_zero hqNat
  have hfPos : 0 < qsN f := by exact_mod_cast Nat.pos_of_ne_zero hfNat
  have hMpos : 0 < M := by linarith
  let P := (UniqueFactorizationMonoid.normalizedFactors 𝔮).toFinset
  have hdecomp := qsTot_factor_decomposition_M2 W hW χ 𝔮 hq0 M hMpos
  have hcard : ((P.powerset.card : ℕ) : ℝ) ≤ Cdiv * qsN 𝔮 ^ γ := by
    calc
      ((P.powerset.card : ℕ) : ℝ) ≤ ((qsDivisors 𝔮).card : ℝ) := by
        simpa [P] using qs_factor_subset_count_bound_M2 𝔮 hq0
      _ ≤ Cdiv * qsN 𝔮 ^ γ := hdivisor 𝔮 hq0
  have hprodN : 1 ≤ qsN 𝔮 * qsN f := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqN) (sub_nonneg.mpr hfN)]
  have hexp : β + γ ≤ η := by dsimp [β, γ]; nlinarith
  have hqPower : qsN 𝔮 ^ γ * (qsN 𝔮 * qsN f) ^ β ≤
      (qsN 𝔮 * qsN f) ^ η := by
    have hqBase : qsN 𝔮 ^ γ ≤ (qsN 𝔮 * qsN f) ^ γ :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [hfN]) hγ.le
    calc
      _ ≤ (qsN 𝔮 * qsN f) ^ γ * (qsN 𝔮 * qsN f) ^ β :=
        mul_le_mul_of_nonneg_right hqBase (by positivity)
      _ = (qsN 𝔮 * qsN f) ^ (γ + β) := by
        rw [← Real.rpow_add (by positivity : 0 < qsN 𝔮 * qsN f)]
      _ ≤ (qsN 𝔮 * qsN f) ^ η :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hprodN]) hexp
  have htermBound (s : Finset (Ideal (𝓞 K))) (hs : s ∈ P.powerset) :
      ‖(-1 : ℂ) ^ s.card * χ.idealValue (∏ p ∈ s, p) *
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          χ.idealValue b.1 *
            (W ((Ideal.absNorm b.1 : ℝ) / (M / qsN (∏ p ∈ s, p))) : ℂ)‖ ≤
        Cprim * (2 : ℝ) ^ β * Real.sqrt (qsN f) *
          (qsN 𝔮 * qsN f) ^ β := by
    let e : Ideal (𝓞 K) := ∏ p ∈ s, p
    have hdivQ := qs_factor_subset_product_dvd_M2 𝔮 hq0 s (Finset.mem_powerset.mp hs)
    have he0 : e ≠ ⊥ := by
      intro hebot
      have hbotdiv : (⊥ : Ideal (𝓞 K)) ∣ 𝔮 := by simpa [e, hebot] using hdivQ
      exact hq0 (le_bot_iff.mp (Ideal.dvd_iff_le.mp hbotdiv))
    have heNorm : 0 < qsN e := by
      have heNat : Ideal.absNorm e ≠ 0 := by
        intro h
        exact he0 (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.pos_of_ne_zero heNat
    have heNormLe : qsN e ≤ qsN 𝔮 := by
      have hdivNorm : Ideal.absNorm e ∣ Ideal.absNorm 𝔮 :=
        Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdivQ)
      have hleNat : Ideal.absNorm e ≤ Ideal.absNorm 𝔮 :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hqNat) hdivNorm
      exact_mod_cast hleNat
    let X : ℝ := M / qsN e
    have hX : 0 < X := div_pos hMpos heNorm
    have hsumBound := hprim χ f X hf hsq hne hinf hX
    have hfrac : qsN f / X ≤ qsN f * qsN 𝔮 := by
      have hscale : qsN f / X = (qsN f * qsN e) / M := by
        dsimp [X]
        field_simp [ne_of_gt hMpos, ne_of_gt heNorm] <;> ring
      rw [hscale]
      have hnum : qsN f * qsN e ≤ qsN f * qsN 𝔮 :=
        mul_le_mul_of_nonneg_left heNormLe (by positivity)
      exact (div_le_self (by positivity) hM).trans hnum
    have hbase : 1 + qsN f / X ≤ 2 * (qsN 𝔮 * qsN f) := by
      have hz : 1 ≤ qsN 𝔮 * qsN f := hprodN
      have hfrac' : qsN f / X ≤ qsN 𝔮 * qsN f := by simpa [mul_comm] using hfrac
      nlinarith
    have hpower : (1 + qsN f / X) ^ β ≤
        (2 * (qsN 𝔮 * qsN f)) ^ β :=
      Real.rpow_le_rpow (by positivity) hbase hβ.le
    have htwo : (2 * (qsN 𝔮 * qsN f)) ^ β =
        (2 : ℝ) ^ β * (qsN 𝔮 * qsN f) ^ β := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    have hprimitive := hsumBound
    have htermNorm :
        ‖(-1 : ℂ) ^ s.card * χ.idealValue e *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            χ.idealValue b.1 * (W ((Ideal.absNorm b.1 : ℝ) / X) : ℂ)‖ ≤
          Cprim * Real.sqrt (qsN f) * (1 + qsN f / X) ^ β := by
      have hsign : ‖(-1 : ℂ) ^ s.card‖ = 1 := by simp
      have hchar := qs_idealValue_norm_le_one χ hsq e
      calc
        _ = ‖(-1 : ℂ) ^ s.card‖ * ‖χ.idealValue e‖ *
            ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              χ.idealValue b.1 * (W ((Ideal.absNorm b.1 : ℝ) / X) : ℂ)‖ := by
          rw [norm_mul, norm_mul]
        _ = ‖χ.idealValue e‖ *
            ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              χ.idealValue b.1 * (W ((Ideal.absNorm b.1 : ℝ) / X) : ℂ)‖ := by rw [hsign]; ring
        _ ≤ 1 * ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              χ.idealValue b.1 * (W ((Ideal.absNorm b.1 : ℝ) / X) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
        _ = ‖∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              χ.idealValue b.1 * (W ((Ideal.absNorm b.1 : ℝ) / X) : ℂ)‖ := by simp
        _ ≤ Cprim * Real.sqrt (qsN f) * (1 + qsN f / X) ^ β := by
          simpa using hprimitive
    calc
      _ = ‖(-1 : ℂ) ^ s.card * χ.idealValue e *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              χ.idealValue b.1 * (W ((Ideal.absNorm b.1 : ℝ) / X) : ℂ)‖ := by
        simp [X, e]
      _ ≤ Cprim * Real.sqrt (qsN f) * (1 + qsN f / X) ^ β := htermNorm
      _ ≤ Cprim * Real.sqrt (qsN f) * (2 * (qsN 𝔮 * qsN f)) ^ β :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = Cprim * (2 : ℝ) ^ β * Real.sqrt (qsN f) *
            (qsN 𝔮 * qsN f) ^ β := by rw [htwo]; ring

  have htotal :
      ‖qsTot (fun x => (W x : ℂ)) M 𝔮 χ‖ ≤
        Cdiv * qsN 𝔮 ^ γ *
          (Cprim * (2 : ℝ) ^ β * Real.sqrt (qsN f) *
            (qsN 𝔮 * qsN f) ^ β) := by
    rw [qsTot_factor_decomposition_M2 W hW χ 𝔮 hq0 M hMpos]
    calc
      _ ≤ ∑ s ∈ P.powerset,
          ‖(-1 : ℂ) ^ s.card * χ.idealValue (∏ p ∈ s, p) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              χ.idealValue b.1 *
                (W ((Ideal.absNorm b.1 : ℝ) / (M / qsN (∏ p ∈ s, p))) : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ (P.powerset.card : ℝ) •
          (Cprim * (2 : ℝ) ^ β * Real.sqrt (qsN f) *
            (qsN 𝔮 * qsN f) ^ β) := by
        simpa [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul P.powerset
            (fun s => ‖(-1 : ℂ) ^ s.card * χ.idealValue (∏ p ∈ s, p) *
              ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
                χ.idealValue b.1 *
                  (W ((Ideal.absNorm b.1 : ℝ) / (M / qsN (∏ p ∈ s, p))) : ℂ)‖)
            (Cprim * (2 : ℝ) ^ β * Real.sqrt (qsN f) * (qsN 𝔮 * qsN f) ^ β)
            (by intro s hs; exact htermBound s hs))
      _ ≤ Cdiv * qsN 𝔮 ^ γ *
          (Cprim * (2 : ℝ) ^ β * Real.sqrt (qsN f) *
            (qsN 𝔮 * qsN f) ^ β) := by
        simpa [nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right hcard (by positivity :
            0 ≤ Cprim * (2 : ℝ) ^ β * Real.sqrt (qsN f) * (qsN 𝔮 * qsN f) ^ β)
  have hPowerProduct : qsN 𝔮 ^ γ * (qsN 𝔮 * qsN f) ^ β ≤
      (qsN 𝔮 * qsN f) ^ η := by
    have hqBase : qsN 𝔮 ^ γ ≤ (qsN 𝔮 * qsN f) ^ γ :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [hfN]) hγ.le
    have hExp : γ + β ≤ η := by dsimp [γ, β]; nlinarith
    calc
      _ ≤ (qsN 𝔮 * qsN f) ^ γ * (qsN 𝔮 * qsN f) ^ β :=
        mul_le_mul_of_nonneg_right hqBase (by positivity)
      _ = (qsN 𝔮 * qsN f) ^ (γ + β) := by
        rw [← Real.rpow_add (by positivity : 0 < qsN 𝔮 * qsN f)]
      _ ≤ (qsN 𝔮 * qsN f) ^ η :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [hprodN]) hExp
  have htotal' :
      Cdiv * qsN 𝔮 ^ γ *
          (Cprim * (2 : ℝ) ^ β * Real.sqrt (qsN f) *
            (qsN 𝔮 * qsN f) ^ β) ≤
        C * (qsN 𝔮 * qsN f) ^ η * Real.sqrt (qsN f) := by
    dsimp [C]
    calc
      _ = (Cprim * Cdiv * (2 : ℝ) ^ β * Real.sqrt (qsN f)) *
            (qsN 𝔮 ^ γ * (qsN 𝔮 * qsN f) ^ β) := by ring
      _ ≤ (Cprim * Cdiv * (2 : ℝ) ^ β * Real.sqrt (qsN f)) *
            (qsN 𝔮 * qsN f) ^ η :=
        mul_le_mul_of_nonneg_left hPowerProduct (by positivity)
      _ = Cprim * Cdiv * (2 : ℝ) ^ β *
            (qsN 𝔮 * qsN f) ^ η * Real.sqrt (qsN f) := by ring
  exact htotal.trans htotal'

private theorem qs_sfNorm_pos_M2 (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < (qsSfNorm I : ℝ) := by
  obtain ⟨p, hp, _⟩ := qs_squarefree_decomposition_M1 I hI
  rcases p with ⟨a₀, b⟩
  rcases hp with ⟨ha₀, hIeq⟩
  have hb : b ≠ ⊥ := by
    intro h
    apply hI
    rw [hIeq, h]
    simp
  have ha₀ne : a₀ ≠ ⊥ := by
    intro h
    apply hI
    rw [hIeq, h]
    simp
  have hnormne : Ideal.absNorm a₀ ≠ 0 := by
    intro h
    exact ha₀ne (Ideal.absNorm_eq_zero_iff.mp h)
  rw [hIeq]
  simp only [Prod.fst, Prod.snd]
  rw [qs_sfNorm_eq_M1 a₀ b ha₀ hb]
  exact_mod_cast Nat.pos_of_ne_zero hnormne

private theorem qsN_pos_of_ne_bot_M2 (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < qsN I := by
  have hnormne : Ideal.absNorm I ≠ 0 := by
    intro h
    exact hI (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.pos_of_ne_zero hnormne

private theorem qs_high_eq_tot_zero_cutoff_M2
    (W : ℝ → ℝ) (M : ℝ) (q : Ideal (𝓞 K))
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) :
    qsHigh (fun x => (W x : ℂ)) M 0 q χ = qsTot (fun x => (W x : ℂ)) M q χ := by
  classical
  unfold qsHigh qsTot
  apply tsum_congr
  intro a
  by_cases hcop : IsCoprime a.1 q
  · have hsf := qs_sfNorm_pos_M2 a.1 a.2
    simp [hcop, hsf]
  · simp [hcop]

private theorem qs_modulusRad_ne_bot_M2 (m : ClassFieldTheory.RayClassModulus K) :
    qsModulusRad m ≠ ⊥ := by
  classical
  unfold qsModulusRad
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  exact v.ne_bot

private theorem qs_rad_squarefree_M2 (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Squarefree (qsRad I) := by
  classical
  let P := (UniqueFactorizationMonoid.normalizedFactors I).toFinset
  have hsubset : P ⊆ (UniqueFactorizationMonoid.normalizedFactors I).toFinset := by
    intro p hp
    exact hp
  have hdiv := qs_factor_subset_product_dvd_M2 I hI P hsubset
  have hrad0 : qsRad I ≠ ⊥ := by
    intro hbot
    have hprodBot : (∏ p ∈ P, p) = ⊥ := by
      simpa [qsRad, P] using hbot
    have hbotdiv : (⊥ : Ideal (𝓞 K)) ∣ I := by
      simpa [hprodBot] using hdiv
    exact hI (le_bot_iff.mp (Ideal.dvd_iff_le.mp hbotdiv))
  have hnormFactors :
      UniqueFactorizationMonoid.normalizedFactors (qsRad I) = P.1 := by
    have h := qs_factor_product_normalizedFactors_M2 I hI P hsubset
    simpa [qsRad, P] using h
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hrad0,
    hnormFactors]
  exact P.2

private theorem qs_badRad_squarefree_M2 (m : ClassFieldTheory.RayClassModulus K)
    (qS : Ideal (𝓞 K)) (hqS : qS ≠ ⊥) : Squarefree (qsBadRad m qS) := by
  have hraw : qsModulusRad m * qS ≠ ⊥ :=
    mul_ne_zero (qs_modulusRad_ne_bot_M2 m) hqS
  exact qs_rad_squarefree_M2 (qsModulusRad m * qS) hraw

private theorem qs_badRad_dvd_M2 (m : ClassFieldTheory.RayClassModulus K)
    (qS : Ideal (𝓞 K)) (hqS : qS ≠ ⊥) :
    qsBadRad m qS ∣ qsModulusRad m * qS := by
  have hraw : qsModulusRad m * qS ≠ ⊥ :=
    mul_ne_zero (qs_modulusRad_ne_bot_M2 m) hqS
  have h := qs_factor_subset_product_dvd_M2 (qsModulusRad m * qS) hraw
    (UniqueFactorizationMonoid.normalizedFactors (qsModulusRad m * qS)).toFinset (by intro p hp; exact hp)
  simpa [qsBadRad, qsRad] using h

private theorem qs_admissible_coprime_badRad_M2
    (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K))
    (hqS : qS ≠ ⊥) (c : Ideal (𝓞 K)) (hc : QSAdm m qS c) :
    IsCoprime c (qsBadRad m qS) := by
  have hmod := (qs_isCoprimeTo_iff_M0 (m := m) c).mp hc.2.1
  have hraw : IsCoprime c (qsModulusRad m * qS) := hmod.2.mul_right hc.2.2
  exact hraw.of_isCoprime_of_dvd_right (qs_badRad_dvd_M2 m qS hqS)

private theorem qs_dvd_admissible_data_M2
    (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K))
    (g c : Ideal (𝓞 K)) (hg_c : g ∣ c) (hc : QSAdm m qS c) :
    Squarefree g ∧ ArtinPrimitiveRoots.Hecke.IsCoprimeTo m g ∧ IsCoprime g qS := by
  have hsq : Squarefree g := hc.1.squarefree_of_dvd hg_c
  have hg0 : g ≠ ⊥ := hsq.ne_zero
  have hcopMod := (qs_isCoprimeTo_iff_M0 (m := m) c).mp hc.2.1
  have hcopgMod : IsCoprime g (qsModulusRad m) :=
    hcopMod.2.of_isCoprime_of_dvd_left hg_c
  have hgm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m g :=
    (qs_isCoprimeTo_iff_M0 (m := m) g).mpr ⟨hg0, hcopgMod⟩
  exact ⟨hsq, hgm, hc.2.2.of_isCoprime_of_dvd_left hg_c⟩

private theorem qs_badRad_mul_squarefree_M2
    (m : ClassFieldTheory.RayClassModulus K) (qS g : Ideal (𝓞 K))
    (hqS : qS ≠ ⊥) (hg : Squarefree g)
    (hcop : IsCoprime (qsBadRad m qS) g) : Squarefree (qsBadRad m qS * g) := by
  exact squarefree_mul_iff.mpr ⟨hcop.isRelPrime,
    qs_badRad_squarefree_M2 m qS hqS, hg⟩

private theorem qs_idealUnit_mul_M2 (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) (hIJ : I * J ≠ ⊥) :
    ArtinPrimitiveRoots.Hecke.idealUnit (I * J) hIJ =
      ArtinPrimitiveRoots.Hecke.idealUnit I hI * ArtinPrimitiveRoots.Hecke.idealUnit J hJ := by
  apply Units.ext
  simp [ArtinPrimitiveRoots.Hecke.idealUnit, FractionalIdeal.coeIdeal_mul]

private theorem qs_isCoprimeTo_mul_M2 (I J : Ideal (𝓞 K))
    (hI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I)
    (hJ : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m J) :
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m (I * J) := by
  rcases hI with ⟨hI0, hI'⟩
  rcases hJ with ⟨hJ0, hJ'⟩
  have hIJ0 : I * J ≠ ⊥ := mul_ne_zero hI0 hJ0
  have hIJ' : ArtinPrimitiveRoots.Hecke.idealUnit (I * J) hIJ0 ∈
      ClassFieldTheory.rayClassPrimeToIdeals m := by
    rw [qs_idealUnit_mul_M2 I J hI0 hJ0 hIJ0]
    exact (ClassFieldTheory.rayClassPrimeToIdeals m).mul_mem hI' hJ'
  exact ⟨hIJ0, hIJ'⟩

private theorem qs_rayClass_mul_M2 (I J : Ideal (𝓞 K))
    (hI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I)
    (hJ : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m J) :
    ArtinPrimitiveRoots.Hecke.rayClass m (I * J) (qs_isCoprimeTo_mul_M2 I J hI hJ) =
      ArtinPrimitiveRoots.Hecke.rayClass m I hI * ArtinPrimitiveRoots.Hecke.rayClass m J hJ := by
  rcases hI with ⟨hI0, hI'⟩
  rcases hJ with ⟨hJ0, hJ'⟩
  have hIJ0 : I * J ≠ ⊥ := mul_ne_zero hI0 hJ0
  have hIJ' : ArtinPrimitiveRoots.Hecke.idealUnit (I * J) hIJ0 ∈
      ClassFieldTheory.rayClassPrimeToIdeals m := by
    rw [qs_idealUnit_mul_M2 I J hI0 hJ0 hIJ0]
    exact (ClassFieldTheory.rayClassPrimeToIdeals m).mul_mem hI' hJ'
  change QuotientGroup.mk
      (⟨ArtinPrimitiveRoots.Hecke.idealUnit (I * J) hIJ0, hIJ'⟩ :
        ClassFieldTheory.rayClassPrimeToIdeals m) =
    QuotientGroup.mk
        (⟨ArtinPrimitiveRoots.Hecke.idealUnit I hI0, hI'⟩ :
          ClassFieldTheory.rayClassPrimeToIdeals m) *
      QuotientGroup.mk
        (⟨ArtinPrimitiveRoots.Hecke.idealUnit J hJ0, hJ'⟩ :
          ClassFieldTheory.rayClassPrimeToIdeals m)
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (qs_idealUnit_mul_M2 I J hI0 hJ0 hIJ0)

private theorem qs_rayClass_cancel_left_M2 (I J L : Ideal (𝓞 K))
    (hI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I)
    (hJ : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m J)
    (hL : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m L)
    (hclass : ArtinPrimitiveRoots.Hecke.rayClass m (I * J)
        (qs_isCoprimeTo_mul_M2 I J hI hJ) =
      ArtinPrimitiveRoots.Hecke.rayClass m (I * L)
        (qs_isCoprimeTo_mul_M2 I L hI hL)) :
    ArtinPrimitiveRoots.Hecke.rayClass m J hJ = ArtinPrimitiveRoots.Hecke.rayClass m L hL := by
  rw [qs_rayClass_mul_M2 I J hI hJ, qs_rayClass_mul_M2 I L hI hL] at hclass
  have hcancel := congrArg
    (fun x : ClassFieldTheory.RayClassGroup m =>
      (ArtinPrimitiveRoots.Hecke.rayClass m I hI)⁻¹ * x) hclass
  simpa [mul_assoc] using hcancel

private theorem qs_cap_weight_norm_bound_M2 (W : ℝ → ℝ) (hW : IsCapWeight W) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → ‖(W x : ℂ)‖ ≤ C := by
  let f : ℝ → ℝ := fun x => ‖(W x : ℂ)‖
  have hf : Continuous f := by
    exact hW.1.1.continuous.norm
  have hbounded : BddAbove (f '' Set.Icc (0 : ℝ) (5 / 2)) :=
    isCompact_Icc.bddAbove_image hf.continuousOn
  obtain ⟨B, hB⟩ := hbounded
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  by_cases hxl : x ≤ 5 / 2
  · have hmem : x ∈ Set.Icc (0 : ℝ) (5 / 2) := ⟨hx, hxl⟩
    have hfx : f x ≤ B := hB ⟨x, hmem, rfl⟩
    exact hfx.trans (le_max_left _ _)
  · have hx' : 5 / 2 ≤ x := le_of_lt (lt_of_not_ge hxl)
    simp [f, hW.2.2.2 x hx']

private theorem qs_principal_high_bound_M2 (W : ℝ → ℝ) (hW : IsCapWeight W)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (q : Ideal (𝓞 K)), 1 ≤ M →
      ‖qsHigh (fun x => (W x : ℂ)) M 0 q (1 : ArtinPrimitiveRoots.A1.HeckeChar K)‖ ≤
        C * M ^ (1 + η) := by
  classical
  obtain ⟨Ccnt, hCcnt, hcount⟩ := qs_ideal_count_M1 (K := K) η hη
  obtain ⟨Cw, hCw, hWbound⟩ := qs_cap_weight_norm_bound_M2 W hW
  let C : ℝ := Ccnt * Cw * (3 : ℝ) ^ (1 + η)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M q hM
  have hMpos : 0 < M := by linarith
  have hsum : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      if IsCoprime a.1 q then (W (qsN a.1 / M) : ℂ) else 0) := by
    apply qs_series_supported_norm_summable_M2 M hMpos
    intro a ha
    have hWzero := hW.2.2.2 (qsN a.1 / M) ha
    simp [hWzero]
  let low : Finset (Ideal (𝓞 K)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset
  have hlowmem (I : Ideal (𝓞 K)) : I ∈ low ↔
      (Ideal.absNorm I : ℝ) ≤ 3 * M := by
    simp [low, Nat.le_floor_iff (by positivity : 0 ≤ 3 * M)]
  let B : Set {I : Ideal (𝓞 K) // I ≠ ⊥} := {a | a.1 ∈ low}
  have hB : B.Finite := by
    let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → Ideal (𝓞 K) := Subtype.val
    let S : Set (Ideal (𝓞 K)) := (low : Set (Ideal (𝓞 K)))
    have hS : S.Finite := by simpa [S] using low.finite_toSet
    have hpre : (f ⁻¹' S).Finite :=
      Set.Finite.preimage (f := f) (s := S) Subtype.val_injective.injOn hS
    change (f ⁻¹' S).Finite
    exact hpre
  let s := hB.toFinset
  have hvanish : ∀ a : {I : Ideal (𝓞 K) // I ≠ ⊥}, a ∉ s →
      (if IsCoprime a.1 q then (W (qsN a.1 / M) : ℂ) else 0) = 0 := by
    intro a ha
    have haB : a ∉ B := fun h => ha (hB.mem_toFinset.mpr h)
    have hnotle : ¬ (Ideal.absNorm a.1 : ℝ) ≤ 3 * M := by
      intro hle
      exact haB ((hlowmem a.1).mpr hle)
    have hlt : 3 * M < (Ideal.absNorm a.1 : ℝ) := lt_of_not_ge hnotle
    have harg : 5 / 2 ≤ (Ideal.absNorm a.1 : ℝ) / M := by
      apply (le_div_iff₀ hMpos).2
      nlinarith
    have hWzero := hW.2.2.2 ((Ideal.absNorm a.1 : ℝ) / M) harg
    simp [hWzero]
  have hsumEq :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if IsCoprime a.1 q then (W (qsN a.1 / M) : ℂ) else 0) =
      ∑ a ∈ s, (if IsCoprime a.1 q then (W (qsN a.1 / M) : ℂ) else 0) :=
    tsum_eq_sum (s := s) hvanish
  have hcard : (s.card : ℝ) ≤ (low.card : ℝ) := by
    have hnat : s.card ≤ low.card := by
      apply Finset.card_le_card_of_injOn (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} => a.1)
      · intro a ha
        exact hB.mem_toFinset.mp ha
      · intro a ha b hb hab
        exact Subtype.ext hab
    exact_mod_cast hnat
  have hlowCount : (low.card : ℝ) ≤ Ccnt * (3 * M) ^ (1 + η) := by
    have h := hcount (3 * M) (by nlinarith [hM])
    simpa [low] using h
  have hfiniteBound :
      (∑ a ∈ s, ‖(if IsCoprime a.1 q then (W (qsN a.1 / M) : ℂ) else 0)‖) ≤
        (low.card : ℝ) * Cw := by
    calc
      _ ≤ (s.card : ℝ) * Cw := by
        simpa [nsmul_eq_mul, mul_comm] using
          (Finset.sum_le_card_nsmul s
            (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
              ‖(if IsCoprime a.1 q then (W (qsN a.1 / M) : ℂ) else 0)‖)
            Cw (by
              intro a ha
              by_cases hcop : IsCoprime a.1 q
              · simpa [hcop] using hWbound (qsN a.1 / M) (by positivity)
              · simp [hcop]
                exact le_of_lt hCw))
      _ ≤ (low.card : ℝ) * Cw :=
        mul_le_mul_of_nonneg_right hcard (le_of_lt hCw)
  have hsumNorm :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ‖if IsCoprime a.1 q then (W (qsN a.1 / M) : ℂ) else 0‖) ≤
        (low.card : ℝ) * Cw := by
    rw [tsum_eq_sum (s := s) (by
      intro a ha
      simp [hvanish a ha])]
    exact hfiniteBound
  have hprincipal :
      qsTot (fun x => (W x : ℂ)) M q (1 : ArtinPrimitiveRoots.A1.HeckeChar K) =
      ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if IsCoprime a.1 q then (W (qsN a.1 / M) : ℂ) else 0 := by
    unfold qsTot
    apply tsum_congr
    intro a
    by_cases hcop : IsCoprime a.1 q <;>
      simp [hcop, ArtinPrimitiveRoots.A1.HeckeChar.idealValue,
        ArtinPrimitiveRoots.A1.HeckeChar.primeValue,
        ArtinPrimitiveRoots.A1.HeckeChar.loc,
        ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt]
  rw [qs_high_eq_tot_zero_cutoff_M2 W M q (1 : ArtinPrimitiveRoots.A1.HeckeChar K)]
  rw [hprincipal]
  have hnorm := norm_tsum_le_tsum_norm hsum.norm
  calc
    _ ≤ (low.card : ℝ) * Cw := hnorm.trans hsumNorm
    _ ≤ Ccnt * (3 * M) ^ (1 + η) * Cw :=
      mul_le_mul_of_nonneg_right hlowCount (le_of_lt hCw)
    _ = C * M ^ (1 + η) := by
      dsimp [C]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity : 0 ≤ M)]
      ring

private theorem qs_pairchar_high_bound_M2 [IsTotallyComplex K]
    (W : ℝ → ℝ) (hW : IsCapWeight W) (η : ℝ) (hη : 0 < η)
    (F : QSFamily m qS) (Cpair : ℝ)
    (hkernel : ∀ (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f q : Ideal (𝓞 K)) (M : ℝ),
      IsPrimitiveConductor χ f → χ ^ 2 = 1 → χ ≠ 1 →
      (∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1) →
      Squarefree q → IsCoprime q f → 1 ≤ M →
      ‖qsTot (fun x => (W x : ℂ)) M q χ‖ ≤
        Cpair * (qsN q * qsN f) ^ η * Real.sqrt (qsN f))
    (c d q : Ideal (𝓞 K))
    (M : ℝ)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hclass : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hcdTop : c * d ≠ ⊤) (hq : Squarefree q) (hqf : IsCoprime q (c * d)) (hM : 1 ≤ M) :
    ‖qsHigh (fun x => (W x : ℂ)) M 0 q (qsPairChar F c d)‖ ≤
      Cpair * (qsN q * qsN (c * d)) ^ η * Real.sqrt (qsN (c * d)) := by
  have hprim : IsPrimitiveConductor (qsPairChar F c d) (c * d) := by
    rcases hclass with ⟨hc', hd', hcl⟩
    have hcl' : ArtinPrimitiveRoots.Hecke.rayClass m c hc.2.1 =
        ArtinPrimitiveRoots.Hecke.rayClass m d hd.2.1 := hcl
    exact F.equalClass_product_conductor c d hc.1 hc.2.1 hd.1 hd.2.1 hcd hcl'
  have hsq : (qsPairChar F c d) ^ 2 = 1 := by
    simp only [qsPairChar, mul_pow, inv_pow]
    rw [F.character_order_two c hc.1 hc.2.1, F.character_order_two d hd.1 hd.2.1]
    simp
  have htopDvd : (1 : ArtinPrimitiveRoots.A1.HeckeChar K).ConductorDvd ⊤ := by
    intro v u hu1 hu2 hv
    simp [ArtinPrimitiveRoots.A1.HeckeChar.loc]
  have hne : qsPairChar F c d ≠ 1 := by
    intro htriv
    have htopDvdPair : (qsPairChar F c d).ConductorDvd ⊤ := by
      simpa [htriv] using htopDvd
    have hmin := hprim.2.2 ⊤ (by simp) htopDvdPair
    have hle : Ideal.absNorm (c * d) ≤ 1 := by simpa using hmin
    have hnormne : Ideal.absNorm (c * d) ≠ 0 := by
      intro hzero
      have hcdne : c * d ≠ ⊥ := mul_ne_zero hc.1.ne_zero hd.1.ne_zero
      exact hcdne (Ideal.absNorm_eq_zero_iff.mp hzero)
    have hone : Ideal.absNorm (c * d) = 1 := by omega
    exact hcdTop (Ideal.absNorm_eq_one_iff.mp hone)
  have hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ,
      (qsPairChar F c d).locInf w u = 1 := by
    intro w u
    change (F.character c).locInf w u * ((F.character d).locInf w u)⁻¹ = 1
    rw [F.trivial_infinite_type c w u, F.trivial_infinite_type d w u]
    simp
  rw [qs_high_eq_tot_zero_cutoff_M2 W M q (qsPairChar F c d)]
  exact hkernel (qsPairChar F c d) (c * d) q M hprim hsq hne hinf hq hqf hM

private theorem qs_mul_ne_top_of_ne_M2 (c d : Ideal (𝓞 K)) (hcd : c ≠ d) :
    c * d ≠ ⊤ := by
  intro htop
  have hleC : c * d ≤ c := by
    calc
      c * d ≤ c * ⊤ := by gcongr <;> exact le_top
      _ = c := by simp
  have hleD : c * d ≤ d := by
    calc
      c * d ≤ ⊤ * d := by gcongr <;> exact le_top
      _ = d := by simp
  have hcTop : c = ⊤ := top_unique (by simpa [htop] using hleC)
  have hdTop : d = ⊤ := top_unique (by simpa [htop] using hleD)
  exact hcd (hcTop.trans hdTop.symm)

set_option maxHeartbeats 1000000 in
private theorem qs_pairchar_high_bound_of_sizes_M2 [IsTotallyComplex K]
    (W : ℝ → ℝ) (hW : IsCapWeight W) (η : ℝ) (hη : 0 < η)
    (F : QSFamily m qS) (Cpair : ℝ)
    (hkernel : ∀ (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f q : Ideal (𝓞 K)) (M : ℝ),
      IsPrimitiveConductor χ f → χ ^ 2 = 1 → χ ≠ 1 →
      (∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1) →
      Squarefree q → IsCoprime q f → 1 ≤ M →
      ‖qsTot (fun x => (W x : ℂ)) M q χ‖ ≤
        Cpair * (qsN q * qsN f) ^ η * Real.sqrt (qsN f))
    (g c d : Ideal (𝓞 K)) (M N : ℝ)
    (hqS : qS ≠ ⊥) (hgSq : Squarefree g)
    (hbadg : IsCoprime (qsBadRad m qS) g)
    (hcg : IsCoprime c g) (hdg : IsCoprime d g)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hclass : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hcdne : c ≠ d) (hM : 1 ≤ M) (hN : 1 ≤ N) (hCpair : 0 < Cpair)
    (hgN : qsN g ≤ N) (hcN : qsN c ≤ N) (hdN : qsN d ≤ N) :
    ‖qsHigh (fun x => (W x : ℂ)) M 0 (qsBadRad m qS * g) (qsPairChar F c d)‖ ≤
      Cpair * (qsN (qsBadRad m qS) * N ^ 3) ^ η * N := by
  have hqSq := qs_badRad_mul_squarefree_M2 m qS g hqS hgSq hbadg
  have hbc : IsCoprime (qsBadRad m qS) c :=
    (qs_admissible_coprime_badRad_M2 m qS hqS c hc).symm
  have hbd : IsCoprime (qsBadRad m qS) d :=
    (qs_admissible_coprime_badRad_M2 m qS hqS d hd).symm
  have hqc : IsCoprime (qsBadRad m qS * g) c :=
    hbc.mul_left hcg.symm
  have hqd : IsCoprime (qsBadRad m qS * g) d :=
    hbd.mul_left hdg.symm
  have hqf : IsCoprime (qsBadRad m qS * g) (c * d) := hqc.mul_right hqd
  have hcdTop : c * d ≠ ⊤ := qs_mul_ne_top_of_ne_M2 c d hcdne
  have hpair := qs_pairchar_high_bound_M2 W hW η hη F Cpair hkernel c d
    (qsBadRad m qS * g) M hc hd hcd hclass hcdTop hqSq hqf hM
  have hqNorm : qsN (qsBadRad m qS * g) = qsN (qsBadRad m qS) * qsN g := by
    simp [qsN, map_mul]
  have hfNorm : qsN (c * d) = qsN c * qsN d := by
    simp [qsN, map_mul]
  have hbadSq := qs_badRad_squarefree_M2 m qS hqS
  have hbadN : 0 < qsN (qsBadRad m qS) :=
    qsN_pos_of_ne_bot_M2 _ hbadSq.ne_zero
  have hgNpos : 0 < qsN g := qsN_pos_of_ne_bot_M2 g hgSq.ne_zero
  have hcNpos : 0 < qsN c := qsN_pos_of_ne_bot_M2 c hc.1.ne_zero
  have hdNpos : 0 < qsN d := qsN_pos_of_ne_bot_M2 d hd.1.ne_zero
  have hbase : qsN (qsBadRad m qS * g) * qsN (c * d) ≤
      qsN (qsBadRad m qS) * N ^ 3 := by
    rw [hqNorm, hfNorm]
    have hgc : qsN g * qsN c ≤ N * N := by
      calc
        qsN g * qsN c ≤ N * qsN c :=
          mul_le_mul_of_nonneg_right hgN (by positivity)
        _ ≤ N * N := mul_le_mul_of_nonneg_left hcN (by positivity)
    have hprod : qsN g * (qsN c * qsN d) ≤ N ^ 3 := by
      calc
        qsN g * (qsN c * qsN d) = (qsN g * qsN c) * qsN d := by ring
        _ ≤ (N * N) * qsN d := mul_le_mul_of_nonneg_right hgc (by positivity)
        _ ≤ (N * N) * N := mul_le_mul_of_nonneg_left hdN (by positivity)
        _ = N ^ 3 := by ring
    calc
      qsN (qsBadRad m qS) * qsN g * (qsN c * qsN d) =
          qsN (qsBadRad m qS) * (qsN g * (qsN c * qsN d)) := by ring
      _ ≤
          qsN (qsBadRad m qS) * N ^ 3 :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
  have hbasePos : 0 < qsN (qsBadRad m qS * g) * qsN (c * d) := by
    rw [hqNorm, hfNorm]
    positivity
  have hbigPos : 0 < qsN (qsBadRad m qS) * N ^ 3 := by positivity
  have hpow :
      (qsN (qsBadRad m qS * g) * qsN (c * d)) ^ η ≤
        (qsN (qsBadRad m qS) * N ^ 3) ^ η :=
    Real.rpow_le_rpow hbasePos.le hbase hη.le
  have hroot : Real.sqrt (qsN (c * d)) ≤ N := by
    rw [hfNorm]
    have hmul : qsN c * qsN d ≤ N ^ 2 := by
      calc
        qsN c * qsN d ≤ N * qsN d :=
          mul_le_mul_of_nonneg_right hcN (by positivity)
        _ ≤ N * N := mul_le_mul_of_nonneg_left hdN (by positivity)
        _ = N ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hmul
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ N)] using hsqrt
  have hcoef :
      Cpair * (qsN (qsBadRad m qS * g) * qsN (c * d)) ^ η ≤
        Cpair * (qsN (qsBadRad m qS) * N ^ 3) ^ η :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt hCpair)
  calc
    ‖qsHigh (fun x => (W x : ℂ)) M 0 (qsBadRad m qS * g) (qsPairChar F c d)‖ ≤
        Cpair * (qsN (qsBadRad m qS * g) * qsN (c * d)) ^ η *
          Real.sqrt (qsN (c * d)) := hpair
    _ ≤ Cpair * (qsN (qsBadRad m qS * g) * qsN (c * d)) ^ η * N :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ ≤ Cpair * (qsN (qsBadRad m qS) * N ^ 3) ^ η * N :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)

private theorem qs_pairSum_norm_bound_M2
    (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
    (Φ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (D E : ℝ)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : ∀ c ∈ cols, ‖Φ c c‖ ≤ D)
    (hoff : ∀ c d, c ∈ cols → d ∈ cols → IsCoprime c d → c ≠ d → ‖Φ c d‖ ≤ E) :
    ‖qsPairSum cols z Φ‖ ≤
      (D + E * (cols.card : ℝ)) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let x : Ideal (𝓞 K) → ℝ := fun c => ‖z c‖
  have hx (c : Ideal (𝓞 K)) : 0 ≤ x c := by positivity
  have hterms (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols) :
      ‖if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ ≤
        if c = d then D * x c ^ 2 else E * x c * x d := by
    by_cases hcop : IsCoprime c d
    · by_cases hcd : c = d
      · subst d
        have h := hdiag c hc
        simp only [if_pos hcop, if_pos rfl, norm_mul, Complex.norm_conj]
        calc
          x c * x c * ‖Φ c c‖ ≤ x c * x c * D :=
            mul_le_mul_of_nonneg_left h (by positivity)
          _ = D * x c ^ 2 := by ring
      · have h := hoff c d hc hd hcop hcd
        simp only [if_pos hcop, if_neg hcd, norm_mul, Complex.norm_conj]
        calc
          x c * x d * ‖Φ c d‖ ≤ x c * x d * E :=
            mul_le_mul_of_nonneg_left h (by positivity)
          _ = E * x c * x d := by ring
    · simp only [if_neg hcop, norm_zero]
      split_ifs <;> positivity
  have hdouble :
      ‖∑ c ∈ cols, ∑ d ∈ cols,
        if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ ≤
        ∑ c ∈ cols, ∑ d ∈ cols,
          ‖if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ := by
    calc
      _ ≤ ∑ c ∈ cols,
          ‖∑ d ∈ cols, if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ :=
        norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro c hc
        exact norm_sum_le _ _
  have hmajor :
      (∑ c ∈ cols, ∑ d ∈ cols,
        ‖if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖) ≤
        ∑ c ∈ cols, ∑ d ∈ cols,
          if c = d then D * x c ^ 2 else E * x c * x d := by
    apply Finset.sum_le_sum
    intro c hc
    apply Finset.sum_le_sum
    intro d hd
    exact hterms c d hc hd
  have hrow (c : Ideal (𝓞 K)) (hc : c ∈ cols) :
      (∑ d ∈ cols, if c = d then D * x c ^ 2 else E * x c * x d) ≤
        D * x c ^ 2 + E * x c * (∑ d ∈ cols, x d) := by
    have hdiagSum :
        (∑ d ∈ cols, if c = d then D * x c ^ 2 else 0) = D * x c ^ 2 := by
      simp [hc]
    have hcrossSum :
        (∑ d ∈ cols, E * x c * x d) = E * x c * (∑ d ∈ cols, x d) := by
      calc
        _ = ∑ d ∈ cols, (E * x c) * x d := by
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = _ := by rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ d ∈ cols,
          ((if c = d then D * x c ^ 2 else 0) + E * x c * x d) := by
        apply Finset.sum_le_sum
        intro d hd
        by_cases hcd : c = d
        · subst d
          simp
          positivity
        · simp [hcd]
      _ = _ := by
        rw [Finset.sum_add_distrib, hdiagSum, hcrossSum]
  have hmajor' :
      (∑ c ∈ cols, ∑ d ∈ cols,
        if c = d then D * x c ^ 2 else E * x c * x d) ≤
        D * (∑ c ∈ cols, x c ^ 2) + E * (∑ c ∈ cols, x c) ^ 2 := by
    have hdiagSum :
        (∑ c ∈ cols, D * x c ^ 2) = D * ∑ c ∈ cols, x c ^ 2 := by
      rw [← Finset.mul_sum]
    have hcrossSum (S : ℝ) :
        (∑ c ∈ cols, E * x c * S) = E * S * ∑ c ∈ cols, x c := by
      calc
        _ = ∑ c ∈ cols, (E * S) * x c := by
          apply Finset.sum_congr rfl
          intro c hc
          ring
        _ = _ := by rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ c ∈ cols,
          (D * x c ^ 2 + E * x c * (∑ d ∈ cols, x d)) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hrow c hc
      _ = (∑ c ∈ cols, D * x c ^ 2) +
          (∑ c ∈ cols, E * x c * (∑ d ∈ cols, x d)) := by
        rw [Finset.sum_add_distrib]
      _ = D * (∑ c ∈ cols, x c ^ 2) +
          E * (∑ c ∈ cols, x c) * (∑ d ∈ cols, x d) := by
        rw [hdiagSum, hcrossSum]
      _ = _ := by ring
  have hCauchy : (∑ c ∈ cols, x c) ^ 2 ≤
      (cols.card : ℝ) * ∑ c ∈ cols, x c ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := cols) (f := x)
  have hlast :
      D * (∑ c ∈ cols, x c ^ 2) + E * (∑ c ∈ cols, x c) ^ 2 ≤
        (D + E * (cols.card : ℝ)) * ∑ c ∈ cols, x c ^ 2 := by
    calc
      _ ≤ D * (∑ c ∈ cols, x c ^ 2) +
          E * ((cols.card : ℝ) * ∑ c ∈ cols, x c ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hCauchy hE)
      _ = _ := by ring
  unfold qsPairSum
  calc
    _ ≤ ∑ c ∈ cols, ∑ d ∈ cols,
        ‖if IsCoprime c d then z c * conj (z d) * Φ c d else 0‖ := hdouble
    _ ≤ _ := hmajor
    _ ≤ _ := hmajor'
    _ ≤ (D + E * (cols.card : ℝ)) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
      simpa [x] using hlast

private theorem qs_dvd_mem_qsDivisors_M2 (I J : Ideal (𝓞 K))
    (hJ : J ≠ ⊥) (hIJ : I ∣ J) : I ∈ qsDivisors J := by
  classical
  have hnormDvd : Ideal.absNorm I ∣ Ideal.absNorm J :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hIJ)
  have hnormJne : Ideal.absNorm J ≠ 0 := by
    intro h
    exact hJ (Ideal.absNorm_eq_zero_iff.mp h)
  have hnormLe : Ideal.absNorm I ≤ Ideal.absNorm J :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hnormJne) hnormDvd
  change I ∈ ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm J)).toFinset).filter
    (fun e => e ∣ J)
  exact Finset.mem_filter.mpr
    ⟨(Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Ideal.absNorm J)).mem_toFinset.mpr hnormLe,
      hIJ⟩

private theorem qs_upTo_card_bound_M2 (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      ((qsUpTo m qS N).card : ℝ) ≤ C * N ^ (1 + η) := by
  classical
  obtain ⟨C, hC, hcount⟩ := qs_ideal_count_M1 (K := K) η hη
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hfull := hcount N hN
  have hfilter : (qsUpTo m qS N).card ≤
      ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊N⌋₊).toFinset.card) := by
    unfold qsUpTo
    exact Finset.card_filter_le _ _
  exact (Nat.cast_le.mpr hfilter).trans hfull

private theorem qs_residual_weight_sum_bound_M2
    (G cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ)
    (Cg : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)))
    (zg : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (D θ N : ℝ)
    (hcols0 : ∀ c ∈ cols, c ≠ ⊥)
    (hdivcount : ∀ c ∈ cols, ((qsDivisors c).card : ℝ) ≤ D * N ^ θ)
    (himage : ∀ g ∈ G, ∀ c' ∈ Cg g, g * c' ∈ cols)
    (hzeq : ∀ g ∈ G, ∀ c' ∈ Cg g, zg g c' = z (g * c'))
    (hg0 : ∀ g ∈ G, g ≠ ⊥) :
    (∑ g ∈ G, ∑ c' ∈ Cg g, ‖zg g c'‖ ^ 2) ≤
      D * N ^ θ * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  let w : Ideal (𝓞 K) → ℝ := fun c => ‖z c‖ ^ 2
  have hw (c : Ideal (𝓞 K)) : 0 ≤ w c := by positivity
  have hper (g : Ideal (𝓞 K)) (hg : g ∈ G) :
      (∑ c' ∈ Cg g, ‖zg g c'‖ ^ 2) ≤
        ∑ c ∈ cols, if g ∣ c then w c else 0 := by
    let im := (Cg g).image (fun c' => g * c')
    have hinj : Set.InjOn (fun c' => g * c') (Cg g : Set (Ideal (𝓞 K))) := by
      intro c' hc' d' hd' hEq
      exact mul_left_cancel₀ (hg0 g hg) (by simpa using hEq)
    have hsumImage :
        (∑ c' ∈ Cg g, ‖zg g c'‖ ^ 2) = ∑ c ∈ im, w c := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro c' hc'
      simp [im, w, hzeq g hg c' hc']
    have himsub : im ⊆ cols.filter (fun c => g ∣ c) := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨c', hc', rfl⟩
      exact Finset.mem_filter.mpr ⟨himage g hg c' hc', ⟨c', rfl⟩⟩
    have hsubset :
        (∑ c ∈ im, w c) ≤ ∑ c ∈ cols.filter (fun c => g ∣ c), w c :=
      Finset.sum_le_sum_of_subset_of_nonneg himsub (by
        intro c hc hnot
        exact hw c)
    calc
      _ = ∑ c ∈ im, w c := hsumImage
      _ ≤ ∑ c ∈ cols.filter (fun c => g ∣ c), w c := hsubset
      _ = ∑ c ∈ cols, if g ∣ c then w c else 0 := by rw [Finset.sum_filter]
  have hcountPer (c : Ideal (𝓞 K)) (hc : c ∈ cols) :
      (∑ g ∈ G, if g ∣ c then w c else 0) ≤ D * N ^ θ * w c := by
    let divisors := G.filter (fun g => g ∣ c)
    have hsub : divisors ⊆ qsDivisors c := by
      intro g hg
      rcases Finset.mem_filter.mp hg with ⟨hgG, hgc⟩
      exact qs_dvd_mem_qsDivisors_M2 g c (hcols0 c hc) hgc
    have hcard : (divisors.card : ℝ) ≤ D * N ^ θ := by
      have hnat : divisors.card ≤ (qsDivisors c).card := Finset.card_le_card hsub
      exact (Nat.cast_le.mpr hnat).trans (hdivcount c hc)
    have heq : (∑ g ∈ G, if g ∣ c then w c else 0) = divisors.card • w c := by
      rw [← Finset.sum_filter]
      simp [divisors]
    rw [heq, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (hw c)
  have hsumSwap :
      (∑ g ∈ G, ∑ c ∈ cols, if g ∣ c then w c else 0) =
        ∑ c ∈ cols, ∑ g ∈ G, if g ∣ c then w c else 0 := by
    rw [Finset.sum_comm]
  calc
    _ ≤ ∑ g ∈ G, ∑ c ∈ cols, if g ∣ c then w c else 0 := by
      apply Finset.sum_le_sum
      intro g hg
      exact hper g hg
    _ = ∑ c ∈ cols, ∑ g ∈ G, if g ∣ c then w c else 0 := hsumSwap
    _ ≤ ∑ c ∈ cols, D * N ^ θ * w c := by
      apply Finset.sum_le_sum
      intro c hc
      exact hcountPer c hc
    _ = D * N ^ θ * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
      rw [← Finset.mul_sum]

private theorem qsN_ge_one_M2 (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : 1 ≤ qsN I := by
  have hnormne : Ideal.absNorm I ≠ 0 := by
    intro h
    exact hI (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnormne

private theorem qsN_le_of_dvd_M2 (I J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (hIJ : I ∣ J) :
    qsN I ≤ qsN J := by
  have hnormDvd : Ideal.absNorm I ∣ Ideal.absNorm J :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hIJ)
  have hnormJne : Ideal.absNorm J ≠ 0 := by
    intro h
    exact hJ (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hnormJne) hnormDvd

set_option maxHeartbeats 1000000 in
private theorem qs_same_class_high_energy_bound_M2 [IsTotallyComplex K]
    (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (θ : ℝ) (hθ : 0 < θ)
    (Cpair Cdiag Ccount Cdiv : ℝ)
    (hCdiag : 0 < Cdiag) (hCcount : 0 < Ccount) (hCdiv : 0 < Cdiv)
    (hkernel : ∀ (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f q : Ideal (𝓞 K)) (M : ℝ),
      IsPrimitiveConductor χ f → χ ^ 2 = 1 → χ ≠ 1 →
      (∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1) →
      Squarefree q → IsCoprime q f → 1 ≤ M →
      ‖qsTot (fun x => (W x : ℂ)) M q χ‖ ≤
        Cpair * (qsN q * qsN f) ^ θ * Real.sqrt (qsN f))
    (hCpair : 0 < Cpair)
    (hdiagBound : ∀ (M : ℝ) (q : Ideal (𝓞 K)), 1 ≤ M →
      ‖qsHigh (fun x => (W x : ℂ)) M 0 q (1 : ArtinPrimitiveRoots.A1.HeckeChar K)‖ ≤
        Cdiag * M ^ (1 + θ))
    (hcount : ∀ N : ℝ, 1 ≤ N →
      ((qsUpTo m qS N).card : ℝ) ≤ Ccount * N ^ (1 + θ))
    (hdivcount : ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      ((qsDivisors I).card : ℝ) ≤ Cdiv * qsN I ^ θ)
    (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (cols : Finset (Ideal (𝓞 K)))
    (hcolsUpTo : cols ⊆ qsUpTo m qS N)
    (hclass : ∀ c ∈ cols, ∀ d ∈ cols,
      ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
        (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
        ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd)
    (z : Ideal (𝓞 K) → ℂ) :
    qsHighEnergy F W M 0 cols z ≤
      Cdiv * N ^ θ *
        (Cdiag * M ^ (1 + θ) +
          Cpair * (qsN (qsBadRad m qS) * N ^ 3) ^ θ * N *
            (Ccount * N ^ (1 + θ))) *
        ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  have hMpos : 0 < M := by linarith
  let G := (cols ×ˢ cols).image (fun p => p.1 ⊔ p.2)
  let Pcond : Ideal (𝓞 K) → Prop := fun g =>
    ∃ c d, c ∈ cols ∧ d ∈ cols ∧ c ⊔ d = g
  have hGsource (g : Ideal (𝓞 K)) (hg : g ∈ G) : Pcond g := by
    rcases Finset.mem_image.mp hg with ⟨⟨c, d⟩, hcd, rfl⟩
    rcases Finset.mem_product.mp hcd with ⟨hc, hd⟩
    exact ⟨c, d, hc, hd, rfl⟩
  have hcolsAdm (c : Ideal (𝓞 K)) (hc : c ∈ cols) : QSAdm m qS c := by
    have hmem := hcolsUpTo hc
    simpa [qsUpTo] using (Finset.mem_filter.mp hmem).2.1
  have hcolsNorm (c : Ideal (𝓞 K)) (hc : c ∈ cols) : qsN c ≤ N := by
    have hmem := hcolsUpTo hc
    simpa [qsN] using (Finset.mem_filter.mp hmem).2.2
  have hEpos : 0 ≤ qsHighEnergy F W M 0 cols z := by
    unfold qsHighEnergy
    apply tsum_nonneg
    intro a
    split_ifs
    · exact mul_nonneg (hW.2.1 _) (sq_nonneg _)
    · exact le_rfl
  have hexp := qs_gcd_expansion_S0 F W hW M 0 hMpos cols
    (fun c hc => hcolsAdm c hc) z
  have hrealNorm :
      ‖(qsHighEnergy F W M 0 cols z : ℂ)‖ = qsHighEnergy F W M 0 cols z := by
    simp [abs_of_nonneg hEpos]
  have henergyBlocks :
      qsHighEnergy F W M 0 cols z ≤
        ∑ g ∈ G, ‖qsGcdBlock F W M 0 g cols z‖ := by
    calc
      _ = ‖(qsHighEnergy F W M 0 cols z : ℂ)‖ := hrealNorm.symm
      _ = ‖∑ g ∈ G, qsGcdBlock F W M 0 g cols z‖ := by rw [hexp]
      _ ≤ _ := norm_sum_le _ _
  let Cg : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)) := fun g =>
    Classical.choose (qs_residual_form_S0 F hrf hqS W hW M 0 hMpos g cols
      (fun c hc => hcolsAdm c hc) z)
  let zg : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun g =>
    Classical.choose (Classical.choose_spec
      (qs_residual_form_S0 F hrf hqS W hW M 0 hMpos g cols
        (fun c hc => hcolsAdm c hc) z))
  have hres (g : Ideal (𝓞 K)) :
      (∀ c' ∈ Cg g, QSAdm m qS c' ∧ IsCoprime c' g ∧
        g * c' ∈ cols ∧ zg g c' = z (g * c')) ∧
      (∀ c ∈ cols, g ∣ c → ∃ c' ∈ Cg g, c = g * c') ∧
      qsGcdBlock F W M 0 g cols z =
        qsResidualBlock F W M 0 (qsBadRad m qS * g) (Cg g) (zg g) := by
    exact Classical.choose_spec (Classical.choose_spec
      (qs_residual_form_S0 F hrf hqS W hW M 0 hMpos g cols
        (fun c hc => hcolsAdm c hc) z))
  have hCgCard (g : Ideal (𝓞 K)) (hg : g ∈ G) :
      ((Cg g).card : ℝ) ≤ Ccount * N ^ (1 + θ) := by
    have hg0 : g ≠ ⊥ := by
      obtain ⟨c, d, hc, hd, hgcd⟩ := hGsource g hg
      intro hgbot
      apply (hcolsAdm c hc).1.ne_zero
      have hle : c ≤ ⊥ := by
        simpa [hgcd, hgbot] using (le_sup_left : c ≤ c ⊔ d)
      exact le_bot_iff.mp hle
    have hinj : Set.InjOn (fun c' => g * c') (Cg g : Set (Ideal (𝓞 K))) := by
      intro c' hc' d' hd' hEq
      exact mul_left_cancel₀ hg0 (by simpa using hEq)
    have hnat : (Cg g).card ≤ cols.card := by
      apply Finset.card_le_card_of_injOn (fun c' => g * c')
      · intro c' hc'
        exact (hres g).1 c' hc' |>.2.2.1
      · exact hinj
    have hcountCols := hcount N hN
    have hcolsCard : cols.card ≤ (qsUpTo m qS N).card := Finset.card_le_card hcolsUpTo
    exact (Nat.cast_le.mpr hnat).trans ((Nat.cast_le.mpr hcolsCard).trans hcountCols)
  let D : ℝ := Cdiag * M ^ (1 + θ)
  let E : ℝ := Cpair * (qsN (qsBadRad m qS) * N ^ 3) ^ θ * N
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hblock (g : Ideal (𝓞 K)) (hg : g ∈ G) :
      ‖qsGcdBlock F W M 0 g cols z‖ ≤
        (D + E * (Cg g).card) * ∑ c' ∈ Cg g, ‖zg g c'‖ ^ 2 := by
    have hgsource := hGsource g hg
    rcases hgsource with ⟨c₀, d₀, hc₀, hd₀, hgcd⟩
    have hgDiv : g ∣ c₀ := Ideal.dvd_iff_le.mpr (by rw [← hgcd]; exact le_sup_left)
    have hgData := qs_dvd_admissible_data_M2 m qS g c₀ hgDiv (hcolsAdm c₀ hc₀)
    have hgSq := hgData.1
    have hgM := hgData.2.1
    have hbadg : IsCoprime (qsBadRad m qS) g :=
      ((qs_admissible_coprime_badRad_M2 m qS hqS c₀ (hcolsAdm c₀ hc₀)).of_isCoprime_of_dvd_left
        hgDiv).symm
    have hg0 : g ≠ ⊥ := hgSq.ne_zero
    have hgN : qsN g ≤ N :=
      (qsN_le_of_dvd_M2 g c₀ (by exact (hcolsAdm c₀ hc₀).1.ne_zero) hgDiv).trans
        (hcolsNorm c₀ hc₀)
    let Φ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun c d =>
      qsHigh (fun x => (W x : ℂ)) M 0 (qsBadRad m qS * g) (qsPairChar F c d)
    have hdiag : ∀ c' ∈ Cg g, ‖Φ c' c'‖ ≤ D := by
      intro c' hc'
      have h := hdiagBound M (qsBadRad m qS * g) hM
      simpa [Φ, D, qsPairChar] using h
    have hoff : ∀ c' d', c' ∈ Cg g → d' ∈ Cg g → IsCoprime c' d' → c' ≠ d' →
        ‖Φ c' d'‖ ≤ E := by
      intro c' d' hc' hd' hcop hne
      rcases (hres g).1 c' hc' with ⟨hcAdm, hcg, hgcMem, hzc⟩
      rcases (hres g).1 d' hd' with ⟨hdAdm, hdg, hgdMem, hzd⟩
      rcases hclass (g * c') hgcMem (g * d') hgdMem with ⟨hgcM, hgdM, hclassProd⟩
      have hclassRes := qs_rayClass_cancel_left_M2 g c' d' hgM hcAdm.2.1 hdAdm.2.1 hclassProd
      have hgcNorm : qsN (g * c') = qsN g * qsN c' := by simp [qsN, map_mul]
      have hgdNorm : qsN (g * d') = qsN g * qsN d' := by simp [qsN, map_mul]
      have hc'N : qsN c' ≤ N := by
        calc
          qsN c' = (1 : ℝ) * qsN c' := by ring
          _ ≤ qsN g * qsN c' := mul_le_mul_of_nonneg_right
            (qsN_ge_one_M2 g hg0) (show 0 ≤ qsN c' by positivity)
          _ = qsN (g * c') := hgcNorm.symm
          _ ≤ N := hcolsNorm (g * c') hgcMem
      have hd'N : qsN d' ≤ N := by
        calc
          qsN d' = (1 : ℝ) * qsN d' := by ring
          _ ≤ qsN g * qsN d' := mul_le_mul_of_nonneg_right
            (qsN_ge_one_M2 g hg0) (show 0 ≤ qsN d' by positivity)
          _ = qsN (g * d') := hgdNorm.symm
          _ ≤ N := hcolsNorm (g * d') hgdMem
      have hpair := qs_pairchar_high_bound_of_sizes_M2 W hW θ hθ F Cpair hkernel
        g c' d' M N hqS hgSq hbadg hcg hdg hcAdm hdAdm hcop
        ⟨hcAdm.2.1, hdAdm.2.1, hclassRes⟩ hne hM hN hCpair hgN hc'N hd'N
      simpa [Φ, E] using hpair
    have hsum := qs_pairSum_norm_bound_M2 (Cg g) (zg g) Φ D E hD hE hdiag hoff
    rw [hres g |>.2.2]
    simpa [qsResidualBlock, Φ] using hsum
  let V := ∑ c ∈ cols, ‖z c‖ ^ 2
  let A := D + E * (Ccount * N ^ (1 + θ))
  have hweights := qs_residual_weight_sum_bound_M2 G cols z Cg zg
    (Cdiv) θ N (by intro c hc; exact (hcolsAdm c hc).1.ne_zero)
    (by
      intro c hc
      have hcne := (hcolsAdm c hc).1.ne_zero
      have hdiv := hdivcount c hcne
      have hnorm := hcolsNorm c hc
      have hmono : qsN c ^ θ ≤ N ^ θ := Real.rpow_le_rpow (by positivity) hnorm hθ.le
      exact hdiv.trans (mul_le_mul_of_nonneg_left hmono (by positivity)))
    (by intro g hg c' hc'; exact (hres g).1 c' hc' |>.2.2.1)
    (by intro g hg c' hc'; exact (hres g).1 c' hc' |>.2.2.2)
    (by
      intro g hg
      obtain ⟨c, d, hc, hd, hgcd⟩ := hGsource g hg
      intro hgbot
      apply (hcolsAdm c hc).1.ne_zero
      have hle : c ≤ ⊥ := by simpa [hgcd, hgbot] using (le_sup_left : c ≤ c ⊔ d)
      exact le_bot_iff.mp hle)
  have hblockSum :
      (∑ g ∈ G, ‖qsGcdBlock F W M 0 g cols z‖) ≤ A * (Cdiv * N ^ θ * V) := by
    calc
      _ ≤ ∑ g ∈ G, (D + E * (Cg g).card) * ∑ c' ∈ Cg g, ‖zg g c'‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro g hg
        exact hblock g hg
      _ ≤ A * (∑ g ∈ G, ∑ c' ∈ Cg g, ‖zg g c'‖ ^ 2) := by
        calc
          _ ≤ ∑ g ∈ G, A * ∑ c' ∈ Cg g, ‖zg g c'‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro g hg
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hcard := hCgCard g hg
            dsimp [A]
            gcongr
          _ = _ := by rw [← Finset.mul_sum]
      _ ≤ A * (Cdiv * N ^ θ * V) := by
        apply mul_le_mul_of_nonneg_left hweights
        dsimp [A, D, E]
        positivity
  calc
    _ ≤ ∑ g ∈ G, ‖qsGcdBlock F W M 0 g cols z‖ := henergyBlocks
    _ ≤ A * (Cdiv * N ^ θ * V) := hblockSum
    _ = _ := by dsimp [A, V]; ring

private theorem qs_finite_energy_le_high_M2
    (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N : ℝ) (hM : 0 < M)
    (z : Ideal (𝓞 K) → ℂ) :
    (∑ d ∈ qsUpTo m qS M,
      ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue d‖ ^ 2) ≤
      qsHighEnergy F W M 0 (qsUpTo m qS N) z := by
  classical
  let Rows := qsUpTo m qS M
  let Nidx := {I : Ideal (𝓞 K) // I ≠ ⊥}
  let cond (I : Ideal (𝓞 K)) : Prop :=
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ∧ IsCoprime I qS ∧
      0 < (qsSfNorm I : ℝ)
  let fR : Nidx → ℝ := fun a =>
    if cond a.1 then W (qsN a.1 / M) *
      ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue a.1‖ ^ 2 else 0
  let fC : Nidx → ℂ := fun a =>
    if cond a.1 then
      ((W (qsN a.1 / M) *
        ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue a.1‖ ^ 2 : ℝ) : ℂ) else 0
  have hcomplex : Summable fC := by
    apply qs_series_supported_norm_summable_M2 M hM
    intro a ha
    have hWzero := hW.2.2.2 (qsN a.1 / M) ha
    simp [fC, cond, hWzero]
  have hcast (a : Nidx) : fC a = (fR a : ℂ) := by
    by_cases hc : cond a.1 <;> simp [fC, fR, hc]
  have hreal : Summable fR := by
    apply Summable.of_norm
    simpa [hcast, Complex.norm_real] using hcomplex.norm
  have hfNonneg (a : Nidx) : 0 ≤ fR a := by
    by_cases hc : cond a.1
    · simp [fR, hc]
      exact mul_nonneg (hW.2.1 _) (sq_nonneg _)
    · simp [fR, hc]
  have henergy : qsHighEnergy F W M 0 (qsUpTo m qS N) z = ∑' a : Nidx, fR a := by
    unfold qsHighEnergy
    rfl
  let e : {d : Ideal (𝓞 K) // d ∈ Rows} ↪ Nidx := {
    toFun := fun d => ⟨d.1, by
      have hmem : d.1 ∈ qsUpTo m qS M := by simpa [Rows] using d.2
      have hAdm : QSAdm m qS d.1 := (Finset.mem_filter.mp hmem).2.1
      exact hAdm.2.1.1⟩
    inj' := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun a : Nidx => a.1) hab
  }
  let T := Rows.attach.image e
  have hfinite_le :
      (∑ d ∈ Rows,
        ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue d‖ ^ 2) ≤
        qsHighEnergy F W M 0 (qsUpTo m qS N) z := by
    calc
      _ = ∑ d ∈ Rows.attach,
          ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue d.1‖ ^ 2 := by
        simpa [Rows] using
          (Finset.sum_attach Rows
            (fun d => ‖∑ c ∈ qsUpTo m qS N,
              z c * (F.character c).idealValue d‖ ^ 2)).symm
      _ ≤ ∑ d ∈ Rows.attach, fR (e d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hmem : d.1 ∈ qsUpTo m qS M := by simpa [Rows] using d.2
        have hAdm : QSAdm m qS d.1 := (Finset.mem_filter.mp hmem).2.1
        have hnorm : qsN d.1 ≤ M := by
          simpa [qsN] using (Finset.mem_filter.mp hmem).2.2
        have hsf : 0 < (qsSfNorm d.1 : ℝ) :=
          qs_sfNorm_pos_M2 d.1 hAdm.1.ne_zero
        have hcond : cond d.1 := ⟨hAdm.2.1, hAdm.2.2, hsf⟩
        have hweight : 1 ≤ W (qsN d.1 / M) := by
          apply hW.2.2.1
          constructor
          · positivity
          · exact (div_le_one hM).2 hnorm
        change ‖∑ c ∈ qsUpTo m qS N,
          z c * (F.character c).idealValue d.1‖ ^ 2 ≤
          if cond d.1 then W (qsN d.1 / M) *
            ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue d.1‖ ^ 2 else 0
        rw [if_pos hcond]
        simpa [one_mul] using mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
      _ = ∑ a ∈ T, fR a := by
        simp only [T]
        rw [← Finset.sum_image e.injective.injOn]
      _ ≤ ∑' a : Nidx, fR a := hreal.sum_le_tsum T (fun a ha => hfNonneg a)
      _ = qsHighEnergy F W M 0 (qsUpTo m qS N) z := henergy.symm
  simpa [Rows] using hfinite_le

private theorem qs_log_dyad_count_bound_M2 (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) ≤ C * N ^ δ := by
  let L : ℝ := 1 / (δ * Real.log 2) + 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  refine ⟨L, by dsimp [L]; positivity, ?_⟩
  intro N hN
  have hNpos : 0 < N := by linarith
  have hpowPos : 0 < N ^ δ := Real.rpow_pos_of_pos hNpos _
  have hlogPow := Real.log_le_sub_one_of_pos hpowPos
  have hlogPowEq : Real.log (N ^ δ) = δ * Real.log N := by
    rw [Real.log_rpow hNpos]
  have hlogN : Real.log N ≤ N ^ δ / δ := by
    apply (le_div_iff₀ hδ).2
    calc
      Real.log N * δ = δ * Real.log N := by ring
      _ = Real.log (N ^ δ) := hlogPowEq.symm
      _ ≤ N ^ δ - 1 := hlogPow
      _ ≤ N ^ δ := by linarith
  have hlogb : Real.logb 2 N ≤ (N ^ δ) / (δ * Real.log 2) := by
    rw [Real.logb]
    calc
      Real.log N / Real.log 2 ≤ (N ^ δ / δ) / Real.log 2 :=
        div_le_div_of_nonneg_right hlogN (le_of_lt hlog2)
      _ = N ^ δ / (δ * Real.log 2) := by field_simp <;> ring
  have hlogbNonneg : 0 ≤ Real.logb 2 N := by
    rw [Real.logb]
    apply div_nonneg
    · exact Real.log_nonneg hN
    · exact le_of_lt hlog2
  have hceil : (Nat.ceil (Real.logb 2 N) : ℝ) < Real.logb 2 N + 1 :=
    Nat.ceil_lt_add_one hlogbNonneg
  have hNpow : 1 ≤ N ^ δ := Real.one_le_rpow hN (le_of_lt hδ)
  rw [Nat.cast_add, Nat.cast_one]
  dsimp [L]
  calc
    (Nat.ceil (Real.logb 2 N) : ℝ) + 1 ≤ Real.logb 2 N + 2 := by linarith
    _ ≤ (N ^ δ) / (δ * Real.log 2) + 2 := add_le_add hlogb le_rfl
    _ = (1 / (δ * Real.log 2)) * N ^ δ + 2 := by ring
    _ ≤ (1 / (δ * Real.log 2) + 2) * N ^ δ := by nlinarith [hNpow]

/-- M2 (IMPL over M2a, S0; RETIER `qs_hasExponent_two_M2`): `B1(M,N) ≪_ε (MN)^ε (M + N²)`. -/
theorem qs_hasExponent_two_M2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) :
    QSHasExponent F 2 := by
  classical
  obtain ⟨W, hW⟩ := qs_cap_weight_exists_P0
  intro ε hε
  let θ : ℝ := ε / 16
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have h4θ : 4 * θ ≤ ε := by dsimp [θ]; linarith
  have h7θ : 7 * θ ≤ ε := by dsimp [θ]; linarith
  obtain ⟨Cpair, hCpair, hkernel⟩ :=
    qs_pair_kernel_bound_M2 (K := K) W hW θ hθ
  obtain ⟨Cdiag, hCdiag, hdiagBound⟩ :=
    qs_principal_high_bound_M2 (K := K) W hW θ hθ
  obtain ⟨Ccount, hCcount, hcount⟩ :=
    qs_upTo_card_bound_M2 (m := m) (qS := qS) θ hθ
  obtain ⟨Cdiv, hCdiv, hdivcount⟩ :=
    qs_divisor_bound_M1 (K := K) θ hθ
  obtain ⟨Clog, hClog, hlogCount⟩ := qs_log_dyad_count_bound_M2 θ hθ
  have hbadSq := qs_badRad_squarefree_M2 m qS hqS
  have hbadN : 0 < qsN (qsBadRad m qS) :=
    qsN_pos_of_ne_bot_M2 _ hbadSq.ne_zero
  let B : ℝ := qsN (qsBadRad m qS)
  let Hclass : ℝ := max 1 (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ)
  have hHclasspos : 0 < Hclass := by dsimp [Hclass]; positivity
  have hclassCard : (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) ≤ Hclass :=
    le_max_right _ _
  let Cbase : ℝ := Hclass ^ 2 * Clog ^ 2 * Cdiv
  let Couter : ℝ := Cbase * (Cdiag + Cpair * B ^ θ * Ccount)
  have hCouter : 0 < Couter := by
    dsimp [Couter, Cbase, B]
    positivity
  refine ⟨Couter, hCouter, ?_⟩
  intro M N hM hN
  have hMpos : 0 < M := by linarith
  have hNpos : 0 < N := by linarith
  have hMN1 : 1 ≤ M * N := by nlinarith
  have hMleMN : M ≤ M * N := by
    calc
      M = M * 1 := by ring
      _ ≤ M * N := mul_le_mul_of_nonneg_left hN (by linarith)
  have hNleMN : N ≤ M * N := by
    calc
      N = 1 * N := by ring
      _ ≤ M * N := mul_le_mul_of_nonneg_right hM (by linarith)
  let Hsame : ℝ := Cdiv * N ^ θ *
    (Cdiag * M ^ (1 + θ) +
      Cpair * (B * N ^ 3) ^ θ * N * (Ccount * N ^ (1 + θ)))
  have hHsame : 0 ≤ Hsame := by dsimp [Hsame]; positivity
  have hEnergyAll (z : Ideal (𝓞 K) → ℂ) :
      (∑ d ∈ qsUpTo m qS M,
        ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue d‖ ^ 2) ≤
        Couter * (M * N) ^ ε * (M + N ^ (2 : ℝ)) *
          ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 := by
    obtain ⟨parts, hpartsCount, hpartsSub, _hpartsDisj, _hpartsDyad, hpartsClass,
      hpartsEnergy⟩ :=
        qs_class_dyad_slice_S0 F W hW M N 0 hN z
    have hpartsBound : (parts.card : ℝ) ≤ Hclass * Clog * N ^ θ := by
      calc
        _ ≤ (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
            ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) := hpartsCount
        _ ≤ Hclass * ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hclassCard (by positivity)
        _ ≤ Hclass * (Clog * N ^ θ) :=
          mul_le_mul_of_nonneg_left (hlogCount N hN) (le_of_lt hHclasspos)
        _ ≤ Hclass * Clog * N ^ θ := by
          rw [mul_assoc]
    have hpartsSq : (parts.card : ℝ) ^ 2 ≤
        Hclass ^ 2 * Clog ^ 2 * N ^ (2 * θ) := by
      have hcard0 : 0 ≤ (parts.card : ℝ) := by positivity
      have hpow : N ^ θ * N ^ θ = N ^ (2 * θ) := by
        rw [← Real.rpow_add (by positivity : 0 < N)]
        congr 1 <;> ring
      calc
        (parts.card : ℝ) ^ 2 = (parts.card : ℝ) * (parts.card : ℝ) := by rw [pow_two]
        _ ≤ (Hclass * Clog * N ^ θ) * (parts.card : ℝ) :=
          mul_le_mul_of_nonneg_right hpartsBound hcard0
        _ ≤ (Hclass * Clog * N ^ θ) * (Hclass * Clog * N ^ θ) :=
          mul_le_mul_of_nonneg_left hpartsBound (by positivity)
        _ = Hclass ^ 2 * Clog ^ 2 * (N ^ θ * N ^ θ) := by ring
        _ = Hclass ^ 2 * Clog ^ 2 * N ^ (2 * θ) := by rw [hpow]
    let V : ℝ := ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2
    have hpartUniform (P : Finset (Ideal (𝓞 K))) (hP : P ∈ parts) :
        qsHighEnergy F W M 0 P z ≤ Hsame * V := by
      have hpart := qs_same_class_high_energy_bound_M2 F hrf hqS W hW θ hθ
        Cpair Cdiag Ccount Cdiv hCdiag hCcount hCdiv hkernel hCpair hdiagBound
        hcount hdivcount M N hM hN P (hpartsSub P hP) (hpartsClass P hP) z
      have hPnorm : ∑ c ∈ P, ‖z c‖ ^ 2 ≤ V := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (hpartsSub P hP) (by
          intro c hc hmem
          positivity)
      dsimp [Hsame, V] at hpart ⊢
      calc
        _ ≤ Cdiv * N ^ θ *
            (Cdiag * M ^ (1 + θ) +
              Cpair * (B * N ^ 3) ^ θ * N * (Ccount * N ^ (1 + θ))) *
            ∑ c ∈ P, ‖z c‖ ^ 2 := hpart
        _ ≤ Cdiv * N ^ θ *
            (Cdiag * M ^ (1 + θ) +
              Cpair * (B * N ^ 3) ^ θ * N * (Ccount * N ^ (1 + θ))) *
            V := mul_le_mul_of_nonneg_left hPnorm (by positivity)
    have hpartsEnergySum :
        (∑ P ∈ parts, qsHighEnergy F W M 0 P z) ≤
          (parts.card : ℝ) * (Hsame * V) := by
      calc
        _ ≤ parts.card • (Hsame * V) :=
          Finset.sum_le_card_nsmul parts _ _ (by
            intro P hP
            exact hpartUniform P hP)
        _ = _ := by simp [nsmul_eq_mul]
    have hwholeSq : qsHighEnergy F W M 0 (qsUpTo m qS N) z ≤
        (parts.card : ℝ) ^ 2 * Hsame * V := by
      calc
        _ ≤ (parts.card : ℝ) * ∑ P ∈ parts, qsHighEnergy F W M 0 P z := hpartsEnergy
        _ ≤ (parts.card : ℝ) * ((parts.card : ℝ) * (Hsame * V)) :=
          mul_le_mul_of_nonneg_left hpartsEnergySum (by positivity)
        _ = (parts.card : ℝ) ^ 2 * Hsame * V := by ring
    have hBpow : (B * N ^ 3) ^ θ = B ^ θ * N ^ (3 * θ) := by
      change (qsN (qsBadRad m qS) * N ^ 3) ^ θ =
        qsN (qsBadRad m qS) ^ θ * N ^ (3 * θ)
      calc
        _ = qsN (qsBadRad m qS) ^ θ * (N ^ 3) ^ θ :=
          Real.mul_rpow (le_of_lt hbadN) (by positivity)
        _ = qsN (qsBadRad m qS) ^ θ * N ^ (3 * θ) := by
          rw [(Real.rpow_natCast_mul (by positivity : 0 ≤ N) 3 θ).symm]
          congr 2
    have hNadd : N ^ (1 + θ) = N * N ^ θ := by
      rw [Real.rpow_add hNpos]
      simp
    have hpowAdd (a b : ℝ) : N ^ a * N ^ b = N ^ (a + b) :=
      (Real.rpow_add hNpos a b).symm
    have hNpow2 : N ^ (2 : ℝ) = N ^ 2 := Real.rpow_natCast N 2
    have hNprod :
        N ^ (2 * θ) * N ^ θ * N ^ (3 * θ) * N * N ^ (1 + θ) =
          N ^ (2 + 7 * θ) := by
      have hNN : N * N = N ^ (2 : ℝ) := by
        calc
          N * N = N ^ 2 := by ring
          _ = N ^ (2 : ℝ) := hNpow2.symm
      calc
        _ = N ^ (2 * θ) * N ^ θ * N ^ (3 * θ) * N * N * N ^ θ := by
          rw [hNadd]
          ring
        _ = (N ^ (2 * θ) * N ^ θ) * N ^ (3 * θ) * (N * N) * N ^ θ := by ring
        _ = N ^ (3 * θ) * N ^ (3 * θ) * N ^ (2 : ℝ) * N ^ θ := by
          rw [hpowAdd (2 * θ) θ, hNN]
          rw [show 2 * θ + θ = 3 * θ by ring]
        _ = N ^ (6 * θ) * N ^ (2 : ℝ) * N ^ θ := by
          rw [hpowAdd (3 * θ) (3 * θ)]
          rw [show 3 * θ + 3 * θ = 6 * θ by ring]
        _ = N ^ (6 * θ) * N ^ (2 + θ) := by
          calc
            N ^ (6 * θ) * N ^ (2 : ℝ) * N ^ θ =
                N ^ (6 * θ) * (N ^ (2 : ℝ) * N ^ θ) := by ring
            _ = N ^ (6 * θ) * N ^ (2 + θ) := by
              rw [hpowAdd (2 : ℝ) θ]
        _ = N ^ (6 * θ + (2 + θ)) := by
          rw [hpowAdd (6 * θ) (2 + θ)]
        _ = N ^ (2 + 7 * θ) := by congr 1 <;> ring
    have hcoeffRewrite :
        Hclass ^ 2 * Clog ^ 2 * N ^ (2 * θ) * Hsame =
          Cbase *
            (Cdiag * M ^ (1 + θ) * N ^ (3 * θ) +
              Cpair * B ^ θ * Ccount * N ^ (2 + 7 * θ)) := by
      dsimp [Hsame, Cbase, B]
      rw [hBpow]
      calc
        _ = Hclass ^ 2 * Clog ^ 2 * Cdiv *
              (Cdiag * M ^ (1 + θ) * (N ^ (2 * θ) * N ^ θ) +
                Cpair * B ^ θ * Ccount *
                  (N ^ (2 * θ) * N ^ θ * N ^ (3 * θ) * N * N ^ (1 + θ))) := by ring
        _ = Hclass ^ 2 * Clog ^ 2 * Cdiv *
              (Cdiag * M ^ (1 + θ) * N ^ (3 * θ) +
                Cpair * B ^ θ * Ccount *
                  (N ^ (2 * θ) * N ^ θ * N ^ (3 * θ) * N * N ^ (1 + θ))) := by
          rw [hpowAdd (2 * θ) θ]
          ring
        _ = _ := by rw [hNprod]
    let Q : ℝ := Cpair * B ^ θ * Ccount
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hMadd : M ^ (1 + θ) = M * M ^ θ := by
      rw [Real.rpow_add hMpos]
      simp
    have hdiagExp :
        M ^ (1 + θ) * N ^ (3 * θ) ≤ M * (M * N) ^ ε := by
      have hMpow : M ^ θ ≤ (M * N) ^ θ :=
        Real.rpow_le_rpow (by positivity) hMleMN hθ.le
      have hNpow : N ^ (3 * θ) ≤ (M * N) ^ (3 * θ) :=
        Real.rpow_le_rpow (by positivity) hNleMN (by positivity)
      have hpowProduct :
          M ^ θ * N ^ (3 * θ) ≤ (M * N) ^ θ * (M * N) ^ (3 * θ) := by
        calc
          _ ≤ (M * N) ^ θ * N ^ (3 * θ) :=
            mul_le_mul_of_nonneg_right hMpow (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hNpow (by positivity)
      rw [hMadd]
      calc
        _ = M * (M ^ θ * N ^ (3 * θ)) := by ring
        _ ≤ M * ((M * N) ^ θ * (M * N) ^ (3 * θ)) :=
          mul_le_mul_of_nonneg_left hpowProduct (by positivity)
        _ = M * (M * N) ^ (4 * θ) := by
          rw [← Real.rpow_add (by positivity : 0 < M * N)]
          congr 2 <;> ring
        _ ≤ M * (M * N) ^ ε := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hMN1 h4θ
    have hNpowAdd : N ^ (2 + 7 * θ) = N ^ 2 * N ^ (7 * θ) := by
      calc
        N ^ (2 + 7 * θ) = N ^ (2 : ℝ) * N ^ (7 * θ) := Real.rpow_add hNpos 2 (7 * θ)
        _ = N ^ 2 * N ^ (7 * θ) := by rw [hNpow2]
    have hNpow7 : N ^ (7 * θ) ≤ (M * N) ^ (7 * θ) :=
      Real.rpow_le_rpow (by positivity) hNleMN (by positivity)
    have hNwide : N ^ 2 * N ^ (7 * θ) ≤ N ^ 2 * (M * N) ^ ε := by
      calc
        _ ≤ N ^ 2 * (M * N) ^ (7 * θ) :=
          mul_le_mul_of_nonneg_left hNpow7 (by positivity)
        _ ≤ N ^ 2 * (M * N) ^ ε :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hMN1 h7θ) (by positivity)
    have hdiag' :
        Cdiag * M ^ (1 + θ) * N ^ (3 * θ) ≤ Cdiag * (M * (M * N) ^ ε) := by
      have hdiagBase :
          Cdiag * (M ^ (1 + θ) * N ^ (3 * θ)) ≤ Cdiag * (M * (M * N) ^ ε) :=
        mul_le_mul_of_nonneg_left hdiagExp (le_of_lt hCdiag)
      calc
        _ = Cdiag * (M ^ (1 + θ) * N ^ (3 * θ)) := by ring
        _ ≤ _ := hdiagBase
    have hoff' : Q * N ^ (2 + 7 * θ) ≤ Q * (N ^ 2 * (M * N) ^ ε) := by
      rw [hNpowAdd]
      calc
        _ = Q * (N ^ 2 * N ^ (7 * θ)) := by ring
        _ ≤ Q * (N ^ 2 * (M * N) ^ ε) :=
          mul_le_mul_of_nonneg_left hNwide hQ
    have htermBound :
        Cdiag * M ^ (1 + θ) * N ^ (3 * θ) + Q * N ^ (2 + 7 * θ) ≤
          (Cdiag + Q) * (M * N) ^ ε * (M + N ^ (2 : ℝ)) := by
      have hsum : Cdiag * M + Q * N ^ 2 ≤ (Cdiag + Q) * (M + N ^ 2) := by
        nlinarith [mul_nonneg (le_of_lt hCdiag) (sq_nonneg N),
          mul_nonneg hQ (show 0 ≤ M by linarith)]
      calc
        _ ≤ Cdiag * (M * (M * N) ^ ε) +
              Q * (N ^ 2 * (M * N) ^ ε) := add_le_add hdiag' hoff'
        _ = (Cdiag * M + Q * N ^ 2) * (M * N) ^ ε := by ring
        _ ≤ (Cdiag + Q) * (M + N ^ 2) * (M * N) ^ ε :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = (Cdiag + Q) * (M * N) ^ ε * (M + N ^ (2 : ℝ)) := by
          rw [← hNpow2]
          ring
    have hcoef : (parts.card : ℝ) ^ 2 * Hsame ≤
        Couter * (M * N) ^ ε * (M + N ^ (2 : ℝ)) := by
      calc
        _ ≤ (Hclass ^ 2 * Clog ^ 2 * N ^ (2 * θ)) * Hsame :=
          mul_le_mul_of_nonneg_right hpartsSq hHsame
        _ = Cbase *
              (Cdiag * M ^ (1 + θ) * N ^ (3 * θ) +
                Cpair * B ^ θ * Ccount * N ^ (2 + 7 * θ)) := hcoeffRewrite
        _ = Cbase *
              (Cdiag * M ^ (1 + θ) * N ^ (3 * θ) + Q * N ^ (2 + 7 * θ)) := by
          rfl
        _ ≤ Cbase * ((Cdiag + Q) * (M * N) ^ ε * (M + N ^ (2 : ℝ))) :=
          mul_le_mul_of_nonneg_left htermBound (by positivity)
        _ = Couter * (M * N) ^ ε * (M + N ^ (2 : ℝ)) := by
          dsimp [Couter, Cbase, Q]
          ring
    have hfiniteEnergy := qs_finite_energy_le_high_M2 F W hW M N hMpos z
    calc
      _ ≤ (parts.card : ℝ) ^ 2 * Hsame * V := hfiniteEnergy.trans hwholeSq
      _ ≤ Couter * (M * N) ^ ε * (M + N ^ (2 : ℝ)) * V :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
  exact qs_norm_le_of_energy_M0 F M N
    (Couter * (M * N) ^ ε * (M + N ^ (2 : ℝ))) (by positivity) hEnergyAll

end ArtinPrimitiveRoots.A2
