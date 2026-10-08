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

/-- M2 (IMPL over M2a, S0; RETIER `qs_hasExponent_two_M2`): `B1(M,N) ≪_ε (MN)^ε (M + N²)`. -/
theorem qs_hasExponent_two_M2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) :
    QSHasExponent F 2 := by
  sorry

end ArtinPrimitiveRoots.A2
