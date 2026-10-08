import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0

/-!
# Bilinear divisor-pair bound (helpers for C2)

Arithmetic helpers (admissible divisors and cofactors, inclusion–exclusion for coprimality over
a finite prime set, the count `2^{ω(c)} ≤ τ(c)`) and the bilinear core: for coefficient vectors
on admissible columns, divisor weights and a bounded row weight,
`|Σ_{(c,d)=1} z₁(c) z̄₂(d) Σ_{e₁∣c, e₂∣d} μ(e₁e₂) Σ_a w(a,e₁e₂) χ_c(a) χ_d(a)|`
is bounded by Cauchy–Schwarz in the rows and the up-to matrix norms at the reduced lengths.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain Finset UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSC2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-! ### Arithmetic of admissible ideals -/

theorem ne_bot_of_QSAdm {c : Ideal (𝓞 K)} (hc : QSAdm m qS c) : c ≠ ⊥ := hc.2.1.1

omit [NumberField K] in
theorem isCoprime_of_le {I J L : Ideal (𝓞 K)} (h : IsCoprime I L) (hIJ : I ≤ J) :
    IsCoprime J L := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact eq_top_iff.mpr (h ▸ sup_le_sup_right hIJ L)

theorem QSAdm_of_dvd {c e : Ideal (𝓞 K)} (hc : QSAdm m qS c) (he : e ∣ c) : QSAdm m qS e := by
  obtain ⟨hsq, hcm, hcq⟩ := hc
  have hle : c ≤ e := Ideal.le_of_dvd he
  refine ⟨hsq.squarefree_of_dvd he, ?_, isCoprime_of_le hcq hle⟩
  rw [qs_isCoprimeTo_iff_M0] at hcm ⊢
  refine ⟨?_, isCoprime_of_le hcm.2 hle⟩
  rintro rfl
  exact hcm.1 (eq_bot_iff.mpr (Ideal.le_of_dvd he))

/-- A squarefree ideal splits as `c = e c'` with `e, c'` coprime. -/
theorem exists_cofactor {c e : Ideal (𝓞 K)} (hc : Squarefree c) (he : e ∣ c) :
    ∃ c' : Ideal (𝓞 K), c = e * c' ∧ IsCoprime e c' := by
  obtain ⟨c', rfl⟩ := he
  refine ⟨c', rfl, ?_⟩
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have h1 : P ∣ e := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
  have h2 : P ∣ c' := Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle)
  have := hc P (mul_dvd_mul h1 h2)
  exact hP.ne_top (Ideal.isUnit_iff.mp this)

theorem qsN_mul (I J : Ideal (𝓞 K)) : qsN (I * J) = qsN I * qsN J := by
  simp [qsN, map_mul]

theorem qsN_pos {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 0 < qsN I := by
  have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
  simp only [qsN]
  exact_mod_cast Nat.pos_of_ne_zero this

theorem norm_idealValue_le_one (F : QSFamily m qS) {c : Ideal (𝓞 K)} (hc : QSAdm m qS c)
    (I : Ideal (𝓞 K)) : ‖(F.character c).idealValue I‖ ≤ 1 := by
  rcases F.quadraticValues c hc.1 hc.2.1 I with h | h
  · rw [h]; simp
  · have : ‖(F.character c).idealValue I‖ ^ 2 = 1 := by rw [← norm_pow, h, norm_one]
    have h0 := norm_nonneg ((F.character c).idealValue I)
    nlinarith

theorem mem_qsDivisors {I e : Ideal (𝓞 K)} (hI : I ≠ ⊥) : e ∈ qsDivisors I ↔ e ∣ I := by
  classical
  unfold qsDivisors
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, and_iff_right_iff_imp]
  intro he
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd he))

/-! ### Inclusion–exclusion for coprimality -/

open Classical in
/-- All primes dividing some column. -/
def primeSet (cols : Finset (Ideal (𝓞 K))) : Finset (Ideal (𝓞 K)) :=
  cols.biUnion (fun c => (normalizedFactors c).toFinset)

theorem mem_primeSet_of_dvd {cols : Finset (Ideal (𝓞 K))} {c P : Ideal (𝓞 K)} (hc : c ∈ cols)
    (hc0 : c ≠ ⊥) (hP : P.IsMaximal) (hPc : P ∣ c) : P ∈ primeSet cols := by
  classical
  unfold primeSet
  rw [Finset.mem_biUnion]
  refine ⟨c, hc, ?_⟩
  rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hc0]
  exact ⟨hP.isPrime, Ideal.le_of_dvd hPc⟩

theorem prime_of_mem_primeSet {cols : Finset (Ideal (𝓞 K))} {P : Ideal (𝓞 K)}
    (hP : P ∈ primeSet cols) : Prime P := by
  classical
  unfold primeSet at hP
  rw [Finset.mem_biUnion] at hP
  obtain ⟨c, _, hc⟩ := hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hc)

open Classical in
/-- `1_{(c,d)=1} = Σ_{T ⊆ 𝒫} (-1)^{|T|} 1_{T ∣ c} 1_{T ∣ d}`. -/
theorem coprime_indicator {cols : Finset (Ideal (𝓞 K))} {c d : Ideal (𝓞 K)} (hc : c ∈ cols)
    (hc0 : c ≠ ⊥) :
    (if IsCoprime c d then (1 : ℂ) else 0) =
      ∑ T ∈ (primeSet cols).powerset, (-1 : ℂ) ^ T.card *
        ((if ∀ P ∈ T, P ∣ c then (1 : ℂ) else 0) * (if ∀ P ∈ T, P ∣ d then (1 : ℂ) else 0)) := by
  have hprod : ∏ P ∈ primeSet cols, ((-(if P ∣ c ∧ P ∣ d then (1 : ℂ) else 0)) + 1) =
      ∑ T ∈ (primeSet cols).powerset, (-1 : ℂ) ^ T.card *
        ((if ∀ P ∈ T, P ∣ c then (1 : ℂ) else 0) * (if ∀ P ∈ T, P ∣ d then (1 : ℂ) else 0)) := by
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl (fun T hT => ?_)
    rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_boole]
    congr 1
    simp only [forall₂_and]
    split_ifs <;> simp_all
  rw [← hprod]
  by_cases hcd : IsCoprime c d
  · rw [if_pos hcd]
    symm
    refine Finset.prod_eq_one (fun P hP => ?_)
    have hnot : ¬ (P ∣ c ∧ P ∣ d) := by
      rintro ⟨h1, h2⟩
      have hPp := prime_of_mem_primeSet hP
      rw [Ideal.isCoprime_iff_sup_eq] at hcd
      have : c ⊔ d ≤ P := sup_le (Ideal.le_of_dvd h1) (Ideal.le_of_dvd h2)
      rw [hcd] at this
      exact hPp.ne_one (by rw [Ideal.one_eq_top]; exact eq_top_iff.mpr this)
    simp [hnot]
  · rw [if_neg hcd]
    symm
    rw [Ideal.isCoprime_iff_sup_eq] at hcd
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hcd
    have h1 : P ∣ c := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
    have h2 : P ∣ d := Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle)
    refine Finset.prod_eq_zero (mem_primeSet_of_dvd hc hc0 hP h1) ?_
    simp [h1, h2]

theorem maximal_of_mem_primeSet {cols : Finset (Ideal (𝓞 K))} {P : Ideal (𝓞 K)}
    (hP : P ∈ primeSet cols) : P.IsMaximal := by
  have hp := prime_of_mem_primeSet hP
  have h0 : P ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero
  exact Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hp) h0

theorem mem_of_dvd_prod {cols T : Finset (Ideal (𝓞 K))} {P : Ideal (𝓞 K)}
    (hT : T ⊆ primeSet cols) (hP : P ∈ primeSet cols) (hd : P ∣ ∏ Q ∈ T, Q) : P ∈ T := by
  obtain ⟨Q, hQ, hPQ⟩ := ((prime_of_mem_primeSet hP).dvd_finsetProd_iff (fun Q => Q)).mp hd
  have hQm := maximal_of_mem_primeSet (hT hQ)
  have hPm := maximal_of_mem_primeSet hP
  have : Q = P := hQm.eq_of_le hPm.ne_top (Ideal.le_of_dvd hPQ)
  exact this ▸ hQ

open Classical in
/-- `2^{ω(c)} ≤ τ(c)`: subsets of `𝒫` dividing `c` inject into the divisors of `c`. -/
theorem card_dvd_subsets_le {cols : Finset (Ideal (𝓞 K))} {c : Ideal (𝓞 K)} (hc : c ≠ ⊥) :
    ((primeSet cols).powerset.filter (fun T => ∀ P ∈ T, P ∣ c)).card ≤ (qsDivisors c).card := by
  refine Finset.card_le_card_of_injOn (fun T => ∏ P ∈ T, P) ?_ ?_
  · intro T hT
    rw [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hT
    rw [Finset.mem_coe, mem_qsDivisors hc]
    refine Finset.prod_dvd_of_coprime ?_ hT.2
    intro P hP Q hQ hPQ
    have := maximal_of_mem_primeSet (hT.1 hP)
    have := maximal_of_mem_primeSet (hT.1 hQ)
    exact Ideal.isCoprime_of_isMaximal hPQ
  · intro T₁ hT₁ T₂ hT₂ heq
    rw [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hT₁ hT₂
    simp only at heq
    ext P
    constructor
    · intro hP
      exact mem_of_dvd_prod hT₂.1 (hT₁.1 hP) (heq ▸ Finset.dvd_prod_of_mem _ hP)
    · intro hP
      exact mem_of_dvd_prod hT₁.1 (hT₂.1 hP) (heq.symm ▸ Finset.dvd_prod_of_mem _ hP)

theorem norm_qsMu_le (e : Ideal (𝓞 K)) : ‖((qsMu e : ℤ) : ℂ)‖ ≤ 1 := by
  unfold qsMu
  split_ifs <;> simp

theorem isCoprime_of_squarefree_mul {e c : Ideal (𝓞 K)} (h : Squarefree (e * c)) :
    IsCoprime e c := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have h1 : P ∣ e := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
  have h2 : P ∣ c := Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle)
  exact hP.ne_top (Ideal.isUnit_iff.mp (h P (mul_dvd_mul h1 h2)))

theorem mem_qsUpTo {I : Ideal (𝓞 K)} {Y : ℝ} :
    I ∈ qsUpTo m qS Y ↔ QSAdm m qS I ∧ qsN I ≤ Y := by
  classical
  unfold qsUpTo
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2⟩
    refine ⟨Nat.le_floor h2, h1, h2⟩

/-! ### Reindexing columns divisible by a fixed divisor -/

open Classical in
theorem sum_reindex_mul {M : Type*} [AddCommMonoid M] (cols : Finset (Ideal (𝓞 K)))
    (q : Ideal (𝓞 K) → Prop) [DecidablePred q] (e : Ideal (𝓞 K)) (he : e ≠ ⊥) (X D : ℝ) (hD : 0 < D)
    (heD : D ≤ qsN e) (hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ X) (G : Ideal (𝓞 K) → M) :
    ∑ c' ∈ qsUpTo m qS (X / D), (if e * c' ∈ cols ∧ q (e * c') then G (e * c') else 0) =
      ∑ c ∈ cols, if q c ∧ e ∣ c then G c else 0 := by
  have he0 : e ≠ 0 := by rwa [Ideal.zero_eq_bot]
  refine Finset.sum_bij_ne_zero (fun c' _ _ => e * c') ?_ ?_ ?_ ?_
  · intro c' _ h
    by_contra hn
    exact h (if_neg (fun h' => hn h'.1))
  · intro c₁ _ _ c₂ _ _ h
    exact mul_left_cancel₀ he0 h
  · intro c hc hne
    have hqc : q c ∧ e ∣ c := by
      by_contra hn
      exact hne (if_neg hn)
    obtain ⟨c', rfl⟩ := hqc.2
    have hadm := (hcols _ hc).1
    have hc'adm : QSAdm m qS c' := QSAdm_of_dvd hadm (Dvd.intro_left _ rfl)
    have hNe : 0 < qsN e := lt_of_lt_of_le hD heD
    have hX : qsN (e * c') ≤ X := (hcols _ hc).2
    rw [qsN_mul] at hX
    have hX0 : 0 ≤ X := le_trans (by positivity) hX
    have hc'N : qsN c' ≤ X / D := by
      calc qsN c' ≤ X / qsN e := by
            rw [le_div_iff₀ hNe]; linarith
        _ ≤ X / D := div_le_div_of_nonneg_left hX0 hD heD
    refine ⟨c', mem_qsUpTo.mpr ⟨hc'adm, hc'N⟩, ?_, rfl⟩
    rw [if_pos ⟨hc, hqc.1⟩]
    rwa [if_pos hqc] at hne
  · intro c' _ h
    have hmem : e * c' ∈ cols := by
      by_contra hn
      exact h (if_neg (fun h' => hn h'.1))
    simp [hmem]

open Classical in
/-- Energy of the columns divisible by `e`: `c = e c'`, `χ_c = χ_e χ_{c'}`, then M0 at the
reduced length `X / D`. -/
theorem energy_divisor (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (cols rows : Finset (Ideal (𝓞 K))) (q : Ideal (𝓞 K) → Prop) [DecidablePred q]
    (e : Ideal (𝓞 K)) (he : QSAdm m qS e) (X R D : ℝ) (hD : 0 < D) (heD : D ≤ qsN e)
    (hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ X)
    (hrows : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ R) (z : Ideal (𝓞 K) → ℂ) :
    ∑ a ∈ rows, ‖∑ c ∈ cols, if q c ∧ e ∣ c then z c * (F.character c).idealValue a else 0‖ ^ 2 ≤
      qsNorm F R (X / D) * ∑ c ∈ cols, if q c ∧ e ∣ c then ‖z c‖ ^ 2 else 0 := by
  set y : Ideal (𝓞 K) → ℂ := fun c' => if e * c' ∈ cols ∧ q (e * c') then z (e * c') else 0
    with hy
  have he0 := ne_bot_of_QSAdm he
  have hrow : ∀ a ∈ rows,
      (∑ c ∈ cols, if q c ∧ e ∣ c then z c * (F.character c).idealValue a else 0) =
        (F.character e).idealValue a *
          ∑ c' ∈ qsUpTo m qS (X / D), y c' * (F.character c').idealValue a := by
    intro a ha
    rw [← sum_reindex_mul cols q e he0 X D hD heD hcols, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c' _ => ?_)
    simp only [hy]
    split_ifs with h
    · have hsq := (hcols _ h.1).1
      have hc' : QSAdm m qS c' := QSAdm_of_dvd hsq (Dvd.intro_left _ rfl)
      have hcop : IsCoprime e c' := isCoprime_of_squarefree_mul hsq.1
      have haA := (hrows a ha).1
      rw [qs_family_mul_S0 F hrf e c' he hc' hcop a haA.2.1 haA.2.2]
      ring
    · simp
  calc ∑ a ∈ rows, ‖∑ c ∈ cols, if q c ∧ e ∣ c then z c * (F.character c).idealValue a else 0‖ ^ 2
      = ∑ a ∈ rows, ‖(F.character e).idealValue a *
          ∑ c' ∈ qsUpTo m qS (X / D), y c' * (F.character c').idealValue a‖ ^ 2 :=
        Finset.sum_congr rfl (fun a ha => by rw [hrow a ha])
    _ ≤ ∑ a ∈ rows, ‖∑ c' ∈ qsUpTo m qS (X / D), y c' * (F.character c').idealValue a‖ ^ 2 := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        rw [norm_mul, mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _)
          (pow_le_one₀ (norm_nonneg _) (norm_idealValue_le_one F he a))
    _ ≤ ∑ a ∈ qsUpTo m qS R,
          ‖∑ c' ∈ qsUpTo m qS (X / D), y c' * (F.character c').idealValue a‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_) (fun _ _ _ => sq_nonneg _)
        exact mem_qsUpTo.mpr (hrows a ha)
    _ ≤ qsNorm F R (X / D) * ∑ c' ∈ qsUpTo m qS (X / D), ‖y c'‖ ^ 2 :=
        qs_energy_le_norm_M0 F R (X / D) y
    _ = qsNorm F R (X / D) * ∑ c ∈ cols, if q c ∧ e ∣ c then ‖z c‖ ^ 2 else 0 := by
        congr 1
        rw [← sum_reindex_mul cols q e he0 X D hD heD hcols (fun c => ‖z c‖ ^ 2)]
        refine Finset.sum_congr rfl (fun c' _ => ?_)
        simp only [hy]
        split_ifs <;> simp

/-! ### The bilinear core -/

theorem sum5_comm {M : Type*} [AddCommMonoid M] {α β γ δ ε : Type*} (s₁ : Finset α)
    (s₂ : Finset β) (s₃ : Finset γ) (s₄ : Finset δ) (s₅ : Finset ε)
    (f : α → β → γ → δ → ε → M) :
    ∑ c ∈ s₁, ∑ d ∈ s₂, ∑ x ∈ s₃, ∑ y ∈ s₄, ∑ a ∈ s₅, f c d x y a =
      ∑ x ∈ s₃, ∑ y ∈ s₄, ∑ a ∈ s₅, ∑ c ∈ s₁, ∑ d ∈ s₂, f c d x y a := by
  calc _ = ∑ c ∈ s₁, ∑ x ∈ s₃, ∑ d ∈ s₂, ∑ y ∈ s₄, ∑ a ∈ s₅, f c d x y a :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ x ∈ s₃, ∑ c ∈ s₁, ∑ d ∈ s₂, ∑ y ∈ s₄, ∑ a ∈ s₅, f c d x y a := Finset.sum_comm
    _ = ∑ x ∈ s₃, ∑ c ∈ s₁, ∑ y ∈ s₄, ∑ d ∈ s₂, ∑ a ∈ s₅, f c d x y a :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ x ∈ s₃, ∑ y ∈ s₄, ∑ c ∈ s₁, ∑ d ∈ s₂, ∑ a ∈ s₅, f c d x y a :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ s₃, ∑ y ∈ s₄, ∑ c ∈ s₁, ∑ a ∈ s₅, ∑ d ∈ s₂, f c d x y a :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ x ∈ s₃, ∑ y ∈ s₄, ∑ a ∈ s₅, ∑ c ∈ s₁, ∑ d ∈ s₂, f c d x y a :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm

open Classical in
theorem divisors_filter_eq (cols : Finset (Ideal (𝓞 K))) (p : Ideal (𝓞 K) → Prop)
    [DecidablePred p] (hcols : ∀ c ∈ cols, c ≠ ⊥) {c : Ideal (𝓞 K)} (hc : c ∈ cols) :
    (qsDivisors c).filter p = (cols.biUnion fun c => (qsDivisors c).filter p).filter (· ∣ c) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨he, hp⟩
    exact ⟨⟨c, hc, he, hp⟩, (mem_qsDivisors (hcols c hc)).mp he⟩
  · rintro ⟨⟨c', hc', _, hp⟩, hdvd⟩
    exact ⟨(mem_qsDivisors (hcols c hc)).mpr hdvd, hp⟩

open Classical in
theorem mem_divisorUnion (cols : Finset (Ideal (𝓞 K))) (p : Ideal (𝓞 K) → Prop)
    [DecidablePred p] (hcols : ∀ c ∈ cols, QSAdm m qS c) {e : Ideal (𝓞 K)}
    (he : e ∈ cols.biUnion fun c => (qsDivisors c).filter p) : QSAdm m qS e ∧ p e := by
  simp only [Finset.mem_filter, Finset.mem_biUnion] at he
  obtain ⟨c, hc, he, hp⟩ := he
  exact ⟨QSAdm_of_dvd (hcols c hc) ((mem_qsDivisors (ne_bot_of_QSAdm (hcols c hc))).mp he), hp⟩

open Classical in
theorem sum_ite_dvd_le (cols : Finset (Ideal (𝓞 K))) (p : Ideal (𝓞 K) → Prop)
    [DecidablePred p] (hcols : ∀ c ∈ cols, c ≠ ⊥) (q : Ideal (𝓞 K) → Prop) [DecidablePred q]
    (Z : ℝ) (τ : ℝ)
    {c : Ideal (𝓞 K)} (hc : c ∈ cols) (hτ : ((qsDivisors c).card : ℝ) ≤ τ) :
    ∑ e ∈ cols.biUnion (fun c => (qsDivisors c).filter p),
        (if q c ∧ e ∣ c then Z ^ 2 else 0) ≤ if q c then τ * Z ^ 2 else 0 := by
  by_cases hq : q c
  · simp only [hq, true_and, if_true]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right (le_trans ?_ hτ) (sq_nonneg _)
    rw [← divisors_filter_eq cols p hcols hc]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  · simp [hq]

open Classical in
/-- The bilinear bound for columns restricted by a predicate `q` (coprimality removed). -/
theorem pair_bound_q (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (p₁ p₂ : Ideal (𝓞 K) → Prop) [DecidablePred p₁] [DecidablePred p₂]
    (X R D₁ D₂ W τ : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (cols rows : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ X)
    (hrows : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ R)
    (hp₁ : ∀ e, p₁ e → D₁ ≤ qsN e) (hp₂ : ∀ e, p₂ e → D₂ ≤ qsN e)
    (hτ : ∀ c ∈ cols, ((qsDivisors c).card : ℝ) ≤ τ) (hτ0 : 0 ≤ τ)
    (z₁ z₂ : Ideal (𝓞 K) → ℂ) (Z : Ideal (𝓞 K) → ℝ) (hz₁ : ∀ c, ‖z₁ c‖ ≤ Z c)
    (hz₂ : ∀ c, ‖z₂ c‖ ≤ Z c)
    (w : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (hw : ∀ a e₁ e₂, ‖w a e₁ e₂‖ ≤ W)
    (q : Ideal (𝓞 K) → Prop) [DecidablePred q] :
    ‖∑ c ∈ cols, ∑ d ∈ cols, ((if q c then (1 : ℂ) else 0) * (if q d then (1 : ℂ) else 0)) *
        (z₁ c * z₂ d * ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
          (qsMu (e₁ * e₂) : ℂ) * ∑ a ∈ rows, w a e₁ e₂ * (F.character c).idealValue a *
            (F.character d).idealValue a)‖ ≤
      W * Real.sqrt (qsNorm F R (X / D₁) * qsNorm F R (X / D₂)) *
        Real.sqrt (((cols.biUnion fun c => (qsDivisors c).filter p₁).card : ℝ) *
          ((cols.biUnion fun c => (qsDivisors c).filter p₂).card : ℝ)) * τ *
        ∑ c ∈ cols, if q c then Z c ^ 2 else 0 := by
  set E₁ := cols.biUnion fun c => (qsDivisors c).filter p₁ with hE₁
  set E₂ := cols.biUnion fun c => (qsDivisors c).filter p₂ with hE₂
  set N₁ := qsNorm F R (X / D₁) with hN₁def
  set N₂ := qsNorm F R (X / D₂) with hN₂def
  set Y := ∑ c ∈ cols, if q c then Z c ^ 2 else 0 with hYdef
  have hW : 0 ≤ W := le_trans (norm_nonneg _) (hw ⊥ ⊥ ⊥)
  have hZ : ∀ c, 0 ≤ Z c := fun c => le_trans (norm_nonneg _) (hz₁ c)
  have hN₁ : 0 ≤ N₁ := by rw [hN₁def, qsNorm]; positivity
  have hN₂ : 0 ≤ N₂ := by rw [hN₂def, qsNorm]; positivity
  have hY : 0 ≤ Y := Finset.sum_nonneg fun c _ => by split_ifs <;> positivity
  have hne : ∀ c ∈ cols, c ≠ ⊥ := fun c hc => ne_bot_of_QSAdm (hcols c hc).1
  have hadm : ∀ c ∈ cols, QSAdm m qS c := fun c hc => (hcols c hc).1
  set U : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun e a =>
    ∑ c ∈ cols, if q c ∧ e ∣ c then z₁ c * (F.character c).idealValue a else 0 with hU
  set V : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun e a =>
    ∑ d ∈ cols, if q d ∧ e ∣ d then z₂ d * (F.character d).idealValue a else 0 with hV
  have heq : (∑ c ∈ cols, ∑ d ∈ cols,
      ((if q c then (1 : ℂ) else 0) * (if q d then (1 : ℂ) else 0)) *
        (z₁ c * z₂ d * ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
          (qsMu (e₁ * e₂) : ℂ) * ∑ a ∈ rows, w a e₁ e₂ * (F.character c).idealValue a *
            (F.character d).idealValue a)) =
      ∑ e₁ ∈ E₁, ∑ e₂ ∈ E₂, ∑ a ∈ rows,
        ((qsMu (e₁ * e₂) : ℂ) * w a e₁ e₂) * (U e₁ a * V e₂ a) := by
    have h1 : ∀ e₁ e₂ a, ((qsMu (e₁ * e₂) : ℂ) * w a e₁ e₂) * (U e₁ a * V e₂ a) =
        ∑ c ∈ cols, ∑ d ∈ cols, ((qsMu (e₁ * e₂) : ℂ) * w a e₁ e₂) *
          ((if q c ∧ e₁ ∣ c then z₁ c * (F.character c).idealValue a else 0) *
            (if q d ∧ e₂ ∣ d then z₂ d * (F.character d).idealValue a else 0)) := by
      intro e₁ e₂ a
      rw [hU, hV]
      simp only
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
    simp only [h1]
    rw [← sum5_comm]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
    rw [divisors_filter_eq cols p₁ hne hc, divisors_filter_eq cols p₂ hne hd]
    simp only [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    by_cases h₁ : e₁ ∣ c
    · simp only [h₁, if_true, and_true, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e₂ _ => ?_
      by_cases h₂ : e₂ ∣ d
      · simp only [h₂, if_true, and_true, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hqc : q c <;> by_cases hqd : q d <;> simp [hqc, hqd] <;> ring
      · simp [h₂]
    · simp [h₁]
  rw [heq]
  set Z₁ : Ideal (𝓞 K) → ℝ := fun e => ∑ c ∈ cols, if q c ∧ e ∣ c then Z c ^ 2 else 0 with hZ₁
  have hZ₁0 : ∀ e, 0 ≤ Z₁ e := fun e => Finset.sum_nonneg fun c _ => by
    split_ifs <;> positivity
  have hUb : ∀ e ∈ E₁, ∑ a ∈ rows, ‖U e a‖ ^ 2 ≤ N₁ * Z₁ e := by
    intro e he
    obtain ⟨heA, hep⟩ := mem_divisorUnion cols p₁ hadm he
    calc _ ≤ N₁ * ∑ c ∈ cols, if q c ∧ e ∣ c then ‖z₁ c‖ ^ 2 else 0 :=
          energy_divisor F hrf cols rows q e heA X R D₁ hD₁ (hp₁ e hep) hcols hrows z₁
      _ ≤ N₁ * Z₁ e := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) hN₁
          split_ifs
          · exact pow_le_pow_left₀ (norm_nonneg _) (hz₁ c) 2
          · exact le_rfl
  have hVb : ∀ e ∈ E₂, ∑ a ∈ rows, ‖V e a‖ ^ 2 ≤ N₂ * Z₁ e := by
    intro e he
    obtain ⟨heA, hep⟩ := mem_divisorUnion cols p₂ hadm he
    calc _ ≤ N₂ * ∑ c ∈ cols, if q c ∧ e ∣ c then ‖z₂ c‖ ^ 2 else 0 :=
          energy_divisor F hrf cols rows q e heA X R D₂ hD₂ (hp₂ e hep) hcols hrows z₂
      _ ≤ N₂ * Z₁ e := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) hN₂
          split_ifs
          · exact pow_le_pow_left₀ (norm_nonneg _) (hz₂ c) 2
          · exact le_rfl
  have hsumZ : ∀ (p : Ideal (𝓞 K) → Prop) [DecidablePred p],
      ∑ e ∈ cols.biUnion (fun c => (qsDivisors c).filter p), Z₁ e ≤ τ * Y := by
    intro p _
    rw [hZ₁]
    simp only
    rw [Finset.sum_comm, hYdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    refine (sum_ite_dvd_le cols p hne q (Z c) τ hc (hτ c hc)).trans ?_
    split_ifs <;> simp
  have hsq : ∀ (E : Finset (Ideal (𝓞 K))), ∑ e ∈ E, Z₁ e ≤ τ * Y →
      ∑ e ∈ E, Real.sqrt (Z₁ e) ≤ Real.sqrt ((E.card : ℝ) * (τ * Y)) := by
    intro E hE
    calc ∑ e ∈ E, Real.sqrt (Z₁ e) = ∑ e ∈ E, Real.sqrt 1 * Real.sqrt (Z₁ e) := by simp
      _ ≤ Real.sqrt (∑ e ∈ E, (1 : ℝ)) * Real.sqrt (∑ e ∈ E, Z₁ e) :=
          Real.sum_sqrt_mul_sqrt_le E (fun _ => zero_le_one) hZ₁0
      _ ≤ Real.sqrt (E.card : ℝ) * Real.sqrt (τ * Y) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (Real.sqrt_nonneg _)
      _ = Real.sqrt ((E.card : ℝ) * (τ * Y)) := (Real.sqrt_mul (by positivity) _).symm
  calc ‖∑ e₁ ∈ E₁, ∑ e₂ ∈ E₂, ∑ a ∈ rows,
          ((qsMu (e₁ * e₂) : ℂ) * w a e₁ e₂) * (U e₁ a * V e₂ a)‖
      ≤ ∑ e₁ ∈ E₁, ∑ e₂ ∈ E₂, W * (Real.sqrt (N₁ * Z₁ e₁) * Real.sqrt (N₂ * Z₁ e₂)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e₁ he₁ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun e₂ he₂ => ?_))
        calc _ ≤ ∑ a ∈ rows, ‖((qsMu (e₁ * e₂) : ℂ) * w a e₁ e₂) * (U e₁ a * V e₂ a)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ a ∈ rows, W * (‖U e₁ a‖ * ‖V e₂ a‖) := by
              refine Finset.sum_le_sum fun a _ => ?_
              rw [norm_mul, norm_mul, norm_mul]
              have hmw : ‖((qsMu (e₁ * e₂) : ℤ) : ℂ)‖ * ‖w a e₁ e₂‖ ≤ W := by
                calc _ ≤ 1 * W := mul_le_mul (norm_qsMu_le _) (hw a e₁ e₂) (norm_nonneg _)
                      zero_le_one
                  _ = W := one_mul W
              exact mul_le_mul_of_nonneg_right hmw (by positivity)
          _ = W * ∑ a ∈ rows, ‖U e₁ a‖ * ‖V e₂ a‖ := by rw [Finset.mul_sum]
          _ ≤ W * (Real.sqrt (∑ a ∈ rows, ‖U e₁ a‖ ^ 2) *
                Real.sqrt (∑ a ∈ rows, ‖V e₂ a‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hW
          _ ≤ W * (Real.sqrt (N₁ * Z₁ e₁) * Real.sqrt (N₂ * Z₁ e₂)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt (hUb e₁ he₁))
                (Real.sqrt_le_sqrt (hVb e₂ he₂)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hW
    _ = W * Real.sqrt N₁ * Real.sqrt N₂ *
          ∑ e₁ ∈ E₁, ∑ e₂ ∈ E₂, Real.sqrt (Z₁ e₁) * Real.sqrt (Z₁ e₂) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun e₂ _ => ?_
        rw [Real.sqrt_mul hN₁, Real.sqrt_mul hN₂]
        ring
    _ = W * Real.sqrt N₁ * Real.sqrt N₂ *
          ((∑ e₁ ∈ E₁, Real.sqrt (Z₁ e₁)) * ∑ e₂ ∈ E₂, Real.sqrt (Z₁ e₂)) := by
        rw [Finset.sum_mul_sum]
    _ ≤ W * Real.sqrt N₁ * Real.sqrt N₂ *
          (Real.sqrt ((E₁.card : ℝ) * (τ * Y)) * Real.sqrt ((E₂.card : ℝ) * (τ * Y))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (hsq E₁ (hsumZ p₁)) (hsq E₂ (hsumZ p₂))
          (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
    _ = W * Real.sqrt (N₁ * N₂) * Real.sqrt ((E₁.card : ℝ) * (E₂.card : ℝ)) * τ * Y := by
        have hτY : 0 ≤ τ * Y := mul_nonneg hτ0 hY
        rw [← Real.sqrt_mul (by positivity),
          show (E₁.card : ℝ) * (τ * Y) * ((E₂.card : ℝ) * (τ * Y)) =
            ((E₁.card : ℝ) * (E₂.card : ℝ)) * (τ * Y) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hτY, Real.sqrt_mul hN₁]
        ring

open Classical in
/-- The bilinear core with the coprimality condition, by inclusion–exclusion over `primeSet`:
`‖Σ_{(c,d)=1} …‖ ≤ W √(N₁N₂) √(#E₁ #E₂) τ² Σ Z²`. -/
theorem core_bound (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (p₁ p₂ : Ideal (𝓞 K) → Prop) [DecidablePred p₁] [DecidablePred p₂]
    (X R D₁ D₂ W τ : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (cols rows : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ X)
    (hrows : ∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ R)
    (hp₁ : ∀ e, p₁ e → D₁ ≤ qsN e) (hp₂ : ∀ e, p₂ e → D₂ ≤ qsN e)
    (hτ : ∀ c ∈ cols, ((qsDivisors c).card : ℝ) ≤ τ) (hτ0 : 0 ≤ τ)
    (z₁ z₂ : Ideal (𝓞 K) → ℂ) (Z : Ideal (𝓞 K) → ℝ) (hz₁ : ∀ c, ‖z₁ c‖ ≤ Z c)
    (hz₂ : ∀ c, ‖z₂ c‖ ≤ Z c)
    (w : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (hw : ∀ a e₁ e₂, ‖w a e₁ e₂‖ ≤ W) :
    ‖∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then z₁ c * z₂ d *
        ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
          (qsMu (e₁ * e₂) : ℂ) * ∑ a ∈ rows, w a e₁ e₂ * (F.character c).idealValue a *
            (F.character d).idealValue a else 0‖ ≤
      W * Real.sqrt (qsNorm F R (X / D₁) * qsNorm F R (X / D₂)) *
        Real.sqrt (((cols.biUnion fun c => (qsDivisors c).filter p₁).card : ℝ) *
          ((cols.biUnion fun c => (qsDivisors c).filter p₂).card : ℝ)) * τ ^ 2 *
        ∑ c ∈ cols, Z c ^ 2 := by
  set A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun c d => z₁ c * z₂ d *
        ∑ e₁ ∈ (qsDivisors c).filter p₁, ∑ e₂ ∈ (qsDivisors d).filter p₂,
          (qsMu (e₁ * e₂) : ℂ) * ∑ a ∈ rows, w a e₁ e₂ * (F.character c).idealValue a *
            (F.character d).idealValue a with hA
  set K₀ := W * Real.sqrt (qsNorm F R (X / D₁) * qsNorm F R (X / D₂)) *
        Real.sqrt (((cols.biUnion fun c => (qsDivisors c).filter p₁).card : ℝ) *
          ((cols.biUnion fun c => (qsDivisors c).filter p₂).card : ℝ)) with hK₀
  have hW : 0 ≤ W := le_trans (norm_nonneg _) (hw ⊥ ⊥ ⊥)
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hZ : ∀ c, 0 ≤ Z c := fun c => le_trans (norm_nonneg _) (hz₁ c)
  have hne : ∀ c ∈ cols, c ≠ ⊥ := fun c hc => ne_bot_of_QSAdm (hcols c hc).1
  set ι : Finset (Ideal (𝓞 K)) → Ideal (𝓞 K) → ℂ := fun T c =>
    if ∀ P ∈ T, P ∣ c then (1 : ℂ) else 0 with hι
  have hS : (∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then A c d else 0) =
      ∑ T ∈ (primeSet cols).powerset, (-1 : ℂ) ^ T.card *
        ∑ c ∈ cols, ∑ d ∈ cols, (ι T c * ι T d) * A c d := by
    calc (∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then A c d else 0)
        = ∑ c ∈ cols, ∑ d ∈ cols, ∑ T ∈ (primeSet cols).powerset,
            (-1 : ℂ) ^ T.card * ((ι T c * ι T d) * A c d) := by
          refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d _ => ?_
          rw [← boole_mul, coprime_indicator hc (hne c hc), Finset.sum_mul]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [hι]
          ring
      _ = ∑ c ∈ cols, ∑ T ∈ (primeSet cols).powerset, ∑ d ∈ cols,
            (-1 : ℂ) ^ T.card * ((ι T c * ι T d) * A c d) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ T ∈ (primeSet cols).powerset, ∑ c ∈ cols, ∑ d ∈ cols,
            (-1 : ℂ) ^ T.card * ((ι T c * ι T d) * A c d) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
  have hT : ∀ T : Finset (Ideal (𝓞 K)),
      ‖∑ c ∈ cols, ∑ d ∈ cols, (ι T c * ι T d) * A c d‖ ≤
        K₀ * τ * ∑ c ∈ cols, if (∀ P ∈ T, P ∣ c) then Z c ^ 2 else 0 := by
    intro T
    exact pair_bound_q F hrf p₁ p₂ X R D₁ D₂ W τ hD₁ hD₂ cols rows hcols hrows hp₁ hp₂ hτ hτ0
      z₁ z₂ Z hz₁ hz₂ w hw (fun c => ∀ P ∈ T, P ∣ c)
  have hcount : ∑ T ∈ (primeSet cols).powerset,
      (∑ c ∈ cols, if (∀ P ∈ T, P ∣ c) then Z c ^ 2 else 0) ≤ τ * ∑ c ∈ cols, Z c ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right (le_trans ?_ (hτ c hc)) (sq_nonneg _)
    exact_mod_cast card_dvd_subsets_le (hne c hc)
  show ‖∑ c ∈ cols, ∑ d ∈ cols, if IsCoprime c d then A c d else 0‖ ≤ K₀ * τ ^ 2 * _
  rw [hS]
  calc ‖∑ T ∈ (primeSet cols).powerset, (-1 : ℂ) ^ T.card *
          ∑ c ∈ cols, ∑ d ∈ cols, (ι T c * ι T d) * A c d‖
      ≤ ∑ T ∈ (primeSet cols).powerset,
          K₀ * τ * ∑ c ∈ cols, if (∀ P ∈ T, P ∣ c) then Z c ^ 2 else 0 := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun T _ => ?_)
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact hT T
    _ = K₀ * τ * ∑ T ∈ (primeSet cols).powerset,
          (∑ c ∈ cols, if (∀ P ∈ T, P ∣ c) then Z c ^ 2 else 0) := by rw [Finset.mul_sum]
    _ ≤ K₀ * τ * (τ * ∑ c ∈ cols, Z c ^ 2) :=
        mul_le_mul_of_nonneg_left hcount (mul_nonneg hK₀0 hτ0)
    _ = K₀ * τ ^ 2 * ∑ c ∈ cols, Z c ^ 2 := by ring

end ArtinPrimitiveRoots.A2.QSC2
