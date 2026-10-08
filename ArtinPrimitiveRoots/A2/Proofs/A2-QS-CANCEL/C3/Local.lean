import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2u

/-!
# Pair characters at fixed ideals as column twists; good and bad row parts

For an equal-class coprime admissible pair `(c, d)`, `ψ = χ_c χ_d⁻¹` has primitive conductor
`c d`, so at a squarefree ideal `I` coprime to `c d` it is unramified at every prime of `I` and
`ψ(I) = Π_{P ∣ I} χ_{c,P}(ϖ_P) · χ_{d,P}(ϖ_P)⁻¹ = twist_c(I) · twistInv_d(I)`: a product of a
function of `c` and a function of `d`, each of modulus one (local components of order two).
On rows coprime to `m` and `qS`, `ψ(a) = χ_c(a) χ_d(a)` (S0 gcd identity at `g = ⊤`).

Every squarefree row `a` splits as `a = a₂ a₁` with `a₂ = a ⊔ R ∣ R`, `R = qsModulusRad m * qS`,
and `a₁` admissible; the row sum regroups accordingly (`sum_rows_split`).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSC3

open QSC2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-! ### Local values and twists -/

/-- `χ_{c,v}(ϖ_v)`. -/
def locVal (F : QSFamily m qS) (c : Ideal (𝓞 K)) (v : A1.FinPlace K) : ℂ :=
  ((F.character c).loc v (A1.toLoc v (Units.mk0 (A1.unif v) (A1.unif_ne_zero v))) : ℂ)

open Classical in
/-- Column twist `Π_{P ∣ I} χ_{c,P}(ϖ_P)`. -/
def twist (F : QSFamily m qS) (c I : Ideal (𝓞 K)) : ℂ :=
  ((normalizedFactors I).map fun P =>
    if h : P.IsPrime ∧ P ≠ ⊥ then locVal F c ⟨P, h.1, h.2⟩ else 1).prod

open Classical in
/-- Column twist `Π_{P ∣ I} χ_{d,P}(ϖ_P)⁻¹`. -/
def twistInv (F : QSFamily m qS) (d I : Ideal (𝓞 K)) : ℂ :=
  ((normalizedFactors I).map fun P =>
    if h : P.IsPrime ∧ P ≠ ⊥ then (locVal F d ⟨P, h.1, h.2⟩)⁻¹ else 1).prod

theorem norm_multiset_prod_le_one {α : Type*} (s : Multiset α) (f : α → ℂ)
    (h : ∀ x ∈ s, ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (h a (Multiset.mem_cons_self a s)) (norm_nonneg _)
        (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem norm_locVal (F : QSFamily m qS) {c : Ideal (𝓞 K)} (hc : QSAdm m qS c)
    (v : A1.FinPlace K) : ‖locVal F c v‖ = 1 := by
  have h2 := F.character_order_two c hc.1 hc.2.1
  set x := A1.toLoc v (Units.mk0 (A1.unif v) (A1.unif_ne_zero v))
  have hsq : ((F.character c).loc v x) ^ 2 = 1 := by
    have := congrArg (fun χ : A1.HeckeChar K => χ.loc v x) h2
    simpa [A1.HeckeChar.loc, pow_two] using this
  have hsqC : (locVal F c v) ^ 2 = 1 := by
    unfold locVal
    rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  have h1 : ‖locVal F c v‖ ^ 2 = 1 := by rw [← norm_pow, hsqC, norm_one]
  have h0 := norm_nonneg (locVal F c v)
  nlinarith

theorem norm_twist_le (F : QSFamily m qS) {c : Ideal (𝓞 K)} (hc : QSAdm m qS c)
    (I : Ideal (𝓞 K)) : ‖twist F c I‖ ≤ 1 := by
  unfold twist
  refine norm_multiset_prod_le_one _ _ fun P _ => ?_
  split_ifs
  · exact (norm_locVal F hc _).le
  · simp

theorem norm_twistInv_le (F : QSFamily m qS) {c : Ideal (𝓞 K)} (hc : QSAdm m qS c)
    (I : Ideal (𝓞 K)) : ‖twistInv F c I‖ ≤ 1 := by
  unfold twistInv
  refine norm_multiset_prod_le_one _ _ fun P _ => ?_
  split_ifs
  · rw [norm_inv, norm_locVal F hc _, inv_one]
  · simp

theorem unramified_of_conductor (χ : A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf0 : f ≠ ⊥) (hcond : χ.ConductorDvd f) (v : A1.FinPlace K)
    (hnot : ¬ v.asIdeal ∣ f) : χ.UnramifiedAt v := by
  have hPrime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  have hexp0 : A1.idealExp v f = 0 := by
    dsimp [A1.idealExp]
    by_contra hne
    exact hnot ((Associates.count_ne_zero_iff_dvd hf0 hPrime.irreducible).mp hne)
  intro u hu huinv
  have hsub : (u : v.adicCompletion K) - 1 ∈ v.adicCompletionIntegers K :=
    (v.adicCompletionIntegers K).sub_mem hu (v.adicCompletionIntegers K).one_mem
  have hbound : Valued.v ((u : v.adicCompletion K) - 1) ≤ 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hsub
    exact hsub
  apply hcond v u hu huinv
  simpa [hexp0] using hbound

/-- `ψ_{c,d}(I) = twist_c(I) · twistInv_d(I)` for squarefree... in fact any nonzero `I` coprime
to `c d`. -/
theorem pairChar_eq_twist (F : QSFamily m qS) {c d : Ideal (𝓞 K)} (hc : QSAdm m qS c)
    (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (I : Ideal (𝓞 K)) (hI : IsCoprime I (c * d)) :
    (qsPairChar F c d).idealValue I = twist F c I * twistInv F d I := by
  obtain ⟨hc', hd', hclass⟩ := hcl
  have hprim := F.equalClass_product_conductor c d hc.1 hc' hd.1 hd' hcd hclass
  have hcd0 : c * d ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mul_ne_zero (by rw [Ideal.zero_eq_bot]; exact ne_bot_of_QSAdm hc)
      (by rw [Ideal.zero_eq_bot]; exact ne_bot_of_QSAdm hd)
  unfold twist twistInv
  rw [← Multiset.prod_map_mul]
  unfold A1.HeckeChar.idealValue
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  split_ifs with h
  · set v : A1.FinPlace K := ⟨P, h.1, h.2⟩
    have hnot : ¬ v.asIdeal ∣ c * d := by
      intro hdvd
      have hPI : P ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
      rw [Ideal.isCoprime_iff_sup_eq] at hI
      have hle : I ⊔ (c * d) ≤ P := sup_le (Ideal.le_of_dvd hPI) (Ideal.le_of_dvd hdvd)
      rw [hI] at hle
      exact h.1.ne_top (eq_top_iff.mpr hle)
    have hun := unramified_of_conductor _ _ hcd0 hprim.2.1 v hnot
    unfold A1.HeckeChar.primeValue
    rw [if_pos (show (qsPairChar F c d).UnramifiedAt v from hun)]
    unfold qsPairChar locVal
    simp [A1.HeckeChar.loc]
    exact Units.val_inv_eq_inv_val (α := ℂ) _
  · simp

theorem QSAdm_top : QSAdm m qS (⊤ : Ideal (𝓞 K)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(Ideal.one_eq_top).symm]; exact squarefree_one
  · rw [qs_isCoprimeTo_iff_M0]
    refine ⟨by simp, ?_⟩
    rw [(Ideal.one_eq_top).symm]; exact isCoprime_one_left
  · rw [(Ideal.one_eq_top).symm]; exact isCoprime_one_left

theorem conj_idealValue (F : QSFamily m qS) {d : Ideal (𝓞 K)} (hd : QSAdm m qS d)
    (a : Ideal (𝓞 K)) : conj ((F.character d).idealValue a) = (F.character d).idealValue a := by
  rcases F.quadraticValues d hd.1 hd.2.1 a with h | h
  · rw [h, map_zero]
  · have h' : (F.character d).idealValue a * (F.character d).idealValue a = 1 := by
      rw [← pow_two, h]
    rcases mul_self_eq_one_iff.mp h' with h1 | h1 <;> rw [h1] <;> simp

/-- On admissible rows, `ψ(a) = χ_c(a) χ_d(a)`. -/
theorem pairChar_eq_mul (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    {c d : Ideal (𝓞 K)} (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    {a : Ideal (𝓞 K)} (ha : QSAdm m qS a) :
    (qsPairChar F c d).idealValue a =
      (F.character c).idealValue a * (F.character d).idealValue a := by
  have htop : (⊤ : Ideal (𝓞 K)) = 1 := (Ideal.one_eq_top).symm
  have h := qs_gcd_pair_identity_S0 F hrf ⊤ c d QSAdm_top hc hd
    (by rw [htop]; exact isCoprime_one_left) (by rw [htop]; exact isCoprime_one_left) hcd
    a ha.2.1 ha.2.2
  rw [Ideal.top_mul, Ideal.top_mul, if_pos (by rw [htop]; exact isCoprime_one_right),
    conj_idealValue F hd] at h
  exact h.symm

/-! ### Bad part of a row -/

/-- The bad ideal `R = qsModulusRad m * qS`. -/
def badIdeal (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  qsModulusRad m * qS

theorem qsModulusRad_ne_bot : qsModulusRad m ≠ ⊥ := by
  unfold qsModulusRad
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro v _
  rw [Ideal.zero_eq_bot]
  exact v.ne_bot

theorem badIdeal_ne_bot (hqS : qS ≠ ⊥) : badIdeal m qS ≠ ⊥ := by
  unfold badIdeal
  rw [← Ideal.zero_eq_bot]
  exact mul_ne_zero (by rw [Ideal.zero_eq_bot]; exact qsModulusRad_ne_bot)
    (by rw [Ideal.zero_eq_bot]; exact hqS)

theorem QSAdm_of_coprime_bad {a : Ideal (𝓞 K)} (ha : Squarefree a) (ha0 : a ≠ ⊥)
    (h : IsCoprime a (badIdeal m qS)) : QSAdm m qS a := by
  unfold badIdeal at h
  refine ⟨ha, ?_, IsCoprime.of_mul_right_right h⟩
  rw [qs_isCoprimeTo_iff_M0]
  exact ⟨ha0, IsCoprime.of_mul_right_left h⟩

/-- A prime dividing `I ≠ ⊥` divides `qsRad I`. -/
theorem dvd_qsRad {P I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hPI : P ∣ I) : P ∣ qsRad I := by
  classical
  unfold qsRad
  refine Finset.dvd_prod_of_mem _ ?_
  rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI]
  exact ⟨hP, Ideal.le_of_dvd hPI⟩

/-- A divisor of the bad ideal is coprime to every column coprime to `𝔮 ⊇ qsBadRad`. -/
theorem coprime_of_dvd_bad (hqS : qS ≠ ⊥) {𝔮 c a₂ : Ideal (𝓞 K)}
    (h𝔮 : qsBadRad m qS ∣ 𝔮) (hc : IsCoprime c 𝔮) (ha₂ : a₂ ∣ badIdeal m qS) :
    IsCoprime a₂ c := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hP0 : P ≠ ⊥ := by
    intro h0
    have ha0 : a₂ = ⊥ := le_bot_iff.mp (h0 ▸ le_trans le_sup_left hle)
    rw [ha0] at ha₂
    exact badIdeal_ne_bot hqS (le_bot_iff.mp (Ideal.le_of_dvd ha₂))
  have hPa : P ∣ badIdeal m qS :=
    dvd_trans (Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)) ha₂
  have hPrad : P ∣ qsBadRad m qS := dvd_qsRad (badIdeal_ne_bot hqS) hP.isPrime hP0 hPa
  have h𝔮P : 𝔮 ≤ P := le_trans (Ideal.le_of_dvd h𝔮) (Ideal.le_of_dvd hPrad)
  rw [Ideal.isCoprime_iff_sup_eq] at hc
  have : c ⊔ 𝔮 ≤ P := sup_le (le_trans le_sup_right hle) h𝔮P
  rw [hc] at this
  exact hP.ne_top (eq_top_iff.mpr this)

/-- The good cofactor of a squarefree row is coprime to the bad ideal. -/
theorem coprime_cofactor {a a₁ R : Ideal (𝓞 K)} (ha : Squarefree a) (h : a = (a ⊔ R) * a₁) :
    IsCoprime a₁ R := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have h1 : P ∣ a₁ := Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle)
  have hPa : P ∣ a := by rw [h]; exact dvd_mul_of_dvd_right h1 _
  have h2 : P ∣ a ⊔ R := Ideal.dvd_iff_le.mpr
    (sup_le (Ideal.le_of_dvd hPa) (le_trans le_sup_right hle))
  have := ha P (by rw [h]; exact mul_dvd_mul h2 h1)
  exact hP.ne_top (Ideal.isUnit_iff.mp this)

open Classical in
/-- Generic reindexing `a = e a₁` of the rows divisible by `e`. -/
theorem sum_reindex_gen {M : Type*} [AddCommMonoid M] (S U : Finset (Ideal (𝓞 K)))
    (q : Ideal (𝓞 K) → Prop) [DecidablePred q] (e : Ideal (𝓞 K)) (he : e ≠ ⊥)
    (hU : ∀ a ∈ S, q a → ∀ a₁, a = e * a₁ → a₁ ∈ U) (G : Ideal (𝓞 K) → M) :
    ∑ a₁ ∈ U, (if e * a₁ ∈ S ∧ q (e * a₁) then G (e * a₁) else 0) =
      ∑ a ∈ S, if q a ∧ e ∣ a then G a else 0 := by
  classical
  have he0 : e ≠ 0 := by rwa [Ideal.zero_eq_bot]
  refine Finset.sum_bij_ne_zero (fun a₁ _ _ => e * a₁) ?_ ?_ ?_ ?_
  · intro a₁ _ h
    by_contra hn
    exact h (if_neg (fun h' => hn h'.1))
  · intro a₁ _ _ a₂ _ _ h
    exact mul_left_cancel₀ he0 h
  · intro a ha hne
    have hqa : q a ∧ e ∣ a := by
      by_contra hn
      exact hne (if_neg hn)
    obtain ⟨a₁, rfl⟩ := hqa.2
    refine ⟨a₁, hU _ ha hqa.1 a₁ rfl, ?_, rfl⟩
    rw [if_pos ⟨ha, hqa.1⟩]
    rwa [if_pos hqa] at hne
  · intro a₁ _ h
    have hmem : e * a₁ ∈ S ∧ q (e * a₁) := by
      by_contra hn
      exact h (if_neg hn)
    rw [if_pos hmem, if_pos ⟨hmem.2, dvd_mul_right e a₁⟩]

open Classical in
/-- Row regrouping: `Σ_{a ∈ S} G(a) = Σ_{a₂ ∣ R} Σ_{a₁ admissible} 1[a₂ a₁ ∈ S, a₂ a₁ ⊔ R = a₂] G(a₂ a₁)`
for a finite set `S` of nonzero squarefree ideals of norm `≤ X`. -/
theorem sum_rows_split {M : Type*} [AddCommMonoid M] (hqS : qS ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) (X : ℝ)
    (hS : ∀ a ∈ S, a ≠ ⊥ ∧ Squarefree a ∧ qsN a ≤ X) (G : Ideal (𝓞 K) → M) :
    ∑ a ∈ S, G a = ∑ a₂ ∈ qsDivisors (badIdeal m qS), ∑ a₁ ∈ qsUpTo m qS X,
      if a₂ * a₁ ∈ S ∧ a₂ * a₁ ⊔ badIdeal m qS = a₂ then G (a₂ * a₁) else 0 := by
  set R := badIdeal m qS with hR
  have hR0 : R ≠ ⊥ := badIdeal_ne_bot hqS
  have hmaps : ∀ a ∈ S, a ⊔ R ∈ qsDivisors R := fun a _ =>
    (mem_qsDivisors hR0).mpr (Ideal.dvd_iff_le.mpr le_sup_right)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun a₂ ha₂ => ?_
  have ha₂0 : a₂ ≠ ⊥ := by
    intro h0
    have := (mem_qsDivisors hR0).mp ha₂
    rw [h0] at this
    exact hR0 (le_bot_iff.mp (Ideal.le_of_dvd this))
  rw [sum_reindex_gen S (qsUpTo m qS X) (fun a => a ⊔ R = a₂) a₂ ha₂0 ?_ G, Finset.sum_filter]
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a ⊔ R = a₂
    · have hdvd : a₂ ∣ a := h ▸ Ideal.dvd_iff_le.mpr le_sup_left
      rw [if_pos h, if_pos ⟨h, hdvd⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  · intro a ha hq a₁ heq
    obtain ⟨ha0, hsq, hN⟩ := hS a ha
    have heq' : a = (a ⊔ R) * a₁ := by rw [hq]; exact heq
    have hcop := coprime_cofactor hsq heq'
    have ha₁0 : a₁ ≠ ⊥ := by
      intro h0; rw [h0, Ideal.mul_bot] at heq; exact ha0 heq
    have hsq₁ : Squarefree a₁ := hsq.squarefree_of_dvd (by rw [heq]; exact dvd_mul_left _ _)
    refine mem_qsUpTo.mpr ⟨QSAdm_of_coprime_bad hsq₁ ha₁0 hcop, le_trans ?_ hN⟩
    rw [heq, qsN_mul]
    have h1 : 1 ≤ qsN a₂ := by
      have : Ideal.absNorm a₂ ≠ 0 := fun h => ha₂0 (Ideal.absNorm_eq_zero_iff.mp h)
      simp only [qsN]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    nlinarith [qsN_pos ha₁0]

end ArtinPrimitiveRoots.A2.QSC3
