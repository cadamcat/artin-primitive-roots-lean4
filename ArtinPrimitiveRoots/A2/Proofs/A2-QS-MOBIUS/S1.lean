import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P1

/-!
# A2-QS-MOBIUS, part S1: squarefree removal with both principal terms retained

For one coprime
equal-class residual pair `(c, d)`, `c d ≠ ⊤`, with `ψ = χ_c χ_d⁻¹` of exact conductor `f = c d`
(`equalClass_product_conductor`) and the squarefree coprimality ideal `𝔮` coprime to `c d`:

`qsHigh W M κ 𝔮 ψ = DualLow + DualHigh − OrigLow`, where
* `Tot = Σ_{e∣𝔮} μ(e) ψ(e) Σ_a ψ(a) W(N e N a/M)` (Möbius), then P1 at `X = M/N e`;
* the dual sum `Σ_a ψ(a) (T W)(N a/Y_e)` splits at `sf(a) ≤ κ` / `> κ`;
* `a = a₀ b²` with `ψ(b)² = 1_{(b,f)=1}` turns each low sum into
  `Σ_{a₀} ψ(a₀) · qsCoprimeSq (h∘sq) √(X/N a₀) 𝔫`.
The "full" piece `fun F Z 𝔫 _ _ => qsCoprimeSq F Z 𝔫` inserted in the kernels expresses this.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

private theorem qs_dvd_sup_iff_S1 (t a b : Ideal (𝓞 K)) :
    t ∣ a ⊔ b ↔ t ∣ a ∧ t ∣ b := by
  rw [Ideal.dvd_iff_le]
  constructor
  · intro h
    exact ⟨Ideal.dvd_iff_le.mpr (le_sup_left.trans h),
      Ideal.dvd_iff_le.mpr (le_sup_right.trans h)⟩
  · rintro ⟨ha, hb⟩
    exact sup_le (Ideal.dvd_iff_le.mp ha) (Ideal.dvd_iff_le.mp hb)

open Classical in
private theorem qsMu_coprime_sum_S1 (a q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (∑ e ∈ (qsDivisors q).filter (fun e => e ∣ a), (qsMu e : ℤ)) =
      if IsCoprime a q then 1 else 0 := by
  classical
  have hJ : a ⊔ q ≠ ⊥ := by
    intro h
    exact hq (le_bot_iff.mp (by simpa [h] using (le_sup_right : q ≤ a ⊔ q)))
  letI : Fintype {e : Ideal (𝓞 K) // e ∣ a ⊔ q} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd (a ⊔ q) hJ
  have hset : (qsDivisors q).filter (fun e => e ∣ a) = qsDivisors (a ⊔ q) := by
    ext e
    constructor
    · intro he
      have hqdiv := (Finset.mem_filter.mp he).1
      have hadiv := (Finset.mem_filter.mp he).2
      have hdq := (Finset.mem_filter.mp hqdiv).2
      apply qs_dvd_mem_qsDivisors e (a ⊔ q) hJ
      exact (qs_dvd_sup_iff_S1 e a q).2 ⟨hadiv, hdq⟩
    · intro he
      have hsup := (Finset.mem_filter.mp he).2
      have hdivs := (qs_dvd_sup_iff_S1 e a q).mp hsup
      exact Finset.mem_filter.mpr
        ⟨qs_dvd_mem_qsDivisors e q hq hdivs.2, hdivs.1⟩
  have hsum : (∑ e ∈ qsDivisors (a ⊔ q), (qsMu e : ℤ)) =
      ∑ e : {e : Ideal (𝓞 K) // e ∣ a ⊔ q}, (qsMu e.1 : ℤ) := by
    apply Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩)
    · intro e he
      exact Finset.mem_univ _
    · intro e he f hf heq
      exact congrArg Subtype.val heq
    · intro e he
      exact ⟨e.1, qs_dvd_mem_qsDivisors e.1 (a ⊔ q) hJ e.2, Subtype.ext rfl⟩
    · intro e he
      rfl
  calc
    _ = ∑ e ∈ qsDivisors (a ⊔ q), (qsMu e : ℤ) := by rw [hset]
    _ = ∑ e : {e : Ideal (𝓞 K) // e ∣ a ⊔ q}, (qsMu e.1 : ℤ) := hsum
    _ = if a ⊔ q = ⊤ then 1 else 0 := qsMu_sum_divisors (a ⊔ q) hJ
    _ = if IsCoprime a q then 1 else 0 := by
      simp [Ideal.isCoprime_iff_sup_eq]

private theorem qs_pair_character_data_S1 (F : QSFamily m qS)
    (c d : Ideal (𝓞 K)) (hc : QSAdm m qS c) (hd : QSAdm m qS d)
    (hcd : IsCoprime c d) (hcd1 : c * d ≠ ⊤)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd') :
    IsPrimitiveConductor (qsPairChar F c d) (c * d) ∧
      (qsPairChar F c d) ^ 2 = 1 ∧ qsPairChar F c d ≠ 1 ∧
        (∀ w : InfinitePlace K, ∀ u : w.Completionˣ,
          (qsPairChar F c d).locInf w u = 1) := by
  rcases hcl with ⟨hc', hd', hcl'⟩
  have hf : IsPrimitiveConductor (qsPairChar F c d) (c * d) := by
    simpa [qsPairChar] using F.equalClass_product_conductor c d hc.1 hc.2.1
      hd.1 hd.2.1 hcd hcl'
  have hsqc := F.character_order_two c hc.1 hc.2.1
  have hsqd := F.character_order_two d hd.1 hd.2.1
  have hsq : (qsPairChar F c d) ^ 2 = 1 := by
    change (F.character c * (F.character d)⁻¹) ^ 2 = 1
    calc
      _ = (F.character c) ^ 2 * ((F.character d)⁻¹) ^ 2 := by rw [mul_pow]
      _ = 1 := by rw [inv_pow, hsqc, hsqd]; simp
  have hne : qsPairChar F c d ≠ 1 := by
    intro hψ
    have htopCon : (1 : ArtinPrimitiveRoots.A1.HeckeChar K).ConductorDvd ⊤ := by
      intro v u hu huv hcong
      simp [ArtinPrimitiveRoots.A1.HeckeChar.loc]
    have hcon := hf.2.2 ⊤ (by simp) (by simpa [hψ] using htopCon)
    have hcd0 : c * d ≠ ⊥ := mul_ne_zero hc.1.ne_zero hd.1.ne_zero
    have hpos : 0 < Ideal.absNorm (c * d) :=
      Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero hcd0)
    have hge : 1 ≤ Ideal.absNorm (c * d) := Nat.succ_le_iff.mpr hpos
    have hone : Ideal.absNorm (c * d) = 1 := by
      have hle : Ideal.absNorm (c * d) ≤ 1 := by simpa using hcon
      omega
    exact hcd1 (Ideal.absNorm_eq_one_iff.mp hone)
  have hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ,
      (qsPairChar F c d).locInf w u = 1 := by
    intro w u
    change (F.character c).locInf w u * ((F.character d).locInf w u)⁻¹ = 1
    rw [F.trivial_infinite_type c w u, F.trivial_infinite_type d w u]
    simp
  exact ⟨hf, hsq, hne, hinf⟩

private abbrev QSSquarefreePair :=
  {p : Ideal (𝓞 K) × Ideal (𝓞 K) // Squarefree p.1 ∧ p.2 ≠ ⊥}

private def qsSqfPairToIdeal (p : QSSquarefreePair (K := K)) :
    {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  ⟨p.1.1 * p.1.2 ^ 2, mul_ne_zero p.2.1.ne_zero (pow_ne_zero _ p.2.2)⟩

private noncomputable def qsSquarefreeDecompEquiv :
    QSSquarefreePair (K := K) ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} := by
  classical
  apply Equiv.ofBijective qsSqfPairToIdeal
  constructor
  · intro p q h
    have hprod : p.1.1 * p.1.2 ^ 2 = q.1.1 * q.1.2 ^ 2 :=
      congrArg Subtype.val h
    obtain ⟨r, hr, hunique⟩ :=
      qs_squarefree_decomposition_M1 (p.1.1 * p.1.2 ^ 2) (qsSqfPairToIdeal p).2
    have hp : Squarefree p.1.1 ∧ p.1.1 * p.1.2 ^ 2 = p.1.1 * p.1.2 ^ 2 :=
      ⟨p.2.1, rfl⟩
    have hq : Squarefree q.1.1 ∧ p.1.1 * p.1.2 ^ 2 = q.1.1 * q.1.2 ^ 2 :=
      ⟨q.2.1, hprod⟩
    have hpr : p.1 = r := hunique p.1 hp
    have hqr : q.1 = r := hunique q.1 hq
    have hpq : p.1 = q.1 := hpr.trans hqr.symm
    exact Subtype.ext hpq
  · intro I
    obtain ⟨p, hp, _⟩ := qs_squarefree_decomposition_M1 I.1 I.2
    have hb : p.2 ≠ ⊥ := by
      intro hb
      apply I.2
      rw [hp.2, hb]
      simp
    refine ⟨⟨p, hp.1, hb⟩, ?_⟩
    apply Subtype.ext
    exact hp.2.symm

private noncomputable def qsSquarefreePairProdEquiv :
    QSSquarefreePair (K := K) ≃
      ({a : Ideal (𝓞 K) // Squarefree a} × {b : Ideal (𝓞 K) // b ≠ ⊥}) where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

private theorem qsN_mul_S1 (a b : Ideal (𝓞 K)) : qsN (a * b) = qsN a * qsN b := by
  simp [qsN, map_mul]

private theorem qs_square_scale_identity_S1 (A B M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    (B / Real.sqrt (M / A)) ^ 2 = A * B ^ 2 / M := by
  have hMA : 0 < M / A := div_pos hM hA
  have hsqrt : (Real.sqrt (M / A)) ^ 2 = M / A := Real.sq_sqrt hMA.le
  rw [div_pow, hsqrt]
  field_simp

private noncomputable def qsMulDivEquiv_S1 (e : Ideal (𝓞 K)) (he : e ≠ ⊥) :
    {b : Ideal (𝓞 K) // b ≠ ⊥} ≃
      {a : {I : Ideal (𝓞 K) // I ≠ ⊥} // e ∣ a.1} where
  toFun b := ⟨⟨e * b.1, mul_ne_zero he b.2⟩, ⟨b.1, rfl⟩⟩
  invFun a := ⟨Classical.choose a.2, by
    intro hb
    apply a.1.2
    rw [Classical.choose_spec a.2, hb]
    simp⟩
  left_inv b := by
    apply Subtype.ext
    change Classical.choose (show e ∣ e * b.1 from ⟨b.1, rfl⟩) = b.1
    apply mul_left_cancel₀ he
    exact (Classical.choose_spec (show e ∣ e * b.1 from ⟨b.1, rfl⟩)).symm
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec a.2).symm

private theorem qs_divisor_ne_zero_S1 (q e : Ideal (𝓞 K)) (hq : q ≠ ⊥)
    (he : e ∈ qsDivisors q) : e ≠ ⊥ := by
  classical
  intro he0
  have hdiv := (Finset.mem_filter.mp he).2
  rcases hdiv with ⟨u, hu⟩
  apply hq
  rw [he0] at hu
  simpa using hu

open Classical in
private theorem qs_dvd_smooth_sum_S1 (e : Ideal (𝓞 K)) (he : e ≠ ⊥)
    (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X) :
    (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
      if e ∣ a.1 then ψ.idealValue a.1 * W (qsN a.1 / X) else 0) =
      ψ.idealValue e * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ψ.idealValue b.1 * W (qsN b.1 / (X / qsN e)) := by
  classical
  let divs := {a : {I : Ideal (𝓞 K) // I ≠ ⊥} // e ∣ a.1}
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ :=
    fun a => ψ.idealValue a.1 * W (qsN a.1 / X)
  let s : Set {I : Ideal (𝓞 K) // I ≠ ⊥} := {a | e ∣ a.1}
  have hsubtype :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if e ∣ a.1 then f a else 0) =
        ∑' a : divs, ψ.idealValue a.1.1 * W (qsN a.1.1 / X) := by
    have hIndicator : (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if e ∣ a.1 then f a else 0) = Set.indicator s f := by
      funext a
      by_cases h : e ∣ a.1 <;> simp [s, h]
    rw [hIndicator, ← tsum_subtype]
    rfl
  have heNpos : 0 < qsN e := by
    have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_of_ne_zero he)
    exact_mod_cast hp
  calc
    _ = ∑' a : divs, ψ.idealValue a.1.1 * W (qsN a.1.1 / X) := hsubtype
    _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ψ.idealValue (e * b.1) * W (qsN (e * b.1) / X) :=
        (Equiv.tsum_eq (qsMulDivEquiv_S1 e he)
          (fun a : divs => ψ.idealValue a.1.1 * W (qsN a.1.1 / X))).symm
    _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ψ.idealValue e * (ψ.idealValue b.1 * W (qsN b.1 / (X / qsN e))) := by
        apply tsum_congr
        intro b
        have hmul := qs_idealValue_mul_M0 ψ e b.1 he b.2
        have hscale : qsN (e * b.1) / X = qsN b.1 / (X / qsN e) := by
          rw [qsN_mul_S1]
          field_simp
        rw [hmul, hscale]
        ring
    _ = ψ.idealValue e * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ψ.idealValue b.1 * W (qsN b.1 / (X / qsN e)) := by rw [tsum_mul_left]

private theorem qs_coprime_mul_square_iff_S1 (a b q : Ideal (𝓞 K)) :
    IsCoprime (a * b ^ 2) q ↔ IsCoprime a q ∧ IsCoprime b q := by
  constructor
  · intro h
    refine ⟨h.of_mul_left_left, ?_⟩
    have hb2 := h.of_mul_left_right
    exact hb2.of_isCoprime_of_dvd_left ⟨b, by simp [pow_two, mul_comm]⟩
  · rintro ⟨ha, hb⟩
    exact ha.mul_left hb.pow_left

private abbrev QSSquarefreeIdeal := {a : Ideal (𝓞 K) // Squarefree a}

open Classical in
private def qsSqfUpToSubtype_S1 (κ : ℝ) (q : Ideal (𝓞 K)) :
    Finset (QSSquarefreeIdeal (K := K)) :=
  (qsSqfUpTo κ q).attach.image
    (fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2.2.1⟩)

private theorem mem_qsSqfUpToSubtype_S1 (κ : ℝ) (q : Ideal (𝓞 K))
    (a : QSSquarefreeIdeal (K := K)) :
    a ∈ qsSqfUpToSubtype_S1 κ q ↔ a.1 ∈ qsSqfUpTo κ q := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨x, hx, heq⟩
    have hval := congrArg Subtype.val heq
    exact hval ▸ x.2
  · intro ha
    apply Finset.mem_image.mpr
    refine ⟨⟨a.1, ha⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

private theorem qsSqfUpTo_mem_of_conditions_S1 (κ : ℝ) (q a : Ideal (𝓞 K))
    (ha : Squarefree a) (hcop : IsCoprime a q) (hnorm : qsN a ≤ κ) :
    a ∈ qsSqfUpTo κ q := by
  classical
  have hfloor : Ideal.absNorm a ≤ ⌊κ⌋₊ := by exact Nat.le_floor (by exact_mod_cast hnorm)
  have hbase : a ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊κ⌋₊).toFinset := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hfloor
  exact Finset.mem_filter.mpr ⟨hbase, ⟨ha.ne_zero, ha, hcop, hnorm⟩⟩

private theorem qs_unramified_of_conductorDvd_not_dvd_S1
    (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : ψ.ConductorDvd f) (hf0 : f ≠ ⊥)
    (v : ArtinPrimitiveRoots.A1.FinPlace K)
    (hv : ¬ v.asIdeal ∣ f) : ψ.UnramifiedAt v := by
  classical
  have hcount :
      (Associates.mk v.asIdeal).count (Associates.mk f).factors = 0 := by
    by_contra hne
    have hcnt := Associates.count_ne_zero_iff_dvd (a := f) (p := v.asIdeal)
      hf0 v.irreducible
    exact hv (hcnt.mp hne)
  have hexp : ArtinPrimitiveRoots.A1.idealExp v f = 0 := hcount
  intro u hu huv
  have hone : (1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp
  have hsub : ((u : v.adicCompletion K) - 1) ∈ v.adicCompletionIntegers K :=
    (v.adicCompletionIntegers K).sub_mem hu hone
  have hval : Valued.v ((u : v.adicCompletion K) - 1) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hsub
  have hcong : Valued.v ((u : v.adicCompletion K) - 1) ≤
      WithZero.exp (-(ArtinPrimitiveRoots.A1.idealExp v f : ℤ)) := by
    rw [hexp]
    simpa
  exact hf v u hu huv hcong

private theorem qs_idealValue_ne_zero_of_coprime_conductor_S1
    (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) (f I : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor ψ f) (hI : I ≠ ⊥) (hcop : IsCoprime I f) :
    ψ.idealValue I ≠ 0 := by
  classical
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  apply Multiset.prod_ne_zero
  intro hx
  rcases Multiset.mem_map.mp hx with ⟨P, hP, hzero⟩
  have hPprimeU : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime hPprimeU
  have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hP
  have hPI : P ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hPF : IsCoprime P f := hcop.of_isCoprime_of_dvd_left hPI
  have hPnotF : ¬ P ∣ f := by
    intro hPdiv
    have hs : P ⊔ f = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hPF
    have hle : f ≤ P := Ideal.dvd_iff_le.mp hPdiv
    have htop : P = ⊤ := by
      calc
        P = P ⊔ f := (sup_eq_left.mpr hle).symm
        _ = ⊤ := hs
    exact hPprime.ne_top htop
  let v : ArtinPrimitiveRoots.A1.FinPlace K := HeightOneSpectrum.ofPrime hPprimeU
  have hvP : v.asIdeal = P := rfl
  have hUn : ψ.UnramifiedAt v := by
    apply qs_unramified_of_conductorDvd_not_dvd_S1 ψ f hf.2.1 hf.1 v
    simpa [hvP] using hPnotF
  have hfactor :
      (if h : P.IsPrime ∧ P ≠ ⊥ then
        ψ.primeValue ⟨P, h.1, h.2⟩ else 1) ≠ 0 := by
    have hcond : P.IsPrime ∧ P ≠ ⊥ := ⟨hPprime, hPne⟩
    rw [dif_pos hcond]
    change ψ.primeValue v ≠ 0
    unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
    rw [if_pos hUn]
    exact Units.ne_zero _
  exact hfactor hzero

private theorem qs_idealValue_sq_eq_one_of_coprime_S1
    (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) (f I : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor ψ f) (hsq : ψ ^ 2 = 1)
    (hI : I ≠ ⊥) (hcop : IsCoprime I f) : ψ.idealValue I ^ 2 = 1 := by
  classical
  unfold ArtinPrimitiveRoots.A1.HeckeChar.idealValue
  rw [← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro x hx
  rcases Multiset.mem_map.mp hx with ⟨P, hP, rfl⟩
  have hPprimeU : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime hPprimeU
  have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hP
  have hPI : P ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hPF : IsCoprime P f := hcop.of_isCoprime_of_dvd_left hPI
  have hPnotF : ¬ P ∣ f := by
    intro hPdiv
    have hs : P ⊔ f = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hPF
    have hle : f ≤ P := Ideal.dvd_iff_le.mp hPdiv
    have htop : P = ⊤ := by
      calc
        P = P ⊔ f := (sup_eq_left.mpr hle).symm
        _ = ⊤ := hs
    exact hPprime.ne_top htop
  let v : ArtinPrimitiveRoots.A1.FinPlace K := HeightOneSpectrum.ofPrime hPprimeU
  have hUn : ψ.UnramifiedAt v := by
    apply qs_unramified_of_conductorDvd_not_dvd_S1 ψ f hf.2.1 hf.1 v
    simpa [show v.asIdeal = P from rfl] using hPnotF
  let u : (v.adicCompletion K)ˣ := ArtinPrimitiveRoots.A1.toLoc v
    (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
      (ArtinPrimitiveRoots.A1.unif_ne_zero v))
  have hlocSq : (ψ.loc v u) ^ 2 = 1 := by
    have h := congrArg (fun χ : ArtinPrimitiveRoots.A1.HeckeChar K => χ.loc v u) hsq
    simpa [ArtinPrimitiveRoots.A1.HeckeChar.loc] using h
  have hvalSq : ((ψ.loc v u : ℂˣ) : ℂ) ^ 2 = 1 := by
    calc
      ((ψ.loc v u : ℂˣ) : ℂ) ^ 2 = (((ψ.loc v u) ^ 2 : ℂˣ) : ℂ) := by simp
      _ = 1 := by rw [hlocSq]; simp
  have hpv : ψ.primeValue v ^ 2 = 1 := by
    unfold ArtinPrimitiveRoots.A1.HeckeChar.primeValue
    rw [if_pos hUn]
    exact hvalSq
  have hcond : P.IsPrime ∧ P ≠ ⊥ := ⟨hPprime, hPne⟩
  simp only [dif_pos hcond]
  exact hpv

open Classical in
private theorem qs_pairValue_sq_indicator_S1 (F : QSFamily m qS)
    (c d : Ideal (𝓞 K)) (hdata : IsPrimitiveConductor (qsPairChar F c d) (c * d))
    (hsq : (qsPairChar F c d) ^ 2 = 1) (b : Ideal (𝓞 K)) (hb : b ≠ ⊥) :
    (qsPairChar F c d).idealValue b ^ 2 =
      if IsCoprime b (c * d) then 1 else 0 := by
  classical
  by_cases hcop : IsCoprime b (c * d)
  · rw [if_pos hcop]
    exact qs_idealValue_sq_eq_one_of_coprime_S1
      (qsPairChar F c d) (c * d) b hdata hsq hb hcop
  · rw [if_neg hcop]
    have hj0 : b ⊔ (c * d) ≠ ⊥ := by
      intro hbot
      exact hb (le_bot_iff.mp (by simpa [hbot] using (le_sup_left : b ≤ b ⊔ (c * d))))
    have hnotUnit : ¬ IsUnit (b ⊔ (c * d)) := by
      intro hu
      exact hcop (Ideal.isCoprime_iff_sup_eq.mpr (Ideal.isUnit_iff.mp hu))
    obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hj0 hnotUnit
    have hPprimeU : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime hPprimeU
    have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hP
    have hPdiv := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hdivs := (qs_dvd_sup_iff_S1 P b (c * d)).mp hPdiv
    have hzero := qs_idealValue_eq_zero_of_conductor_M0
      (qsPairChar F c d) (c * d) hdata P b hPprime hPne hdivs.2 hb hdivs.1
    rw [hzero]
    simp

open Classical in
private theorem qs_cap_tsum_eq_finite_S1 (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M : ℝ) (hM : 0 < M) (ψ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (A : Ideal (𝓞 K) → Prop) :
    ∃ rows : Finset {I : Ideal (𝓞 K) // I ≠ ⊥},
      (∀ a, a ∉ rows →
        (if A a.1 then ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0) = 0) ∧
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if A a.1 then ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0) =
        ∑ a ∈ rows, if A a.1 then ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0 := by
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
  have hzero (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) (ha : a ∉ rows) :
      (if A a.1 then ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0) = 0 := by
    by_cases hA : A a.1
    · have hnot : ¬ Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊ := by
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
      rw [if_pos hA, hW.2.2.2 _ hratio]
      simp
    · simp [hA]
  refine ⟨rows, hzero, ?_⟩
  exact tsum_eq_sum hzero

open Classical in
private theorem qs_cap_series_summable_S1 (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M : ℝ) (hM : 0 < M) (ψ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (A : Ideal (𝓞 K) → Prop) :
    Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      if A a.1 then ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0) := by
  classical
  obtain ⟨rows, hzero, _⟩ := qs_cap_tsum_eq_finite_S1 W hW M hM ψ A
  have hfinite : {a : {I : Ideal (𝓞 K) // I ≠ ⊥} | (if A a.1 then
      ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0) ≠ 0}.Finite := by
    apply (Finset.finite_toSet rows).subset
    intro a ha
    by_contra hnot
    exact ha (hzero a hnot)
  exact summable_of_hasFiniteSupport hfinite

open Classical in
private theorem qsTot_mobius_reindex_S1 [IsTotallyComplex K]
    (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor ψ f) (hsq : ψ ^ 2 = 1) (hne : ψ ≠ 1)
    (hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ, ψ.locInf w u = 1)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M : ℝ) (hM : 0 < M)
    (q : Ideal (𝓞 K)) (hq : Squarefree q) :
    qsTot (fun x => (W x : ℂ)) M q ψ =
      ∑ e ∈ qsDivisors q, (qsMu e : ℂ) * ψ.idealValue e *
        ((M / (qsN e * Real.sqrt (qsN f)) : ℝ) : ℂ) *
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ψ.idealValue b.1 * qsTransform K (fun x => (W x : ℂ))
            ((M / qsN e) * qsN b.1 / qsN f) := by
  classical
  have hq0 : q ≠ ⊥ := hq.ne_zero
  have hf0 : f ≠ ⊥ := hf.1
  have hqdiv0 (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors q) : e ≠ ⊥ :=
    qs_divisor_ne_zero_S1 q e hq0 he
  have hcoeff (a : Ideal (𝓞 K)) :
      (∑ e ∈ qsDivisors q, if e ∣ a then (qsMu e : ℂ) else 0) =
        if IsCoprime a q then 1 else 0 := by
    have hz := qsMu_coprime_sum_S1 a q hq0
    have hzC : (∑ e ∈ qsDivisors q,
        if e ∣ a then (qsMu e : ℂ) else 0) =
        if IsCoprime a q then 1 else 0 := by
      calc
        _ = ∑ e ∈ (qsDivisors q).filter (fun e => e ∣ a), (qsMu e : ℂ) := by
          rw [← Finset.sum_filter]
        _ = _ := by exact_mod_cast hz
    exact hzC
  have hpoint (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      (if IsCoprime a.1 q then
          ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0) =
        ∑ e ∈ qsDivisors q, if e ∣ a.1 then
          (qsMu e : ℂ) * ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0 := by
    calc
      _ = (if IsCoprime a.1 q then (1 : ℂ) else 0) *
            (ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ)) := by
          by_cases hc : IsCoprime a.1 q <;> simp [hc] <;> ring
      _ = (∑ e ∈ qsDivisors q,
            if e ∣ a.1 then (qsMu e : ℂ) else 0) *
              (ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ)) := by rw [hcoeff]
      _ = ∑ e ∈ qsDivisors q, if e ∣ a.1 then
            (qsMu e : ℂ) * ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hdiv : e ∣ a.1 <;> simp [hdiv] <;> ring
  have hsmooth (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors q) :
      Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if e ∣ a.1 then ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0) :=
    qs_cap_series_summable_S1 W hW M hM ψ (fun a => e ∣ a)
  have hsumTerm (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors q) :
      Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if e ∣ a.1 then (qsMu e : ℂ) * ψ.idealValue a.1 *
          (W (qsN a.1 / M) : ℂ) else 0) := by
    have hs := (hsmooth e he).mul_left (qsMu e : ℂ)
    exact hs.congr (by
      intro a
      by_cases hdiv : e ∣ a.1 <;> simp [hdiv, mul_assoc] <;> ring)
  have hmobius : qsTot (fun x => (W x : ℂ)) M q ψ =
      ∑ e ∈ qsDivisors q,
        ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
          if e ∣ a.1 then (qsMu e : ℂ) * ψ.idealValue a.1 *
            (W (qsN a.1 / M) : ℂ) else 0 := by
    calc
      _ = ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
            ∑ e ∈ qsDivisors q, if e ∣ a.1 then
              (qsMu e : ℂ) * ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0 := by
        unfold qsTot
        apply tsum_congr
        exact hpoint
      _ = _ := by
        rw [Summable.tsum_finsetSum (fun e he => hsumTerm e he)]
  have hdivsum (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors q) :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if e ∣ a.1 then (qsMu e : ℂ) * ψ.idealValue a.1 *
          (W (qsN a.1 / M) : ℂ) else 0) =
        (qsMu e : ℂ) * ψ.idealValue e *
          (((M / qsN e / Real.sqrt (qsN f) : ℝ) : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              ψ.idealValue b.1 * qsTransform K (fun x => (W x : ℂ))
                ((M / qsN e) * qsN b.1 / qsN f)) := by
    have he0 := hqdiv0 e he
    have heNpos : 0 < qsN e := by
      have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero he0)
      exact_mod_cast hp
    have hX : 0 < M / qsN e := div_pos hM heNpos
    have hprimitive := qs_primitive_smooth_poisson_P1 ψ f hf hsq hne hinf
      (fun x => (W x : ℂ)) hW.1 (M / qsN e) hX
    have hsmoothEq :
        (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ψ.idealValue b.1 * (W (qsN b.1 / (M / qsN e)) : ℂ)) =
          ((M / qsN e / Real.sqrt (qsN f) : ℝ) : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              ψ.idealValue b.1 * qsTransform K (fun x => (W x : ℂ))
                ((M / qsN e) * qsN b.1 / qsN f) := hprimitive.2
    calc
      _ = (qsMu e : ℂ) *
            (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
              if e ∣ a.1 then ψ.idealValue a.1 *
                (W (qsN a.1 / M) : ℂ) else 0) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro a
          by_cases hdiv : e ∣ a.1 <;> simp [hdiv] <;> ring
      _ = (qsMu e : ℂ) * ψ.idealValue e *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              ψ.idealValue b.1 * (W (qsN b.1 / (M / qsN e)) : ℂ) := by
          rw [qs_dvd_smooth_sum_S1 e he0 ψ (fun x => (W x : ℂ)) M hM]
          ring
      _ = _ := by rw [hsmoothEq]
  have hP1Total : qsTot (fun x => (W x : ℂ)) M q ψ =
      ∑ e ∈ qsDivisors q, (qsMu e : ℂ) * ψ.idealValue e *
        ((M / (qsN e * Real.sqrt (qsN f)) : ℝ) : ℂ) *
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          ψ.idealValue b.1 * qsTransform K (fun x => (W x : ℂ))
            ((M / qsN e) * qsN b.1 / qsN f) := by
    rw [hmobius]
    apply Finset.sum_congr rfl
    intro e he
    rw [hdivsum e he]
    have hePos : 0 < qsN e := by
      have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero (hqdiv0 e he))
      exact_mod_cast hp
    have hden : M / qsN e / Real.sqrt (qsN f) =
        M / (qsN e * Real.sqrt (qsN f)) := by
      field_simp
    rw [hden]
    ring
  exact hP1Total

open Classical in
private theorem qs_split_smooth_core_S1 (ψ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (H : ℝ → ℂ) (Y κ : ℝ)
    (hs : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      ψ.idealValue a.1 * H (qsN a.1 / Y))) :
    (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
      ψ.idealValue a.1 * H (qsN a.1 / Y)) =
      qsLow H Y κ ⊤ ψ + qsHigh H Y κ ⊤ ψ ∧
      Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if (qsSfNorm a.1 : ℝ) ≤ κ then ψ.idealValue a.1 * H (qsN a.1 / Y) else 0) ∧
      Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if κ < (qsSfNorm a.1 : ℝ) then ψ.idealValue a.1 * H (qsN a.1 / Y) else 0) := by
  classical
  let lo : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if (qsSfNorm a.1 : ℝ) ≤ κ then ψ.idealValue a.1 * H (qsN a.1 / Y) else 0
  let hi : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if κ < (qsSfNorm a.1 : ℝ) then ψ.idealValue a.1 * H (qsN a.1 / Y) else 0
  have hsLo : Summable lo := by
    apply Summable.of_norm_bounded hs.norm
    intro a
    by_cases h : (qsSfNorm a.1 : ℝ) ≤ κ <;> simp [lo, h] <;> positivity
  have hsHi : Summable hi := by
    apply Summable.of_norm_bounded hs.norm
    intro a
    by_cases h : κ < (qsSfNorm a.1 : ℝ) <;> simp [hi, h] <;> positivity
  have hpoint (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      ψ.idealValue a.1 * H (qsN a.1 / Y) = lo a + hi a := by
    by_cases h : (qsSfNorm a.1 : ℝ) ≤ κ
    · have hnot : ¬ κ < (qsSfNorm a.1 : ℝ) := not_lt_of_ge h
      simp [lo, hi, h, hnot]
    · have hlt : κ < (qsSfNorm a.1 : ℝ) := lt_of_not_ge h
      simp [lo, hi, h, hlt]
  have hlo : (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, lo a) = qsLow H Y κ ⊤ ψ := by
    unfold qsLow lo
    apply tsum_congr
    intro (a : {I : Ideal (𝓞 K) // I ≠ ⊥})
    have htop : IsCoprime a.1 ⊤ := by
      rw [Ideal.isCoprime_iff_sup_eq]
      simp
    simp [htop]
  have hhi : (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, hi a) = qsHigh H Y κ ⊤ ψ := by
    unfold qsHigh hi
    apply tsum_congr
    intro (a : {I : Ideal (𝓞 K) // I ≠ ⊥})
    have htop : IsCoprime a.1 ⊤ := by
      rw [Ideal.isCoprime_iff_sup_eq]
      simp
    simp [htop]
  have hsumEq :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ψ.idealValue a.1 * H (qsN a.1 / Y)) =
        qsLow H Y κ ⊤ ψ + qsHigh H Y κ ⊤ ψ := by
    calc
    _ = ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, (lo a + hi a) := by
      apply tsum_congr
      intro (a : {I : Ideal (𝓞 K) // I ≠ ⊥})
      exact hpoint a
    _ = (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, lo a) +
          (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, hi a) := hsLo.tsum_add hsHi
    _ = qsLow H Y κ ⊤ ψ + qsHigh H Y κ ⊤ ψ := by rw [hlo, hhi]
  exact ⟨hsumEq, hsLo, hsHi⟩

open Classical in
private theorem qs_low_b_summable_S1 (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M : ℝ) (hM : 0 < M) (ψ : ArtinPrimitiveRoots.A1.HeckeChar K)
    (a₀ : Ideal (𝓞 K)) (ha₀ : Squarefree a₀) (𝔫 : Ideal (𝓞 K)) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      if IsCoprime b.1 𝔫 then
        ψ.idealValue (a₀ * b.1 ^ 2) * (W (qsN (a₀ * b.1 ^ 2) / M) : ℂ) else 0) := by
  classical
  let support : Set {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    {b | Ideal.absNorm b.1 ≤ ⌊3 * M + 1⌋₊}
  have hfinite : support.Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le
        (S := 𝓞 K) ⌊3 * M + 1⌋₊).preimage
    intro a ha b hb hab
    exact Subtype.ext hab
  have hNa₀ : 1 ≤ qsN a₀ := by
    have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_of_ne_zero ha₀.ne_zero)
    exact_mod_cast (Nat.succ_le_iff.mpr hp)
  have hzero (b : {I : Ideal (𝓞 K) // I ≠ ⊥})
      (hb : b ∉ support) :
      (if IsCoprime b.1 𝔫 then
        ψ.idealValue (a₀ * b.1 ^ 2) * (W (qsN (a₀ * b.1 ^ 2) / M) : ℂ) else 0) = 0 := by
    by_cases hcop : IsCoprime b.1 𝔫
    · have hnot : ¬ Ideal.absNorm b.1 ≤ ⌊3 * M + 1⌋₊ := by
        intro h
        exact hb (by simpa [support] using h)
      have hnat : ⌊3 * M + 1⌋₊ < Ideal.absNorm b.1 := Nat.lt_of_not_ge hnot
      have hcast : (⌊3 * M + 1⌋₊ : ℝ) + 1 ≤ qsN b.1 := by
        have hnat' : ⌊3 * M + 1⌋₊ + 1 ≤ Ideal.absNorm b.1 := Nat.succ_le_iff.mpr hnat
        exact_mod_cast hnat'
      have hfloor : 3 * M + 1 < (⌊3 * M + 1⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hlarge : 3 * M + 1 < qsN b.1 := hfloor.trans_le hcast
      have hnormmul : qsN (a₀ * b.1 ^ 2) = qsN a₀ * (qsN b.1) ^ 2 := by
        calc
          qsN (a₀ * b.1 ^ 2) = qsN a₀ * qsN (b.1 ^ 2) := qsN_mul_S1 _ _
          _ = qsN a₀ * (qsN b.1 * qsN b.1) := by rw [pow_two, qsN_mul_S1]
          _ = qsN a₀ * (qsN b.1) ^ 2 := by rw [pow_two]
      have hlargeSq : (3 * M + 1) ^ 2 < (qsN b.1) ^ 2 := by
        have hpos : 0 < qsN b.1 + (3 * M + 1) := by positivity
        have hmul := mul_pos (sub_pos.mpr hlarge) hpos
        nlinarith
      by_cases hw : W (qsN (a₀ * b.1 ^ 2) / M) = 0
      · simp [hcop, hw]
      · have hratio : qsN (a₀ * b.1 ^ 2) / M < 5 / 2 := by
          by_contra h
          have hle : (5 / 2 : ℝ) ≤ qsN (a₀ * b.1 ^ 2) / M := le_of_not_gt h
          rw [hW.2.2.2 _ hle] at hw
          exact hw rfl
        have hboundProduct :
            qsN a₀ * (qsN b.1) ^ 2 < (5 / 2 : ℝ) * M := by
          rw [hnormmul] at hratio
          exact (div_lt_iff₀ hM).mp hratio
        have hbsq : (qsN b.1) ^ 2 < (5 / 2 : ℝ) * M := by
          nlinarith [sq_nonneg (qsN b.1)]
        have hsmallSq : (3 * M + 1) ^ 2 ≥ (5 / 2 : ℝ) * M := by nlinarith
        nlinarith [hlargeSq, hsmallSq]
    · simp [hcop]
  have hsupport : {b | (if IsCoprime b.1 𝔫 then
        ψ.idealValue (a₀ * b.1 ^ 2) * (W (qsN (a₀ * b.1 ^ 2) / M) : ℂ) else 0) ≠ 0} ⊆ support := by
    intro b hb
    by_contra hnot
    exact hb (hzero b hnot)
  exact summable_of_hasFiniteSupport (hfinite.subset hsupport)

open Classical in
private theorem qs_coprimeSq_cap_summable_S1 (W : ℝ → ℝ) (hW : IsCapWeight W)
    (Z : ℝ) (hZ : 0 < Z) (𝔫 : Ideal (𝓞 K)) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      if IsCoprime b.1 𝔫 then (W ((qsN b.1 / Z) ^ 2) : ℂ) else 0) := by
  classical
  let support : Set {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    {b | Ideal.absNorm b.1 ≤ ⌊3 * Z + 1⌋₊}
  have hfinite : support.Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le
        (S := 𝓞 K) ⌊3 * Z + 1⌋₊).preimage
    intro a ha b hb hab
    exact Subtype.ext hab
  have hzero (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) (hb : b ∉ support) :
      (if IsCoprime b.1 𝔫 then (W ((qsN b.1 / Z) ^ 2) : ℂ) else 0) = 0 := by
    by_cases hcop : IsCoprime b.1 𝔫
    · have hnot : ¬ Ideal.absNorm b.1 ≤ ⌊3 * Z + 1⌋₊ := by
        intro h
        exact hb (by simpa [support] using h)
      have hnat : ⌊3 * Z + 1⌋₊ < Ideal.absNorm b.1 := Nat.lt_of_not_ge hnot
      have hcast : (⌊3 * Z + 1⌋₊ : ℝ) + 1 ≤ qsN b.1 := by
        have hnat' : ⌊3 * Z + 1⌋₊ + 1 ≤ Ideal.absNorm b.1 := Nat.succ_le_iff.mpr hnat
        exact_mod_cast hnat'
      have hfloor : 3 * Z + 1 < (⌊3 * Z + 1⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hlarge : 3 * Z < qsN b.1 := by linarith [hfloor.trans_le hcast]
      have hratio : 3 < qsN b.1 / Z := (lt_div_iff₀ hZ).2 hlarge
      have hsq : (5 / 2 : ℝ) ≤ (qsN b.1 / Z) ^ 2 := by nlinarith
      simp only [if_pos hcop]
      rw [hW.2.2.2 _ hsq]
      simp
    · simp [hcop]
  have hsupport : {b | (if IsCoprime b.1 𝔫 then
        (W ((qsN b.1 / Z) ^ 2) : ℂ) else 0) ≠ 0} ⊆ support := by
    intro b hb
    by_contra hnot
    exact hb (hzero b hnot)
  exact summable_of_hasFiniteSupport (hfinite.subset hsupport)

open Classical in
set_option maxHeartbeats 1000000 in
private theorem qs_low_squarefree_decomp_general_S1 (F : QSFamily m qS)
    (h : ℝ → ℂ) (X κ : ℝ) (hX : 0 < X)
    (𝔮 c d : Ideal (𝓞 K))
    (hsIdeal : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      if IsCoprime a.1 𝔮 ∧ (qsSfNorm a.1 : ℝ) ≤ κ then
        (qsPairChar F c d).idealValue a.1 * h (qsN a.1 / X) else 0))
    (hvalue : ∀ b : Ideal (𝓞 K), b ≠ ⊥ →
      (qsPairChar F c d).idealValue b ^ 2 =
        if IsCoprime b (c * d) then 1 else 0) :
    qsLow h X κ 𝔮 (qsPairChar F c d) =
      ∑ a₀ ∈ qsSqfUpTo κ 𝔮, (qsPairChar F c d).idealValue a₀ *
        qsCoprimeSq (fun y => h (y ^ 2)) (Real.sqrt (X / qsN a₀)) (𝔮 * (c * d)) := by
  classical
  let ψ := qsPairChar F c d
  let Aset := qsSqfUpTo κ 𝔮
  let Asq := qsSqfUpToSubtype_S1 κ 𝔮
  let rowPred := fun a : Ideal (𝓞 K) =>
    IsCoprime a 𝔮 ∧ (qsSfNorm a : ℝ) ≤ κ
  let fIdeal : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if rowPred a.1 then ψ.idealValue a.1 * h (qsN a.1 / X) else 0
  let fProd : ({a : Ideal (𝓞 K) // Squarefree a} ×
      {b : Ideal (𝓞 K) // b ≠ ⊥}) → ℂ := fun x =>
    if rowPred (x.1.1 * x.2.1 ^ 2) then
      ψ.idealValue (x.1.1 * x.2.1 ^ 2) *
        h (qsN (x.1.1 * x.2.1 ^ 2) / X) else 0
  have hlowEq : qsLow h X κ 𝔮 ψ = ∑' a, fIdeal a := by
    rfl
  have hsPair : Summable (fun p : QSSquarefreePair (K := K) =>
      fIdeal (qsSquarefreeDecompEquiv p)) :=
    (Equiv.summable_iff qsSquarefreeDecompEquiv).2 hsIdeal
  have hsProd : Summable fProd := by
    apply (Equiv.summable_iff qsSquarefreePairProdEquiv).1
    exact hsPair.congr (by intro p; rfl)
  have hAdata (a₀ : QSSquarefreeIdeal (K := K)) (ha₀ : a₀ ∈ Asq) :
      IsCoprime a₀.1 𝔮 ∧ qsN a₀.1 ≤ κ := by
    have hraw := (mem_qsSqfUpToSubtype_S1 κ 𝔮 a₀).mp ha₀
    rcases Finset.mem_filter.mp hraw with ⟨_, hprop⟩
    exact ⟨hprop.2.2.1, hprop.2.2.2⟩
  have hsfCast (a₀ : Ideal (𝓞 K)) (ha₀ : Squarefree a₀)
      (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      (qsSfNorm (a₀ * b.1 ^ 2) : ℝ) = qsN a₀ := by
    have hsf := qs_sfNorm_eq_M1 a₀ b.1 ha₀ b.2
    exact_mod_cast hsf
  have hnormProd (a₀ : Ideal (𝓞 K)) (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      qsN (a₀ * b.1 ^ 2) = qsN a₀ * (qsN b.1) ^ 2 := by
    calc
      qsN (a₀ * b.1 ^ 2) = qsN a₀ * qsN (b.1 ^ 2) := qsN_mul_S1 _ _
      _ = qsN a₀ * (qsN b.1 * qsN b.1) := by rw [pow_two, qsN_mul_S1]
      _ = qsN a₀ * (qsN b.1) ^ 2 := by rw [pow_two]
  have hrowEquiv (a₀ : QSSquarefreeIdeal (K := K)) (ha₀ : a₀ ∈ Asq)
      (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      rowPred (a₀.1 * b.1 ^ 2) ↔ IsCoprime b.1 𝔮 := by
    have hA := hAdata a₀ ha₀
    constructor
    · intro h
      exact ((qs_coprime_mul_square_iff_S1 a₀.1 b.1 𝔮).mp h.1).2
    · intro hbq
      refine ⟨(qs_coprime_mul_square_iff_S1 a₀.1 b.1 𝔮).mpr ⟨hA.1, hbq⟩, ?_⟩
      rw [hsfCast a₀.1 a₀.2 b]
      exact hA.2
  have hA0_of_row (a₀ : QSSquarefreeIdeal (K := K))
      (b : {I : Ideal (𝓞 K) // I ≠ ⊥})
      (hrow : rowPred (a₀.1 * b.1 ^ 2)) : a₀ ∈ Asq := by
    have hcop := ((qs_coprime_mul_square_iff_S1 a₀.1 b.1 𝔮).mp hrow.1).1
    have hnorm : qsN a₀.1 ≤ κ := by
      rw [← hsfCast a₀.1 a₀.2 b]
      exact hrow.2
    apply (mem_qsSqfUpToSubtype_S1 κ 𝔮 a₀).mpr
    exact qsSqfUpTo_mem_of_conditions_S1 κ 𝔮 a₀.1 a₀.2 hcop hnorm
  have htermEq (a₀ : QSSquarefreeIdeal (K := K)) (ha₀ : a₀ ∈ Asq)
      (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      fProd (a₀, b) = ψ.idealValue a₀.1 *
        (if IsCoprime b.1 (𝔮 * (c * d)) then
          h ((qsN b.1 / Real.sqrt (X / qsN a₀.1)) ^ 2) else 0) := by
    have hA := hAdata a₀ ha₀
    have hNa0pos : 0 < qsN a₀.1 := by
      have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero a₀.2.ne_zero)
      exact_mod_cast hp
    have harg : qsN (a₀.1 * b.1 ^ 2) / X =
        (qsN b.1 / Real.sqrt (X / qsN a₀.1)) ^ 2 := by
      calc
        _ = qsN a₀.1 * (qsN b.1) ^ 2 / X := by rw [hnormProd]
        _ = _ := (qs_square_scale_identity_S1 (qsN a₀.1) (qsN b.1) X hNa0pos hX).symm
    have hcharA :
        ψ.idealValue (a₀.1 * b.1 ^ 2) =
          ψ.idealValue a₀.1 * ψ.idealValue b.1 ^ 2 := by
      have hmul1 := qs_idealValue_mul_M0 ψ a₀.1 (b.1 ^ 2)
        a₀.2.ne_zero (pow_ne_zero _ b.2)
      have hmul2 := qs_idealValue_mul_M0 ψ b.1 b.1 b.2 b.2
      calc
        _ = ψ.idealValue a₀.1 * ψ.idealValue (b.1 ^ 2) := hmul1
        _ = ψ.idealValue a₀.1 * (ψ.idealValue b.1 * ψ.idealValue b.1) := by
          rw [pow_two, hmul2]
        _ = _ := by rw [pow_two]
    have hcharB := hvalue b.1 b.2
    have hcopBoth : IsCoprime b.1 (𝔮 * (c * d)) ↔
        IsCoprime b.1 𝔮 ∧ IsCoprime b.1 (c * d) := IsCoprime.mul_right_iff
    by_cases hbq : IsCoprime b.1 𝔮
    · have hrow := (hrowEquiv a₀ ha₀ b).mpr hbq
      dsimp [fProd]
      rw [if_pos hrow, hcharA, hcharB, harg]
      by_cases hbf : IsCoprime b.1 (c * d)
      · have hbc : IsCoprime b.1 (𝔮 * (c * d)) :=
          hcopBoth.mpr ⟨hbq, hbf⟩
        simp [hbf, hbc]
      · have hbc : ¬ IsCoprime b.1 (𝔮 * (c * d)) :=
          fun h => hbf (hcopBoth.mp h).2
        simp [hbf, hbc]
    · have hrow : ¬ rowPred (a₀.1 * b.1 ^ 2) :=
        fun h => hbq ((hrowEquiv a₀ ha₀ b).mp h)
      have hbc : ¬ IsCoprime b.1 (𝔮 * (c * d)) :=
        fun h => hbq (hcopBoth.mp h).1
      simp [fProd, hrow, hbc, hbq]
  have houterSupport (a₀ : QSSquarefreeIdeal (K := K))
      (ha₀ : a₀ ∉ Asq) (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      fProd (a₀, b) = 0 := by
    by_cases hrow : rowPred (a₀.1 * b.1 ^ 2)
    · exact False.elim (ha₀ (hA0_of_row a₀ b hrow))
    · simp [fProd, hrow]
  have hsProd : Summable fProd := by
    apply (Equiv.summable_iff qsSquarefreePairProdEquiv).1
    exact hsPair.congr (by intro p; rfl)
  have hiter := hsProd.tsum_prod
  have hlowPair : qsLow h X κ 𝔮 ψ =
      ∑' a₀ : QSSquarefreeIdeal (K := K),
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, fProd (a₀, b) := by
    calc
      _ = ∑' x : ({a : Ideal (𝓞 K) // Squarefree a} ×
          {b : Ideal (𝓞 K) // b ≠ ⊥}), fProd x := by
            calc
              _ = ∑' p : QSSquarefreePair (K := K),
                    fIdeal (qsSquarefreeDecompEquiv p) :=
                      (Equiv.tsum_eq qsSquarefreeDecompEquiv fIdeal).symm
              _ = _ := Equiv.tsum_eq qsSquarefreePairProdEquiv fProd
      _ = _ := hiter
  have houterZero : ∀ a₀ : QSSquarefreeIdeal (K := K), a₀ ∉ Asq →
      (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, fProd (a₀, b)) = 0 := by
    intro a₀ ha₀
    simp_rw [houterSupport a₀ ha₀]
    simp
  have hlowOuter :
      (∑' a₀ : QSSquarefreeIdeal (K := K),
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, fProd (a₀, b)) =
      ∑ a₀ ∈ Asq, ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, fProd (a₀, b) :=
        tsum_eq_sum houterZero
  have hlowInner (a₀ : QSSquarefreeIdeal (K := K)) (ha₀ : a₀ ∈ Asq) :
      (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, fProd (a₀, b)) =
        ψ.idealValue a₀.1 *
          qsCoprimeSq (fun y => h (y ^ 2))
            (Real.sqrt (X / qsN a₀.1)) (𝔮 * (c * d)) := by
    calc
      _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, ψ.idealValue a₀.1 *
            (if IsCoprime b.1 (𝔮 * (c * d)) then
              h ((qsN b.1 / Real.sqrt (X / qsN a₀.1)) ^ 2) else 0) := by
        apply tsum_congr
        intro b
        exact htermEq a₀ ha₀ b
      _ = ψ.idealValue a₀.1 * qsCoprimeSq
            (fun y => h (y ^ 2)) (Real.sqrt (X / qsN a₀.1))
              (𝔮 * (c * d)) := by
        rw [tsum_mul_left]
        rfl
  have hAsqSum :
      (∑ a₀ ∈ Asq, ψ.idealValue a₀.1 *
          qsCoprimeSq (fun y => h (y ^ 2))
            (Real.sqrt (X / qsN a₀.1)) (𝔮 * (c * d))) =
        ∑ a₀ ∈ Aset, ψ.idealValue a₀ *
          qsCoprimeSq (fun y => h (y ^ 2))
            (Real.sqrt (X / qsN a₀)) (𝔮 * (c * d)) := by
    apply Finset.sum_bij (fun a₀ _ => a₀.1)
    · intro a₀ ha₀
      exact (mem_qsSqfUpToSubtype_S1 κ 𝔮 a₀).mp ha₀
    · intro a₀ ha₀ b hb heq
      exact Subtype.ext heq
    · intro a hA
      refine ⟨⟨a, ?_⟩, ?_, rfl⟩
      · exact (Finset.mem_filter.mp hA).2.2.1
      · exact (mem_qsSqfUpToSubtype_S1 κ 𝔮 ⟨a, (Finset.mem_filter.mp hA).2.2.1⟩).mpr hA
    · intro a₀ ha₀
      rfl
  calc
    qsLow h X κ 𝔮 ψ =
        ∑' a₀ : QSSquarefreeIdeal (K := K),
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, fProd (a₀, b) := hlowPair
    _ = ∑ a₀ ∈ Asq, ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, fProd (a₀, b) := hlowOuter
    _ = ∑ a₀ ∈ Asq, ψ.idealValue a₀.1 *
          qsCoprimeSq (fun y => h (y ^ 2))
            (Real.sqrt (X / qsN a₀.1)) (𝔮 * (c * d)) := by
          apply Finset.sum_congr rfl
          intro a₀ ha₀
          exact hlowInner a₀ ha₀
    _ = ∑ a₀ ∈ Aset, ψ.idealValue a₀ *
          qsCoprimeSq (fun y => h (y ^ 2))
            (Real.sqrt (X / qsN a₀)) (𝔮 * (c * d)) := hAsqSum

open Classical in
set_option maxHeartbeats 1000000 in
private theorem qsTot_dual_kernels_S1 [IsTotallyComplex K] (F : QSFamily m qS)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ Λ n : ℝ) (hM : 0 < M)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮)
    (hdata : IsPrimitiveConductor (qsPairChar F c d) (c * d))
    (hsq : (qsPairChar F c d) ^ 2 = 1) (hne : qsPairChar F c d ≠ 1)
    (hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ,
      (qsPairChar F c d).locInf w u = 1)
    (hvalue : ∀ b : Ideal (𝓞 K), b ≠ ⊥ →
      (qsPairChar F c d).idealValue b ^ 2 =
        if IsCoprime b (c * d) then 1 else 0) :
    qsTot (fun x => (W x : ℂ)) M 𝔮 (qsPairChar F c d) =
      qsDualKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫)
          F W M κ Λ n 𝔮 c d + qsDualHighKernel F W M κ 𝔮 c d := by
  classical
  let ψ := qsPairChar F c d
  let f := c * d
  let H : ℝ → ℂ := fun x => qsTransform K (fun y => (W y : ℂ)) x
  let Y (e : Ideal (𝓞 K)) := qsN e * qsN f / M
  let coeff (e : Ideal (𝓞 K)) := (qsMu e : ℂ) * ψ.idealValue e *
    ((M / (qsN e * Real.sqrt (qsN f)) : ℝ) : ℂ)
  have htot := qsTot_mobius_reindex_S1 ψ f hdata hsq hne hinf W hW M hM 𝔮 h𝔮
  have hf0 : f ≠ ⊥ := hdata.1
  have hNfpos : 0 < qsN f := by
    have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_of_ne_zero hf0)
    exact_mod_cast hp
  have hsplit (e : Ideal (𝓞 K)) (he : e ∈ qsDivisors 𝔮) :
      (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        ψ.idealValue b.1 * qsTransform K (fun x => (W x : ℂ))
          ((M / qsN e) * qsN b.1 / qsN f)) =
        qsLow H (Y e) κ ⊤ ψ + qsHigh H (Y e) κ ⊤ ψ := by
    have he0 := qs_divisor_ne_zero_S1 𝔮 e h𝔮.ne_zero he
    have heNpos : 0 < qsN e := by
      have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero he0)
      exact_mod_cast hp
    have hYpos : 0 < Y e := by positivity
    have harg (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
        (M / qsN e) * qsN b.1 / qsN f = qsN b.1 / Y e := by
      dsimp [Y]
      field_simp [ne_of_gt hM, ne_of_gt heNpos, ne_of_gt hNfpos]
    have hP1 := qs_primitive_smooth_poisson_P1 ψ f hdata hsq hne hinf
      (fun x => (W x : ℂ)) hW.1 (M / qsN e) (div_pos hM heNpos)
    have hsDual0 := hP1.1.of_norm
    have hsDual : Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ψ.idealValue b.1 * H (qsN b.1 / Y e)) := by
      apply hsDual0.congr
      intro b
      dsimp [H]
      rw [harg b]
    obtain ⟨hsplitEq, hsLo, _hsHi⟩ := qs_split_smooth_core_S1 ψ H (Y e) κ hsDual
    have hsLowTop : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if IsCoprime a.1 ⊤ ∧ (qsSfNorm a.1 : ℝ) ≤ κ then
          ψ.idealValue a.1 * H (qsN a.1 / Y e) else 0) := by
      simpa [Ideal.isCoprime_iff_sup_eq] using hsLo
    have hlow := qs_low_squarefree_decomp_general_S1 F H (Y e) κ hYpos
      ⊤ c d hsLowTop hvalue
    calc
      _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            ψ.idealValue b.1 * H (qsN b.1 / Y e) := by
              apply tsum_congr
              intro b
              dsimp [H]
              rw [harg b]
      _ = qsLow H (Y e) κ ⊤ ψ + qsHigh H (Y e) κ ⊤ ψ := hsplitEq
  have hLowKernel :
      (∑ e ∈ qsDivisors 𝔮, coeff e * qsLow H (Y e) κ ⊤ ψ) =
        qsDualKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫)
          F W M κ Λ n 𝔮 c d := by
    unfold qsDualKernel
    apply Finset.sum_congr rfl
    intro e he
    have he0 := qs_divisor_ne_zero_S1 𝔮 e h𝔮.ne_zero he
    have hepos : 0 < qsN e := by
      have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero he0)
      exact_mod_cast hp
    have hP1 := qs_primitive_smooth_poisson_P1 ψ f hdata hsq hne hinf
      (fun x => (W x : ℂ)) hW.1 (M / qsN e) (div_pos hM hepos)
    have hs0 := hP1.1.of_norm
    have harg (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
        (M / qsN e) * qsN a.1 / qsN f = qsN a.1 / Y e := by
      dsimp [Y]
      field_simp [ne_of_gt hM, ne_of_gt hepos, ne_of_gt hNfpos]
    have hs : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ψ.idealValue a.1 * H (qsN a.1 / Y e)) := by
      apply hs0.congr
      intro a
      dsimp [H]
      rw [harg a]
    obtain ⟨_, hsLo, _⟩ := qs_split_smooth_core_S1 ψ H (Y e) κ hs
    have hlowInput : Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if IsCoprime a.1 ⊤ ∧ (qsSfNorm a.1 : ℝ) ≤ κ then
          ψ.idealValue a.1 * H (qsN a.1 / Y e) else 0) := by
      simpa [Ideal.isCoprime_iff_sup_eq] using hsLo
    have hlow := qs_low_squarefree_decomp_general_S1 F H (Y e) κ
      (by positivity) ⊤ c d hlowInput hvalue
    have hlowRoot : qsLow H (Y e) κ ⊤ ψ =
        ∑ a₀ ∈ qsSqfUpTo κ ⊤, ψ.idealValue a₀ *
          qsCoprimeSq (fun y => H (y ^ 2))
            (Real.sqrt (qsN e * qsN f / (M * qsN a₀))) f := by
      calc
        qsLow H (Y e) κ ⊤ ψ =
            ∑ a₀ ∈ qsSqfUpTo κ ⊤, ψ.idealValue a₀ *
              qsCoprimeSq (fun y => H (y ^ 2)) (Real.sqrt (Y e / qsN a₀))
                (⊤ * f) := hlow
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a₀ ha₀
          have hA0 : 0 < qsN a₀ := by
            have hne0 := (Finset.mem_filter.mp ha₀).2.1
            have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
              (mem_nonZeroDivisors_of_ne_zero hne0)
            exact_mod_cast hp
          have hroot : Real.sqrt (Y e / qsN a₀) =
              Real.sqrt (qsN e * qsN f / (M * qsN a₀)) := by
            congr 1
            dsimp [Y]
            field_simp [ne_of_gt hM, ne_of_gt hepos, ne_of_gt hNfpos, ne_of_gt hA0]
          rw [hroot]
          simp
    calc
      _ = coeff e * qsLow H (Y e) κ ⊤ ψ := by rfl
      _ = coeff e * ∑ a₀ ∈ qsSqfUpTo κ ⊤, ψ.idealValue a₀ *
            qsCoprimeSq (fun y => H (y ^ 2))
              (Real.sqrt (qsN e * qsN f / (M * qsN a₀))) f :=
                congrArg (fun z : ℂ => coeff e * z) hlowRoot
      _ = _ := by simp [coeff, H, f, ψ]
  have hHighKernel :
      (∑ e ∈ qsDivisors 𝔮, coeff e * qsHigh H (Y e) κ ⊤ ψ) =
        qsDualHighKernel F W M κ 𝔮 c d := by
    unfold qsDualHighKernel
    apply Finset.sum_congr rfl
    intro e he
    simp [coeff, Y, H, f, ψ]
  calc
    qsTot (fun x => (W x : ℂ)) M 𝔮 ψ =
        ∑ e ∈ qsDivisors 𝔮, coeff e *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            ψ.idealValue b.1 * qsTransform K (fun x => (W x : ℂ))
              ((M / qsN e) * qsN b.1 / qsN f) := by
      simpa [coeff, f, ψ] using htot
    _ = ∑ e ∈ qsDivisors 𝔮, coeff e *
          (qsLow H (Y e) κ ⊤ ψ + qsHigh H (Y e) κ ⊤ ψ) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hsplit e he]
    _ = (∑ e ∈ qsDivisors 𝔮, coeff e * qsLow H (Y e) κ ⊤ ψ) +
          ∑ e ∈ qsDivisors 𝔮, coeff e * qsHigh H (Y e) κ ⊤ ψ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ = qsDualKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫)
          F W M κ Λ n 𝔮 c d + qsDualHighKernel F W M κ 𝔮 c d := by
      rw [hLowKernel, hHighKernel]

private theorem qs_high_eq_tot_sub_low_S1 (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ : ℝ) (hM : 0 < M) (𝔮 : Ideal (𝓞 K))
    (ψ : ArtinPrimitiveRoots.A1.HeckeChar K) :
    qsHigh (fun x => (W x : ℂ)) M κ 𝔮 ψ =
      qsTot (fun x => (W x : ℂ)) M 𝔮 ψ -
        qsLow (fun x => (W x : ℂ)) M κ 𝔮 ψ := by
  classical
  let tot : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if IsCoprime a.1 𝔮 then ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0
  let lo : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if IsCoprime a.1 𝔮 ∧ (qsSfNorm a.1 : ℝ) ≤ κ then
      ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0
  let hi : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if IsCoprime a.1 𝔮 ∧ κ < (qsSfNorm a.1 : ℝ) then
      ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0
  have hsLo : Summable lo := by
    simpa [lo] using qs_cap_series_summable_S1 W hW M hM ψ
      (fun a => IsCoprime a 𝔮 ∧ (qsSfNorm a : ℝ) ≤ κ)
  have hsHi : Summable hi := by
    simpa [hi] using qs_cap_series_summable_S1 W hW M hM ψ
      (fun a => IsCoprime a 𝔮 ∧ κ < (qsSfNorm a : ℝ))
  have hpoint (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) : tot a = hi a + lo a := by
    by_cases hcop : IsCoprime a.1 𝔮
    · by_cases hlo : (qsSfNorm a.1 : ℝ) ≤ κ
      · have hnot : ¬ κ < (qsSfNorm a.1 : ℝ) := not_lt_of_ge hlo
        simp [tot, hi, lo, hcop, hlo, hnot]
      · have hhigh : κ < (qsSfNorm a.1 : ℝ) := lt_of_not_ge hlo
        simp [tot, hi, lo, hcop, hlo, hhigh]
    · simp [tot, hi, lo, hcop]
  have hlo : (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, lo a) =
      qsLow (fun x => (W x : ℂ)) M κ 𝔮 ψ := by
    unfold qsLow lo
    apply tsum_congr
    intro (a : {I : Ideal (𝓞 K) // I ≠ ⊥})
    rfl
  have hhi : (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, hi a) =
      qsHigh (fun x => (W x : ℂ)) M κ 𝔮 ψ := by
    unfold qsHigh hi
    apply tsum_congr
    intro (a : {I : Ideal (𝓞 K) // I ≠ ⊥})
    rfl
  have hsplit : qsTot (fun x => (W x : ℂ)) M 𝔮 ψ =
      qsHigh (fun x => (W x : ℂ)) M κ 𝔮 ψ +
        qsLow (fun x => (W x : ℂ)) M κ 𝔮 ψ := by
    calc
      _ = ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, (hi a + lo a) := by
        unfold qsTot
        apply tsum_congr
        intro (a : {I : Ideal (𝓞 K) // I ≠ ⊥})
        exact hpoint a
      _ = (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, hi a) +
            (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, lo a) := hsHi.tsum_add hsLo
      _ = _ := by rw [hhi, hlo]
  calc
    qsHigh (fun x => (W x : ℂ)) M κ 𝔮 ψ =
        (qsHigh (fun x => (W x : ℂ)) M κ 𝔮 ψ +
          qsLow (fun x => (W x : ℂ)) M κ 𝔮 ψ) -
          qsLow (fun x => (W x : ℂ)) M κ 𝔮 ψ := by ring
    _ = _ := by rw [← hsplit]

private theorem qs_low_squarefree_removal_S1 (F : QSFamily m qS)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ Λ : ℝ) (hM : 0 < M)
    (𝔮 c d : Ideal (𝓞 K))
    (hdata : IsPrimitiveConductor (qsPairChar F c d) (c * d))
    (hsq : (qsPairChar F c d) ^ 2 = 1) :
    qsLow (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) =
      qsOrigKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫)
        F W M κ Λ 𝔮 c d := by
  classical
  let ψ := qsPairChar F c d
  let rowPred := fun a : Ideal (𝓞 K) =>
    IsCoprime a 𝔮 ∧ (qsSfNorm a : ℝ) ≤ κ
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a =>
    if rowPred a.1 then ψ.idealValue a.1 * (W (qsN a.1 / M) : ℂ) else 0
  obtain ⟨rows, hzero, _⟩ := qs_cap_tsum_eq_finite_S1 W hW M hM ψ rowPred
  have hfinite : {a | f a ≠ 0}.Finite := by
    apply (Finset.finite_toSet rows).subset
    intro a ha
    by_contra hnot
    exact ha (by simpa [f, rowPred] using hzero a hnot)
  have hs : Summable f := summable_of_hasFiniteSupport hfinite
  have h := qs_low_squarefree_decomp_general_S1 F (fun x => (W x : ℂ)) M κ hM
    𝔮 c d hs (qs_pairValue_sq_indicator_S1 F c d hdata hsq)
  simpa [qsOrigKernel] using h

/-- S1 (IMPL; RETIER `qs_squarefree_removal_S1`, hardest of MOBIUS): exact squarefree-removal
identity for one residual pair. -/
theorem qs_squarefree_removal_S1 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ Λ n : ℝ) (hM : 0 < M)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮) (h𝔮bad : qsBadRad m qS ∣ 𝔮)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d) (hcd1 : c * d ≠ ⊤)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hc𝔮 : IsCoprime c 𝔮) (hd𝔮 : IsCoprime d 𝔮) :
    qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) =
      qsDualKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫) F W M κ Λ n 𝔮 c d +
        qsDualHighKernel F W M κ 𝔮 c d -
          qsOrigKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫) F W M κ Λ 𝔮 c d := by
  classical
  rcases qs_pair_character_data_S1 F c d hc hd hcd hcd1 hcl with
    ⟨hdata, hsq, hne, hinf⟩
  have hvalue := qs_pairValue_sq_indicator_S1 F c d hdata hsq
  have htotal := qsTot_dual_kernels_S1 F W hW M κ Λ n hM 𝔮 c d h𝔮
    hdata hsq hne hinf hvalue
  have hlow := qs_low_squarefree_removal_S1 F W hW M κ Λ hM 𝔮 c d hdata hsq
  have hsplit := qs_high_eq_tot_sub_low_S1 W hW M κ hM 𝔮 (qsPairChar F c d)
  calc
    qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) =
        qsTot (fun x => (W x : ℂ)) M 𝔮 (qsPairChar F c d) -
          qsLow (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) := hsplit
    _ = _ := by rw [htotal, hlow]

end ArtinPrimitiveRoots.A2
