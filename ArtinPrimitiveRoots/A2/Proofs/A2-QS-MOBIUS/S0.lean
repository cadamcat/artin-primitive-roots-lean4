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

/-- S0 (IMPL): family multiplicativity on rows coprime to `m` and `qS` (trivial ray factor):
`χ_{cd}(a) = χ_c(a) χ_d(a)` for coprime admissible `c, d`.  Prime by prime:
`χ_{cd}(P) = χ_P(cd) = χ_P(c) χ_P(d) = χ_c(P) χ_d(P)` for `P ∤ cd`, and both sides vanish at
`P ∣ cd`. -/
theorem qs_family_mul_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (c d : Ideal (𝓞 K)) (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (a : Ideal (𝓞 K)) (ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a) (haq : IsCoprime a qS) :
    (F.character (c * d)).idealValue a =
      (F.character c).idealValue a * (F.character d).idealValue a := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
