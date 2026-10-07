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
