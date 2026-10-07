import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.TypeII.Marked
import Mathlib.NumberTheory.EulerProduct.Basic

namespace ArtinPrimitiveRoots.Construction

open Classical
open ArtinPrimitiveRoots.TypeII

noncomputable def rpowSeriesTerm (t : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.rpow (n : ℝ) (-t)

private lemma rpowSeriesTerm_one (t : ℝ) : rpowSeriesTerm t 1 = 1 := by
  simp [rpowSeriesTerm]

private lemma rpowSeriesTerm_mul (t : ℝ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    rpowSeriesTerm t (m * n) = rpowSeriesTerm t m * rpowSeriesTerm t n := by
  rw [rpowSeriesTerm, if_neg (mul_ne_zero hm hn), rpowSeriesTerm, if_neg hm,
    rpowSeriesTerm, if_neg hn, Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

private lemma rpowSeriesTerm_primePow (t : ℝ) (p : ℕ) (e : ℕ) (hp : p.Prime) :
    rpowSeriesTerm t (p ^ e) = (Real.rpow (p : ℝ) (-t)) ^ e := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpcast : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpPow : p ^ e ≠ 0 := pow_ne_zero e hp0
  rw [rpowSeriesTerm, if_neg hpPow, Nat.cast_pow]
  calc
    Real.rpow ((p : ℝ) ^ e) (-t) = Real.rpow (p : ℝ) ((e : ℝ) * (-t)) :=
      (Real.rpow_natCast_mul hpcast e (-t)).symm
    _ = Real.rpow (p : ℝ) ((-t) * (e : ℝ)) := by congr 1 <;> ring
    _ = (Real.rpow (p : ℝ) (-t)) ^ e := Real.rpow_mul_natCast hpcast (-t) e

private lemma rpowSeriesTerm_primePow_summable {t : ℝ} (ht : 0 < t)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖rpowSeriesTerm t (p ^ e)‖) := by
  have hpcast : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpcast
  have hz : 0 < Real.rpow (p : ℝ) (-t) := Real.rpow_pos_of_pos (by linarith) _
  have hzlt : Real.rpow (p : ℝ) (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpcast (by linarith)
  have hgeom := summable_geometric_of_lt_one hz.le hzlt
  apply hgeom.congr
  intro e
  rw [rpowSeriesTerm_primePow t p e hp]
  rw [Real.norm_of_nonneg (pow_nonneg hz.le _)]

theorem hasSum_rpowSeries_factoredNumbers {s : Finset ℕ} {t : ℝ} (ht : 0 < t)
    (hs : ∀ p ∈ s, p.Prime) :
    Summable (fun n : Nat.factoredNumbers s => rpowSeriesTerm t n) ∧
      HasSum (fun n : Nat.factoredNumbers s => rpowSeriesTerm t n)
        (∏ p ∈ s with p.Prime,
          (1 - Real.rpow (p : ℝ) (-t))⁻¹) := by
  let f : ℕ → ℝ := rpowSeriesTerm t
  have hf1 : f 1 = 1 := rpowSeriesTerm_one t
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n _
    by_cases hm : m = 0
    · simp [f, hm, rpowSeriesTerm]
    · by_cases hn : n = 0
      · simp [f, hn, rpowSeriesTerm]
      · exact rpowSeriesTerm_mul t hm hn
  obtain ⟨hsm, hhas⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      hf1 hmul (fun {_} hp => rpowSeriesTerm_primePow_summable ht hp) s
  have hlocal (p : ℕ) (hp : p ∈ s) (hpp : p.Prime) :
      ∑' e : ℕ, f (p ^ e) = (1 - Real.rpow (p : ℝ) (-t))⁻¹ := by
    have hz : 0 < Real.rpow (p : ℝ) (-t) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hpp.pos) _
    have hpcast : 1 < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hzlt : Real.rpow (p : ℝ) (-t) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpcast (by linarith)
    rw [show (fun e : ℕ => f (p ^ e)) =
        (fun e : ℕ => (Real.rpow (p : ℝ) (-t)) ^ e) by
          funext e
          exact rpowSeriesTerm_primePow t p e hpp]
    exact tsum_geometric_of_lt_one hz.le hzlt
  have hprod :
      (∏ p ∈ s with p.Prime, (1 - Real.rpow (p : ℝ) (-t))⁻¹) =
        ∏ p ∈ s with p.Prime, ∑' e : ℕ, f (p ^ e) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    exact (hlocal p (Finset.mem_filter.mp hp).1 hpp).symm
  have hhas' : HasSum (fun n : Nat.factoredNumbers s => rpowSeriesTerm t n)
      (∏ p ∈ s with p.Prime, (1 - Real.rpow (p : ℝ) (-t))⁻¹) := by
    rw [hprod]
    simpa [f] using hhas
  have hsm' : Summable (fun n : Nat.factoredNumbers s => rpowSeriesTerm t n) := by
    simpa [f] using hsm.of_norm
  exact ⟨hsm', hhas'⟩

/- Adapted from the finite-band separation and one-prime-choice arguments in
   lane c3's Construction/Proofs/c3/Positivity.lean. -/
theorem harmonic_primeBands_disjoint_large (K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ i j : Fin K, i ≠ j →
        Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
  have hdis (i j : Fin K) (hij : a i < a j) :
      ∀ᶠ x : ℝ in Filter.atTop,
        Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
    let δ := a j - a i
    have hδ : 0 < δ := sub_pos.mpr hij
    have hpow : Filter.Tendsto (fun x : ℝ => Real.rpow (Real.log x) δ)
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hδ).comp Real.tendsto_log_atTop
    have hlarge := hpow.eventually_gt_atTop 2
    have hlog : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log x := by
      filter_upwards [Filter.eventually_atTop.2 ⟨Real.exp 1,
        fun x hx => by
          have h1exp : (1 : ℝ) < Real.exp 1 := by
            simpa using (Real.exp_strictMono (by norm_num : (0 : ℝ) < 1))
          exact Real.log_pos (lt_of_lt_of_le h1exp hx)⟩] with x hx
      exact hx
    filter_upwards [hlarge, hlog] with x hxlarge hxlog
    have hfactor : Real.rpow (Real.log x) (a j) =
        Real.rpow (Real.log x) (a i) * Real.rpow (Real.log x) δ := by
      calc
        Real.rpow (Real.log x) (a j) =
            Real.rpow (Real.log x) (a i + δ) := by
              congr 1
              dsimp [δ]
              ring
        _ = Real.rpow (Real.log x) (a i) * Real.rpow (Real.log x) δ :=
          Real.rpow_add hxlog _ _
    have hsep : 2 * Real.rpow (Real.log x) (a i) <
        Real.rpow (Real.log x) (a j) := by
      have hpos : 0 < Real.rpow (Real.log x) (a i) :=
        Real.rpow_pos_of_pos hxlog _
      calc
        2 * Real.rpow (Real.log x) (a i) <
            Real.rpow (Real.log x) (a i) * Real.rpow (Real.log x) δ := by
              nlinarith
        _ = Real.rpow (Real.log x) (a j) := hfactor.symm
    have hexp : Real.exp (2 * Real.rpow (Real.log x) (a i)) <
        Real.exp (Real.rpow (Real.log x) (a j)) := Real.exp_lt_exp.mpr hsep
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    rcases Finset.mem_filter.mp hpi with ⟨_, ⟨_, _, hupper⟩⟩
    rcases Finset.mem_filter.mp hpj with ⟨_, ⟨_, hlower, _⟩⟩
    have hpupper : (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) (a i)) := hupper
    have hplower : Real.exp (Real.rpow (Real.log x) (a j)) ≤ (p : ℝ) := hlower
    linarith
  have hpair (i j : Fin K) (hij : i ≠ j) :
      ∀ᶠ x : ℝ in Filter.atTop,
        Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
    have hlt : a i < a j ∨ a j < a i := by
      by_cases hval : i.val < j.val
      · exact Or.inl (ha.2.2 i j hval)
      · have hval' : j.val < i.val := by omega
        exact Or.inr (ha.2.2 j i hval')
    rcases hlt with hlt | hlt
    · exact hdis i j hlt
    · exact (hdis j i hlt).mono fun x h => h.symm
  have hall : ∀ᶠ x : ℝ in Filter.atTop,
      ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro j
    by_cases hij : i = j
    · subst j
      filter_upwards [] with x
      exact fun h => False.elim (h rfl)
    · filter_upwards [hpair i j hij] with x hx
      exact fun _ => hx
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hall
  exact ⟨x₀, hx₀⟩

theorem harmonic_markedWeight_onePrimeChoice (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (f : Fin K → ℕ)
    (hf : f ∈ Fintype.piFinset (fun i : Fin K => primeBand x (a i)))
    (hbands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    markedWeight x K a (1 / 2 : ℝ) (∏ i : Fin K, f i) =
      ∏ i : Fin K, 1 / bandMass x (a i) := by
  let B : Fin K → Finset ℕ := fun i => primeBand x (a i)
  let r : ℕ := ∏ i : Fin K, f i
  have hfi (i : Fin K) : f i ∈ B i := Fintype.mem_piFinset.mp hf i
  have hprime (i : Fin K) : (f i).Prime := by
    dsimp [B, primeBand] at hfi
    exact (Finset.mem_filter.mp (hfi i)).2.1
  have hfactor (i : Fin K) (p : ℕ) (hp : p ∈ B i) (hpd : p ∣ r) :
      ∃ j : Fin K, p = f j := by
    have hpp : p.Prime := by
      dsimp [B, primeBand] at hp
      exact (Finset.mem_filter.mp hp).2.1
    obtain ⟨j, _, hdiv⟩ :=
      (_root_.Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp) f).mp hpd
    exact ⟨j, (Nat.prime_dvd_prime_iff_eq hpp (hprime j)).mp hdiv⟩
  have hfilter (i : Fin K) :
      (B i).filter (fun p => p ∣ r) = {f i} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hpd⟩
      obtain ⟨j, hpj⟩ := hfactor i p hp hpd
      by_cases hji : j = i
      · simpa [hji] using hpj
      · have hmemj : p ∈ B j := by rw [hpj]; exact hfi j
        exact False.elim ((Finset.disjoint_left.mp (hbands i j (Ne.symm hji))) hp hmemj)
    · intro hp
      subst p
      refine ⟨hfi i, ?_⟩
      exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hbandOmega (i : Fin K) : bandOmega x (a i) r = 1 := by
    unfold bandOmega
    change ((B i).filter (fun p => p ∣ r)).card = 1
    rw [hfilter i]
    simp
  have hSupport : ∀ i : Fin K, ∃ p ∈ primeBand x (a i), p ∣ r := by
    intro i
    exact ⟨f i, hfi i, Finset.dvd_prod_of_mem f (Finset.mem_univ i)⟩
  have hOmega : markedOmega x K a r = K := by
    unfold markedOmega
    simp [hbandOmega]
  change markedWeight x K a (1 / 2 : ℝ) r = ∏ i : Fin K, 1 / bandMass x (a i)
  unfold markedWeight
  rw [if_pos hSupport]
  simp [hOmega, hbandOmega]

theorem bandMass_upper_all {K : ℕ} {a : Fin K → ℝ} (ha : ValidBands K a) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      ∀ i : Fin K, bandMass x (a i) ≤ 2 * Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  choose X hX hmass using fun i : Fin K =>
    band_mass (a i) (by linarith [ha.2.1 i])
      (by linarith [ha.2.1 i]) (Real.log 2) hlog2
  let Xall := ∑ i : Fin K, X i
  have hXi_le (i : Fin K) : X i ≤ Xall :=
    Finset.single_le_sum (fun j hj => by linarith [hX j]) (Finset.mem_univ i)
  have hK : 0 < K := ha.1
  have hXall : 2 ≤ Xall := by
    let i : Fin K := ⟨0, hK⟩
    exact (hX i).trans (hXi_le i)
  refine ⟨Xall, hXall, ?_⟩
  intro x hx i
  have hx_i : X i ≤ x := (hXi_le i).trans hx
  have h := (hmass i x hx_i).1
  have := (abs_le.mp h).2
  linarith

theorem isGroupInteger_iff_mem_factoredNumbers
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (r : ℕ) :
    IsGroupInteger x K a r ↔ r ∈ Nat.factoredNumbers (markedPrimes x K a) := by
  rw [Nat.mem_factoredNumbers']
  rfl

theorem groupHarmonicMass_eq_tsum_factoredNumbers
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :
    groupHarmonicMass x K a =
      ∑' n : Nat.factoredNumbers (markedPrimes x K a),
        markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ) := by
  let S := markedPrimes x K a
  let f : ℕ → ℝ := fun r =>
    if IsGroupInteger x K a r then
      markedWeight x K a (1 / 2 : ℝ) r / (r : ℝ) else 0
  have hsupp : Function.support f ⊆ Nat.factoredNumbers S := by
    intro r hr
    change f r ≠ 0 at hr
    by_cases hg : IsGroupInteger x K a r
    · exact (isGroupInteger_iff_mem_factoredNumbers x K a r).mp hg
    · simp [f, hg] at hr
  have hsum := tsum_subtype_eq_of_support_subset (f := f) hsupp
  rw [groupHarmonicMass]
  calc
    (∑' r : ℕ, f r) =
        ∑' n : Nat.factoredNumbers S, f n := hsum.symm
    _ = ∑' n : Nat.factoredNumbers (markedPrimes x K a),
        markedWeight x K a (1 / 2 : ℝ) n / (n : ℝ) := by
          apply tsum_congr
          intro n
          have hgroup :=
            (isGroupInteger_iff_mem_factoredNumbers x K a n).mpr n.property
          simp [f, hgroup]

theorem finite_group_sum_le_tsum
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (T : Finset ℕ)
    (hT : ∀ r ∈ T, IsGroupInteger x K a r)
    (f : ℕ → ℝ)
    (g : Nat.factoredNumbers (markedPrimes x K a) → ℝ)
    (heq : ∀ r (hr : r ∈ T), f r = g ⟨r,
      (isGroupInteger_iff_mem_factoredNumbers x K a r).mp (hT r hr)⟩)
    (hg : Summable g) (hgnonneg : ∀ n, 0 ≤ g n) :
    (∑ r ∈ T, f r) ≤ ∑' n, g n := by
  classical
  let e : {r : ℕ // r ∈ T} ↪ Nat.factoredNumbers (markedPrimes x K a) := {
    toFun := fun r => ⟨r, (isGroupInteger_iff_mem_factoredNumbers x K a r).mp
      (hT r r.property)⟩
    inj' := by
      intro r s hrs
      apply Subtype.ext
      exact congrArg
        (fun n : Nat.factoredNumbers (markedPrimes x K a) => (n : ℕ)) hrs
  }
  let U := T.attach.map e
  have hattach : (∑ r ∈ T, f r) = ∑ r ∈ T.attach, f r := by
    simpa using (Finset.sum_attach T f).symm
  have hmap : (∑ r ∈ T.attach, g (e r)) = ∑ n ∈ U, g n := by
    apply Finset.sum_bij (fun r _ => e r)
    · intro r hr
      exact Finset.mem_map.mpr ⟨r, hr, rfl⟩
    · intro r hr s hs hEq
      exact e.injective hEq
    · intro n hn
      rcases Finset.mem_map.mp hn with ⟨r, hr, hEq⟩
      exact ⟨r, hr, hEq⟩
    · intro r hr
      rfl
  calc
    (∑ r ∈ T, f r) = ∑ r ∈ T.attach, g (e r) := by
      rw [hattach]
      apply Finset.sum_congr rfl
      intro r hr
      exact heq r.1 r.2
    _ = ∑ n ∈ U, g n := hmap
    _ ≤ ∑' n, g n := hg.sum_le_tsum U (fun n hn => hgnonneg n)

private noncomputable def natPosEquiv : ℕ ≃ {n : ℕ // n ≠ 0} where
  toFun n := ⟨n + 1, by omega⟩
  invFun n := n.val - 1
  left_inv n := by simp
  right_inv n := by
    apply Subtype.ext
    have hpos : 1 ≤ n.val := Nat.one_le_iff_ne_zero.mpr n.property
    exact Nat.sub_add_cancel hpos

theorem tsum_geometric_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, if n = 0 then 0 else r ^ n) = r / (1 - r) := by
  let f : ℕ → ℝ := fun n => if n = 0 then 0 else r ^ n
  have hsupp : Function.support f ⊆ {n : ℕ | n ≠ 0} := by
    intro n hn
    change f n ≠ 0 at hn
    by_contra hzero
    have hn0 : n = 0 := by simpa using hzero
    subst n
    simp [f] at hn
  have hsub :
      (∑' n : {n : ℕ // n ≠ 0}, f n) = ∑' n : ℕ, f n :=
    tsum_subtype_eq_of_support_subset (f := f) hsupp
  calc
    (∑' n : ℕ, if n = 0 then 0 else r ^ n) =
        ∑' n : {n : ℕ // n ≠ 0}, r ^ (n : ℕ) := by
          rw [show (fun n : ℕ => if n = 0 then 0 else r ^ n) = f by rfl]
          rw [← hsub]
          apply tsum_congr
          intro n
          simp [f, n.property]
    _ = ∑' n : ℕ, r ^ (n + 1) := by
          exact (natPosEquiv.tsum_eq (fun n : {n : ℕ // n ≠ 0} => r ^ (n : ℕ))).symm
    _ = r * ∑' n : ℕ, r ^ n := by
          rw [show (fun n : ℕ => r ^ (n + 1)) =
            (fun n : ℕ => r * r ^ n) by
              funext n
              rw [pow_succ]
              ring]
          rw [tsum_mul_left]
    _ = r / (1 - r) := by
          rw [tsum_geometric_of_lt_one hr0 hr1]
          ring

noncomputable def halfOmegaTerm (n : ℕ) : ℝ :=
  if n = 0 then 0 else (1 / 2 : ℝ) ^ n.primeFactors.card / (n : ℝ)

private lemma halfOmegaTerm_one : halfOmegaTerm 1 = 1 := by
  simp [halfOmegaTerm]

private lemma halfOmegaTerm_mul {m n : ℕ} (hcop : Nat.Coprime m n) :
    halfOmegaTerm (m * n) = halfOmegaTerm m * halfOmegaTerm n := by
  by_cases hm : m = 0
  · have hn : n = 1 := (Nat.coprime_zero_left n).mp (by simpa [hm] using hcop)
    simp [halfOmegaTerm, hm, hn]
  · by_cases hn : n = 0
    · have hm1 : m = 1 := (Nat.coprime_zero_right m).mp (by simpa [hn] using hcop)
      simp [halfOmegaTerm, hm, hn, hm1]
    · have hdisj := hcop.disjoint_primeFactors
      have hcard : (m * n).primeFactors.card =
          m.primeFactors.card + n.primeFactors.card := by
        rw [Nat.Coprime.primeFactors_mul hcop, Finset.card_union_of_disjoint hdisj]
      rw [halfOmegaTerm, if_neg (mul_ne_zero hm hn), halfOmegaTerm, if_neg hm,
        halfOmegaTerm, if_neg hn, hcard, pow_add, Nat.cast_mul]
      field_simp [Nat.cast_ne_zero.mpr hm, Nat.cast_ne_zero.mpr hn]
      <;> ring

private lemma halfOmegaTerm_primePow (p e : ℕ) (hp : p.Prime) :
    halfOmegaTerm (p ^ e) = if e = 0 then 1 else
      (1 / 2 : ℝ) / (p ^ e : ℕ) := by
  by_cases he : e = 0
  · simp [halfOmegaTerm, he]
  · have hpow0 : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
    rw [halfOmegaTerm, if_neg hpow0, Nat.primeFactors_pow p he]
    simp [hp, he]

private lemma halfOmegaPrimePowerSummable (p : ℕ) (hp : p.Prime) :
    Summable (fun e : ℕ => ‖halfOmegaTerm (p ^ e)‖) := by
  have hpcast : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpcast0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := (div_lt_one hpcast0).2 hpcast
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  apply Summable.of_nonneg_of_le
    (fun e => norm_nonneg (halfOmegaTerm (p ^ e)))
    (fun e => ?_)
    hgeom
  by_cases he : e = 0
  · subst e
    norm_num [halfOmegaTerm]
  · rw [halfOmegaTerm_primePow p e hp, if_neg he]
    have hterm : 0 ≤ (1 / 2 : ℝ) / (p ^ e : ℕ) := by positivity
    rw [Real.norm_of_nonneg hterm]
    have hpowle : (1 / 2 : ℝ) / (p ^ e : ℕ) ≤ 1 / (p ^ e : ℕ) :=
      div_le_div_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.cast_nonneg _)
    have hpowEq : 1 / (p ^ e : ℕ) = (1 / (p : ℝ)) ^ e := by
      rw [Nat.cast_pow]
      simp only [one_div, inv_pow]
    calc
      (1 / 2 : ℝ) / (p ^ e : ℕ) ≤ 1 / (p ^ e : ℕ) := hpowle
      _ = (1 / (p : ℝ)) ^ e := hpowEq

theorem hasSum_halfOmega_factoredNumbers {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    Summable (fun n : Nat.factoredNumbers S => halfOmegaTerm n) ∧
      HasSum (fun n : Nat.factoredNumbers S => halfOmegaTerm n)
        (∏ p ∈ S, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1))) := by
  obtain ⟨hsum, hhas⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      halfOmegaTerm_one halfOmegaTerm_mul
      (fun {_} hp => halfOmegaPrimePowerSummable _ hp) S
  have hlocal (p : ℕ) (hp : p ∈ S) (hpp : p.Prime) :
      ∑' e : ℕ, halfOmegaTerm (p ^ e) =
        1 + (1 / 2 : ℝ) / ((p : ℝ) - 1) := by
    have hpcast : 1 < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hratio0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hpcast0 : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
    have hratio1 : 1 / (p : ℝ) < 1 := (div_lt_one hpcast0).2 hpcast
    have hseries : Summable (fun e : ℕ => halfOmegaTerm (p ^ e)) :=
      (halfOmegaPrimePowerSummable p hpp).of_norm
    have hsplit := hseries.tsum_eq_add_tsum_ite 0
    have htail :
        (∑' e : ℕ, if e = 0 then 0 else halfOmegaTerm (p ^ e)) =
          (1 / 2 : ℝ) * (1 / (p : ℝ) / (1 - 1 / (p : ℝ))) := by
      calc
        (∑' e : ℕ, if e = 0 then 0 else halfOmegaTerm (p ^ e)) =
            (1 / 2 : ℝ) *
              ∑' e : ℕ, if e = 0 then 0 else (1 / (p : ℝ)) ^ e := by
                calc
                  (∑' e : ℕ, if e = 0 then 0 else halfOmegaTerm (p ^ e)) =
                      ∑' e : ℕ, (1 / 2 : ℝ) *
                        (if e = 0 then 0 else (1 / (p : ℝ)) ^ e) := by
                          apply tsum_congr
                          intro e
                          by_cases he : e = 0
                          · simp [he]
                          · have hpowEq : 1 / (p ^ e : ℕ) =
                                (1 / (p : ℝ)) ^ e := by
                              rw [Nat.cast_pow]
                              simp only [one_div, inv_pow]
                            calc
                              (if e = 0 then 0 else halfOmegaTerm (p ^ e)) =
                                  halfOmegaTerm (p ^ e) := by simp [he]
                              _ = (1 / 2 : ℝ) / (p ^ e : ℕ) := by
                                    rw [halfOmegaTerm_primePow p e hpp, if_neg he]
                              _ = (1 / 2 : ℝ) * (1 / (p : ℝ)) ^ e := by
                                    calc
                                      (1 / 2 : ℝ) / (p ^ e : ℕ) =
                                          (1 / 2 : ℝ) * (1 / (p ^ e : ℕ)) := by ring
                                      _ = (1 / 2 : ℝ) * (1 / (p : ℝ)) ^ e := by
                                            rw [hpowEq]
                            simp [he]
                  _ = (1 / 2 : ℝ) *
                        ∑' e : ℕ, if e = 0 then 0 else (1 / (p : ℝ)) ^ e :=
                          tsum_mul_left
        _ = (1 / 2 : ℝ) * (1 / (p : ℝ) / (1 - 1 / (p : ℝ))) := by
              congr 1
              rw [tsum_geometric_pos hratio0 hratio1]
    calc
      (∑' e : ℕ, halfOmegaTerm (p ^ e)) =
          halfOmegaTerm (p ^ 0) +
            ∑' e : ℕ, if e = 0 then 0 else halfOmegaTerm (p ^ e) := hsplit
      _ = 1 + (1 / 2 : ℝ) / ((p : ℝ) - 1) := by
            rw [halfOmegaTerm_primePow p 0 hpp, if_pos rfl, htail]
            field_simp [ne_of_gt hpcast]
            <;> ring
  have hfilter : S.filter Nat.Prime = S := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro hp
      exact ⟨hp, hS p hp⟩
  have hprod :
      (∏ p ∈ S with p.Prime, ∑' e : ℕ, halfOmegaTerm (p ^ e)) =
        ∏ p ∈ S, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
    rw [hfilter]
    apply Finset.prod_congr rfl
    intro p hp
    exact hlocal p hp (hS p hp)
  have hhas' : HasSum (fun n : Nat.factoredNumbers S => halfOmegaTerm n)
      (∏ p ∈ S, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1))) := by
    rw [← hprod]
    exact hhas
  exact ⟨hsum.of_norm, hhas'⟩

theorem halfOmega_divisor_indicator_inclusion (D : Finset ℕ)
    (hDprime : ∀ p ∈ D, p.Prime) (n : ℕ) (hn : n ≠ 0) :
    (if D ⊆ n.primeFactors then (1 : ℝ) else 0) =
      ∑ E ∈ D.powerset,
        (-1 : ℝ) ^ E.card * (if ∀ p ∈ E, ¬ p ∣ n then 1 else 0) := by
  classical
  have hprodDiv :
      (∏ p ∈ D, if p ∣ n then (1 : ℝ) else 0) =
        if D ⊆ n.primeFactors then 1 else 0 := by
    by_cases hsub : D ⊆ n.primeFactors
    · have hdiv : ∀ p ∈ D, p ∣ n := by
        intro p hp
        exact (Nat.mem_primeFactors_of_ne_zero hn).mp (hsub hp) |>.2
      calc
        (∏ p ∈ D, if p ∣ n then (1 : ℝ) else 0) = ∏ p ∈ D, (1 : ℝ) := by
          apply Finset.prod_congr rfl
          intro p hp
          simp [hdiv p hp]
        _ = 1 := by simp
        _ = if D ⊆ n.primeFactors then 1 else 0 := by simp [hsub]
    · obtain ⟨p, hpD, hpnot⟩ := Finset.not_subset.mp hsub
      have hpnotdiv : ¬ p ∣ n := by
        intro hpd
        exact hpnot ((Nat.mem_primeFactors_of_ne_zero hn).mpr
          ⟨hDprime p hpD, hpd⟩)
      have hzero : (if p ∣ n then (1 : ℝ) else 0) = 0 := if_neg hpnotdiv
      rw [Finset.prod_eq_zero hpD hzero]
      simp [hsub]
  have hfactor (p : ℕ) (hp : p ∈ D) :
      (if p ∣ n then (1 : ℝ) else 0) =
        (-(if ¬ p ∣ n then (1 : ℝ) else 0)) + 1 := by
    by_cases hpd : p ∣ n <;> simp [hpd]
  rw [← hprodDiv]
  calc
    (∏ p ∈ D, if p ∣ n then (1 : ℝ) else 0) =
        ∏ p ∈ D, ((-(if ¬ p ∣ n then (1 : ℝ) else 0)) + 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          exact hfactor p hp
    _ = ∑ E ∈ D.powerset,
          (-1 : ℝ) ^ E.card * (if ∀ p ∈ E, ¬ p ∣ n then 1 else 0) := by
            rw [Finset.prod_add]
            apply Finset.sum_congr rfl
            intro E hE
            have havoid :
                (∏ p ∈ E, if ¬ p ∣ n then (1 : ℝ) else 0) =
                  if ∀ p ∈ E, ¬ p ∣ n then 1 else 0 := by
              by_cases h : ∀ p ∈ E, ¬ p ∣ n
              · calc
                  (∏ p ∈ E, if ¬ p ∣ n then (1 : ℝ) else 0) =
                      ∏ p ∈ E, (1 : ℝ) := by
                        apply Finset.prod_congr rfl
                        intro p hp
                        simp [h p hp]
                  _ = 1 := by simp
                  _ = if ∀ p ∈ E, ¬ p ∣ n then 1 else 0 := (if_pos h).symm
              · push_neg at h
                obtain ⟨p, hpE, hpd⟩ := h
                have hnotall : ¬ ∀ p ∈ E, ¬ p ∣ n := by
                  intro hall
                  exact (hall p hpE) hpd
                have hzero : (if ¬ p ∣ n then (1 : ℝ) else 0) = 0 :=
                  if_neg (not_not.mpr hpd)
                rw [Finset.prod_eq_zero hpE hzero]
                simp [hnotall]
            calc
              (∏ p ∈ E, -(if ¬ p ∣ n then (1 : ℝ) else 0)) *
                  ∏ p ∈ D \ E, (1 : ℝ) =
              (∏ p ∈ E, (-1 : ℝ)) *
                  ∏ p ∈ E, (if ¬ p ∣ n then (1 : ℝ) else 0) := by
                    rw [Finset.prod_const_one]
                    calc
                      (∏ p ∈ E, -(if ¬ p ∣ n then (1 : ℝ) else 0)) * 1 =
                          ∏ p ∈ E, -(if ¬ p ∣ n then (1 : ℝ) else 0) := by simp
                      _ =
                          ∏ p ∈ E, ((-1 : ℝ) * (if ¬ p ∣ n then (1 : ℝ) else 0)) := by
                            apply Finset.prod_congr rfl
                            intro p hp
                            ring
                      _ = (∏ p ∈ E, (-1 : ℝ)) *
                          ∏ p ∈ E, (if ¬ p ∣ n then (1 : ℝ) else 0) :=
                            Finset.prod_mul_distrib
              _ = (-1 : ℝ) ^ E.card * (if ∀ p ∈ E, ¬ p ∣ n then 1 else 0) := by
                    rw [havoid]
                    simp

private noncomputable def factoredAvoidEquiv (S E : Finset ℕ) (hE : E ⊆ S)
    (hS : ∀ p ∈ S, p.Prime) :
    {n : Nat.factoredNumbers S // ∀ p ∈ E, ¬ p ∣ (n : ℕ)} ≃
      Nat.factoredNumbers (S \ E) where
  toFun n := ⟨n.1, Nat.mem_factoredNumbers'.2 fun p hp hpd => by
    have hpS := (Nat.mem_factoredNumbers'.1 n.1.property) p hp hpd
    by_cases hpE : p ∈ E
    · exact False.elim (n.2 p hpE hpd)
    · exact Finset.mem_sdiff.mpr ⟨hpS, hpE⟩⟩
  invFun n := ⟨
    ⟨n.1, Nat.mem_factoredNumbers'.2 fun p hp hpd =>
      (Finset.mem_sdiff.mp ((Nat.mem_factoredNumbers'.1 n.2) p hp hpd)).1⟩,
    fun p hpE hpd => by
      have hpPrime : p.Prime := hS p (hE hpE)
      have hpSdiff := (Nat.mem_factoredNumbers'.1 n.2) p hpPrime hpd
      exact (Finset.mem_sdiff.mp hpSdiff).2 hpE⟩
  left_inv n := by
    apply Subtype.ext
    rfl
  right_inv n := by
    apply Subtype.ext
    rfl

theorem tsum_halfOmega_avoid {S E : Finset ℕ} (hE : E ⊆ S)
    (hS : ∀ p ∈ S, p.Prime) :
    (∑' n : Nat.factoredNumbers S,
      if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then halfOmegaTerm n else 0) =
      ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
  let A : Set (Nat.factoredNumbers S) :=
    {n | ∀ p ∈ E, ¬ p ∣ (n : ℕ)}
  let f : Nat.factoredNumbers S → ℝ := fun n =>
    if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then halfOmegaTerm n else 0
  have hsupp : Function.support f ⊆ A := by
    intro n hn
    change f n ≠ 0 at hn
    by_cases havoid : ∀ p ∈ E, ¬ p ∣ (n : ℕ)
    · exact havoid
    · simp [f, havoid] at hn
  have hsub := tsum_subtype_eq_of_support_subset (f := f) hsupp
  let e : A ≃ Nat.factoredNumbers (S \ E) := factoredAvoidEquiv S E hE hS
  have hseries := hasSum_halfOmega_factoredNumbers (S := S \ E)
    (fun p hp => hS p (Finset.mem_sdiff.mp hp).1)
  calc
    (∑' n : Nat.factoredNumbers S,
        if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then halfOmegaTerm n else 0) =
      ∑' n : A, halfOmegaTerm n := by
        rw [← hsub]
        apply tsum_congr
        intro n
        have havoid : ∀ p ∈ E, ¬ p ∣ (n : ℕ) := n.property
        change (if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then halfOmegaTerm n else 0) =
          halfOmegaTerm n
        rw [if_pos havoid]
    _ = ∑' n : Nat.factoredNumbers (S \ E), halfOmegaTerm n := by
        exact e.tsum_eq (fun n => halfOmegaTerm n)
    _ = ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) :=
        hseries.2.tsum_eq

theorem tsum_halfOmega_selected {S D : Finset ℕ} (hD : D ⊆ S)
    (hS : ∀ p ∈ S, p.Prime) :
    (∑' n : Nat.factoredNumbers S,
      if D ⊆ (n : ℕ).primeFactors then halfOmegaTerm n else 0) =
      ∑ E ∈ D.powerset,
        (-1 : ℝ) ^ E.card *
          ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
  classical
  let g (E : Finset ℕ) (n : Nat.factoredNumbers S) : ℝ :=
    (-1 : ℝ) ^ E.card *
      (if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then halfOmegaTerm n else 0)
  have hbase := (hasSum_halfOmega_factoredNumbers (S := S) hS).1
  have htermNonneg (n : Nat.factoredNumbers S) : 0 ≤ halfOmegaTerm n := by
    have hn : (n : ℕ) ≠ 0 := n.property.1
    simp [halfOmegaTerm, hn]
    positivity
  have havoidSummable (E : Finset ℕ) :
      Summable (fun n : Nat.factoredNumbers S =>
        if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then halfOmegaTerm n else 0) := by
    apply Summable.of_nonneg_of_le
    · intro n
      by_cases h : ∀ p ∈ E, ¬ p ∣ (n : ℕ)
      · rw [if_pos h]
        exact htermNonneg n
      · rw [if_neg h]
    · intro n
      by_cases h : ∀ p ∈ E, ¬ p ∣ (n : ℕ)
      · rw [if_pos h]
      · rw [if_neg h]
        exact htermNonneg n
    · exact hbase
  have hgSummable : ∀ E ∈ D.powerset, Summable (g E) := by
    intro E hE
    simpa [g] using (havoidSummable E).mul_left ((-1 : ℝ) ^ E.card)
  have hpoint (n : Nat.factoredNumbers S) :
      (if D ⊆ (n : ℕ).primeFactors then halfOmegaTerm n else 0) =
        ∑ E ∈ D.powerset, g E n := by
    have hindicator := halfOmega_divisor_indicator_inclusion
      D (fun p hp => hS p (hD hp)) (n : ℕ) n.property.1
    calc
      (if D ⊆ (n : ℕ).primeFactors then halfOmegaTerm n else 0) =
          halfOmegaTerm n * (if D ⊆ (n : ℕ).primeFactors then 1 else 0) := by
            by_cases hsub : D ⊆ (n : ℕ).primeFactors <;> simp [hsub]
      _ = halfOmegaTerm n *
          ∑ E ∈ D.powerset,
            (-1 : ℝ) ^ E.card * (if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then 1 else 0) := by
              rw [hindicator]
      _ = ∑ E ∈ D.powerset, g E n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro E hE
        by_cases hAvoid : ∀ p ∈ E, ¬ p ∣ (n : ℕ)
        · unfold g
          simp only [if_pos hAvoid]
          ring
        · unfold g
          simp only [if_neg hAvoid]
          simp
  calc
    (∑' n : Nat.factoredNumbers S,
        if D ⊆ (n : ℕ).primeFactors then halfOmegaTerm n else 0) =
        ∑' n : Nat.factoredNumbers S, ∑ E ∈ D.powerset, g E n := by
          apply tsum_congr
          exact hpoint
    _ = ∑ E ∈ D.powerset, ∑' n : Nat.factoredNumbers S, g E n := by
          rw [Summable.tsum_finsetSum hgSummable]
    _ = ∑ E ∈ D.powerset,
          (-1 : ℝ) ^ E.card *
            ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
          apply Finset.sum_congr rfl
          intro E hE
          rw [show (∑' n : Nat.factoredNumbers S, g E n) =
              (-1 : ℝ) ^ E.card *
                ∑' n : Nat.factoredNumbers S,
                  if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then halfOmegaTerm n else 0 by
                  change (∑' n : Nat.factoredNumbers S,
                    (-1 : ℝ) ^ E.card *
                      (if ∀ p ∈ E, ¬ p ∣ (n : ℕ) then halfOmegaTerm n else 0)) = _
                  rw [tsum_mul_left]]
          rw [tsum_halfOmega_avoid (Finset.Subset.trans
            (Finset.mem_powerset.mp hE) hD) hS]

theorem halfOmega_selected_product_identity {S D : Finset ℕ} (hD : D ⊆ S) :
    (∑ E ∈ D.powerset,
      (-1 : ℝ) ^ E.card *
        ∏ p ∈ S \ E, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1))) =
      (∏ p ∈ D, (1 / 2 : ℝ) / ((p : ℝ) - 1)) *
        ∏ p ∈ S \ D, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
  classical
  let F (p : ℕ) : ℝ := 1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)
  have hprodExpand :
      (∏ p ∈ D, (F p - 1)) =
        ∑ E ∈ D.powerset, (-1 : ℝ) ^ E.card * ∏ p ∈ D \ E, F p := by
    calc
      (∏ p ∈ D, (F p - 1)) = ∏ p ∈ D, ((-1 : ℝ) + F p) := by
        apply Finset.prod_congr rfl
        intro p hp
        ring
      _ = ∑ E ∈ D.powerset,
            (∏ p ∈ E, (-1 : ℝ)) * ∏ p ∈ D \ E, F p := Finset.prod_add _ _ _
      _ = ∑ E ∈ D.powerset, (-1 : ℝ) ^ E.card * ∏ p ∈ D \ E, F p := by
            apply Finset.sum_congr rfl
            intro E hE
            simp
  have hsdiff (E : Finset ℕ) (hE : E ⊆ D) :
      S \ E = (D \ E) ∪ (S \ D) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro hp
      by_cases hpD : p ∈ D
      · exact Or.inl ⟨hpD, hp.2⟩
      · exact Or.inr ⟨hp.1, hpD⟩
    · rintro (hp | hp)
      · exact ⟨hD hp.1, hp.2⟩
      · exact ⟨hp.1, fun hpe => hp.2 (hE hpe)⟩
  have hdisj (E : Finset ℕ) : Disjoint (D \ E) (S \ D) := by
    apply Finset.disjoint_left.mpr
    intro p hpD hpS
    exact (Finset.mem_sdiff.mp hpS).2 (Finset.mem_sdiff.mp hpD).1
  calc
    (∑ E ∈ D.powerset,
        (-1 : ℝ) ^ E.card * ∏ p ∈ S \ E, F p) =
      ∑ E ∈ D.powerset,
        (-1 : ℝ) ^ E.card *
          (∏ p ∈ D \ E, F p) * ∏ p ∈ S \ D, F p := by
            apply Finset.sum_congr rfl
            intro E hE
            rw [hsdiff E (Finset.mem_powerset.mp hE)]
            rw [Finset.prod_union (hdisj E)]
            ring
    _ = (∑ E ∈ D.powerset,
          (-1 : ℝ) ^ E.card * ∏ p ∈ D \ E, F p) *
          ∏ p ∈ S \ D, F p := by rw [Finset.sum_mul]
    _ = (∏ p ∈ D, (F p - 1)) * ∏ p ∈ S \ D, F p := by rw [hprodExpand]
    _ = (∏ p ∈ D, (1 / 2 : ℝ) / ((p : ℝ) - 1)) *
          ∏ p ∈ S \ D, (1 + (1 / 2 : ℝ) / ((p : ℝ) - 1)) := by
            congr 1
            apply Finset.prod_congr rfl
            intro p hp
            simp [F]

end ArtinPrimitiveRoots.Construction
