import ArtinPrimitiveRoots.Controlled
import ArtinPrimitiveRoots.Splitting

open Filter
open scoped Topology

/-!
# Reduction to controlled predecessors and complete splitting (paper: Theorem `thm:main`)

Source: `01-introduction.tex`, lines 17–26 (statement); `01a-reduction.tex`, lines 98–220 (the
quadratic-nonresidue progression and the proof). Frozen interface: `thm_main`.
-/

namespace ArtinPrimitiveRoots

private def progressionFactors (a : ℤ) : Finset ℕ :=
  insert 3 (a.natAbs.primeFactors.erase 2)

private def defaultResidue (l : ℕ) : ℕ := if l = 3 then 2 else 4

private theorem progressionFactors_prime (a : ℤ) :
    ∀ l ∈ progressionFactors a, l.Prime := by
  intro l hl
  rcases Finset.mem_insert.mp hl with h | h
  · simpa [h] using Nat.prime_three
  · exact Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp h).2

private theorem progressionFactors_ne_two (a : ℤ) :
    ∀ l ∈ progressionFactors a, l ≠ 2 := by
  intro l hl
  rcases Finset.mem_insert.mp hl with h | h
  · simpa [h]
  · exact (Finset.mem_erase.mp h).1

private theorem prime_in_class_not_dvd {a : ℤ} (ha0 : a.natAbs ≠ 0)
    {u p : ℕ}
    (hg : Int.gcd (u : ℤ) (8 * (progressionFactors a).prod id : ℕ) = 1)
    (hclass : (p : ℤ) ≡ (u : ℤ) [ZMOD (8 * (progressionFactors a).prod id)])
    (hp : p.Prime) : ¬ (p : ℤ) ∣ a := by
  intro hpa
  have hpaNat : p ∣ a.natAbs := Int.natCast_dvd.mp hpa
  have hpM : p ∣ 8 * (progressionFactors a).prod id := by
    by_cases hp2 : p = 2
    · subst p
      exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 8) _
    · have hpfac : p ∈ a.natAbs.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpaNat, ha0⟩
      have hpF : p ∈ progressionFactors a := by
        simp [progressionFactors, hp2, hpfac]
      have hpR : p ∣ (progressionFactors a).prod id :=
        Finset.dvd_prod_of_mem _ hpF
      exact dvd_mul_of_dvd_right hpR 8
  have hpMInt : (p : ℤ) ∣ (8 * (progressionFactors a).prod id : ℕ) :=
    Int.natCast_dvd_natCast.mpr hpM
  have hpDiff : (p : ℤ) ∣ (u : ℤ) - p := hpMInt.trans hclass.dvd
  have hpU : (p : ℤ) ∣ (u : ℤ) := by
    have h := Int.dvd_add hpDiff (dvd_rfl : (p : ℤ) ∣ (p : ℤ))
    simpa using h
  have hpUNat : p ∣ u := by simpa using (Int.natCast_dvd.mp hpU)
  have hcop : Nat.Coprime u (8 * (progressionFactors a).prod id) := by
    change Nat.gcd u (8 * (progressionFactors a).prod id) = 1
    have h := hg
    rw [Int.gcd_def] at h
    simpa only [Int.natAbs_natCast] using h
  have hcommon : p ∣ Nat.gcd u (8 * (progressionFactors a).prod id) :=
    Nat.dvd_gcd hpUNat hpM
  rw [hcop] at hcommon
  exact hp.ne_one (Nat.dvd_one.mp hcommon)

private theorem legendre_square_factor {a e : ℤ} {t d p : ℕ} [Fact p.Prime]
    (hpart : a = e * ((t : ℤ) ^ 2 * d))
    (hnot : ¬ (p : ℤ) ∣ a)
    (hsigned : legendreSym p (e * (d : ℤ)) = -1) :
    legendreSym p a = -1 := by
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro hz
    exact hnot ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)
  have ht0 : ((t : ℤ) : ZMod p) ≠ 0 := by
    intro ht
    have hazero : (a : ZMod p) = 0 := by
      rw [hpart]
      simp only [Int.cast_mul, Int.cast_pow]
      rw [ht]
      simp
    exact ha0 hazero
  have htsq : legendreSym p ((t : ℤ) ^ 2) = 1 := legendreSym.sq_one' p ht0
  calc
    legendreSym p a = legendreSym p (e * ((t : ℤ) ^ 2 * d)) := by rw [hpart]
    _ = legendreSym p e * legendreSym p ((t : ℤ) ^ 2 * d) := legendreSym.mul p e _
    _ = legendreSym p e * (legendreSym p ((t : ℤ) ^ 2) * legendreSym p d) := by
      rw [legendreSym.mul p ((t : ℤ) ^ 2) d]
    _ = legendreSym p e * legendreSym p d := by rw [htsq]; simp
    _ = legendreSym p (e * (d : ℤ)) := (legendreSym.mul p e d).symm
    _ = -1 := hsigned

private theorem defaultResidue_pos (a : ℤ) :
    ∀ l ∈ progressionFactors a, 0 < defaultResidue l := by
  intro l hl
  by_cases h : l = 3 <;> simp [defaultResidue, h]

private theorem defaultResidue_ne_one (a : ℤ) :
    ∀ l ∈ progressionFactors a, defaultResidue l ≠ 1 := by
  intro l hl
  by_cases h : l = 3 <;> simp [defaultResidue, h]

private theorem defaultResidue_lt (a : ℤ) :
    ∀ l ∈ progressionFactors a, defaultResidue l < l := by
  intro l hl
  have hp := progressionFactors_prime a l hl
  by_cases h3 : l = 3
  · simp [defaultResidue, h3]
  · have h2 : l ≠ 2 := progressionFactors_ne_two a l hl
    have h4 : l ≠ 4 := by
      intro h4
      subst l
      norm_num at hp
    have hge2 : 2 ≤ l := hp.two_le
    have h5 : 5 ≤ l := by omega
    have h4lt : 4 < l := by omega
    simpa [defaultResidue, h3] using h4lt

private theorem abs_gt_one_of_admissible (a : ℤ) (ha : a ≠ -1) (ha' : ¬ IsSquare a) :
    1 < |a| := by
  by_contra h
  have habs : |a| ≤ 1 := le_of_not_gt h
  have hv : a = -1 ∨ a = 0 ∨ a = 1 := by
    have h' := abs_le.mp habs
    omega
  rcases hv with hneg | hzero | hone
  · exact ha hneg
  · subst a
    exact ha' ⟨0, by norm_num⟩
  · subst a
    exact ha' ⟨1, by norm_num⟩

private theorem squarefree_part (a : ℤ) :
    ∃ t d : ℕ, a.natAbs = t ^ 2 * d ∧ Squarefree d := by
  obtain ⟨t, d, h, hd⟩ := exists_sq_mul_squarefree a.natAbs
  exact ⟨t, d, h.symm, hd⟩

private theorem int_eq_sign_mul_natAbs (a : ℤ) :
    a = Int.sign a * (a.natAbs : ℤ) := by
  rw [Int.natCast_natAbs]
  exact (Int.sign_mul_abs a).symm

private theorem natAbs_ne_zero_of_admissible (a : ℤ) (ha : a ≠ -1) (ha' : ¬ IsSquare a) :
    a.natAbs ≠ 0 := by
  have habs := abs_gt_one_of_admissible a ha ha'
  intro hz
  have hz' : |a| = 0 := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hz
  rw [hz'] at habs
  norm_num at habs

private theorem signed_squarefree_part (a : ℤ) :
    ∃ t d : ℕ, a = Int.sign a * ((t : ℤ) ^ 2 * d) ∧
      a.natAbs = t ^ 2 * d ∧ Squarefree d := by
  obtain ⟨t, d, hnat, hd⟩ := squarefree_part a
  have hcast : (a.natAbs : ℤ) = (t : ℤ) ^ 2 * d := by exact_mod_cast hnat
  refine ⟨t, d, ?_, hnat, hd⟩
  calc
    a = Int.sign a * (a.natAbs : ℤ) := int_eq_sign_mul_natAbs a
    _ = Int.sign a * ((t : ℤ) ^ 2 * d) := by rw [hcast]

private theorem sign_eq_one_or_neg_one_of_not_square {a : ℤ} (ha' : ¬ IsSquare a) :
    Int.sign a = 1 ∨ Int.sign a = -1 := by
  cases a with
  | ofNat n =>
      cases n with
      | zero => exact (ha' ⟨0, by norm_num⟩).elim
      | succ n => exact Or.inl (by simp [Int.sign])
  | negSucc n => exact Or.inr (by simp [Int.sign])

private theorem square_of_positive_sign_part_one {a : ℤ} {t d : ℕ}
    (hsign : Int.sign a = 1)
    (hpart : a = Int.sign a * ((t : ℤ) ^ 2 * d)) (hd : d = 1) : IsSquare a := by
  rw [isSquare_iff_exists_sq]
  refine ⟨(t : ℤ), ?_⟩
  rw [hpart, hsign, hd]
  ring

private theorem exists_low_choice {e : ℤ} {d : ℕ}
    (he : e = 1 ∨ e = -1) (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6)
    (hnot : ¬ (e = 1 ∧ d = 1)) :
    ∃ r c : ℕ,
      ((c = 2 ∧ (r = 3 ∨ r = 7)) ∨ (c = 4 ∧ r = 5)) ∧
      ((e = -1 ∧ d = 1 ∧ r = 3) ∨
        (e = 1 ∧ d = 2 ∧ r = 3) ∨
        (e = -1 ∧ d = 2 ∧ r = 7) ∨
        (e = 1 ∧ d = 3 ∧ r = 5) ∨
        (e = -1 ∧ d = 3 ∧ r = 5) ∨
        (e = 1 ∧ d = 6 ∧ r = 3) ∨
        (e = -1 ∧ d = 6 ∧ r = 7)) := by
  rcases hd with hd1 | hd2 | hd3 | hd6
  · subst d
    rcases he with he | he
    · subst e
      exact (hnot ⟨rfl, rfl⟩).elim
    · subst e
      exact ⟨3, 2, by simp, by simp⟩
  · subst d
    rcases he with he | he
    · subst e
      exact ⟨3, 2, by simp, by simp⟩
    · subst e
      exact ⟨7, 2, by simp, by simp⟩

  · subst d
    rcases he with he | he
    · subst e
      exact ⟨5, 4, by simp, by simp⟩
    · subst e
      exact ⟨5, 4, by simp, by simp⟩
  · subst d
    rcases he with he | he
    · subst e
      exact ⟨3, 2, by simp, by simp⟩
    · subst e
      exact ⟨7, 2, by simp, by simp⟩

private theorem nat_predecessor_eq {u r c q : ℕ}
    (hcr : (c = 2 ∧ (r = 3 ∨ r = 7)) ∨ (c = 4 ∧ r = 5))
    (hu8 : u ≡ r [MOD 8]) (hq : q = (u - 1) / c) : u = c * q + 1 := by
  have hur : u % 8 = r := by
    have hrlt : r < 8 := by rcases hcr with ⟨_, hr | hr⟩ | ⟨_, hr⟩ <;> simp [hr]
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hrlt] using hu8
  rcases hcr with ⟨hc, hr⟩ | ⟨hc, hr⟩
  · rcases hr with hr3 | hr7
    · rw [hc] at hq ⊢
      rw [hr3] at hur
      have hdiv : 2 ∣ u - 1 := by omega
      have hmul := Nat.mul_div_cancel' hdiv
      omega
    · rw [hc] at hq ⊢
      rw [hr7] at hur
      have hdiv : 2 ∣ u - 1 := by omega
      have hmul := Nat.mul_div_cancel' hdiv
      omega
  · rw [hc] at hq ⊢
    rw [hr] at hur
    have hdiv : 4 ∣ u - 1 := by omega
    have hmul := Nat.mul_div_cancel' hdiv
    omega

private theorem squarefree_part_cases {d : ℕ} (hd : Squarefree d) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 ∨ ∃ j : ℕ, j.Prime ∧ 5 ≤ j ∧ j ∣ d := by
  by_cases hlarge : ∃ j : ℕ, j.Prime ∧ 5 ≤ j ∧ j ∣ d
  · exact Or.inr (Or.inr (Or.inr (Or.inr hlarge)))
  · have hsub : d.primeFactors ⊆ {2, 3} := by
      intro q hq
      have hq' := (Nat.mem_primeFactors.mp hq)
      rcases hq' with ⟨hqPrime, hqd⟩
      have hqeq : q = 2 ∨ q = 3 := by
        by_contra hne
        have hqge2 : 2 ≤ q := hqPrime.two_le
        have hqne4 : q ≠ 4 := by
          intro hq4
          subst q
          norm_num at hqPrime
        have hqge5 : 5 ≤ q := by omega
        exact hlarge ⟨q, hqPrime, hqge5, hqd.1⟩
      simpa [hqeq]
    have hprod : (∏ q ∈ d.primeFactors, q) ∣ 6 := by
      calc
        (∏ q ∈ d.primeFactors, q) ∣ ∏ q ∈ ({2, 3} : Finset ℕ), q :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
        _ = 6 := by norm_num
    have hdvd : d ∣ 6 := by
      rw [← Nat.prod_primeFactors_of_squarefree hd]
      exact hprod
    have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases d <;> simp_all

private theorem exists_nonsquare_residue {j : ℕ} [Fact j.Prime] (hj5 : 5 ≤ j) :
    ∃ v : ℕ, legendreSym j (v : ℤ) = -1 ∧ 0 < v ∧ v < j ∧ v ≠ 1 := by
  have hj : j.Prime := Fact.out
  letI : NeZero j := ⟨hj.ne_zero⟩
  have hj2 : j ≠ 2 := by omega
  have hchar : ringChar (ZMod j) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hj2
  obtain ⟨z, hz⟩ : ∃ z : ZMod j, quadraticChar (ZMod j) z = -1 :=
    quadraticChar_exists_neg_one hchar
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    norm_num at hz
  refine ⟨z.val, ?_, ?_, z.val_lt, ?_⟩
  · simp only [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hz
  · exact Nat.pos_of_ne_zero (z.val_ne_zero.mpr hz0)
  · exact (ZMod.val_eq_one hj.one_lt z).not.mpr hz1

private theorem legendreSym_four_eq_one {j : ℕ} [Fact j.Prime] (hj5 : 5 ≤ j) :
    legendreSym j (4 : ℤ) = 1 := by
  have hj : j.Prime := Fact.out
  have hnonzeroNat : (4 : ZMod j) ≠ 0 := by
    intro h
    have hdvd : j ∣ 4 := (ZMod.natCast_eq_zero_iff 4 j).mp h
    have hle : j ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hnonzero : ((4 : ℤ) : ZMod j) ≠ 0 := by exact_mod_cast hnonzeroNat
  rw [legendreSym.eq_one_iff j hnonzero]
  exact ⟨2, by norm_num⟩

private theorem legendreSym_three_two : legendreSym 3 (2 : ℤ) = -1 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [legendreSym.eq_neg_one_iff 3]
  decide

private theorem exists_residue_for_symbol {j : ℕ} [Fact j.Prime] (hj5 : 5 ≤ j)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∃ v : ℕ, 0 < v ∧ v < j ∧ v ≠ 1 ∧ legendreSym j (v : ℤ) = s := by
  rcases hs with h1 | hneg
  · subst s
    refine ⟨4, by norm_num, by omega, by norm_num, ?_⟩
    exact legendreSym_four_eq_one hj5
  · subst s
    obtain ⟨v, hv, hpos, hlt, hne⟩ := exists_nonsquare_residue hj5
    exact ⟨v, hpos, hlt, hne, hv⟩

private theorem crt_mod8 {F : Finset ℕ} (hprime : ∀ l ∈ F, l.Prime)
    (hnot2 : ∀ l ∈ F, l ≠ 2) (r : ℕ) (hr : r < 8)
    (b : ℕ → ℕ) (hb : ∀ l ∈ F, b l < l) :
    ∃ u : ℕ, u < 8 * F.prod id ∧ u ≡ r [MOD 8] ∧
      ∀ l ∈ F, u ≡ b l [MOD l] := by
  classical
  let R : ℕ := F.prod id
  have hRpos : 0 < R := by
    dsimp [R]
    apply Finset.prod_pos
    intro l hl
    exact (hprime l hl).pos
  have hRodd : Odd R := by
    have haux : ∀ G : Finset ℕ, (∀ l ∈ G, l.Prime) → (∀ l ∈ G, l ≠ 2) →
        Odd (G.prod id) := by
      intro G
      induction G using Finset.induction_on with
      | empty => intro _ _; simp
      | @insert l s hls ih =>
          intro hpr hne
          rw [Finset.prod_insert hls]
          apply ((hpr l (by simp)).odd_of_ne_two (hne l (by simp))).mul
          exact ih (by intro q hq; exact hpr q (by simp [hq]))
            (by intro q hq; exact hne q (by simp [hq]))
    exact haux F hprime hnot2
  have h2R : Nat.Coprime 2 R := Nat.coprime_two_left.mpr hRodd
  have h8R : Nat.Coprime 8 R := by
    have hpow : Nat.Coprime (2 ^ 3) R :=
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 3) 2 R).mpr h2R
    simpa using hpow
  have hpair : Set.Pairwise (F : Set ℕ) (fun l m : ℕ => Nat.Coprime l m) := by
    intro l hl m hm hlm
    exact (Nat.coprime_primes (hprime l hl) (hprime m hm)).2 hlm
  have hmoduli : ∀ l ∈ F, l ≠ 0 := by
    intro l hl
    exact (hprime l hl).ne_zero
  let vSub := Nat.chineseRemainderOfFinset b id F hmoduli hpair
  let w := Nat.chineseRemainder h8R r (vSub : ℕ)
  have hwlt : (w : ℕ) < 8 * R :=
    Nat.chineseRemainder_lt_mul h8R r (vSub : ℕ) (by omega) (by omega)
  have hw8 : (w : ℕ) ≡ r [MOD 8] := w.property.1
  have hwR : (w : ℕ) ≡ (vSub : ℕ) [MOD R] := w.property.2
  refine ⟨w, ?_, hw8, ?_⟩
  · simpa [R] using hwlt
  · intro l hl
    have hlR : l ∣ R := by
      dsimp [R]
      exact Finset.dvd_prod_of_mem _ hl
    have hwmod : (w : ℕ) % R = (vSub : ℕ) % R := by
      simpa [Nat.ModEq] using hwR
    have hvmod : (vSub : ℕ) % l = b l % l := by
      simpa [Nat.ModEq] using vSub.property l hl
    have h := calc
      (w : ℕ) % l = ((w : ℕ) % R) % l := by
        rw [Nat.mod_mod_of_dvd _ hlR]
      _ = ((vSub : ℕ) % R) % l := by rw [hwmod]
      _ = (vSub : ℕ) % l := by rw [Nat.mod_mod_of_dvd _ hlR]
      _ = b l % l := hvmod
    change (w : ℕ) % l = b l % l
    exact h

private theorem crt_coprime {F : Finset ℕ} (hprime : ∀ l ∈ F, l.Prime)
    (b : ℕ → ℕ) (hb0 : ∀ l ∈ F, 0 < b l) (hblt : ∀ l ∈ F, b l < l)
    {u r : ℕ} (hr : r = 3 ∨ r = 5 ∨ r = 7)
    (hu8 : u ≡ r [MOD 8]) (hul : ∀ l ∈ F, u ≡ b l [MOD l]) :
    Nat.Coprime u (8 * F.prod id) := by
  have hrlt : r < 8 := by rcases hr with hr | hr | hr <;> norm_num [hr]
  have hur : u % 8 = r := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hrlt] using hu8
  have huOdd : Odd u := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hdiv : 2 ∣ u := even_iff_two_dvd.mp he
    have hmod2 : u % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).mp hdiv
    have hmod2' : (u % 8) % 2 = u % 2 := Nat.mod_mod_of_dvd u (by norm_num : 2 ∣ 8)
    rw [← hmod2', hur] at hmod2
    rcases hr with hr | hr | hr <;> simp [hr] at hmod2
  have hcop2 : Nat.Coprime 2 u := Nat.coprime_two_left.mpr huOdd
  have hcop8 : Nat.Coprime 8 u := by
    have h := (Nat.coprime_pow_left_iff (by norm_num : 0 < 3) 2 u).mpr hcop2
    simpa using h
  have hcopR : Nat.Coprime u (F.prod id) := by
    apply Nat.Coprime.prod_right
    intro l hl
    have hrem : u % l = b l := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (hblt l hl)] using hul l hl
    have hnotdiv : ¬ l ∣ u := by
      intro hd
      have hzero : u % l = 0 := (Nat.dvd_iff_mod_eq_zero).mp hd
      rw [hrem] at hzero
      exact (Nat.ne_of_gt (hb0 l hl)) hzero
    exact ((hprime l hl).coprime_iff_not_dvd.mpr hnotdiv).symm
  have hcopM : Nat.Coprime (8 * F.prod id) u := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcop8, hcopR.symm⟩
  exact hcopM.symm

private theorem crt_quotient_coprime {F : Finset ℕ} (hprime : ∀ l ∈ F, l.Prime)
    (hnot2 : ∀ l ∈ F, l ≠ 2) (b : ℕ → ℕ)
    (hb0 : ∀ l ∈ F, 0 < b l) (hbne1 : ∀ l ∈ F, b l ≠ 1)
    (hblt : ∀ l ∈ F, b l < l)
    {u r c q : ℕ}
    (hcr : (c = 2 ∧ (r = 3 ∨ r = 7)) ∨ (c = 4 ∧ r = 5))
    (hu8 : u ≡ r [MOD 8]) (hul : ∀ l ∈ F, u ≡ b l [MOD l])
    (huEq : u = c * q + 1) : Nat.Coprime q ((8 / c) * F.prod id) := by
  have hrlt : r < 8 := by rcases hcr with ⟨_, hr | hr⟩ | ⟨_, hr⟩ <;> simp [hr]
  have hur : u % 8 = r := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hrlt] using hu8
  have hqOdd : Odd q := by
    by_contra h
    have he : Even q := Nat.not_odd_iff_even.mp h
    obtain ⟨k, hk⟩ := he
    rcases hcr with ⟨hc, hr⟩ | ⟨hc, hr⟩
    · rcases hr with hr3 | hr7
      · rw [hc, hk] at huEq
        rw [hr3, huEq] at hur
        omega
      · rw [hc, hk] at huEq
        rw [hr7, huEq] at hur
        omega
    · rw [hc, hk] at huEq
      rw [hr, huEq] at hur
      omega
  have hcop2 : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hqOdd
  have hcopFactor : Nat.Coprime q (8 / c) := by
    rcases hcr with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
    · have hcop4 : Nat.Coprime 4 q := by
        have h := (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2 q).mpr hcop2
        simpa using h
      simpa using hcop4.symm
    · simpa using hcop2.symm
  have hcopR : Nat.Coprime q (F.prod id) := by
    apply Nat.Coprime.prod_right
    intro l hl
    have hrem : u % l = b l := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (hblt l hl)] using hul l hl
    have hnotdiv : ¬ l ∣ q := by
      intro hlq
      have hremOne : u % l = 1 := by
        rw [huEq, Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hlq c),
          Nat.zero_add]
        simp [Nat.mod_eq_of_lt (hprime l hl).one_lt]
      rw [hremOne] at hrem
      exact hbne1 l hl hrem.symm
    exact ((hprime l hl).coprime_iff_not_dvd.mpr hnotdiv).symm
  have hcopM : Nat.Coprime ((8 / c) * F.prod id) q := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcopFactor.symm, hcopR.symm⟩
  exact hcopM.symm

private theorem crt_progression_data {F : Finset ℕ} (hprime : ∀ l ∈ F, l.Prime)
    (hnot2 : ∀ l ∈ F, l ≠ 2) (b : ℕ → ℕ)
    (hb0 : ∀ l ∈ F, 0 < b l) (hbne1 : ∀ l ∈ F, b l ≠ 1)
    (hblt : ∀ l ∈ F, b l < l)
    {u r c q : ℕ}
    (hcr : (c = 2 ∧ (r = 3 ∨ r = 7)) ∨ (c = 4 ∧ r = 5))
    (hu8 : u ≡ r [MOD 8]) (hul : ∀ l ∈ F, u ≡ b l [MOD l])
    (huEq : u = c * q + 1) :
    Int.gcd (u : ℤ) (8 * F.prod id : ℕ) = 1 ∧
      (c : ℤ) ∣ (u : ℤ) - 1 ∧
      Int.gcd (((u : ℤ) - 1) / c) ((8 * F.prod id / c : ℕ) : ℤ) = 1 := by
  have hcop := crt_coprime hprime b hb0 hblt (by
    rcases hcr with ⟨hc, hr⟩ | ⟨hc, hr⟩
    · rcases hr with hr | hr
      · exact Or.inl hr
      · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl hr)) hu8 hul
  have hgcd : Int.gcd (u : ℤ) (8 * F.prod id : ℕ) = 1 := by
    rw [Int.gcd_def]
    simpa only [Int.natAbs_natCast] using hcop
  have hdiv : (c : ℤ) ∣ (u : ℤ) - 1 := by
    refine ⟨q, ?_⟩
    rw [huEq]
    push_cast
    ring
  have hcastEq : (u : ℤ) - 1 = (c : ℤ) * q := by
    rw [huEq]
    push_cast
    ring
  have hcne : (c : ℤ) ≠ 0 := by
    rcases hcr with ⟨hc, _⟩ | ⟨hc, _⟩ <;> simp [hc]
  have hquot : ((u : ℤ) - 1) / c = q := by
    rw [hcastEq, Int.mul_ediv_cancel_left _ hcne]
  have hMdiv : (8 * F.prod id) / c = (8 / c) * F.prod id := by
    rcases hcr with ⟨hc, _⟩ | ⟨hc, _⟩
    · subst c
      calc
        (8 * F.prod id) / 2 = (2 * (4 * F.prod id)) / 2 := by congr 1 <;> ring
        _ = 4 * F.prod id := Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
    · subst c
      calc
        (8 * F.prod id) / 4 = (4 * (2 * F.prod id)) / 4 := by congr 1 <;> ring
        _ = 2 * F.prod id := Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)
  have hcopq := crt_quotient_coprime hprime hnot2 b hb0 hbne1 hblt hcr hu8 hul huEq
  have hgcdq : Nat.gcd q ((8 * F.prod id) / c) = 1 := by
    rw [hMdiv]
    exact hcopq
  refine ⟨hgcd, hdiv, ?_⟩
  rw [Int.gcd_def]
  change Nat.gcd ((((u : ℤ) - 1) / c).natAbs) ((8 * F.prod id) / c) = 1
  rw [hquot, Int.natAbs_natCast]
  exact hgcdq

private theorem legendre_two_mod8_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hmod : p % 8 = 3) : legendreSym p (2 : ℤ) = -1 := by
  rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]
  have hpOdd : p % 2 ≠ 0 := by omega
  simp [hmod, hpOdd]

private theorem legendre_two_mod8_five {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hmod : p % 8 = 5) : legendreSym p (2 : ℤ) = -1 := by
  rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]
  have hpOdd : p % 2 ≠ 0 := by omega
  simp [hmod, hpOdd]

private theorem legendre_two_mod8_seven {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hmod : p % 8 = 7) : legendreSym p (2 : ℤ) = 1 := by
  rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]
  have hpOdd : p % 2 ≠ 0 := by omega
  simp [hmod, hpOdd]

private theorem legendre_negOne_mod4_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hmod : p % 4 = 1) : legendreSym p (-1 : ℤ) = 1 := by
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four]
  have hpOdd : p % 2 = 1 := by omega
  simp [hpOdd, hmod]

private theorem legendre_negOne_mod4_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hmod : p % 4 = 3) : legendreSym p (-1 : ℤ) = -1 := by
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four]
  have hpOdd : p % 2 = 1 := by omega
  simp [hpOdd, hmod]

private theorem legendre_three_mod3_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hmod3 : p % 3 = 2) (hmod4 : p % 4 = 1 ∨ p % 4 = 3) :
    legendreSym p (3 : ℤ) = if p % 4 = 1 then -1 else 1 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod3z : (p : ℤ) % (3 : ℤ) = 2 := by exact_mod_cast hmod3
  have h3sym : legendreSym 3 (p : ℤ) = -1 := by
    rw [legendreSym.mod 3 (p : ℤ)]
    change legendreSym 3 ((p : ℤ) % (3 : ℤ)) = -1
    rw [hmod3z]
    norm_num [legendreSym]
  have hqr := legendreSym.quadratic_reciprocity' (p := 3) (q := p) (by norm_num) hp2
  have hpOdd : p % 2 = 1 := by
    have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    exact Nat.odd_iff.mp ho
  have hchi : ZMod.χ₄ p = (-1 : ℤ) ^ (p / 2) := ZMod.χ₄_eq_neg_one_pow hpOdd
  have hstep : legendreSym p (3 : ℤ) = ZMod.χ₄ p * -1 := by
    calc
      legendreSym p (3 : ℤ) = (-1 : ℤ) ^ (3 / 2 * (p / 2)) * legendreSym 3 (p : ℤ) := hqr
      _ = (-1 : ℤ) ^ (p / 2) * -1 := by rw [h3sym]; norm_num
      _ = ZMod.χ₄ p * -1 := by rw [← hchi]
  rcases hmod4 with h1 | h3
  · rw [hstep, ZMod.χ₄_nat_eq_if_mod_four]
    simp [hpOdd, h1]
  · rw [hstep, ZMod.χ₄_nat_eq_if_mod_four]
    simp [hpOdd, h3]

private theorem mod4_of_mod8 {p r : ℕ} (h : p % 8 = r) : p % 4 = r % 4 := by
  have hm := Nat.mod_mod_of_dvd p (by norm_num : 4 ∣ 8)
  rw [h] at hm
  exact hm.symm

private theorem legendre_mul_natCast {p : ℕ} [Fact p.Prime] (e : ℤ) (d : ℕ) :
    legendreSym p (e * (d : ℤ)) = legendreSym p e * legendreSym p (d : ℤ) :=
  legendreSym.mul p e (d : ℤ)

private theorem legendre_natCast_mul {p : ℕ} [Fact p.Prime] (m n : ℕ) :
    legendreSym p ((m * n : ℕ) : ℤ) = legendreSym p (m : ℤ) * legendreSym p (n : ℤ) := by
  rw [Nat.cast_mul]
  exact legendreSym.mul p (m : ℤ) (n : ℤ)

private theorem legendre_squarefree_prod {p d : ℕ} [Fact p.Prime] (hd : Squarefree d) :
    legendreSym p (d : ℤ) = ∏ l ∈ d.primeFactors, legendreSym p (l : ℤ) := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  rw [Nat.cast_prod]
  change (legendreSym.hom p) (∏ l ∈ d.primeFactors, (l : ℤ)) = _
  rw [map_prod]
  simp [legendreSym.hom]

private def legendreAtNatPrime (l : ℕ) (hl : l.Prime) (a : ℤ) : ℤ :=
  @legendreSym l ⟨hl⟩ a

private noncomputable def quadraticResidueFactor (d l : ℕ) : ℤ :=
  if hmem : l ∈ d.primeFactors then
    if l = 2 then -1 else
      (if l % 4 = 3 then -1 else 1) *
        legendreAtNatPrime l (Nat.prime_of_mem_primeFactors (n := d) hmem)
          (if l = 3 then 2 else 4)
  else 1

private theorem finset_prod_sign {α : Type*} (s : Finset α) (f : α → ℤ)
    (hf : ∀ a ∈ s, f a = 1 ∨ f a = -1) : s.prod f = 1 ∨ s.prod f = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hfa := hf a (by simp)
      have hfs := ih (by intro x hx; exact hf x (by simp [hx]))
      rcases hfa with hfa | hfa <;> rcases hfs with hfs | hfs <;> simp [hfa, hfs]

private theorem choose_high_residue {d j : ℕ} [Fact j.Prime] (hd : Squarefree d)
    (hj5 : 5 ≤ j) (hjd : j ∣ d) {e : ℤ} (he : e = 1 ∨ e = -1) :
    ∃ v : ℕ, 0 < v ∧ v < j ∧ v ≠ 1 ∧
      (e * ((d.primeFactors.erase j).prod (quadraticResidueFactor d)) *
          (if j % 4 = 3 then -1 else 1) = 1 ∨
        e * ((d.primeFactors.erase j).prod (quadraticResidueFactor d)) *
          (if j % 4 = 3 then -1 else 1) = -1) ∧
      legendreSym j (v : ℤ) =
        -(e * ((d.primeFactors.erase j).prod (quadraticResidueFactor d)) *
          (if j % 4 = 3 then -1 else 1)) := by
  have hj : j.Prime := Fact.out
  have hjD : j ∈ d.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hj, hjd, hd.ne_zero⟩
  have hterm : ∀ l ∈ d.primeFactors.erase j,
      quadraticResidueFactor d l = 1 ∨ quadraticResidueFactor d l = -1 := by
    intro l hl
    have hlD : l ∈ d.primeFactors := (Finset.mem_erase.mp hl).2
    have hlp : l.Prime := Nat.prime_of_mem_primeFactors (n := d) hlD
    by_cases hl2 : l = 2
    · subst l
      simp [quadraticResidueFactor, hlD]
    · by_cases hl3 : l = 3
      · subst l
        letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hfac : quadraticResidueFactor d 3 = 1 := by
          simp [quadraticResidueFactor, hlD, legendreAtNatPrime,
            legendreSym_three_two]
        exact Or.inl hfac
      · have hlge2 : 2 ≤ l := hlp.two_le
        have hlne4 : l ≠ 4 := by
          intro h
          subst l
          norm_num at hlp
        have hl5 : 5 ≤ l := by omega
        letI : Fact l.Prime := ⟨hlp⟩
        have hfour := legendreSym_four_eq_one hl5
        by_cases hl4 : l % 4 = 3
        · simp [quadraticResidueFactor, hlD, hl2, hl3, hl4,
            legendreAtNatPrime, hfour]
        · simp [quadraticResidueFactor, hlD, hl2, hl3, hl4,
            legendreAtNatPrime, hfour]
  have hprod : (d.primeFactors.erase j).prod (quadraticResidueFactor d) = 1 ∨
      (d.primeFactors.erase j).prod (quadraticResidueFactor d) = -1 :=
    finset_prod_sign _ _ hterm
  have hqrj : (if j % 4 = 3 then (-1 : ℤ) else 1) = 1 ∨
      (if j % 4 = 3 then (-1 : ℤ) else 1) = -1 := by
    by_cases h : j % 4 = 3 <;> simp [h]
  let A : ℤ := e * ((d.primeFactors.erase j).prod (quadraticResidueFactor d)) *
    (if j % 4 = 3 then -1 else 1)
  have hA : A = 1 ∨ A = -1 := by
    unfold A
    rcases he with he | he
    · rw [he]
      rcases hprod with hp | hp <;> rcases hqrj with hq | hq
      all_goals rw [hp, hq] <;> norm_num
    · rw [he]
      rcases hprod with hp | hp <;> rcases hqrj with hq | hq
      all_goals rw [hp, hq] <;> norm_num
  have htarget : -A = 1 ∨ -A = -1 := by
    rcases hA with h | h <;> rw [h] <;> norm_num
  obtain ⟨v, hvpos, hvlt, hvne, hvchar⟩ :=
    exists_residue_for_symbol (j := j) hj5 (-A) htarget
  refine ⟨v, hvpos, hvlt, hvne, hA, ?_⟩
  simpa [A] using hvchar

private theorem legendre_modEq {q : ℕ} [Fact q.Prime] {a b : ℤ}
    (h : a ≡ b [ZMOD q]) : legendreSym q a = legendreSym q b := by
  have hmod : a % q = b % q := by simpa [Int.ModEq] using h
  rw [legendreSym.mod q a, legendreSym.mod q b, hmod]

private theorem int_modEq_of_modulus_dvd {a b M m : ℤ}
    (h : a ≡ b [ZMOD M]) (hm : m ∣ M) : a ≡ b [ZMOD m] :=
  Int.modEq_iff_dvd.mpr (hm.trans h.dvd)

private theorem legendre_qr_mod4_three {p l : ℕ} [Fact p.Prime] [Fact l.Prime]
    (hp2 : p ≠ 2) (hl2 : l ≠ 2) (hp4 : p % 4 = 3)
    {b : ℤ} (hmod : (p : ℤ) ≡ b [ZMOD l]) :
    legendreSym p (l : ℤ) =
      (if l % 4 = 3 then -1 else 1) * legendreSym l b := by
  have hl4 : l % 4 = 1 ∨ l % 4 = 3 := by
    have hlo : l % 2 = 1 := by
      have ho := (Fact.out : l.Prime).odd_of_ne_two hl2
      exact Nat.odd_iff.mp ho
    omega
  have hchar : legendreSym l (p : ℤ) = legendreSym l b := legendre_modEq hmod
  rcases hl4 with h1 | h3
  · have hqr := legendreSym.quadratic_reciprocity_one_mod_four (p := l) (q := p) h1 hp2
    rw [hchar] at hqr
    simpa [h1] using hqr
  · have hqr := legendreSym.quadratic_reciprocity_three_mod_four
      (p := l) (q := p) h3 hp4
    rw [hchar] at hqr
    simpa [h3] using hqr

private theorem high_part_legendre {p d j : ℕ} [Fact p.Prime] [Fact j.Prime]
    (hp2 : p ≠ 2) (hp8 : p % 8 = 3) (hd : Squarefree d) (hj5 : 5 ≤ j)
    (hjd : j ∣ d) {e : ℤ} (he : e = 1 ∨ e = -1) (b : ℕ → ℕ) (v : ℕ)
    (hbOther : ∀ l ∈ d.primeFactors.erase j, b l = if l = 3 then 2 else 4)
    (hmodOther : ∀ l ∈ d.primeFactors.erase j, l ≠ 2 →
      (p : ℤ) ≡ (b l : ℤ) [ZMOD l])
    (hmodj : (p : ℤ) ≡ (v : ℤ) [ZMOD j])
    (hA : e * ((d.primeFactors.erase j).prod (quadraticResidueFactor d)) *
      (if j % 4 = 3 then -1 else 1) = 1 ∨
      e * ((d.primeFactors.erase j).prod (quadraticResidueFactor d)) *
        (if j % 4 = 3 then -1 else 1) = -1)
    (hv : legendreSym j (v : ℤ) =
      -(e * ((d.primeFactors.erase j).prod (quadraticResidueFactor d)) *
        (if j % 4 = 3 then -1 else 1))) :
    legendreSym p (e * (d : ℤ)) = -1 := by
  have hj : j.Prime := Fact.out
  have hjD : j ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hj, hjd, hd.ne_zero⟩
  have hp4 : p % 4 = 3 := by simpa [mod4_of_mod8 hp8]
  have hechar : legendreSym p e = e := by
    rcases he with he | he
    · rw [he]
      simp
    · rw [he, legendre_negOne_mod4_three hp2 hp4]
  have hprodChar :
      (d.primeFactors.erase j).prod (fun l => legendreSym p (l : ℤ)) =
        (d.primeFactors.erase j).prod (quadraticResidueFactor d) := by
    apply Finset.prod_congr rfl
    intro l hl
    have hlD : l ∈ d.primeFactors := (Finset.mem_erase.mp hl).2
    have hlPrime : l.Prime := Nat.prime_of_mem_primeFactors (n := d) hlD
    by_cases hl2 : l = 2
    · subst l
      have htwo := legendre_two_mod8_three hp2 hp8
      have hfactor : quadraticResidueFactor d 2 = -1 := by
        simp [quadraticResidueFactor, hlD]
      change legendreSym p (2 : ℤ) = quadraticResidueFactor d 2
      rw [htwo, hfactor]
    · letI : Fact l.Prime := ⟨hlPrime⟩
      have hqr := legendre_qr_mod4_three hp2 hl2 hp4 (hmodOther l hl hl2)
      rw [hbOther l hl] at hqr
      have hfactor : quadraticResidueFactor d l =
          (if l % 4 = 3 then -1 else 1) *
            legendreSym l ((if l = 3 then 2 else 4 : ℕ) : ℤ) := by
        simp [quadraticResidueFactor, hlD, hl2, legendreAtNatPrime]
      rw [hfactor]
      exact hqr
  have hDprod := legendre_squarefree_prod (p := p) hd
  have hjNot : j ∉ d.primeFactors.erase j := by simp
  have hsplit :
      (∏ l ∈ d.primeFactors, legendreSym p (l : ℤ)) =
        legendreSym p (j : ℤ) *
          (d.primeFactors.erase j).prod (fun l => legendreSym p (l : ℤ)) := by
    calc
      (∏ l ∈ d.primeFactors, legendreSym p (l : ℤ)) =
          (∏ l ∈ insert j (d.primeFactors.erase j), legendreSym p (l : ℤ)) := by
        congr 1
        exact (Finset.insert_erase hjD).symm
      _ = legendreSym p (j : ℤ) *
          (d.primeFactors.erase j).prod (fun l => legendreSym p (l : ℤ)) := by
        rw [Finset.prod_insert hjNot]
  have hdchar : legendreSym p (d : ℤ) =
      legendreSym p (j : ℤ) *
        (d.primeFactors.erase j).prod (fun l => legendreSym p (l : ℤ)) := by
    rw [hDprod, hsplit]
  have hjqr := legendre_qr_mod4_three hp2 (by omega : j ≠ 2) hp4 hmodj
  let E : ℤ := e * ((d.primeFactors.erase j).prod (quadraticResidueFactor d)) *
    (if j % 4 = 3 then -1 else 1)
  calc
    legendreSym p (e * (d : ℤ)) = legendreSym p e * legendreSym p (d : ℤ) :=
      legendreSym.mul p e (d : ℤ)
    _ = e * (legendreSym p (j : ℤ) *
        (d.primeFactors.erase j).prod (fun l => legendreSym p (l : ℤ)) ) := by rw [hechar, hdchar]
    _ = e * ((if j % 4 = 3 then -1 else 1) * legendreSym j (v : ℤ) *
        (d.primeFactors.erase j).prod (quadraticResidueFactor d)) := by
      rw [hjqr, hprodChar]
    _ = -1 := by
      have halg : e * ((if j % 4 = 3 then -1 else 1) * (-E) *
          (d.primeFactors.erase j).prod (quadraticResidueFactor d)) = E * (-E) := by
        dsimp [E]
        ring
      rw [hv, halg]
      have hE : E = 1 ∨ E = -1 := by simpa [E] using hA
      rcases hE with h | h <;> rw [h] <;> norm_num

private theorem legendre_small_signed_part {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hmod3 : p % 3 = 2) {e : ℤ} {d : ℕ}
    (hcase :
      (e = -1 ∧ d = 1 ∧ p % 8 = 3) ∨
      (e = 1 ∧ d = 2 ∧ p % 8 = 3) ∨
      (e = -1 ∧ d = 2 ∧ p % 8 = 7) ∨
      (e = 1 ∧ d = 3 ∧ p % 8 = 5) ∨
      (e = -1 ∧ d = 3 ∧ p % 8 = 5) ∨
      (e = 1 ∧ d = 6 ∧ p % 8 = 3) ∨
      (e = -1 ∧ d = 6 ∧ p % 8 = 7)) :
    legendreSym p (e * (d : ℤ)) = -1 := by
  rcases hcase with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rcases h1 with ⟨rfl, rfl, hr⟩
    have hp4 : p % 4 = 3 := by simpa [mod4_of_mod8 hr]
    simpa using legendre_negOne_mod4_three hp2 hp4
  · rcases h2 with ⟨rfl, rfl, hr⟩
    exact legendre_two_mod8_three hp2 hr
  · rcases h3 with ⟨rfl, rfl, hr⟩
    have hp4 : p % 4 = 3 := by simpa [mod4_of_mod8 hr]
    rw [legendre_mul_natCast (-1 : ℤ) 2]
    change legendreSym p (-1 : ℤ) * legendreSym p (2 : ℤ) = -1
    rw [legendre_negOne_mod4_three hp2 hp4, legendre_two_mod8_seven hp2 hr]
    norm_num
  · rcases h4 with ⟨rfl, rfl, hr⟩
    have hp4 : p % 4 = 1 := by simpa [mod4_of_mod8 hr]
    rw [legendre_mul_natCast (1 : ℤ) 3]
    change legendreSym p (1 : ℤ) * legendreSym p (3 : ℤ) = -1
    simp only [legendreSym.at_one, one_mul]
    simpa [hp4] using legendre_three_mod3_two hp2 hmod3 (Or.inl hp4)
  · rcases h5 with ⟨rfl, rfl, hr⟩
    have hp4 : p % 4 = 1 := by simpa [mod4_of_mod8 hr]
    rw [legendre_mul_natCast (-1 : ℤ) 3, legendre_negOne_mod4_one hp2 hp4]
    simp only [one_mul]
    simpa [hp4] using legendre_three_mod3_two hp2 hmod3 (Or.inl hp4)
  · rcases h6 with ⟨rfl, rfl, hr⟩
    have hp4 : p % 4 = 3 := by simpa [mod4_of_mod8 hr]
    rw [legendre_mul_natCast (1 : ℤ) 6]
    change legendreSym p (1 : ℤ) * legendreSym p (6 : ℤ) = -1
    simp only [legendreSym.at_one]
    have h6 : legendreSym p (6 : ℤ) = legendreSym p (2 : ℤ) * legendreSym p (3 : ℤ) := by
      simpa using legendreSym.mul p (2 : ℤ) (3 : ℤ)
    rw [h6]
    rw [legendre_two_mod8_three hp2 hr]
    rw [legendre_three_mod3_two hp2 hmod3 (Or.inr hp4)]
    simp [hp4]
  · rcases h7 with ⟨rfl, rfl, hr⟩
    have hp4 : p % 4 = 3 := by simpa [mod4_of_mod8 hr]
    rw [legendre_mul_natCast (-1 : ℤ) 6]
    change legendreSym p (-1 : ℤ) * legendreSym p (6 : ℤ) = -1
    have h6 : legendreSym p (6 : ℤ) = legendreSym p (2 : ℤ) * legendreSym p (3 : ℤ) := by
      simpa using legendreSym.mul p (2 : ℤ) (3 : ℤ)
    rw [h6, legendre_negOne_mod4_three hp2 hp4]
    rw [legendre_two_mod8_seven hp2 hr]
    rw [legendre_three_mod3_two hp2 hmod3 (Or.inr hp4)]
    simp [hp4]

private theorem orderIndex_odd {a : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : (a : ZMod p) ≠ 0)
    (hneg : (a : ZMod p) ^ ((p - 1) / 2) = -1) :
    Odd ((p - 1) / orderOf (a : ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have ho : orderOf (a : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha
  by_contra hodd
  have heven : 2 ∣ (p - 1) / orderOf (a : ZMod p) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨k, hk⟩ := heven
  have hfactor : p - 1 = 2 * (orderOf (a : ZMod p) * k) := by
    calc
      p - 1 = orderOf (a : ZMod p) * ((p - 1) / orderOf (a : ZMod p)) := by
        symm
        exact Nat.mul_div_cancel' ho
      _ = 2 * (orderOf (a : ZMod p) * k) := by rw [hk]; ring
  have hhalf : (p - 1) / 2 = orderOf (a : ZMod p) * k := by
    rw [hfactor, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hdiv : orderOf (a : ZMod p) ∣ (p - 1) / 2 := by
    exact ⟨k, hhalf⟩
  have hone : (a : ZMod p) ^ ((p - 1) / 2) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hdiv
  rw [hone] at hneg
  have hne : (1 : ZMod p) ≠ -1 := by
    intro hh
    have htwo : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = 1 + 1 := by norm_num
        _ = 1 - (-1) := by ring
        _ = 0 := sub_eq_zero.mpr hh
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (Nat.le_antisymm hp_le hp.two_le)
  exact hne hneg

private theorem prime_dvd_orderIndex {a : ℤ} {p : ℕ}
    (ho : orderOf (a : ZMod p) ∣ p - 1)
    (hidx : 1 < (p - 1) / orderOf (a : ZMod p)) :
    ∃ q : ℕ, q.Prime ∧ q ∣ (p - 1) / orderOf (a : ZMod p) ∧ q ∣ p - 1 ∧
      orderOf (a : ZMod p) ∣ (p - 1) / q := by
  let o := orderOf (a : ZMod p)
  let i := (p - 1) / o
  have hne : i ≠ 1 := by
    change 1 < i at hidx
    omega
  obtain ⟨q, hq, hqi⟩ := Nat.exists_prime_and_dvd hne
  have hoidx : o * i = p - 1 := Nat.mul_div_cancel' ho
  have hprod : p - 1 = q * (o * (i / q)) := by
    calc
      p - 1 = o * i := hoidx.symm
      _ = o * (q * (i / q)) := by rw [Nat.mul_div_cancel' hqi]
      _ = q * (o * (i / q)) := by ring
  have hqdiv : q ∣ p - 1 := ⟨o * (i / q), hprod⟩
  have hdiv : (p - 1) / q = o * (i / q) := by
    rw [hprod, Nat.mul_div_cancel_left _ hq.pos]
  refine ⟨q, hq, hqi, hqdiv, ?_⟩
  change o ∣ (p - 1) / q
  exact ⟨i / q, hdiv⟩

private theorem orderIndex_gt_one {a : ℤ} {p : ℕ}
    (hn : 0 < p - 1) (ho : orderOf (a : ZMod p) ∣ p - 1)
    (hne : orderOf (a : ZMod p) ≠ p - 1) :
    1 < (p - 1) / orderOf (a : ZMod p) := by
  let o := orderOf (a : ZMod p)
  let i := (p - 1) / o
  have hfactor : o * i = p - 1 := Nat.mul_div_cancel' ho
  have hi0 : i ≠ 0 := by
    intro hiz
    rw [hiz] at hfactor
    simp at hfactor
    omega
  have hi1 : i ≠ 1 := by
    intro hiz
    rw [hiz] at hfactor
    simp at hfactor
    exact hne (by simpa [o] using hfactor)
  change 1 < i
  have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
  omega

private theorem prime_factor_controlled {a : ℤ} {p c r Q q : ℕ}
    (ho : orderOf (a : ZMod p) ∣ p - 1)
    (hc : c = 2 ∨ c = 4)
    (hfac : p - 1 = c * r * Q)
    (hodd : Odd ((p - 1) / orderOf (a : ZMod p)))
    (hQ : Q.Prime)
    (hq : q.Prime)
    (hqi : q ∣ (p - 1) / orderOf (a : ZMod p)) :
    q = Q ∨ q ∣ r := by
  have hindex : orderOf (a : ZMod p) * ((p - 1) / orderOf (a : ZMod p)) = p - 1 :=
    Nat.mul_div_cancel' ho
  have hqn : q ∣ p - 1 := by
    rw [← hindex]
    exact dvd_mul_of_dvd_right hqi _
  rw [hfac] at hqn
  have hqnotc : ¬ q ∣ c := by
    intro h
    rcases hc with hc2 | hc4
    · rw [hc2] at h
      have heq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
      subst q
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hqi)) hodd
    · rw [hc4] at h
      have hq2 : q ∣ 2 := by
        change q ∣ 2 * 2 at h
        rcases hq.dvd_mul.mp h with h | h <;> assumption
      have heq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2
      subst q
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hqi)) hodd
  have hqfactor : q ∣ c * (r * Q) := by
    simpa [Nat.mul_assoc] using hqn
  rcases hq.dvd_mul.mp hqfactor with hqc | hqR
  · exact (hqnotc hqc).elim
  · rcases hq.dvd_mul.mp hqR with hqr | hqQ
    · exact Or.inr hqr
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hQ).mp hqQ)

private theorem exists_bad_index_prime {a : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha0 : (a : ZMod p) ≠ 0) (hhalf : (a : ZMod p) ^ ((p - 1) / 2) = -1)
    (hord : orderOf (a : ZMod p) ≠ p - 1) :
    ∃ q : ℕ, q.Prime ∧ q ∣ (p - 1) / orderOf (a : ZMod p) ∧ q ∣ p - 1 ∧
      orderOf (a : ZMod p) ∣ (p - 1) / q ∧
      Odd ((p - 1) / orderOf (a : ZMod p)) ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have ho : orderOf (a : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
  have hodd := orderIndex_odd hp hp2 ha0 hhalf
  have hpge2 : 2 ≤ p := hp.two_le
  have hn : 0 < p - 1 := Nat.sub_pos_of_lt (by omega)
  have hidx := orderIndex_gt_one hn ho hord
  obtain ⟨q, hq, hqi, hqdiv, horderdiv⟩ := prime_dvd_orderIndex ho hidx
  have hpow : (a : ZMod p) ^ ((p - 1) / q) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp horderdiv
  exact ⟨q, hq, hqi, hqdiv, horderdiv, hodd, hpow⟩

private theorem card_primes_above_base_le_power {A N K : ℕ} (hA : 1 < A)
    (hNpos : 0 < N) (hN : N ≤ A ^ K) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, p.Prime) (hlarge : ∀ p ∈ s, A < p)
    (hmem : ∀ p ∈ s, p ∈ N.primeFactors) : s.card ≤ K := by
  have hprodDiv : s.prod id ∣ N := by
    exact (Finset.prod_dvd_prod_of_subset _ _ _ hmem).trans (Nat.prod_primeFactors_dvd N)
  have hprodLe : s.prod id ≤ N := Nat.le_of_dvd hNpos hprodDiv
  have hlow : (A + 1) ^ s.card ≤ s.prod id := by
    calc
      (A + 1) ^ s.card = s.prod (fun _ => A + 1) := by simp
      _ ≤ s.prod id := by
        apply Finset.prod_le_prod
        intro p hp
        exact Nat.succ_le_of_lt (hlarge p hp)
  by_contra hk
  have hk' : K + 1 ≤ s.card := by omega
  have hpow : A ^ K < (A + 1) ^ s.card := by
    calc
      A ^ K < A ^ (K + 1) := Nat.pow_lt_pow_right hA (Nat.lt_succ_self K)
      _ ≤ (A + 1) ^ (K + 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (A + 1) ^ s.card := Nat.pow_le_pow_right (by omega) hk'
  have : (A + 1) ^ s.card ≤ A ^ K := hlow.trans (hprodLe.trans hN)
  exact (not_lt_of_ge this) hpow

private theorem natAbs_pow_sub_one_le (a : ℤ) (hA : 2 ≤ a.natAbs) {k : ℕ} (hk : 0 < k) :
    (a ^ k - 1).natAbs ≤ a.natAbs ^ (k + 1) := by
  let A := a.natAbs
  have hAcast : (A : ℤ) = |a| := Int.natCast_natAbs a
  have hpowpos : 0 < A ^ k := by positivity
  have hpowone : 1 ≤ A ^ k := Nat.succ_le_of_lt hpowpos
  have hpowBound : A ^ k + 1 ≤ A ^ (k + 1) := by
    rw [Nat.pow_succ]
    have hmul := Nat.mul_le_mul_right (A ^ k) hA
    nlinarith
  have htriangle : |a ^ k - 1| ≤ |a| ^ k + 1 := by
    calc
      |a ^ k - 1| = |a ^ k + (-1)| := by congr 1 <;> ring
      _ ≤ |a ^ k| + |-1| := abs_add_le _ _
      _ = |a| ^ k + 1 := by simp [abs_pow]
  have hboundZ : |a ^ k - 1| ≤ (A ^ (k + 1) : ℤ) := by
    calc
      |a ^ k - 1| ≤ |a| ^ k + 1 := htriangle
      _ = (A ^ k + 1 : ℕ) := by rw [← hAcast]; simp
      _ ≤ (A ^ (k + 1) : ℕ) := by exact_mod_cast hpowBound
      _ = (A ^ (k + 1) : ℤ) := by norm_cast
  have hnatZ : ((a ^ k - 1).natAbs : ℤ) ≤ (A ^ (k + 1) : ℤ) := by
    rw [Int.natCast_natAbs]
    exact hboundZ
  exact_mod_cast hnatZ

private theorem shortExponentProduct_bound (a : ℤ) (ha : 1 < |a|) (J : ℕ) :
    0 < (∏ k ∈ Finset.range J, (a ^ (k + 1) - 1).natAbs) ∧
      (∏ k ∈ Finset.range J, (a ^ (k + 1) - 1).natAbs) ≤
        a.natAbs ^ (J * (J + 1)) := by
  let A := a.natAbs
  have hA : 2 ≤ A := by
    have h : (1 : ℤ) < (A : ℤ) := by simpa [A, Int.natCast_natAbs] using ha
    have hNat : 1 < A := by exact_mod_cast h
    omega
  have hpos : ∀ k ∈ Finset.range J, 0 < (a ^ (k + 1) - 1).natAbs := by
    intro k hk
    have hn : 0 < k + 1 := Nat.succ_pos k
    have hpow : a ^ (k + 1) ≠ 1 := by
      intro h
      have hAbs : |a| ^ (k + 1) = 1 := by
        simpa [abs_pow] using congrArg (fun z : ℤ => |z|) h
      have hbase : 1 < A := by omega
      have hpowNat : 1 < A ^ (k + 1) := Nat.one_lt_pow hn.ne' hbase
      have hlt : (1 : ℤ) < |a| ^ (k + 1) := by
        have hcast : (1 : ℤ) < (A ^ (k + 1) : ℕ) := by exact_mod_cast hpowNat
        simpa [A, Int.natCast_natAbs] using hcast
      omega
    have hsub : a ^ (k + 1) - 1 ≠ 0 := by
      intro h
      exact hpow (sub_eq_zero.mp h)
    have hnAbs : (a ^ (k + 1) - 1).natAbs ≠ 0 := by
      intro hz
      have habs : |a ^ (k + 1) - 1| = 0 := by
        calc
          |a ^ (k + 1) - 1| = ((a ^ (k + 1) - 1).natAbs : ℤ) :=
            (Int.natCast_natAbs _).symm
          _ = 0 := by exact_mod_cast hz
      exact hsub (abs_eq_zero.mp habs)
    exact Nat.pos_of_ne_zero hnAbs
  have hbound : ∀ k ∈ Finset.range J,
      (a ^ (k + 1) - 1).natAbs ≤ A ^ (J + 1) := by
    intro k hk
    have hklt : k < J := Finset.mem_range.mp hk
    have hlocal := natAbs_pow_sub_one_le a hA (Nat.succ_pos k)
    have hexp : k + 2 ≤ J + 1 := by omega
    have hpow := Nat.pow_le_pow_right (by omega : 0 < A) hexp
    exact le_trans hlocal (by simpa [A] using hpow)
  refine ⟨Finset.prod_pos hpos, ?_⟩
  calc
    (∏ k ∈ Finset.range J, (a ^ (k + 1) - 1).natAbs) ≤
        ∏ k ∈ Finset.range J, A ^ (J + 1) := by
      apply Finset.prod_le_prod
      intro k hk
      exact hbound k hk
    _ = (A ^ (J + 1)) ^ J := by simp
    _ = A ^ (J * (J + 1)) := by
      rw [← Nat.pow_mul, Nat.mul_comm]
    _ = _ := rfl

private structure QuadraticProgression (a : ℤ) where
  M : ℕ
  c : ℕ
  u : ℤ
  hM0 : 0 < M
  hM8 : 8 ∣ M
  hc : c = 2 ∨ c = 4
  hu : Int.gcd u (M : ℤ) = 1
  hcu : (c : ℤ) ∣ u - 1
  hcu' : Int.gcd ((u - 1) / c) ((M / c : ℕ) : ℤ) = 1
  primes : ∀ p : ℕ, (hp : p.Prime) → (p : ℤ) ≡ u [ZMOD M] →
    ¬ (p : ℤ) ∣ a ∧ @legendreSym p ⟨hp⟩ a = -1

private def targetIntervalPrimes (a : ℤ) (x : ℝ) : Set ℕ :=
  {p | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ ¬ (p : ℤ) ∣ a ∧
    orderOf (a : ZMod p) = p - 1}

private def controlledIntervalPrimes (x : ℝ) (M c : ℕ) (u : ℤ) : Set ℕ :=
  {p | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
    ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (9 / 10 : ℝ) < (Q : ℝ) ∧
      0 < r ∧ ∀ l : ℕ, l.Prime → l ∣ r →
        Real.exp (Real.log x ^ (1 / 10 : ℝ)) < (l : ℝ) ∧
          (l : ℝ) < Real.exp (Real.log x ^ (3 / 10 : ℝ))}

private def qFactorExceptions (a : ℤ) (x : ℝ) : Set ℕ :=
  {p | p.Prime ∧ x < (p : ℝ) ∧ ∃ k : ℕ, 0 < k ∧
    (k : ℝ) < 2 * x ^ (1 / 10 : ℝ) ∧ (p : ℤ) ∣ a ^ k - 1}

private def splittingConditionSet (a : ℤ) (x : ℝ) (q : ℕ) : Set ℕ :=
  {p | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ q ∣ p - 1 ∧
    (a : ZMod p) ^ ((p - 1) / q) = 1}

private def rFactorExceptions (a : ℤ) (x : ℝ) : Set ℕ :=
  {p | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ ∃ q : ℕ, q.Prime ∧
    Real.exp (Real.log x ^ (1 / 10 : ℝ)) < (q : ℝ) ∧
    (q : ℝ) < Real.exp (Real.log x ^ (3 / 10 : ℝ)) ∧
    p ∈ splittingConditionSet a x q}

private theorem pow_half_of_legendre_eq_neg_one {a : ℤ} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hsym : @legendreSym p ⟨hp⟩ a = -1) :
    (a : ZMod p) ^ ((p - 1) / 2) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpOdd := hp.odd_of_ne_two hp2
  have hpMod2 : p % 2 = 1 := Nat.odd_iff.mp hpOdd
  have hdiv : p / 2 = (p - 1) / 2 := by omega
  have hcast : (legendreSym p a : ZMod p) = (-1 : ZMod p) := by
    simpa using congrArg (fun z : ℤ => (z : ZMod p)) hsym
  rw [legendreSym.eq_pow p a, hdiv] at hcast
  exact hcast

private theorem controlled_nonprimitive_exception {a : ℤ} {x : ℝ}
    (G : QuadraticProgression a) (hx : 2 ≤ x) {p : ℕ}
    (hpMem : p ∈ controlledIntervalPrimes x G.M G.c G.u)
    (hord : orderOf (a : ZMod p) ≠ p - 1) :
    p ∈ qFactorExceptions a x ∨ p ∈ rFactorExceptions a x := by
  rcases hpMem with ⟨hp, hpx, hp2x, hclass, r, Q, hfac, hQ, hQlarge, hrpos, hR⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpx
    linarith
  rcases G.primes p hp hclass with ⟨hnotdiv, hsym⟩
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro hz
    exact hnotdiv ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)
  have hhalf := pow_half_of_legendre_eq_neg_one hp hp2 hsym
  have ho : orderOf (a : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
  obtain ⟨q, hq, hqi, hqdiv, horderdiv, hodd, hpow⟩ :=
    exists_bad_index_prime hp hp2 ha0 hhalf hord
  rcases prime_factor_controlled ho G.hc hfac hodd hQ hq hqi with hqQ | hqr
  · subst q
    let k : ℕ := (p - 1) / Q
    have hpge3 : 3 ≤ p := hp.odd_iff.mp (hp.odd_of_ne_two (by omega))
    have hkpos : 0 < k := by
      dsimp [k]
      exact Nat.div_pos (Nat.le_of_dvd (by omega) hqdiv) hQ.pos
    have hkpow : (a : ZMod p) ^ k = 1 := by simpa [k] using hpow
    have hpDivPower : (p : ℤ) ∣ a ^ k - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ k - 1) p).mp
      simp only [Int.cast_sub, Int.cast_pow, Int.cast_one]
      rw [hkpow]
      simp
    have hkfac : k = G.c * r := by
      dsimp [k]
      calc
        (p - 1) / Q = ((G.c * r) * Q) / Q := by rw [hfac]
        _ = (Q * (G.c * r)) / Q := by rw [Nat.mul_comm (G.c * r) Q]
        _ = G.c * r := Nat.mul_div_cancel_left _ hQ.pos
    have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      exact_mod_cast (Nat.cast_sub (show 1 ≤ p by omega))
    have hRealFac : (p : ℝ) - 1 = (k : ℝ) * Q := by
      have hnCast : ((p - 1 : ℕ) : ℝ) = (G.c : ℝ) * r * Q := by exact_mod_cast hfac
      have hkCast : (k : ℝ) = (G.c : ℝ) * r := by exact_mod_cast hkfac
      calc
        (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := hsub.symm
        _ = (G.c : ℝ) * r * Q := hnCast
        _ = (k : ℝ) * Q := by rw [hkCast]
    have hxpos : 0 < x := by linarith
    have hpowprod : x ^ (9 / 10 : ℝ) * x ^ (1 / 10 : ℝ) = x := by
      rw [← Real.rpow_add hxpos]
      norm_num
    have hkBig : (k : ℝ) * x ^ (9 / 10 : ℝ) < 2 * x := by
      have hkQ : (k : ℝ) * x ^ (9 / 10 : ℝ) < (k : ℝ) * Q :=
        mul_lt_mul_of_pos_left hQlarge (by exact_mod_cast hkpos)
      calc
        (k : ℝ) * x ^ (9 / 10 : ℝ) < (k : ℝ) * Q := hkQ
        _ = (p : ℝ) - 1 := hRealFac.symm
        _ < 2 * x := by linarith
    have hRight : (2 * x ^ (1 / 10 : ℝ)) * x ^ (9 / 10 : ℝ) = 2 * x := by
      calc
        (2 * x ^ (1 / 10 : ℝ)) * x ^ (9 / 10 : ℝ) =
            2 * (x ^ (9 / 10 : ℝ) * x ^ (1 / 10 : ℝ)) := by ring
        _ = 2 * x := by rw [hpowprod]
    have hklt : (k : ℝ) < 2 * x ^ (1 / 10 : ℝ) := by
      have hmul : (k : ℝ) * x ^ (9 / 10 : ℝ) <
          (2 * x ^ (1 / 10 : ℝ)) * x ^ (9 / 10 : ℝ) := by
        rw [hRight]
        exact hkBig
      exact lt_of_mul_lt_mul_right hmul (Real.rpow_pos_of_pos hxpos _).le
    exact Or.inl ⟨hp, hpx, k, hkpos, hklt, hpDivPower⟩
  · have hrange := hR q hq hqr
    exact Or.inr ⟨hp, hpx, le_of_lt hp2x, q, hq, hrange.1, hrange.2,
      ⟨hp, hpx, le_of_lt hp2x, hqdiv, hpow⟩⟩

private theorem qFactorExceptions_ncard_le (a : ℤ) (ha : 1 < |a|) (x : ℝ)
    (hx : (a.natAbs : ℝ) + 1 ≤ x) (hxpos : 0 < x) :
    (qFactorExceptions a x).Finite ∧
      (qFactorExceptions a x).ncard ≤
      Nat.ceil (2 * x ^ (1 / 10 : ℝ)) * (Nat.ceil (2 * x ^ (1 / 10 : ℝ)) + 1) := by
  classical
  let A := a.natAbs
  let J := Nat.ceil (2 * x ^ (1 / 10 : ℝ))
  let B : ℕ := ∏ k ∈ Finset.range J, (a ^ (k + 1) - 1).natAbs
  rcases shortExponentProduct_bound a ha J with ⟨hBpos, hBbound⟩
  have hAInt : (1 : ℤ) < (A : ℤ) := by simpa [A, Int.natCast_natAbs] using ha
  have hAgt : 1 < A := by exact_mod_cast hAInt
  have hAbase : 2 ≤ A := by omega
  have hBpow : B ≤ A ^ (J * (J + 1)) := by simpa [B, A] using hBbound
  let S : Finset ℕ := B.primeFactors.filter (fun p => A < p)
  have hScard : S.card ≤ J * (J + 1) := by
    apply card_primes_above_base_le_power hAgt hBpos hBpow S
    · intro p hp
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp
      exact (Finset.mem_filter.mp hp).1
  have hsubset : qFactorExceptions a x ⊆ (S : Set ℕ) := by
    intro p hp
    rcases hp with ⟨hp, hpx, k, hkpos, hklt, hpdvd⟩
    have hkLtJReal : (k : ℝ) < (J : ℝ) := lt_of_lt_of_le hklt (Nat.le_ceil _)
    have hkLtJ : k < J := by exact_mod_cast hkLtJReal
    have hkidx : k - 1 < J := by omega
    let i := k - 1
    have hi : i ∈ Finset.range J := Finset.mem_range.mpr hkidx
    have hkEq : i + 1 = k := by dsimp [i]; omega
    have hfactorDiv : (a ^ k - 1).natAbs ∣ B := by
      have hmemDiv : (a ^ (i + 1) - 1).natAbs ∣
          ∏ j ∈ Finset.range J, (a ^ (j + 1) - 1).natAbs :=
        Finset.dvd_prod_of_mem _ hi
      have hmemDiv' : (a ^ (i + 1) - 1).natAbs ∣ B := by simpa [B] using hmemDiv
      simpa [hkEq] using hmemDiv'
    have hpdvdNat : p ∣ (a ^ k - 1).natAbs := Int.natCast_dvd.mp hpdvd
    have hpB : p ∣ B := hpdvdNat.trans hfactorDiv
    have hpPrimeFactor : p ∈ B.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpB, hBpos.ne'⟩
    have hpBig : A < p := by
      have hxA : (A : ℝ) + 1 ≤ x := by simpa [A] using hx
      have hreal : (A : ℝ) < (p : ℝ) := by linarith
      exact_mod_cast hreal
    exact Finset.mem_filter.mpr ⟨hpPrimeFactor, hpBig⟩
  have hcard : (qFactorExceptions a x).ncard ≤ S.card := by
    calc
      (qFactorExceptions a x).ncard ≤ (S : Set ℕ).ncard :=
        Set.ncard_le_ncard hsubset (Finset.finite_toSet S)
      _ = S.card := Set.ncard_coe_finset S
  have hmain := hcard.trans hScard
  exact ⟨(Finset.finite_toSet S).subset hsubset, by simpa [J] using hmain⟩

private theorem q_factor_error_eventually (a : ℤ) (ha : 1 < |a|) (D : ℝ)
    (hD : 0 < D) : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (qFactorExceptions a x).Finite ∧
        ((qFactorExceptions a x).ncard : ℝ) ≤ D * x / Real.log x ^ 2 := by
  classical
  let θ : ℝ := 1 / 10
  let α : ℝ := 4 / 5
  have hlittle := isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : 0 < α)
  have hsmall := hlittle.bound (show 0 < D / 24 by positivity)
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.1 hsmall
  let X := max X0 (max ((a.natAbs : ℝ) + 1) (max 2 (Real.exp 1)))
  refine ⟨X, ?_⟩
  intro x hx
  have hx0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hbase : max ((a.natAbs : ℝ) + 1) (max 2 (Real.exp 1)) ≤ x := by
    exact le_trans (le_max_right _ _) hx
  have hsize : (a.natAbs : ℝ) + 1 ≤ x :=
    le_trans (le_max_left _ _) hbase
  have h2x : 2 ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hbase
  have hxpos : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ x :=
      le_trans (le_max_right _ _) (le_max_right _ _) |>.trans hbase
    have hlog := Real.log_le_log (Real.exp_pos 1) hexp
    simpa using hlog
  have hLogSmall := hX0 x hx0
  have hLogSq : Real.log x ^ 2 ≤ (D / 24) * x ^ α := by
    have hLogNonneg : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    have hxpow : 0 ≤ x ^ α := Real.rpow_nonneg hxpos.le _
    simpa [Real.norm_eq_abs, abs_of_nonneg hLogNonneg, abs_of_nonneg hxpow] using hLogSmall
  let J := Nat.ceil (2 * x ^ θ)
  have hroot1 : 1 ≤ x ^ θ := by
    calc
      1 = x ^ (0 : ℝ) := by simp
      _ ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num [θ])
  have hceilNat : J ≤ Nat.floor (2 * x ^ θ) + 1 := Nat.ceil_le_floor_add_one _
  have hfloor : (Nat.floor (2 * x ^ θ) : ℝ) ≤ 2 * x ^ θ :=
    Nat.floor_le (by positivity)
  have hJsmall : (J : ℝ) ≤ 3 * x ^ θ := by
    have hceilReal : (J : ℝ) ≤ 2 * x ^ θ + 1 := by
      have hcast : (J : ℝ) ≤ (Nat.floor (2 * x ^ θ) : ℝ) + 1 := by exact_mod_cast hceilNat
      linarith
    nlinarith
  have hJplus : ((J + 1 : ℕ) : ℝ) ≤ 4 * x ^ θ := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith [hJsmall, hroot1]
  have hpowθ : x ^ θ * x ^ θ = x ^ (2 * θ) := by
    rw [← Real.rpow_add hxpos]
    norm_num [θ]
  have hJprod : (J : ℝ) * ((J + 1 : ℕ) : ℝ) ≤ 12 * x ^ (2 * θ) := by
    calc
      (J : ℝ) * ((J + 1 : ℕ) : ℝ) ≤ (3 * x ^ θ) * (4 * x ^ θ) :=
        mul_le_mul hJsmall hJplus (by positivity) (by positivity)
      _ = 12 * (x ^ θ * x ^ θ) := by ring
      _ = 12 * x ^ (2 * θ) := by rw [hpowθ]
  have hpowCombine : x ^ (2 * θ) * x ^ α = x := by
    rw [← Real.rpow_add hxpos]
    norm_num [θ, α]
  have herror :
      (J : ℝ) * ((J + 1 : ℕ) : ℝ) * Real.log x ^ 2 ≤ D * x := by
    calc
      (J : ℝ) * ((J + 1 : ℕ) : ℝ) * Real.log x ^ 2 ≤
          12 * x ^ (2 * θ) * Real.log x ^ 2 := by
        gcongr
      _ ≤ 12 * x ^ (2 * θ) * ((D / 24) * x ^ α) := by
        gcongr
      _ = (D / 2) * x := by
        calc
          12 * x ^ (2 * θ) * (D / 24 * x ^ α) =
              (12 * (D / 24)) * (x ^ (2 * θ) * x ^ α) := by ring
          _ = (D / 2) * x := by rw [hpowCombine]; ring
      _ ≤ D * x := by nlinarith [mul_nonneg hD.le hxpos.le]
  have hcountFacts := qFactorExceptions_ncard_le a ha x hsize hxpos
  have hcountReal : ((qFactorExceptions a x).ncard : ℝ) ≤
      (J : ℝ) * ((J + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [J, θ] using hcountFacts.2)
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hLsqpos : 0 < Real.log x ^ 2 := by positivity
  have hQcount : ((qFactorExceptions a x).ncard : ℝ) ≤ D * x / Real.log x ^ 2 := by
    apply (le_div_iff₀ hLsqpos).2
    calc
      ((qFactorExceptions a x).ncard : ℝ) * Real.log x ^ 2 ≤
          ((J : ℝ) * ((J + 1 : ℕ) : ℝ)) * Real.log x ^ 2 :=
        mul_le_mul_of_nonneg_right hcountReal (sq_nonneg _)
      _ ≤ D * x := herror
  exact ⟨hcountFacts.1, hQcount⟩

private theorem reciprocal_factor_bound {q : ℕ} (hq : 2 ≤ q) :
    (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤ 2 / ((q : ℝ) ^ 2) := by
  have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : 0 < (q : ℝ) := by linarith
  have hqsub : 0 < (q : ℝ) - 1 := by linarith
  have hden1 : 0 < (q : ℝ) * ((q : ℝ) - 1) := mul_pos hqpos hqsub
  have hden2 : 0 < (q : ℝ) ^ 2 := pow_pos hqpos _
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith

private theorem reciprocal_factor_sum_bound {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    (∑ q ∈ Finset.Ioc n N, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) ≤ 2 / n := by
  have hsq := sum_Ioc_inv_sq_le_sub (α := ℝ)
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)) hnN
  have hterms :
      (∑ q ∈ Finset.Ioc n N, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) ≤
        ∑ q ∈ Finset.Ioc n N, 2 / ((q : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro q hq
    exact reciprocal_factor_bound (by
      have hqn := Finset.mem_Ioc.mp hq
      omega)
  have hsum :
      (∑ q ∈ Finset.Ioc n N, 2 / ((q : ℝ) ^ 2)) =
        2 * ∑ q ∈ Finset.Ioc n N, ((q : ℝ) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    simp [div_eq_mul_inv]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)))
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one hn) hnN)
  calc
    _ ≤ ∑ q ∈ Finset.Ioc n N, 2 / ((q : ℝ) ^ 2) := hterms
    _ = 2 * ∑ q ∈ Finset.Ioc n N, ((q : ℝ) ^ 2)⁻¹ := hsum
    _ ≤ 2 * ((n : ℝ)⁻¹ - (N : ℝ)⁻¹) := by nlinarith [hsq]
    _ ≤ 2 * (n : ℝ)⁻¹ := by
      have hInvNonneg : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
      nlinarith
    _ = 2 / n := by simp [div_eq_mul_inv]

private theorem rFactorExceptions_sum_bound (a : ℤ) (ha : 1 < |a|)
    (C : ℝ) (hC : 0 < C) (q₀ : ℕ) (x : ℝ)
    (hx2 : 2 ≤ x) (hlog1 : 1 ≤ Real.log x)
    (hq₀ : (q₀ : ℝ) ≤ Real.exp (Real.log x ^ (1 / 10 : ℝ)))
    (hSplitx : ∀ q : ℕ, q.Prime → q₀ ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (3 / 10 : ℝ)) →
        ((splittingConditionSet a x q).ncard : ℝ) ≤
          C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) +
            x ^ (1 - (1 / 1000000 : ℝ)))) :
    (rFactorExceptions a x).Finite ∧
      (rFactorExceptions a x).ncard ≤
      C * (x / Real.log x * (2 / (Nat.floor (Real.exp (Real.log x ^ (1 / 10 : ℝ))) : ℝ)) +
        (Nat.ceil (Real.exp (Real.log x ^ (3 / 10 : ℝ)) : ℝ) : ℝ) *
          x ^ (1 - (1 / 1000000 : ℝ))) := by
  classical
  let L := Real.log x
  let lo := Real.exp (L ^ (1 / 10 : ℝ))
  let hi := Real.exp (L ^ (3 / 10 : ℝ))
  let n := Nat.floor lo
  let N := Nat.ceil hi
  let S : Finset ℕ := (Finset.range N).filter fun q => q.Prime ∧ q₀ ≤ q ∧ n < q
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hlog1
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi, L]
    exact Real.exp_le_exp.mpr <| Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
  have hnFloor : (n : ℝ) ≤ lo := by
    exact Nat.floor_le (Real.exp_pos _).le
  have hNceil : hi ≤ (N : ℝ) := Nat.le_ceil _
  have hnN : n ≤ N := by
    exact_mod_cast (le_trans hnFloor (le_trans hlohi hNceil))
  have hpowLo : 1 ≤ L ^ (1 / 10 : ℝ) := by
    calc
      1 = L ^ (0 : ℝ) := by simp
      _ ≤ L ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
  have hloGt1 : 1 < lo := by
    dsimp [lo, L]
    exact Real.one_lt_exp_iff.mpr (lt_of_lt_of_le zero_lt_one hpowLo)
  have hn1 : 1 ≤ n := by
    apply (Nat.le_floor_iff' (n := 1) (by norm_num)).2
    exact_mod_cast le_of_lt hloGt1
  have hUpperExp : hi ≤ (N : ℝ) := hNceil
  have hSrange : S ⊆ Finset.range N := Finset.filter_subset _ _
  obtain ⟨P, hPx⟩ := exists_nat_gt (2 * x)
  have hUnionSub : (⋃ q ∈ S, splittingConditionSet a x q) ⊆ Set.Iio P := by
    intro p hp
    simp only [Set.mem_iUnion] at hp
    rcases hp with ⟨q, hqMem, hpSplit⟩
    have hpUpper : (p : ℝ) ≤ 2 * x := hpSplit.2.2.1
    change p < P
    exact_mod_cast lt_of_le_of_lt hpUpper hPx
  have hUnionFin : (⋃ q ∈ S, splittingConditionSet a x q).Finite :=
    (Set.finite_Iio P).subset hUnionSub
  have hRSub : rFactorExceptions a x ⊆ ⋃ q ∈ S, splittingConditionSet a x q := by
    intro p hp
    rcases hp with ⟨hp, hpx, hp2x, q, hq, hqlo, hqhi, hpsplit⟩
    have hq0lt : (q₀ : ℝ) < (q : ℝ) := lt_of_le_of_lt hq₀ hqlo
    have hq0NatLt : q₀ < q := by exact_mod_cast hq0lt
    have hnqReal : (n : ℝ) < (q : ℝ) := lt_of_le_of_lt hnFloor hqlo
    have hnq : n < q := by exact_mod_cast hnqReal
    have hqNReal : (q : ℝ) < (N : ℝ) := lt_of_lt_of_le hqhi hUpperExp
    have hqN : q < N := by exact_mod_cast hqNReal
    have hqS : q ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqN,
      ⟨hq, le_of_lt hq0NatLt, hnq⟩⟩
    simp only [Set.mem_iUnion]
    exact ⟨q, hqS, hpsplit⟩
  have hEcardNat : (rFactorExceptions a x).ncard ≤
      ∑ q ∈ S, (splittingConditionSet a x q).ncard := by
    exact (Set.ncard_le_ncard hRSub hUnionFin).trans (Finset.set_ncard_biUnion_le S _)
  have hEcardReal : ((rFactorExceptions a x).ncard : ℝ) ≤
      ∑ q ∈ S, ((splittingConditionSet a x q).ncard : ℝ) := by
    exact_mod_cast hEcardNat
  have hSplitEach : ∀ q ∈ S,
      ((splittingConditionSet a x q).ncard : ℝ) ≤
        C * (x / ((q : ℝ) * ((q : ℝ) - 1) * L) +
          x ^ (1 - (1 / 1000000 : ℝ))) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqRange, ⟨hqPrime, hqmin, hnq⟩⟩
    have hqUpper : (q : ℝ) ≤ hi := by
      have hqNatLeFloor : q ≤ Nat.floor hi := by
        have hqNatLtN : q < N := Finset.mem_range.mp hqRange
        have hceilFloor : N ≤ Nat.floor hi + 1 := Nat.ceil_le_floor_add_one hi
        omega
      exact (Nat.cast_le.mpr hqNatLeFloor).trans (Nat.floor_le (Real.exp_pos _).le)
    have h := hSplitx q hqPrime hqmin hqUpper
    simpa [L] using h
  have hRecip : (∑ q ∈ S,
      (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) ≤ 2 / n := by
    have hSsub : S ⊆ Finset.Ioc n N := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqRange, ⟨_, _, hnq⟩⟩
      exact Finset.mem_Ioc.mpr ⟨hnq, (Finset.mem_range.mp hqRange).le⟩
    have hnonneg : ∀ q ∈ Finset.Ioc n N, 0 ≤
        (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) := by
      intro q hq
      have hq2 : 2 ≤ q := by
        have := (Finset.mem_Ioc.mp hq).1
        omega
      have hqposNat : 0 < q := by omega
      have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqposNat
      have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
      have hqsub : 0 < (q : ℝ) - 1 := by linarith
      positivity
    calc
      (∑ q ∈ S, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) ≤
          ∑ q ∈ Finset.Ioc n N, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub (by
          intro q hq _
          exact hnonneg q hq)
      _ ≤ 2 / n := reciprocal_factor_sum_bound hn1 hnN
  have hScard : (S.card : ℝ) ≤ (N : ℝ) := by
    have hcard : S.card ≤ N := (Finset.card_le_card hSrange).trans_eq (Finset.card_range N)
    exact_mod_cast hcard
  let Xcoef : ℝ := x / L
  let Ycoef : ℝ := x ^ (1 - (1 / 1000000 : ℝ))
  have hxpos : 0 < x := by linarith
  have hXnonneg : 0 ≤ Xcoef := by
    dsimp [Xcoef]
    exact div_nonneg hxpos.le hLpos.le
  have hYnonneg : 0 ≤ Ycoef := by
    dsimp [Ycoef]
    exact Real.rpow_nonneg hxpos.le _
  have hSumUpper :
      (∑ q ∈ S, ((splittingConditionSet a x q).ncard : ℝ)) ≤
        C * (Xcoef * (2 / n) + (N : ℝ) * Ycoef) := by
    calc
      (∑ q ∈ S, ((splittingConditionSet a x q).ncard : ℝ)) ≤
          ∑ q ∈ S, C * (Xcoef *
            ((1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) + Ycoef) := by
        apply Finset.sum_le_sum
        intro q hq
        have hq2 : 2 ≤ q := by
          rcases Finset.mem_filter.mp hq with ⟨_, ⟨_, _, hnq⟩⟩
          omega
        have hqposNat : 0 < q := by omega
        have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqposNat
        have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
        have hqsub : 0 < (q : ℝ) - 1 := by linarith
        have hden : (q : ℝ) * ((q : ℝ) - 1) ≠ 0 := (mul_pos hqpos hqsub).ne'
        have hdivision : x / ((q : ℝ) * ((q : ℝ) - 1) * L) =
            Xcoef * ((1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) := by
          dsimp [Xcoef]
          field_simp [hden, ne_of_gt hLpos]
        have hEach := hSplitEach q hq
        rw [hdivision] at hEach
        simpa [Ycoef] using hEach
      _ = C * (Xcoef *
          (∑ q ∈ S, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) +
          (S.card : ℝ) * Ycoef) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * (Xcoef * (2 / n) + (N : ℝ) * Ycoef) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        nlinarith [mul_le_mul_of_nonneg_left hRecip hXnonneg,
          mul_le_mul_of_nonneg_right hScard hYnonneg]
  have hRfinite : (rFactorExceptions a x).Finite := hUnionFin.subset hRSub
  refine ⟨hRfinite, ?_⟩
  calc
    ((rFactorExceptions a x).ncard : ℝ) ≤
        ∑ q ∈ S, ((splittingConditionSet a x q).ncard : ℝ) := hEcardReal
    _ ≤ C * (Xcoef * (2 / n) + (N : ℝ) * Ycoef) := hSumUpper
    _ = C * (x / Real.log x *
          (2 / (Nat.floor (Real.exp (Real.log x ^ (1 / 10 : ℝ))) : ℝ)) +
          (Nat.ceil (Real.exp (Real.log x ^ (3 / 10 : ℝ)) : ℝ) : ℝ) *
            x ^ (1 - (1 / 1000000 : ℝ))) := by
      simp [Xcoef, Ycoef, L, lo, hi, n, N]

set_option maxHeartbeats 0 in
private theorem r_factor_error_eventually (a : ℤ) (ha : 1 < |a|)
    (C : ℝ) (hC : 0 < C) (q₀ : ℕ) (Xs : ℝ)
    (hSplit : ∀ y : ℝ, Xs ≤ y → ∀ q : ℕ, q.Prime → q₀ ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log y ^ (3 / 10 : ℝ)) →
        ((splittingConditionSet a y q).ncard : ℝ) ≤
          C * (y / ((q : ℝ) * ((q : ℝ) - 1) * Real.log y) +
            y ^ (1 - (1 / 1000000 : ℝ))))
    (D : ℝ) (hD : 0 < D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (rFactorExceptions a x).Finite ∧
        ((rFactorExceptions a x).ncard : ℝ) ≤ D * x / Real.log x ^ 2 := by
  classical
  let θ : ℝ := 1 / 10
  let β : ℝ := 3 / 10
  let δ : ℝ := 1 / 1000000
  let ε : ℝ := D / (2 * C)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hlogTendsto : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hyTendsto : Tendsto (fun x : ℝ => Real.log x ^ θ) atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num [θ])).comp hlogTendsto
  have hloTendsto : Tendsto (fun x : ℝ => Real.exp (Real.log x ^ θ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hyTendsto
  have hq₀ev : ∀ᶠ x : ℝ in atTop,
      (q₀ : ℝ) ≤ Real.exp (Real.log x ^ θ) :=
    hloTendsto.eventually_ge_atTop (q₀ : ℝ)
  have hlo2ev : ∀ᶠ x : ℝ in atTop, 2 ≤ Real.exp (Real.log x ^ θ) :=
    hloTendsto.eventually_ge_atTop 2
  have hlog1ev : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    hlogTendsto.eventually_ge_atTop 1
  have hyPowerSmall : ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ (-(7 / 10 : ℝ)) < δ / 2 := by
    have hpow : Tendsto (fun t : ℝ => t ^ (-(7 / 10 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : 0 < (7 / 10 : ℝ))
    exact (hpow.comp hlogTendsto).eventually (Iio_mem_nhds (by positivity))
  have hRatioSmall : ∀ᶠ x : ℝ in atTop,
      (Real.log x ^ θ) ^ 10 * Real.exp (-(Real.log x ^ θ)) < ε / 4 := by
    have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 10 1 (by norm_num)
    simpa [Function.comp_apply] using
      (hdecay.comp hyTendsto).eventually (Iio_mem_nhds (by positivity))
  have hFinalDecay : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ 2 * Real.exp (-(δ / 2) * Real.log x) < ε / 2 := by
    have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (δ / 2) (by positivity)
    simpa [Function.comp_apply] using
      (hdecay.comp hlogTendsto).eventually (Iio_mem_nhds (by positivity))
  have hXsEv : ∀ᶠ x : ℝ in atTop, Xs ≤ x := eventually_ge_atTop Xs
  have h2Ev : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hTogether : ∀ᶠ x : ℝ in atTop,
      Xs ≤ x ∧ 2 ≤ x ∧ 1 ≤ Real.log x ∧
        (q₀ : ℝ) ≤ Real.exp (Real.log x ^ θ) ∧
        2 ≤ Real.exp (Real.log x ^ θ) ∧
        (Real.log x ^ θ) ^ 10 * Real.exp (-(Real.log x ^ θ)) < ε / 4 ∧
        Real.log x ^ (-(7 / 10 : ℝ)) < δ / 2 ∧
        Real.log x ^ 2 * Real.exp (-(δ / 2) * Real.log x) < ε / 2 := by
    filter_upwards [hXsEv, h2Ev, hlog1ev, hq₀ev, hlo2ev, hRatioSmall,
      hyPowerSmall, hFinalDecay] with x hXs hx2 hlog hq hlo2 hratio hpow hdecay
    exact ⟨hXs, hx2, hlog, hq, hlo2, hratio, hpow, hdecay⟩
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hTogether
  refine ⟨X, ?_⟩
  intro x hx
  rcases hX x hx with ⟨hxSplit, hx2, hlog1, hq₀, hlo2, hratio, hpowSmall, hdecay⟩
  let L : ℝ := Real.log x
  let lo : ℝ := Real.exp (L ^ θ)
  let hi : ℝ := Real.exp (L ^ β)
  let n : ℕ := Nat.floor lo
  let N : ℕ := Nat.ceil hi
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hxpos : 0 < x := by linarith
  have hloq₀ : (q₀ : ℝ) ≤ lo := by simpa [lo, L] using hq₀
  have hloLarge : 2 ≤ lo := by simpa [lo, L] using hlo2
  have hloPos : 0 < lo := by simpa [lo, L] using Real.exp_pos (L ^ θ)
  have hnlt : lo < (n : ℝ) + 1 := by
    exact_mod_cast (Nat.lt_floor_add_one lo)
  have hnHalf : lo / 2 ≤ (n : ℝ) := by nlinarith
  have hnpos : 0 < (n : ℝ) :=
    lt_of_lt_of_le (div_pos hloPos (by norm_num)) hnHalf
  have hpowTen : (L ^ θ) ^ 10 = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num [θ]
  have hratioL : L / lo ≤ ε / 4 := by
    calc
      L / lo = (L ^ θ) ^ 10 * Real.exp (-(L ^ θ)) := by
        rw [hpowTen, div_eq_mul_inv, Real.exp_neg]
      _ ≤ ε / 4 := by
        exact le_of_lt (by simpa [L] using hratio)
  have hβRelation : L ^ β = L * L ^ (-(7 / 10 : ℝ)) := by
    calc
      L ^ β = L ^ (1 + (-(7 / 10 : ℝ))) := by norm_num [β]
      _ = L ^ (1 : ℝ) * L ^ (-(7 / 10 : ℝ)) := by rw [Real.rpow_add hLpos]
      _ = L * L ^ (-(7 / 10 : ℝ)) := by rw [Real.rpow_one]
  have hβSmall : L ^ β ≤ (δ / 2) * L := by
    rw [hβRelation]
    calc
      L * L ^ (-(7 / 10 : ℝ)) ≤ L * (δ / 2) :=
        mul_le_mul_of_nonneg_left hpowSmall.le hLpos.le
      _ = (δ / 2) * L := by ring
  have hexpβ : Real.exp (L ^ β) ≤ Real.exp ((δ / 2) * L) :=
    Real.exp_le_exp.mpr hβSmall
  have hNnat : N ≤ Nat.floor hi + 1 := Nat.ceil_le_floor_add_one hi
  have hNreal : (N : ℝ) ≤ hi + 1 := by
    have hcast : (N : ℝ) ≤ (Nat.floor hi : ℝ) + 1 := by exact_mod_cast hNnat
    have hfloor : (Nat.floor hi : ℝ) ≤ hi := Nat.floor_le (Real.exp_pos _).le
    linarith
  have hhiOne : 1 ≤ hi := by
    apply (Real.one_le_exp_iff).2
    exact Real.rpow_nonneg hLpos.le β
  have hNupper : (N : ℝ) ≤ 2 * Real.exp ((δ / 2) * L) := by
    calc
      (N : ℝ) ≤ hi + 1 := hNreal
      _ ≤ 2 * hi := by dsimp [hi]; nlinarith [hhiOne]
      _ ≤ 2 * Real.exp ((δ / 2) * L) := by dsimp [hi]; gcongr
  have hxPowδ : x ^ δ = Real.exp (L * δ) := by
    rw [Real.rpow_def_of_pos hxpos]
  have hLsqBound : L ^ 2 ≤ (ε / 2) * Real.exp ((δ / 2) * L) := by
    have hcancel : L ^ 2 =
        (L ^ 2 * Real.exp (-((δ / 2) * L))) * Real.exp ((δ / 2) * L) := by
      calc
        L ^ 2 = L ^ 2 * (Real.exp (-((δ / 2) * L)) * Real.exp ((δ / 2) * L)) := by
          rw [← Real.exp_add]
          simp
        _ = (L ^ 2 * Real.exp (-((δ / 2) * L))) * Real.exp ((δ / 2) * L) := by ring
    have hmul := mul_le_mul_of_nonneg_right hdecay.le
      (Real.exp_pos ((δ / 2) * L)).le
    calc
      L ^ 2 = (L ^ 2 * Real.exp (-((δ / 2) * L))) * Real.exp ((δ / 2) * L) := hcancel
      _ ≤ (ε / 2) * Real.exp ((δ / 2) * L) := by
        simpa [L] using hmul
  have hNLog : (N : ℝ) * L ^ 2 ≤ ε * x ^ δ := by
    calc
      (N : ℝ) * L ^ 2 ≤ (2 * Real.exp ((δ / 2) * L)) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hNupper (sq_nonneg _)
      _ = L ^ 2 * (2 * Real.exp ((δ / 2) * L)) := by ring
      _ ≤ ((ε / 2) * Real.exp ((δ / 2) * L)) *
          (2 * Real.exp ((δ / 2) * L)) :=
        mul_le_mul_of_nonneg_right hLsqBound (by positivity)
      _ = ε * (Real.exp ((δ / 2) * L) * Real.exp ((δ / 2) * L)) := by ring
      _ = ε * Real.exp (L * δ) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [δ]
        ring_nf
      _ = ε * x ^ δ := by rw [← hxPowδ]
  have hxPowSplit : x ^ δ * x ^ (1 - δ) = x := by
    rw [← Real.rpow_add hxpos]
    norm_num
  let A : ℝ := x / L * (2 / (n : ℝ))
  let B : ℝ := (N : ℝ) * x ^ (1 - δ)
  have hRatioFirst : 2 * L / (n : ℝ) ≤ ε := by
    have hden : 0 < (n : ℝ) := hnpos
    have hcompare : 2 * L / (n : ℝ) ≤ 4 * L / lo := by
      rw [div_le_div_iff₀ hden hloPos]
      have hloN : lo ≤ 2 * (n : ℝ) := by nlinarith [hnHalf]
      have hnonneg : 0 ≤ 2 * L := by positivity
      have hmul := mul_le_mul_of_nonneg_left hloN hnonneg
      nlinarith
    calc
      2 * L / (n : ℝ) ≤ 4 * L / lo := hcompare
      _ = 4 * (L / lo) := by ring
      _ ≤ ε := by nlinarith [hratioL]
  have hAidentity : A * L ^ 2 = x * (2 * L / (n : ℝ)) := by
    dsimp [A]
    field_simp [ne_of_gt hLpos, hnpos.ne']
  have hAbound : A * L ^ 2 ≤ ε * x := by
    calc
      A * L ^ 2 = x * (2 * L / (n : ℝ)) := hAidentity
      _ ≤ x * ε := mul_le_mul_of_nonneg_left hRatioFirst hxpos.le
      _ = ε * x := by ring
  have hBbound : B * L ^ 2 ≤ ε * x := by
    calc
      B * L ^ 2 = ((N : ℝ) * L ^ 2) * x ^ (1 - δ) := by dsimp [B]; ring
      _ ≤ (ε * x ^ δ) * x ^ (1 - δ) :=
        mul_le_mul_of_nonneg_right hNLog (Real.rpow_nonneg hxpos.le _)
      _ = ε * (x ^ δ * x ^ (1 - δ)) := by ring
      _ = ε * x := by rw [hxPowSplit]
  have hInner : (A + B) * L ^ 2 ≤ (D / C) * x := by
    calc
      (A + B) * L ^ 2 = A * L ^ 2 + B * L ^ 2 := by ring
      _ ≤ ε * x + ε * x := add_le_add hAbound hBbound
      _ = (D / C) * x := by dsimp [ε]; field_simp [hC.ne']; ring
  have hSplitx : ∀ q : ℕ, q.Prime → q₀ ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (3 / 10 : ℝ)) →
        ((splittingConditionSet a x q).ncard : ℝ) ≤
          C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) +
            x ^ (1 - (1 / 1000000 : ℝ))) := by
    intro q hq hqmin hqupper
    exact hSplit x hxSplit q hq hqmin hqupper
  have hRfacts := rFactorExceptions_sum_bound a ha C hC q₀ x hx2 hlog1 hloq₀ hSplitx
  have hR' : ((rFactorExceptions a x).ncard : ℝ) ≤ C * (A + B) := by
    simpa [A, B, L, lo, hi, n, N, θ, β, δ] using hRfacts.2
  have hLsqpos : 0 < L ^ 2 := by positivity
  have hRcount : ((rFactorExceptions a x).ncard : ℝ) ≤ D * x / L ^ 2 := by
    apply (le_div_iff₀ hLsqpos).2
    calc
      ((rFactorExceptions a x).ncard : ℝ) * L ^ 2 ≤ C * (A + B) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hR' (sq_nonneg _)
      _ = C * ((A + B) * L ^ 2) := by ring
      _ ≤ C * ((D / C) * x) := mul_le_mul_of_nonneg_left hInner hC.le
      _ = D * x := by field_simp [hC.ne']
  exact ⟨hRfacts.1, by simpa [L] using hRcount⟩

private noncomputable def low_progression {a : ℤ} {t d : ℕ}
    (hpart : a = Int.sign a * ((t : ℤ) ^ 2 * d)) (hd : Squarefree d)
    (e : ℤ) (he : e = Int.sign a ∧ (e = 1 ∨ e = -1))
    (hnot : ¬ (e = 1 ∧ d = 1)) (hdSmall : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6)
    (haNat0 : a.natAbs ≠ 0) : QuadraticProgression a := by
  classical
  let F := progressionFactors a
  let M : ℕ := 8 * F.prod id
  have hFprime : ∀ l ∈ F, l.Prime := progressionFactors_prime a
  have hFnot2 : ∀ l ∈ F, l ≠ 2 := progressionFactors_ne_two a
  have hRpos : 0 < F.prod id := by
    apply Finset.prod_pos
    intro l hl
    exact (hFprime l hl).pos
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hM8 : 8 ∣ M := by dsimp [M]; exact ⟨F.prod id, rfl⟩
  let choices := exists_low_choice he.2 hdSmall hnot
  let r := Classical.choose choices
  have cExists : ∃ c : ℕ,
      ((c = 2 ∧ (r = 3 ∨ r = 7)) ∨ (c = 4 ∧ r = 5)) ∧
        ((e = -1 ∧ d = 1 ∧ r = 3) ∨
          (e = 1 ∧ d = 2 ∧ r = 3) ∨
          (e = -1 ∧ d = 2 ∧ r = 7) ∨
          (e = 1 ∧ d = 3 ∧ r = 5) ∨
          (e = -1 ∧ d = 3 ∧ r = 5) ∨
          (e = 1 ∧ d = 6 ∧ r = 3) ∨
          (e = -1 ∧ d = 6 ∧ r = 7)) := Classical.choose_spec choices
  let c := Classical.choose cExists
  have hchoice := Classical.choose_spec cExists
  rcases hchoice with ⟨hcr, hsmall⟩
  let b := defaultResidue
  have hrlt : r < 8 := by
    rcases hcr with ⟨_, hr | hr⟩ | ⟨_, hr⟩ <;> omega
  let crt := crt_mod8 hFprime hFnot2 r hrlt b
    (by simpa [F, b] using defaultResidue_lt a)
  let u := Classical.choose crt
  have hcrt := Classical.choose_spec crt
  rcases hcrt with ⟨_, hu8, hul⟩
  let q := (u - 1) / c
  have huEq : u = c * q + 1 := nat_predecessor_eq hcr hu8 rfl
  obtain ⟨hgcd, hcu, hcu'⟩ := crt_progression_data hFprime hFnot2 b
    (defaultResidue_pos a) (defaultResidue_ne_one a) (defaultResidue_lt a)
    hcr hu8 hul huEq
  have hc : c = 2 ∨ c = 4 := by
    rcases hcr with ⟨hc, _⟩ | ⟨hc, _⟩
    · exact Or.inl hc
    · exact Or.inr hc
  refine {
    M := M
    c := c
    u := (u : ℤ)
    hM0 := hMpos
    hM8 := hM8
    hc := hc
    hu := hgcd
    hcu := hcu
    hcu' := hcu'
    primes := ?_
  }
  intro p hp hclass
  letI : Fact p.Prime := ⟨hp⟩
  have hnotdiv : ¬ (p : ℤ) ∣ a := by
    exact prime_in_class_not_dvd haNat0 hgcd hclass hp
  have h8Int : (8 : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hM8
  have hp8I := int_modEq_of_modulus_dvd hclass h8Int
  have hu8I : (u : ℤ) ≡ (r : ℤ) [ZMOD 8] := by exact_mod_cast hu8
  have hp8I := hp8I.trans hu8I
  have hp8Eq : (p : ℤ) % 8 = (r : ℤ) % 8 := by simpa [Int.ModEq] using hp8I
  have hp8 : p % 8 = r := by
    have hp8mod : p % 8 = r % 8 := by exact_mod_cast hp8Eq
    simpa [Nat.mod_eq_of_lt hrlt] using hp8mod
  have h3F : 3 ∈ F := by simp [F, progressionFactors]
  have h3R : 3 ∣ F.prod id := Finset.dvd_prod_of_mem _ h3F
  have h3M : 3 ∣ M := by dsimp [M]; exact dvd_mul_of_dvd_right h3R 8
  have h3Int : (3 : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr h3M
  have hp3I := int_modEq_of_modulus_dvd hclass h3Int
  have hu3Nat : u % 3 = 2 := by
    change (Classical.choose crt) % 3 = 2
    simpa [Nat.ModEq, b, defaultResidue] using hul 3 h3F
  have hu3Eq : (u : ℤ) % 3 = (2 : ℤ) % 3 := by exact_mod_cast hu3Nat
  have hu3I : (u : ℤ) ≡ (2 : ℤ) [ZMOD 3] := by simpa [Int.ModEq] using hu3Eq
  have hp3I := hp3I.trans hu3I
  have hp3Eq : (p : ℤ) % 3 = (2 : ℤ) % 3 := by simpa [Int.ModEq] using hp3I
  have hp3 : p % 3 = 2 := by exact_mod_cast hp3Eq
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    rcases hcr with ⟨_, hr | hr⟩ | ⟨_, hr⟩ <;> omega
  have hsmallP := hsmall
  rw [← hp8] at hsmallP
  have hsmallSym : legendreSym p (e * (d : ℤ)) = -1 :=
    legendre_small_signed_part (e := e) (d := d) hp2 hp3 hsmallP
  have hsym := legendre_square_factor hpart hnotdiv (by simpa [he.1] using hsmallSym)
  exact ⟨hnotdiv, hsym⟩

private noncomputable def high_progression {a : ℤ} {t d j : ℕ}
    (hpart : a = Int.sign a * ((t : ℤ) ^ 2 * d)) (hnat : a.natAbs = t ^ 2 * d)
    (hd : Squarefree d) (e : ℤ) (he : e = Int.sign a ∧ (e = 1 ∨ e = -1))
    (jPrime : j.Prime) (hj5 : 5 ≤ j) (hjd : j ∣ d)
    (haNat0 : a.natAbs ≠ 0) : QuadraticProgression a := by
  classical
  letI : Fact j.Prime := ⟨jPrime⟩
  have hdvdA : d ∣ a.natAbs := by
    refine ⟨t ^ 2, ?_⟩
    calc
      a.natAbs = t ^ 2 * d := hnat
      _ = d * t ^ 2 := Nat.mul_comm _ _
  have hjA : j ∣ a.natAbs := dvd_trans hjd hdvdA
  have hjFactor : j ∈ a.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨jPrime, hjA, haNat0⟩
  let F := progressionFactors a
  let M : ℕ := 8 * F.prod id
  have hFprime : ∀ l ∈ F, l.Prime := progressionFactors_prime a
  have hFnot2 : ∀ l ∈ F, l ≠ 2 := progressionFactors_ne_two a
  have hRpos : 0 < F.prod id := by
    apply Finset.prod_pos
    intro l hl
    exact (hFprime l hl).pos
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hM8 : 8 ∣ M := by dsimp [M]; exact ⟨F.prod id, rfl⟩
  have hjF : j ∈ F := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_erase.mpr ⟨by omega, hjFactor⟩
  let highChoice := choose_high_residue (d := d) (j := j) hd hj5 hjd he.2
  let v := Classical.choose highChoice
  have hvData := Classical.choose_spec highChoice
  rcases hvData with ⟨hvpos, hvlt, hvne, hA, hvchar⟩
  let b : ℕ → ℕ := fun l => if l = j then v else defaultResidue l
  have hbpos : ∀ l ∈ F, 0 < b l := by
    intro l hl
    by_cases hlj : l = j
    · simpa [b, v, hlj] using hvpos
    · simp [b, hlj, defaultResidue_pos a l hl]
  have hbne1 : ∀ l ∈ F, b l ≠ 1 := by
    intro l hl
    by_cases hlj : l = j
    · simpa [b, v, hlj] using hvne
    · simp [b, hlj, defaultResidue_ne_one a l hl]
  have hblt : ∀ l ∈ F, b l < l := by
    intro l hl
    by_cases hlj : l = j
    · simpa [b, v, hlj] using hvlt
    · simpa [b, hlj] using defaultResidue_lt a l hl
  have hcr : (2 = 2 ∧ (3 = 3 ∨ 3 = 7)) ∨ (2 = 4 ∧ 3 = 5) := by simp
  let crt := crt_mod8 hFprime hFnot2 3 (by norm_num) b hblt
  let u := Classical.choose crt
  have hcrt := Classical.choose_spec crt
  rcases hcrt with ⟨-, hu8, hul⟩
  let c : ℕ := 2
  let r : ℕ := 3
  let q : ℕ := (u - 1) / c
  have huEq : u = c * q + 1 := nat_predecessor_eq hcr hu8 rfl
  obtain ⟨hgcd, hcu, hcu'⟩ := crt_progression_data hFprime hFnot2 b
    hbpos hbne1 hblt hcr hu8 hul huEq
  have hc : c = 2 ∨ c = 4 := Or.inl rfl
  refine {
    M := M
    c := c
    u := (u : ℤ)
    hM0 := hMpos
    hM8 := hM8
    hc := hc
    hu := hgcd
    hcu := hcu
    hcu' := hcu'
    primes := ?_
  }
  intro p hp hclass
  letI : Fact p.Prime := ⟨hp⟩
  have hnotdiv : ¬ (p : ℤ) ∣ a := by
    exact prime_in_class_not_dvd haNat0 hgcd hclass hp
  have h8Int : (8 : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hM8
  have hp8I := int_modEq_of_modulus_dvd hclass h8Int
  have hu8I : (u : ℤ) ≡ (3 : ℤ) [ZMOD 8] := by exact_mod_cast hu8
  have hp8I := hp8I.trans hu8I
  have hp8Eq : (p : ℤ) % 8 = (3 : ℤ) % 8 := by simpa [Int.ModEq] using hp8I
  have hp8 : p % 8 = 3 := by exact_mod_cast hp8Eq
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hp8
  have hmodOther : ∀ l ∈ d.primeFactors.erase j, l ≠ 2 →
      (p : ℤ) ≡ (b l : ℤ) [ZMOD l] := by
    intro l hl hl2
    have hlD : l ∈ d.primeFactors := (Finset.mem_erase.mp hl).2
    have hlA : l ∈ a.natAbs.primeFactors :=
      Nat.primeFactors_mono (by
        refine ⟨t ^ 2, ?_⟩
        calc a.natAbs = t ^ 2 * d := hnat
        _ = d * t ^ 2 := Nat.mul_comm _ _) haNat0 hlD
    have hlF : l ∈ F := by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_erase.mpr ⟨hl2, hlA⟩
    have hlR : l ∣ F.prod id := Finset.dvd_prod_of_mem _ hlF
    have hlM : l ∣ M := by dsimp [M]; exact dvd_mul_of_dvd_right hlR 8
    have hlMInt : (l : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hlM
    have hpU := int_modEq_of_modulus_dvd hclass hlMInt
    have huLNat := hul l hlF
    have huLInt : (u : ℤ) ≡ (b l : ℤ) [ZMOD l] := by exact_mod_cast huLNat
    exact hpU.trans huLInt
  have hmodj : (p : ℤ) ≡ (v : ℤ) [ZMOD j] := by
    have hjR : j ∣ F.prod id := Finset.dvd_prod_of_mem _ hjF
    have hjM : j ∣ M := by dsimp [M]; exact dvd_mul_of_dvd_right hjR 8
    have hjMInt : (j : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hjM
    have hpU := int_modEq_of_modulus_dvd hclass hjMInt
    have huJNat : u ≡ v [MOD j] := by
      simpa [b, hjF] using hul j hjF
    have huJInt : (u : ℤ) ≡ (v : ℤ) [ZMOD j] := by exact_mod_cast huJNat
    exact hpU.trans huJInt
  have hsymPart := high_part_legendre hp2 hp8 hd hj5 hjd he.2 b v
    (by intro l hl; simp [b, defaultResidue, (Finset.mem_erase.mp hl).1])
    hmodOther hmodj hA hvchar
  have hsym := legendre_square_factor hpart hnotdiv (by simpa [he.1] using hsymPart)
  exact ⟨hnotdiv, hsym⟩

private noncomputable def quadratic_progression (a : ℤ) (ha : a ≠ -1)
    (ha' : ¬ IsSquare a) : QuadraticProgression a := by
  let squarefreeData := signed_squarefree_part a
  let t := Classical.choose squarefreeData
  have dExists : ∃ d : ℕ,
      a = Int.sign a * ((t : ℤ) ^ 2 * d) ∧ a.natAbs = t ^ 2 * d ∧ Squarefree d :=
    Classical.choose_spec squarefreeData
  let d := Classical.choose dExists
  have hdata := Classical.choose_spec dExists
  rcases hdata with ⟨hpart, hnat, hd⟩
  let e := Int.sign a
  have he : e = 1 ∨ e = -1 := by
    simpa [e] using sign_eq_one_or_neg_one_of_not_square ha'
  have heData : e = Int.sign a ∧ (e = 1 ∨ e = -1) := ⟨rfl, he⟩
  have hnot : ¬ (e = 1 ∧ d = 1) := by
    rintro ⟨heq, hd1⟩
    apply ha'
    exact square_of_positive_sign_part_one (by simpa [e] using heq) hpart hd1
  have haNat0 := natAbs_ne_zero_of_admissible a ha ha'
  have hcases := squarefree_part_cases hd
  by_cases hlarge : ∃ j : ℕ, j.Prime ∧ 5 ≤ j ∧ j ∣ d
  · let j := Classical.choose hlarge
    have hjData := Classical.choose_spec hlarge
    have hj : j.Prime := hjData.1
    have hj5 : 5 ≤ j := hjData.2.1
    have hjd : j ∣ d := hjData.2.2
    letI : Fact j.Prime := ⟨hj⟩
    exact high_progression hpart hnat hd e heData hj hj5 hjd haNat0
  · have hdSmall : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
      rcases hcases with h1 | h2 | h3 | h6 | hh
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr h6))
      · exact (hlarge hh).elim
    exact low_progression hpart hd e heData hnot hdSmall haNat0

/-- **Theorem `thm:main`.** For every integer `a` that is neither `-1` nor a square there are
`c_a > 0` and `x_a ≥ 2` such that for every real `x ≥ x_a`, at least `c_a x / (log x)²` primes
`p ∈ (x, 2x)` with `p ∤ a` have `a` as a primitive root. -/
theorem thm_main (a : ℤ) (ha : a ≠ -1) (ha' : ¬ IsSquare a) :
    ∃ c : ℝ, 0 < c ∧ ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      c * x / Real.log x ^ 2 ≤
        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ ¬ (p : ℤ) ∣ a ∧
            orderOf (a : ZMod p) = p - 1} : Set ℕ).ncard : ℝ) := by
  classical
  have haAbs := abs_gt_one_of_admissible a ha ha'
  let G := quadratic_progression a ha ha'
  obtain ⟨C₀, hC₀, Xc, hcontrolled⟩ :=
    prop_controlled G.M G.hM0 G.hM8 G.c G.hc G.u G.hu G.hcu G.hcu'
  obtain ⟨Cs, hCs, q₀, Xs, hSplit⟩ := prop_splitting a haAbs
  obtain ⟨Xq, hQerr⟩ := q_factor_error_eventually a haAbs (C₀ / 4) (by positivity)
  obtain ⟨Xr, hRerr⟩ :=
    r_factor_error_eventually a haAbs Cs hCs q₀ Xs hSplit (C₀ / 4) (by positivity)
  let X : ℝ := max Xc (max Xq (max Xr 2))
  have hXc : Xc ≤ X := by dsimp [X]; exact le_max_left _ _
  have hXq : Xq ≤ X := by
    dsimp [X]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hXr : Xr ≤ X := by
    dsimp [X]
    exact le_trans (le_max_left _ _) <| le_trans (le_max_right _ _) (le_max_right _ _)
  have hX2 : 2 ≤ X := by
    dsimp [X]
    exact le_trans (le_max_right _ _) <| le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C₀ / 2, by positivity, X, hX2, ?_⟩
  intro x hx
  have hxC : Xc ≤ x := le_trans hXc hx
  have hxQ : Xq ≤ x := le_trans hXq hx
  have hxR : Xr ≤ x := le_trans hXr hx
  have hx2 : 2 ≤ x := le_trans hX2 hx
  have hTlower0 := hcontrolled x hxC
  let T := controlledIntervalPrimes x G.M G.c G.u
  let P := targetIntervalPrimes a x
  let Q := qFactorExceptions a x
  let R := rFactorExceptions a x
  let E := Q ∪ R
  have hTlower : C₀ * x / Real.log x ^ 2 ≤ (T.ncard : ℝ) := by
    simpa [T, controlledIntervalPrimes] using hTlower0
  have hQfacts := hQerr x hxQ
  have hQfinite : Q.Finite := by simpa [Q] using hQfacts.1
  have hQsmall : (Q.ncard : ℝ) ≤ (C₀ / 4) * x / Real.log x ^ 2 := by
    simpa [Q] using hQfacts.2
  have hRfacts := hRerr x hxR
  have hRfinite : R.Finite := by simpa [R] using hRfacts.1
  have hRsmall : (R.ncard : ℝ) ≤ (C₀ / 4) * x / Real.log x ^ 2 := by
    simpa [R] using hRfacts.2
  obtain ⟨B, hB⟩ := exists_nat_gt (2 * x)
  have hTbound : T ⊆ Set.Iio B := by
    intro p hp
    rcases hp with ⟨hpPrime, hpx, hp2x, hclass, r, q, hfactor, hq, hqbig, hrpos, hR⟩
    change p < B
    exact_mod_cast lt_trans hp2x hB
  have hTfinite : T.Finite := (Set.finite_Iio B).subset hTbound
  have hPbound : P ⊆ Set.Iio B := by
    intro p hp
    rcases hp with ⟨hpPrime, hpx, hp2x, hnot, horder⟩
    change p < B
    exact_mod_cast lt_trans hp2x hB
  have hPfinite : P.Finite := (Set.finite_Iio B).subset hPbound
  have hEfinite : E.Finite := hQfinite.union hRfinite
  have hUnionFinite : (P ∪ E).Finite := hPfinite.union hEfinite
  have hTsubset : T ⊆ P ∪ E := by
    intro p hp
    have hpMem := hp
    rcases hp with ⟨hpPrime, hpx, hp2x, hclass, r, q, hfactor, hq, hqbig, hrpos, hR⟩
    by_cases horder : orderOf (a : ZMod p) = p - 1
    · rcases G.primes p hpPrime hclass with ⟨hnot, hlegendre⟩
      exact Or.inl ⟨hpPrime, hpx, hp2x, hnot, horder⟩
    · rcases controlled_nonprimitive_exception G hx2 hpMem horder with hqExc | hrExc
      · exact Or.inr (Or.inl hqExc)
      · exact Or.inr (Or.inr hrExc)
  have hTnat : T.ncard ≤ P.ncard + (Q.ncard + R.ncard) := by
    calc
      T.ncard ≤ (P ∪ E).ncard := Set.ncard_le_ncard hTsubset hUnionFinite
      _ ≤ P.ncard + E.ncard := Set.ncard_union_le P E
      _ ≤ P.ncard + (Q.ncard + R.ncard) :=
        Nat.add_le_add_left (Set.ncard_union_le Q R) P.ncard
  have hTreal : (T.ncard : ℝ) ≤ (P.ncard : ℝ) + ((Q.ncard : ℝ) + (R.ncard : ℝ)) := by
    exact_mod_cast hTnat
  have hLowerCombined : C₀ * x / Real.log x ^ 2 ≤
      (P.ncard : ℝ) + ((Q.ncard : ℝ) + (R.ncard : ℝ)) := hTlower.trans hTreal
  have hLoss : (Q.ncard : ℝ) + (R.ncard : ℝ) ≤
      (C₀ / 2) * x / Real.log x ^ 2 := by
    calc
      (Q.ncard : ℝ) + (R.ncard : ℝ) ≤
          (C₀ / 4) * x / Real.log x ^ 2 + (C₀ / 4) * x / Real.log x ^ 2 :=
        add_le_add hQsmall hRsmall
      _ = (C₀ / 2) * x / Real.log x ^ 2 := by ring
  have hPrimitiveCount : (C₀ / 2) * x / Real.log x ^ 2 ≤ (P.ncard : ℝ) := by
    have hscale : C₀ * x / Real.log x ^ 2 =
        2 * ((C₀ / 2) * x / Real.log x ^ 2) := by ring
    nlinarith [hLowerCombined, hLoss, hscale]
  simpa [P, targetIntervalPrimes] using hPrimitiveCount

end ArtinPrimitiveRoots
