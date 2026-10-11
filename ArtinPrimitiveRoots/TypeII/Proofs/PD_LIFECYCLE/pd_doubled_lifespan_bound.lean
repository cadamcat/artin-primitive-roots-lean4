import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_prime_lifespan_data
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_active_run_count

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

private lemma pdLifeDouble_sum_subtype {α β : Type*} [AddCommMonoid β]
    (T : Finset α) (f : α → β) :
    (∑ x : {x // x ∈ T}, f x.1) = ∑ x ∈ T, f x := by
  classical
  have hAttach : T.attach = (Finset.univ : Finset {x // x ∈ T}) := by
    ext x
    simp
  rw [← hAttach]
  exact Finset.sum_attach (s := T) (f := f)

private lemma pdLifeDouble_prod_subtype {α β : Type*} [CommMonoid β]
    (T : Finset α) (f : α → β) :
    (∏ x : {x // x ∈ T}, f x.1) = ∏ x ∈ T, f x := by
  classical
  have hAttach : T.attach = (Finset.univ : Finset {x // x ∈ T}) := by
    ext x
    simp
  rw [← hAttach]
  exact Finset.prod_attach (s := T) (f := f)

private lemma pdLifeDouble_finiteRankGeomBound {α : Type*} [LinearOrder α]
    [DecidableEq α] (T : Finset α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ c ∈ T, q ^ (T.filter (fun b => b < c)).card) ≤ (1 - q)⁻¹ := by
  classical
  let rank : α → ℕ := fun c => (T.filter (fun b => b < c)).card
  have hrankInj : ∀ a ∈ T, ∀ b ∈ T, rank a = rank b → a = b := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab' | hba'
    · have hsub : T.filter (fun c => c < a) ⊂ T.filter (fun c => c < b) := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro c hc
          rcases Finset.mem_filter.mp hc with ⟨hcT, hca⟩
          exact Finset.mem_filter.mpr ⟨hcT, hca.trans hab'⟩
        · intro heq
          have haB : a ∈ T.filter (fun c => c < b) :=
            Finset.mem_filter.mpr ⟨ha, hab'⟩
          have haA : a ∈ T.filter (fun c => c < a) := by
            rw [← heq] at haB
            exact haB
          exact (lt_irrefl a) (Finset.mem_filter.mp haA).2
      have hlt : rank a < rank b := Finset.card_lt_card hsub
      exact (Nat.ne_of_lt hlt) hab
    · have hsub : T.filter (fun c => c < b) ⊂ T.filter (fun c => c < a) := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro c hc
          rcases Finset.mem_filter.mp hc with ⟨hcT, hcb⟩
          exact Finset.mem_filter.mpr ⟨hcT, hcb.trans hba'⟩
        · intro heq
          have hbA : b ∈ T.filter (fun c => c < a) :=
            Finset.mem_filter.mpr ⟨hb, hba'⟩
          have hbB : b ∈ T.filter (fun c => c < b) := by
            rw [← heq] at hbA
            exact hbA
          exact (lt_irrefl b) (Finset.mem_filter.mp hbB).2
      have hlt : rank b < rank a := Finset.card_lt_card hsub
      exact (Nat.ne_of_lt hlt) hab.symm
  have hrankLt (c : α) (hc : c ∈ T) : rank c < T.card := by
    have hsub : T.filter (fun b => b < c) ⊂ T := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · exact Finset.filter_subset _ _
      · intro heq
        have hc' : c ∈ T.filter (fun b => b < c) := by
          rw [← heq] at hc
          exact hc
        exact (lt_irrefl c) (Finset.mem_filter.mp hc').2
    exact Finset.card_lt_card hsub
  let R := T.image rank
  have hRsub : R ⊆ Finset.range T.card := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨c, hc, rfl⟩
    exact Finset.mem_range.mpr (hrankLt c hc)
  have hImage : (∑ n ∈ R, q ^ n) = ∑ c ∈ T, q ^ rank c := by
    exact Finset.sum_image hrankInj
  have hRange :
      (∑ n ∈ Finset.range T.card, q ^ n) ≤ (1 - q)⁻¹ := by
    have hqne : q ≠ 1 := ne_of_lt hq1
    have hden : 0 < 1 - q := by linarith
    calc
      _ = (q ^ T.card - 1) / (q - 1) := geom_sum_eq hqne _
      _ = (1 - q ^ T.card) / (1 - q) := by
        field_simp [hqne, ne_of_gt hden] <;> ring
      _ ≤ (1 - q)⁻¹ := by
        apply (div_le_iff₀ hden).2
        rw [inv_mul_cancel₀ (ne_of_gt hden)]
        have hpow : 0 ≤ q ^ T.card := pow_nonneg hq0 _
        nlinarith
  calc
    _ = ∑ n ∈ R, q ^ n := hImage.symm
    _ ≤ ∑ n ∈ Finset.range T.card, q ^ n :=
      Finset.sum_le_sum_of_subset_of_nonneg hRsub (fun n hn hnR => pow_nonneg hq0 _)
    _ ≤ (1 - q)⁻¹ := hRange

private def pdLifeDoubleOrphanEndpointTerm {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ)
    (e : Option (Fin (pathLength S.x + 1)) × Option (Fin (pathLength S.x + 1))) : ℝ :=
  let d := (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹
  match e with
  | (none, none) => 1
  | (some a, some c) =>
      if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
        2 * d * memoryEta S.x F.q_d a.val * memoryEta S.x F.q_d c.val *
          ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
            pdLifeSurvival F S γ p (projLine p (γ a).1) j
      else 0
  | _ => 0

private def pdLifeDoubleInactiveChargeRaw {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ)
    (e : Option (Fin (pathLength S.x + 1)) × Option (Fin (pathLength S.x + 1))) : ℝ :=
  let d := (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹
  match e with
  | (none, none) => 1
  | (some a, some c) =>
      d * memoryEta S.x F.q_d a.val * memoryEta S.x F.q_d c.val *
        ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
          pdLifeSurvival F S γ p (projLine p (γ a).1) j
  | _ => 0

private lemma pdLifeDoubleRuns_pos {K : ℕ} (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (hactive : ∃ j, IsActiveAt γ p j) :
    1 ≤ pdActiveRuns S γ p := by
  classical
  let A : Finset (Fin (pathLength S.x + 1)) :=
    Finset.univ.filter (IsActiveAt γ p)
  have hA : A.Nonempty := by
    rcases hactive with ⟨j, hj⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let j₀ := A.min' hA
  have hj₀A : j₀ ∈ A := Finset.min'_mem A hA
  have hstart : IsActiveAt γ p j₀ ∧
      ¬ ∃ k : Fin (pathLength S.x + 1), k.val + 1 = j₀.val ∧ IsActiveAt γ p k := by
    refine ⟨(Finset.mem_filter.mp hj₀A).2, ?_⟩
    rintro ⟨k, hk, hactiveK⟩
    have hkA : k ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactiveK⟩
    have hmin := Finset.min'_le A k hkA
    have hval : j₀.val ≤ k.val := Fin.le_iff_val_le_val.mp hmin
    omega
  unfold pdActiveRuns
  apply Nat.succ_le_iff.mpr
  exact Finset.card_pos.mpr ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstart⟩⟩

private lemma pdLifeDouble_q_bounds {x q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (j : ℕ) : 0 ≤ memoryQ x q j ∧ memoryQ x q j ≤ 1 := by
  unfold memoryQ
  split_ifs
  · exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hq1.le⟩
  · exact ⟨hq0.le, hq1.le⟩

private lemma pdLifeDouble_survival_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (lam : Fin (p + 1))
    (hq0 : 0 < F.q_d) (hq1 : F.q_d < 1) (j : Fin (pathLength S.x + 1)) :
    0 ≤ pdLifeSurvival F S γ p lam j ∧ pdLifeSurvival F S γ p lam j ≤ 1 := by
  by_cases hhit : projLine p (γ j).1 = lam
  · simpa [pdLifeSurvival, hhit, memoryEta] using
      pdLifeDouble_q_bounds hq0 hq1 j.val
  · simp [pdLifeSurvival, hhit]

private lemma pdLifeDouble_internal_q_le_sqrt {x q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (j : Fin (pathLength x + 1)) (hj0 : 0 < j.val) (hjN : j.val < pathLength x) :
    memoryQ x q j.val ≤ Real.sqrt q := by
  have hqbar := Real.sqrt_nonneg q
  have hqbar1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1.le
  have hqbarSq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0.le
  have hpow : 0 ≤ Real.sqrt q * (1 - Real.sqrt q) :=
    mul_nonneg hqbar (by linarith)
  have hqle : q ≤ Real.sqrt q := by nlinarith [hqbarSq, hpow]
  have hnot : ¬ (j.val = 0 ∨ j.val = pathLength x) := by omega
  unfold memoryQ
  rw [if_neg hnot]
  exact hqle

private lemma pdLifeDouble_mul_le_one {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : a * b ≤ 1 := by
  calc
    a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha1 hb0
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb1 (by norm_num)
    _ = 1 := by ring

private lemma pdLifeDouble_active_charge_abs_le_one {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (i : Fin K)
    (hpi : p ∈ primeBand S.x (F.a i))
    (hbp : 1 / 2 ≤ memoryBPrime S.x F.q_d p)
    (hqd0 : 0 < F.q_d) (hqd1 : F.q_d < 1)
    (hA : (pdLifeActive S γ p).Nonempty) (life : PrimeLife S γ p) :
    |primeLifeCharge F S γ p life| ≤ 1 := by
  classical
  let A := pdLifeActive S γ p
  let α := A.min' hA
  let ω := A.max' hA
  let lam := projLine p (γ α).1
  let d : ℝ := (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹
  let mid : ℝ := ∏ j ∈ Finset.univ.filter (fun j =>
    α < j ∧ j < ω ∧ j ∉ A), pdLifeSurvival F S γ p lam j
  let pre (e : Option (Fin (pathLength S.x + 1))) : ℝ :=
    match e with
    | none => 1
    | some a => -memoryEta S.x F.q_d a.val *
        ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < α),
          pdLifeSurvival F S γ p lam j
  let post (e : Option (Fin (pathLength S.x + 1))) : ℝ :=
    match e with
    | none => 1
    | some c => -memoryEta S.x F.q_d c.val *
        ∏ j ∈ Finset.univ.filter (fun j => ω < j ∧ j < c),
          pdLifeSurvival F S γ p lam j
  have hbp0 : 0 < memoryBPrime S.x F.q_d p := by linarith
  have hpPrime : p.Prime := (Finset.mem_filter.mp hpi).2.1
  have hpLower : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
  have hpplus : 0 < (p : ℝ) + 1 := by positivity
  have hden0 : 0 < ((p : ℝ) + 1) * memoryBPrime S.x F.q_d p :=
    mul_pos hpplus hbp0
  have hden1 : 1 ≤ ((p : ℝ) + 1) * memoryBPrime S.x F.q_d p := by
    nlinarith
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    change (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹ ≤ 1
    exact (inv_le_one₀ hden0).2 hden1
  have hqBounds (j : ℕ) :
      0 ≤ memoryQ S.x F.q_d j ∧ memoryQ S.x F.q_d j ≤ 1 :=
    pdLifeDouble_q_bounds hqd0 hqd1 j
  have hetaBounds (j : ℕ) :
      0 ≤ memoryEta S.x F.q_d j ∧ memoryEta S.x F.q_d j ≤ 1 := by
    rw [memoryEta]
    constructor <;> linarith [(hqBounds j).1, (hqBounds j).2]
  have hsurvBounds (j : Fin (pathLength S.x + 1)) :
      0 ≤ pdLifeSurvival F S γ p lam j ∧ pdLifeSurvival F S γ p lam j ≤ 1 :=
    pdLifeDouble_survival_bounds F S γ p lam hqd0 hqd1 j
  have hprodBounds (T : Finset (Fin (pathLength S.x + 1))) :
      0 ≤ (∏ j ∈ T, pdLifeSurvival F S γ p lam j) ∧
        (∏ j ∈ T, pdLifeSurvival F S γ p lam j) ≤ 1 := by
    constructor
    · apply Finset.prod_nonneg
      intro j hj
      exact (hsurvBounds j).1
    · apply Finset.prod_le_one₀
      · intro j hj
        exact (hsurvBounds j).1
      · intro j hj
        exact (hsurvBounds j).2
  have hMin_irrel (hAct : A.Nonempty) : A.min' hAct = α := by rfl
  have hMax_irrel (hAct : A.Nonempty) : A.max' hAct = ω := by rfl
  have hpre (e : Option (Fin (pathLength S.x + 1))) : |pre e| ≤ 1 := by
    cases e with
    | none => simp [pre]
    | some a =>
      have he := hetaBounds a.val
      have hp := hprodBounds (Finset.univ.filter (fun j => a < j ∧ j < α))
      simp only [pre]
      rw [abs_mul, abs_neg, abs_of_nonneg he.1, abs_of_nonneg hp.1]
      exact pdLifeDouble_mul_le_one he.1 he.2 hp.1 hp.2
  have hpost (e : Option (Fin (pathLength S.x + 1))) : |post e| ≤ 1 := by
    cases e with
    | none => simp [post]
    | some c =>
      have he := hetaBounds c.val
      have hp := hprodBounds (Finset.univ.filter (fun j => ω < j ∧ j < c))
      simp only [post]
      rw [abs_mul, abs_neg, abs_of_nonneg he.1, abs_of_nonneg hp.1]
      exact pdLifeDouble_mul_le_one he.1 he.2 hp.1 hp.2
  have hmid := hprodBounds (Finset.univ.filter (fun j =>
    α < j ∧ j < ω ∧ j ∉ A))
  have hCharge :
      primeLifeCharge F S γ p life = d * pre life.1.1 * mid * post life.1.2 := by
    simp [primeLifeCharge, A, α, ω, lam, d, pre, mid, post, hA,
      hMin_irrel, hMax_irrel] <;> rfl
  have hdabs : |d| ≤ 1 := by simpa [abs_of_nonneg hd0] using hd1
  have hmid' : 0 ≤ mid ∧ mid ≤ 1 := by simpa [mid] using hmid
  have hmidabs : |mid| ≤ 1 := by simpa [abs_of_nonneg hmid'.1] using hmid'.2
  have hpabs := hpre life.1.1
  have hcabs := hpost life.1.2
  have hdp0 : 0 ≤ |d| * |pre life.1.1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hdp1 : |d| * |pre life.1.1| ≤ 1 :=
    pdLifeDouble_mul_le_one (abs_nonneg _) hdabs (abs_nonneg _) hpabs
  have hdpMid0 : 0 ≤ |d| * |pre life.1.1| * |mid| :=
    mul_nonneg hdp0 (abs_nonneg _)
  have hdpMid1 : |d| * |pre life.1.1| * |mid| ≤ 1 :=
    pdLifeDouble_mul_le_one hdp0 hdp1 (abs_nonneg _) hmidabs
  calc
    |primeLifeCharge F S γ p life| =
        |d| * |pre life.1.1| * |mid| * |post life.1.2| := by
          rw [hCharge]
          simp only [abs_mul]
    _ ≤ 1 := pdLifeDouble_mul_le_one hdpMid0 hdpMid1
      (abs_nonneg _) hcabs

private lemma pdLifeDouble_orphan_sum_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (i : Fin K)
    (hpi : p ∈ primeBand S.x (F.a i))
    (hbp : 1 / 2 ≤ memoryBPrime S.x F.q_d p)
    (hqd0 : 0 < F.q_d) (hqd1 : F.q_d < 1)
    (hAempty : ¬ (pdLifeActive S γ p).Nonempty) :
    (∑ life : PrimeLife S γ p,
      (if life.1.1.isSome then 2 else 1) * |primeLifeCharge F S γ p life|) ≤
      1 + 4 * ((pathLength S.x : ℝ) + 1) /
        (1 - Real.sqrt F.q_d) / ((p : ℝ) + 1) := by
  classical
  let J := Fin (pathLength S.x + 1)
  let qbar := Real.sqrt F.q_d
  let Uq := (1 - qbar)⁻¹
  let d := (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹
  let G : Option J × Option J → ℝ := pdLifeDoubleOrphanEndpointTerm F S γ p
  have hqbar0 : 0 < qbar := by dsimp [qbar]; exact Real.sqrt_pos.2 hqd0
  have hqbar1 : qbar < 1 := by
    dsimp [qbar]
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2 (by nlinarith)
  have hUq0 : 0 < Uq := by dsimp [Uq]; positivity
  have hEta (j : ℕ) :
      0 ≤ memoryEta S.x F.q_d j ∧ memoryEta S.x F.q_d j ≤ 1 := by
    have hq := pdLifeDouble_q_bounds (x := S.x) (q := F.q_d) hqd0 hqd1 j
    rw [memoryEta]
    constructor <;> linarith
  have hSurv (lam : Fin (p + 1)) (j : J) :
      0 ≤ pdLifeSurvival F S γ p lam j ∧ pdLifeSurvival F S γ p lam j ≤ 1 :=
    pdLifeDouble_survival_bounds F S γ p lam hqd0 hqd1 j
  have hProdNonneg (lam : Fin (p + 1)) (T : Finset J) :
      0 ≤ ∏ j ∈ T, pdLifeSurvival F S γ p lam j := by
    apply Finset.prod_nonneg
    intro j hj
    exact (hSurv lam j).1
  have hqbarle : F.q_d ≤ qbar := by
    have hsq : (Real.sqrt F.q_d) ^ 2 = F.q_d := Real.sq_sqrt hqd0.le
    have hfactor : 0 ≤ Real.sqrt F.q_d * (1 - Real.sqrt F.q_d) :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith [hqbar1])
    nlinarith [hsq, hfactor]
  have hInternalProd (a c : J) (hac : a < c)
      (hlc : projLine p (γ c).1 = projLine p (γ a).1) :
      (∏ j ∈ Finset.univ.filter (fun j : J => a < j ∧ j < c),
          pdLifeSurvival F S γ p (projLine p (γ a).1) j) ≤
        qbar ^ ((Finset.univ.filter (fun b : J => a < b ∧
          projLine p (γ b).1 = projLine p (γ a).1)).filter (fun b => b < c)).card := by
    let I : Finset J := Finset.univ.filter (fun j => a < j ∧ j < c)
    let T : Finset J := Finset.univ.filter (fun b =>
      a < b ∧ projLine p (γ b).1 = projLine p (γ a).1)
    have hHitSet : I.filter (fun j => projLine p (γ j).1 = projLine p (γ a).1) =
        T.filter (fun b => b < c) := by
      ext j
      simp [I, T, and_assoc, and_left_comm, and_comm]
    have hFactor (j : J) (hj : j ∈ I) :
        pdLifeSurvival F S γ p (projLine p (γ a).1) j ≤
          if projLine p (γ j).1 = projLine p (γ a).1 then qbar else 1 := by
      have hjI := Finset.mem_filter.mp hj
      have htime : 0 < j.val ∧ j.val < pathLength S.x := by
        have haVal : a.val < j.val := Fin.lt_iff_val_lt_val.mp hjI.2.1
        have hcVal : j.val < c.val := Fin.lt_iff_val_lt_val.mp hjI.2.2
        have hcBound : c.val ≤ pathLength S.x := by
          have := c.isLt
          omega
        constructor <;> omega
      by_cases hhit : projLine p (γ j).1 = projLine p (γ a).1
      · have hq := pdLifeDouble_internal_q_le_sqrt (x := S.x) (q := F.q_d)
          hqd0 hqd1 j htime.1 htime.2
        have hsurv :
            pdLifeSurvival F S γ p (projLine p (γ a).1) j = memoryQ S.x F.q_d j.val := by
          simp [pdLifeSurvival, memoryEta, hhit]
        rw [hsurv]
        simpa [hhit, qbar] using hq
      · simpa [pdLifeSurvival, hhit]
    have hprodle :
        (∏ j ∈ I, pdLifeSurvival F S γ p (projLine p (γ a).1) j) ≤
          ∏ j ∈ I, (if projLine p (γ j).1 = projLine p (γ a).1 then qbar else 1) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact (hSurv (projLine p (γ a).1) j).1
      · intro j hj
        exact hFactor j hj
    have hprodQ :
        (∏ j ∈ I, (if projLine p (γ j).1 = projLine p (γ a).1 then qbar else 1)) =
          qbar ^ (I.filter (fun j => projLine p (γ j).1 = projLine p (γ a).1)).card := by
      rw [Finset.prod_ite]
      simp <;> rfl
    have hprodT :
        (∏ j ∈ I, pdLifeSurvival F S γ p (projLine p (γ a).1) j) ≤
          qbar ^ (T.filter (fun b => b < c)).card := by
      calc
        _ ≤ ∏ j ∈ I,
              (if projLine p (γ j).1 = projLine p (γ a).1 then qbar else 1) := hprodle
        _ = qbar ^ (I.filter (fun j => projLine p (γ j).1 = projLine p (γ a).1)).card := hprodQ
        _ = qbar ^ (T.filter (fun b => b < c)).card := by rw [hHitSet]
    simpa [I, T] using hprodT
  have hEtaSum :
      (∑ a : J, memoryEta S.x F.q_d a.val) ≤ ((pathLength S.x + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ a : J, (1 : ℝ) := Finset.sum_le_sum fun a ha => (hEta a.val).2
      _ = ((pathLength S.x + 1 : ℕ) : ℝ) := by simp [J]
  have hpPrime : p.Prime := (Finset.mem_filter.mp hpi).2.1
  have hpLower : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
  have hpplus : 0 < (p : ℝ) + 1 := by positivity
  have hbp0 : 0 < memoryBPrime S.x F.q_d p := by linarith
  have hden0 : 0 < ((p : ℝ) + 1) * memoryBPrime S.x F.q_d p :=
    mul_pos hpplus hbp0
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hdOrphan : d ≤ 2 / ((p : ℝ) + 1) := by
    dsimp [d]
    rw [← one_div (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)]
    rw [div_le_iff₀ hden0]
    field_simp [hpplus.ne']
    nlinarith [hbp]
  have hEndpointEmpty (e : Option J × Option J) :
      pdLifeEndpointValid S γ p e ↔
        match e with
        | (none, none) => True
        | (some a, some c) => a < c ∧ projLine p (γ c).1 = projLine p (γ a).1
        | _ => False := by
    by_cases hAct : (pdLifeActive S γ p).Nonempty
    · exact (hAempty hAct).elim
    · have hAct' : ¬ (Finset.univ.filter (IsActiveAt γ p)).Nonempty := by
        simpa [pdLifeActive] using hAct
      simp [pdLifeEndpointValid, pdLifeActive, hAct']
      cases e with
      | mk birth delete => cases birth <;> cases delete <;> simp
  have hChargeRaw (e : Option J × Option J) (he : e ∈ pdLifeEndpoints S γ p) :
      primeLifeCharge F S γ p ⟨e, he⟩ =
        pdLifeDoubleInactiveChargeRaw F S γ p e := by
    by_cases hAct : (pdLifeActive S γ p).Nonempty
    · exact (hAempty hAct).elim
    · have hAct' : ¬ (Finset.univ.filter (IsActiveAt γ p)).Nonempty := by
        simpa [pdLifeActive] using hAct
      simp [primeLifeCharge, pdLifeActive, hAct', pdLifeDoubleInactiveChargeRaw] <;> rfl
  have hLifeTerm (life : PrimeLife S γ p) :
      (if life.1.1.isSome then 2 else 1) * |primeLifeCharge F S γ p life| =
        G life.1 := by
    rcases life with ⟨e, he⟩
    change e ∈ Finset.univ.filter (pdLifeEndpointValid S γ p) at he
    have hv := (Finset.mem_filter.mp he).2
    have hcharge := hChargeRaw e (by change e ∈ pdLifeEndpoints S γ p; exact he)
    cases e with
    | mk birth delete =>
        cases birth with
        | none =>
            cases delete with
            | none =>
                rw [hcharge]
                simp [G, pdLifeDoubleOrphanEndpointTerm, pdLifeDoubleInactiveChargeRaw]
            | some c =>
                exact False.elim ((hEndpointEmpty (none, some c)).mp hv)
        | some a =>
            cases delete with
            | none =>
                exact False.elim ((hEndpointEmpty (some a, none)).mp hv)
            | some c =>
                have hends := (hEndpointEmpty (some a, some c)).mp hv
                have ha := hEta a.val
                have hc := hEta c.val
                have hprod0 := hProdNonneg (projLine p (γ a).1)
                  (Finset.univ.filter (fun j => a < j ∧ j < c))
                have hcharge0 :
                    0 ≤ pdLifeDoubleInactiveChargeRaw F S γ p (some a, some c) := by
                  change 0 ≤ (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹ *
                      memoryEta S.x F.q_d a.val * memoryEta S.x F.q_d c.val *
                      ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                        pdLifeSurvival F S γ p (projLine p (γ a).1) j
                  exact mul_nonneg
                    (mul_nonneg (mul_nonneg (inv_nonneg.mpr hden0.le) ha.1) hc.1) hprod0
                rw [hcharge, abs_of_nonneg hcharge0]
                simp [G, pdLifeDoubleOrphanEndpointTerm,
                  pdLifeDoubleInactiveChargeRaw, hends] <;> ring
  have hGzero (e : Option J × Option J) (he : e ∉ pdLifeEndpoints S γ p) : G e = 0 := by
    change e ∉ Finset.univ.filter (pdLifeEndpointValid S γ p) at he
    cases e with
    | mk birth delete =>
        cases birth with
        | none =>
            cases delete with
            | none =>
                have hv := (hEndpointEmpty (none, none)).mpr trivial
                have hem : (none, none) ∈ Finset.univ.filter (pdLifeEndpointValid S γ p) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
                exact False.elim (he hem)
            | some c => simp [G, pdLifeDoubleOrphanEndpointTerm]
        | some a =>
            cases delete with
            | none => simp [G, pdLifeDoubleOrphanEndpointTerm]
            | some c =>
                by_cases hends : a < c ∧ projLine p (γ c).1 = projLine p (γ a).1
                · have hv := (hEndpointEmpty (some a, some c)).mpr hends
                  have hem : (some a, some c) ∈ Finset.univ.filter (pdLifeEndpointValid S γ p) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
                  exact False.elim (he hem)
                · simp [G, pdLifeDoubleOrphanEndpointTerm, hends]
  have hSumEndpoint :
      (∑ life : PrimeLife S γ p,
        (if life.1.1.isSome then 2 else 1) * |primeLifeCharge F S γ p life|) =
        ∑ e : Option J × Option J, G e := by
    calc
      _ = ∑ life : PrimeLife S γ p, G life.1 := by
        apply Finset.sum_congr rfl
        intro life hlife
        exact hLifeTerm life
      _ = ∑ e ∈ pdLifeEndpoints S γ p, G e :=
        pdLifeDouble_sum_subtype (pdLifeEndpoints S γ p) G
      _ = ∑ e : Option J × Option J, G e := by
        apply Finset.sum_subset (Finset.subset_univ (pdLifeEndpoints S γ p))
        intro e he he'
        exact hGzero e he'
  have hOptionExpand :
      (∑ e : Option J × Option J, G e) =
        1 + ∑ a : J, ∑ c : J,
          if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
            2 * d * memoryEta S.x F.q_d a.val * memoryEta S.x F.q_d c.val *
              ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                pdLifeSurvival F S γ p (projLine p (γ a).1) j
          else 0 := by
    rw [Fintype.sum_prod_type]
    simp [Fintype.sum_option, G, pdLifeDoubleOrphanEndpointTerm, d] <;> rfl
  have hTailSum (a : J) :
      (∑ c : J,
        if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
          memoryEta S.x F.q_d c.val *
            ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
              pdLifeSurvival F S γ p (projLine p (γ a).1) j
        else 0) ≤ Uq := by
    let T : Finset J := Finset.univ.filter fun c =>
      a < c ∧ projLine p (γ c).1 = projLine p (γ a).1
    have hTailEq :
        (∑ c : J,
          if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
            memoryEta S.x F.q_d c.val *
              ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                pdLifeSurvival F S γ p (projLine p (γ a).1) j
          else 0) =
        ∑ c ∈ T, memoryEta S.x F.q_d c.val *
          ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
            pdLifeSurvival F S γ p (projLine p (γ a).1) j := by
      change (∑ c ∈ (Finset.univ : Finset J),
          if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
            memoryEta S.x F.q_d c.val *
              ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                pdLifeSurvival F S γ p (projLine p (γ a).1) j
          else 0) = _
      rw [← Finset.sum_filter]
    calc
      _ = ∑ c ∈ T, memoryEta S.x F.q_d c.val *
            ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
              pdLifeSurvival F S γ p (projLine p (γ a).1) j := hTailEq
      _ ≤ ∑ c ∈ T, qbar ^ (T.filter (fun b => b < c)).card := by
        apply Finset.sum_le_sum
        intro c hc
        rcases (Finset.mem_filter.mp hc).2 with ⟨hac, hline⟩
        have hprod := hInternalProd a c hac hline
        have hprod0 := hProdNonneg (projLine p (γ a).1)
          (Finset.univ.filter (fun j => a < j ∧ j < c))
        calc
          memoryEta S.x F.q_d c.val *
              ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                pdLifeSurvival F S γ p (projLine p (γ a).1) j
              ≤ 1 * ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                  pdLifeSurvival F S γ p (projLine p (γ a).1) j :=
                    mul_le_mul_of_nonneg_right (hEta c.val).2 hprod0
          _ = _ := by ring
          _ ≤ qbar ^ (T.filter (fun b => b < c)).card := by simpa [T] using hprod
      _ ≤ Uq := pdLifeDouble_finiteRankGeomBound T qbar (Real.sqrt_nonneg _) hqbar1
  have hPairsBound :
      (∑ a : J, ∑ c : J,
        if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
          2 * d * memoryEta S.x F.q_d a.val * memoryEta S.x F.q_d c.val *
            ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
              pdLifeSurvival F S γ p (projLine p (γ a).1) j
        else 0) ≤ 2 * d * Uq * ((pathLength S.x + 1 : ℕ) : ℝ) := by
    have hInner (a : J) :
        (∑ c : J,
          if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
            2 * d * memoryEta S.x F.q_d a.val * memoryEta S.x F.q_d c.val *
              ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                pdLifeSurvival F S γ p (projLine p (γ a).1) j
          else 0) ≤ 2 * d * Uq * memoryEta S.x F.q_d a.val := by
      have hCoeff : 0 ≤ 2 * d * memoryEta S.x F.q_d a.val :=
        mul_nonneg (mul_nonneg (by norm_num) hd0) (hEta a.val).1
      calc
        _ = ∑ c : J, (2 * d * memoryEta S.x F.q_d a.val) *
              (if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
                memoryEta S.x F.q_d c.val *
                  ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                    pdLifeSurvival F S γ p (projLine p (γ a).1) j else 0) := by
            apply Finset.sum_congr rfl
            intro c hc
            by_cases hcond : a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 <;>
              simp [hcond] <;> ring
        _ = (2 * d * memoryEta S.x F.q_d a.val) *
              ∑ c : J,
                (if a < c ∧ projLine p (γ c).1 = projLine p (γ a).1 then
                  memoryEta S.x F.q_d c.val *
                    ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
                      pdLifeSurvival F S γ p (projLine p (γ a).1) j else 0) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (2 * d * memoryEta S.x F.q_d a.val) * Uq :=
            mul_le_mul_of_nonneg_left (hTailSum a) hCoeff
        _ = 2 * d * Uq * memoryEta S.x F.q_d a.val := by ring
    calc
      _ ≤ ∑ a : J, 2 * d * Uq * memoryEta S.x F.q_d a.val :=
        Finset.sum_le_sum fun a ha => hInner a
      _ = 2 * d * Uq * ∑ a : J, memoryEta S.x F.q_d a.val := by
        rw [← Finset.mul_sum]
      _ ≤ 2 * d * Uq * ((pathLength S.x + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hEtaSum (mul_nonneg (mul_nonneg (by norm_num) hd0) hUq0.le)
  have hCoeffBound : 2 * d ≤ 4 / ((p : ℝ) + 1) := by
    calc
      2 * d ≤ 2 * (2 / ((p : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hdOrphan (by norm_num)
      _ = 4 / ((p : ℝ) + 1) := by ring
  have hPairCoeffBound :
      2 * d * Uq * ((pathLength S.x + 1 : ℕ) : ℝ) ≤
        4 * ((pathLength S.x : ℝ) + 1) * Uq / ((p : ℝ) + 1) := by
    have hN0 : 0 ≤ ((pathLength S.x + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hNcast : ((pathLength S.x + 1 : ℕ) : ℝ) = (pathLength S.x : ℝ) + 1 := by simp
    have hmul := mul_le_mul_of_nonneg_right hCoeffBound (mul_nonneg hUq0.le hN0)
    calc
      _ = (2 * d) * (Uq * ((pathLength S.x + 1 : ℕ) : ℝ)) := by ring
      _ ≤ (4 / ((p : ℝ) + 1)) * (Uq * ((pathLength S.x + 1 : ℕ) : ℝ)) := hmul
      _ = _ := by rw [hNcast]; ring
  have hOptionBound :
      (∑ e : Option J × Option J, G e) ≤
        1 + 4 * ((pathLength S.x : ℝ) + 1) * Uq / ((p : ℝ) + 1) := by
    rw [hOptionExpand]
    exact add_le_add_right (hPairsBound.trans hPairCoeffBound) 1
  rw [hSumEndpoint]
  calc
    _ ≤ 1 + 4 * ((pathLength S.x : ℝ) + 1) * Uq / ((p : ℝ) + 1) := hOptionBound
    _ = 1 + 4 * ((pathLength S.x : ℝ) + 1) /
          (1 - Real.sqrt F.q_d) / ((p : ℝ) + 1) := by
      dsimp [Uq]
      ring

/-- Uniform explicit product bound with one factor two per ghost birth. Orphan endpoints
are bounded by the geometric hit series; active endpoints by their finite cardinality.
Uses pd_lifecycle_parameters and
pd_active_run_count; feeds pd_truncation_tail_absorb. The b-prime denominators are already
inside the majorant, so no baseline factor is lost. -/
theorem pd_doubled_lifespan_bound (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ γ : EnvPath S.x K, IsContributingPath F S γ →
          doubledLifeMajorant F S γ ≤
            (2 * ((pathLength S.x : ℝ) + 2) ^ 2) ^ (K * (slotCount S.x + pathLength S.x)) *
              Real.exp (8 * (K : ℝ) * Real.log 2 / (1 - Real.sqrt F.q_d) *
                ((pathLength S.x : ℝ) + 1)) := by
  classical
  intro K F hF
  obtain ⟨xP, hxP, hParameters⟩ := pd_lifecycle_parameters K F hF
  obtain ⟨xR, hxR, hRunCount⟩ := pd_active_run_count δ c₁ c₂ hδ hc₁ K F hF
  let x₀ := max xP xR
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxP (le_max_left _ _)
  refine ⟨x₀, hx₀, ?_⟩
  intro S hS hx γ hγ
  have hxP' : xP ≤ S.x := (le_max_left xP xR).trans hx
  have hxR' : xR ≤ S.x := (le_max_right xP xR).trans hx
  have hAt := hParameters S.x hxP'
  have hRunAt := hRunCount S hS hxR' γ hγ.1 hγ.2.1
  have hqd0 : 0 < F.q_d := hF.2.1
  have hqd1 : F.q_d < 1 := hF.2.2.1
  let qbar : ℝ := Real.sqrt F.q_d
  let Uq : ℝ := (1 - qbar)⁻¹
  let C : ℝ := 2 * ((pathLength S.x : ℝ) + 2) ^ 2
  let E : ℝ := 8 * Real.log 2 * Uq * ((pathLength S.x : ℝ) + 1)
  have hqbar0 : 0 < qbar := by
    dsimp [qbar]
    exact Real.sqrt_pos.2 hqd0
  have hqbar1 : qbar < 1 := by
    dsimp [qbar]
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2 (by nlinarith)
  have hUq0 : 0 < Uq := by dsimp [Uq]; positivity
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have hN : 0 ≤ (pathLength S.x : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC1
  have hE0 : 0 ≤ E := by
    dsimp [E]
    positivity
  have hGroupBound (i : Fin K) :
      (∏ p : primeBand S.x (F.a i),
        ∑ life : PrimeLife S γ p.1,
          (if life.1.1.isSome then 2 else 1) *
            |primeLifeCharge F S γ p.1 life|) ≤
        C ^ (slotCount S.x + pathLength S.x) * Real.exp E := by
    let B : Finset ℕ := primeBand S.x (F.a i)
    let A : Finset ℕ := B.filter (fun p => ∃ j, IsActiveAt γ p j)
    let I : Finset ℕ := B.filter (fun p => ¬ ∃ j, IsActiveAt γ p j)
    let D : ℝ := 4 * ((pathLength S.x : ℝ) + 1) * Uq
    let t (p : ℕ) : ℝ := D * (1 / ((p : ℝ) + 1))
    let f (p : ℕ) : ℝ :=
      ∑ life : PrimeLife S γ p,
        (if life.1.1.isSome then 2 else 1) * |primeLifeCharge F S γ p life|
    have hD0 : 0 ≤ D := by dsimp [D]; positivity
    have hAsub : A ⊆ B := Finset.filter_subset _ _
    have hRunFin : (∑ p ∈ B, pdActiveRuns S γ p) = slotCount S.x + pathLength S.x := by
      rw [← pdLifeDouble_sum_subtype B (fun p => pdActiveRuns S γ p)]
      simpa [B] using hRunAt i
    have hAcard : A.card ≤ slotCount S.x + pathLength S.x := by
      calc
        A.card = ∑ p ∈ B, if p ∈ A then 1 else 0 := Finset.card_eq_sum_ite hAsub
        _ ≤ ∑ p ∈ B, pdActiveRuns S γ p := by
          apply Finset.sum_le_sum
          intro p hp
          by_cases hpa : p ∈ A
          · have hpos := pdLifeDoubleRuns_pos S γ p
              (Finset.mem_filter.mp hpa).2
            simpa [hpa] using hpos
          · simp [hpa]
        _ = slotCount S.x + pathLength S.x := hRunFin
    have hfactor0 (p : ℕ) : 0 ≤ f p := by
      apply Finset.sum_nonneg
      intro life hlife
      exact mul_nonneg (by split_ifs <;> norm_num) (abs_nonneg _)
    have hfactorBound (p : ℕ) (hpB : p ∈ B) :
        f p ≤ if p ∈ A then C else Real.exp (t p) := by
      have hmarked : p ∈ markedPrimes S.x K F.a := by
        change p ∈ Finset.univ.biUnion (fun j : Fin K => primeBand S.x (F.a j))
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hpB⟩
      have hbp := hAt.2.2 p hmarked
      by_cases hpa : p ∈ A
      · have hactive : ∃ j, IsActiveAt γ p j := (Finset.mem_filter.mp hpa).2
        have hterm (life : PrimeLife S γ p) :
            (if life.1.1.isSome then 2 else 1) *
              |primeLifeCharge F S γ p life| ≤ 2 := by
          have hA : (pdLifeActive S γ p).Nonempty := by
            rcases hactive with ⟨j, hj⟩
            exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
          have hcharge := pdLifeDouble_active_charge_abs_le_one F S γ p i hpB hbp
            hqd0 hqd1 hA life
          have hw : (if life.1.1.isSome then 2 else 1 : ℝ) ≤ 2 := by
            split_ifs <;> norm_num
          calc
            _ ≤ 2 * |primeLifeCharge F S γ p life| :=
              mul_le_mul_of_nonneg_right hw (abs_nonneg _)
            _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hcharge (by norm_num)
            _ = 2 := by norm_num
        have hcardle : Fintype.card (PrimeLife S γ p) ≤
            Fintype.card (Option (Fin (pathLength S.x + 1)) ×
              Option (Fin (pathLength S.x + 1))) :=
          Fintype.card_le_of_injective (fun life : PrimeLife S γ p => life.1)
            (by intro life life' h; exact Subtype.ext h)
        have hcardleR : (Fintype.card (PrimeLife S γ p) : ℝ) ≤
            ((pathLength S.x : ℝ) + 2) ^ 2 := by
          calc
            _ ≤ (Fintype.card (Option (Fin (pathLength S.x + 1)) ×
                  Option (Fin (pathLength S.x + 1))) : ℝ) := by exact_mod_cast hcardle
            _ = ((pathLength S.x : ℝ) + 2) ^ 2 := by simp; push_cast; ring
        calc
          f p ≤ ∑ life : PrimeLife S γ p, (2 : ℝ) :=
            Finset.sum_le_sum fun life hlife => hterm life
          _ = (Fintype.card (PrimeLife S γ p) : ℝ) * 2 := by simp
          _ ≤ ((pathLength S.x : ℝ) + 2) ^ 2 * 2 :=
            mul_le_mul_of_nonneg_right hcardleR (by norm_num)
          _ = C := by dsimp [C]; ring
        simp [hpa]
      · have hAempty : ¬ (pdLifeActive S γ p).Nonempty := by
          intro hne
          apply hpa
          rcases hne with ⟨j, hj⟩
          exact Finset.mem_filter.mpr ⟨hpB, ⟨j, (Finset.mem_filter.mp hj).2⟩⟩
        have horphan := pdLifeDouble_orphan_sum_bound F S γ p i hpB hbp hqd0 hqd1 hAempty
        have harg :
            4 * ((pathLength S.x : ℝ) + 1) /
                (1 - Real.sqrt F.q_d) / ((p : ℝ) + 1) = t p := by
          dsimp [t, D, Uq, qbar]
          ring
        have hexp :
            1 + 4 * ((pathLength S.x : ℝ) + 1) /
                (1 - Real.sqrt F.q_d) / ((p : ℝ) + 1) ≤ Real.exp (t p) := by
          rw [harg]
          calc
            1 + t p = t p + 1 := by ring
            _ ≤ Real.exp (t p) := Real.add_one_le_exp _
        simpa [f, hpa] using horphan.trans hexp
    have hprodPoint :
        (∏ p ∈ B, f p) ≤
          ∏ p ∈ B, if p ∈ A then C else Real.exp (t p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact hfactor0 p
      · intro p hp
        exact hfactorBound p hp
    have hAfilter : B.filter (fun p => p ∈ A) = A := by
      ext p
      simp [A]
    have hIfilter : B.filter (fun p => ¬ p ∈ A) = I := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hpB, hnotA⟩
        exact Finset.mem_filter.mpr ⟨hpB, by
          intro hactive
          exact hnotA (Finset.mem_filter.mpr ⟨hpB, hactive⟩)⟩
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hpB, hnotActive⟩
        exact Finset.mem_filter.mpr ⟨hpB, by
          intro hA
          exact hnotActive (Finset.mem_filter.mp hA).2⟩
    have hprodSplit :
        (∏ p ∈ B, if p ∈ A then C else Real.exp (t p)) =
          C ^ A.card * Real.exp (∑ p ∈ I, t p) := by
      rw [Finset.prod_ite, hAfilter, hIfilter]
      simp only [Finset.prod_const]
      rw [← Real.exp_sum]
    have hIsub : I ⊆ B := Finset.filter_subset _ _
    have hIsum : (∑ p ∈ I, t p) ≤ E := by
      calc
        _ ≤ ∑ p ∈ I, D * (1 / (p : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hpI
          have hpB : p ∈ B := (Finset.mem_filter.mp hpI).1
          have hpPrime : p.Prime := (Finset.mem_filter.mp hpB).2.1
          have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
          have hpplus : 0 < (p : ℝ) + 1 := by linarith
          have hrecip : 1 / ((p : ℝ) + 1) ≤ 1 / (p : ℝ) := by
            rw [div_le_div_iff₀ hpplus hp0]
            nlinarith
          exact mul_le_mul_of_nonneg_left hrecip hD0
        _ = D * (∑ p ∈ I, 1 / (p : ℝ)) := (Finset.mul_sum _ _ _).symm
        _ ≤ D * (∑ p ∈ B, 1 / (p : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hD0
          exact Finset.sum_le_sum_of_subset_of_nonneg hIsub
            (fun p hpB hpI => by positivity)
        _ ≤ D * (2 * Real.log 2) := by
          apply mul_le_mul_of_nonneg_left _ hD0
          simpa [bandMass, B] using (hAt.1 i).2
        _ = E := by dsimp [D, E]; ring
    have hpow : C ^ A.card ≤ C ^ (slotCount S.x + pathLength S.x) :=
      pow_le_pow_right₀ hC1 hAcard
    have hProdBound :
        (∏ p ∈ B, f p) ≤
          C ^ (slotCount S.x + pathLength S.x) * Real.exp E := by
      calc
        _ ≤ C ^ A.card * Real.exp (∑ p ∈ I, t p) := by
          rw [← hprodSplit]
          exact hprodPoint
        _ ≤ C ^ (slotCount S.x + pathLength S.x) * Real.exp (∑ p ∈ I, t p) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
        _ ≤ C ^ (slotCount S.x + pathLength S.x) * Real.exp E :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hIsum)
            (pow_nonneg hC0 _)
    calc
      _ = ∏ p ∈ B, f p := by
        simpa [B, f] using pdLifeDouble_prod_subtype B
          (fun p => ∑ life : PrimeLife S γ p,
            (if life.1.1.isSome then 2 else 1) * |primeLifeCharge F S γ p life|)
      _ ≤ C ^ (slotCount S.x + pathLength S.x) * Real.exp E := hProdBound
  let groupMajorant : Fin K → ℝ := fun i =>
    ∏ p : primeBand S.x (F.a i),
      ∑ life : PrimeLife S γ p.1,
        (if life.1.1.isSome then 2 else 1) * |primeLifeCharge F S γ p.1 life|
  have hAllGroups :
      doubledLifeMajorant F S γ ≤
        ∏ i : Fin K, C ^ (slotCount S.x + pathLength S.x) * Real.exp E := by
    unfold doubledLifeMajorant
    apply Finset.prod_le_prod₀
    · intro i hi
      exact Finset.prod_nonneg fun p hp => Finset.sum_nonneg fun life hlife =>
        mul_nonneg (by split_ifs <;> norm_num) (abs_nonneg _)
    · intro i hi
      exact hGroupBound i
  calc
    doubledLifeMajorant F S γ ≤
        ∏ i : Fin K, C ^ (slotCount S.x + pathLength S.x) * Real.exp E := hAllGroups
    _ = C ^ (K * (slotCount S.x + pathLength S.x)) * Real.exp ((K : ℝ) * E) := by
      calc
        _ = (C ^ (slotCount S.x + pathLength S.x) * Real.exp E) ^ K := by simp
        _ = (C ^ (slotCount S.x + pathLength S.x)) ^ K * (Real.exp E) ^ K := by
          rw [mul_pow]
        _ = C ^ ((slotCount S.x + pathLength S.x) * K) * Real.exp ((K : ℝ) * E) := by
          rw [pow_mul, ← Real.exp_nat_mul E K]
        _ = _ := by rw [Nat.mul_comm]
    _ = (2 * ((pathLength S.x : ℝ) + 2) ^ 2) ^
          (K * (slotCount S.x + pathLength S.x)) *
        Real.exp (8 * (K : ℝ) * Real.log 2 / (1 - Real.sqrt F.q_d) *
          ((pathLength S.x : ℝ) + 1)) := by
      dsimp [C, E, Uq, qbar]
      ring

end
end ArtinPrimitiveRoots.TypeII.PD
