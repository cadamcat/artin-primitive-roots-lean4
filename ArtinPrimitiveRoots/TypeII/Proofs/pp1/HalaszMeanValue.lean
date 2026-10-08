import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.pp1.OAI.Halasz.HalaszClassicalMeanValue
import ArtinPrimitiveRoots.TypeII.Proofs.pp1.OAI.Halasz.HalaszConstantGrowth
import ArtinPrimitiveRoots.TypeII.Proofs.pp1.OAI.Halasz.HalaszSmallDefect

/-! Local adaptation of the OAI TwoPoint/Halasz mean-value result. The 55 source modules are
retained under `OAI/Halasz` with their original theorem namespaces and attribution. -/

namespace ArtinPrimitiveRoots.TypeII.PP

open Classical

/-! The PP definition counts the same system as the OAI Vinogradov count:
encode each allowed positive coordinate `u ≤ M` by the zero-based coordinate
`u - 1 : Fin M`. -/

noncomputable def ppHalaszSolutions (s k M : ℕ) :
    Finset ((Fin s → Fin M) × (Fin s → Fin M)) :=
  Finset.univ.filter fun uv =>
    ∀ j ∈ Finset.Icc 1 k,
      (∑ i, ((uv.1 i).val + 1) ^ j) = ∑ i, ((uv.2 i).val + 1) ^ j

theorem ppHalaszSolutions_card (s k M : ℕ) :
    (ppHalaszSolutions s k M).card =
      OAI.TwoPointCorrelations.halaszVinogradovCount s k M := by
  classical
  let P := ppHalaszSolutions s k M
  have hsum : P.card =
      ∑ x : Fin s → Fin M, (P.filter (fun uv => uv.1 = x)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
    (f := fun uv : (Fin s → Fin M) × (Fin s → Fin M) => uv.1)
      (s := P) (t := Finset.univ) (by intro uv huv; simp))
  have hfib (x : Fin s → Fin M) :
      (P.filter (fun uv => uv.1 = x)).card =
        (OAI.TwoPointCorrelations.halaszVinogradovFiber x k).card := by
    calc
      (P.filter (fun uv => uv.1 = x)).card =
        ((OAI.TwoPointCorrelations.halaszVinogradovFiber x k).image
            fun y => (x, y)).card := by
        congr 1
        ext uv
        rw [Finset.mem_filter, Finset.mem_image]
        change (uv ∈ ppHalaszSolutions s k M ∧ uv.1 = x) ↔
          ∃ y, y ∈ OAI.TwoPointCorrelations.halaszVinogradovFiber x k ∧ (x, y) = uv
        constructor
        · rintro ⟨hrel, hfst⟩
          refine ⟨uv.2, ?_, ?_⟩
          · have hrel' : ∀ j ∈ Finset.Icc 1 k,
                (∑ i, ((x i).val + 1) ^ j) =
                  ∑ i, ((uv.2 i).val + 1) ^ j := by
              simpa [ppHalaszSolutions, hfst] using hrel
            simpa [OAI.TwoPointCorrelations.halaszVinogradovFiber] using hrel'
          · exact Prod.ext hfst.symm rfl
        · rintro ⟨y, hy, huv⟩
          cases huv
          constructor
          · simpa [ppHalaszSolutions,
              OAI.TwoPointCorrelations.halaszVinogradovFiber] using hy
          · rfl
      _ = (OAI.TwoPointCorrelations.halaszVinogradovFiber x k).card := by
        rw [Finset.card_image_of_injective _ (by
          intro y z hyz
          exact congrArg Prod.snd hyz)]
  calc
    P.card = ∑ x : Fin s → Fin M, (P.filter (fun uv => uv.1 = x)).card := hsum
    _ = ∑ x : Fin s → Fin M,
          (OAI.TwoPointCorrelations.halaszVinogradovFiber x k).card := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hfib x
    _ = OAI.TwoPointCorrelations.halaszVinogradovCount s k M := rfl

lemma pp_two_pow_dominates_sq (k : ℕ) (hk : 2 ≤ k) :
    8 * k ^ 2 ≤ 9 * 2 ^ k := by
  by_cases hk2 : k = 2
  · subst k
    norm_num
  have hk3 : 3 ≤ k := by omega
  have hbound : ∀ n : ℕ, 3 ≤ n → 8 * n ^ 2 ≤ 9 * 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ]
      have hpoly : 8 * (n + 1) ^ 2 ≤ 16 * n ^ 2 := by
        have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
        have hpolyR : (8 : ℝ) * ((n : ℝ) + 1) ^ 2 ≤ 16 * (n : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((n : ℝ) - 2)]
        exact_mod_cast hpolyR
      have hstep : 16 * n ^ 2 ≤ 9 * (2 ^ n * 2) := by nlinarith [ih]
      exact hpoly.trans hstep
  exact hbound k hk3

lemma pp_halasz_defect_small (k : ℕ) (hk : 2 ≤ k) :
    OAI.TwoPointCorrelations.halaszClassicalDefect k (10 * k ^ 2) ≤ 1 / 100 := by
  have hk0 : 0 < k := by omega
  have hratio0 : 0 ≤ 1 - 1 / (k : ℝ) :=
    (OAI.TwoPointCorrelations.halasz_classical_ratio_bounds hk0).1
  have hratio := OAI.TwoPointCorrelations.halasz_classical_ratio_block hk
  have hpow :
      (1 - 1 / (k : ℝ)) ^ (10 * k ^ 2) =
        ((1 - 1 / (k : ℝ)) ^ k) ^ (10 * k) := by
    rw [← pow_mul]
    congr 1
    ring
  have hdecay :
      ((1 - 1 / (k : ℝ)) ^ k) ^ (10 * k) ≤ (1 / 2 : ℝ) ^ (10 * k) :=
    pow_le_pow_left₀ (pow_nonneg hratio0 k) hratio (10 * k)
  have hexp : k + 7 ≤ 10 * k := by omega
  have hhalf : (1 / 2 : ℝ) ^ (10 * k) ≤ (1 / 2 : ℝ) ^ (k + 7) :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hexp
  have hcast : 8 * (k : ℝ) ^ 2 ≤ 9 * (2 : ℝ) ^ k := by
    exact_mod_cast pp_two_pow_dominates_sq k hk
  have hhalfpow : (1 / 2 : ℝ) ^ (k + 7) =
      1 / ((128 : ℝ) * (2 : ℝ) ^ k) := by
    have hkpow : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by
      rw [div_pow]
      simp
    rw [pow_add, hkpow]
    norm_num
  have hfrac : (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k + 7) ≤ 1 / 100 := by
    rw [hhalfpow]
    have hquot : (k : ℝ) ^ 2 / ((128 : ℝ) * (2 : ℝ) ^ k) ≤ 9 / 1024 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [hcast]
    calc
      (k : ℝ) ^ 2 * (1 / ((128 : ℝ) * (2 : ℝ) ^ k)) =
          (k : ℝ) ^ 2 / ((128 : ℝ) * (2 : ℝ) ^ k) := by ring
      _ ≤ 9 / 1024 := hquot
      _ ≤ 1 / 100 := by norm_num
  have hK :
      (OAI.TwoPointCorrelations.halaszTriangularDegree k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rw [OAI.TwoPointCorrelations.halasz_triangular_degree_cast hk0]
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hkminus : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    nlinarith
  unfold OAI.TwoPointCorrelations.halaszClassicalDefect
  rw [hpow]
  calc
    (OAI.TwoPointCorrelations.halaszTriangularDegree k : ℝ) *
        ((1 - 1 / (k : ℝ)) ^ k) ^ (10 * k) ≤
      (OAI.TwoPointCorrelations.halaszTriangularDegree k : ℝ) *
        (1 / 2 : ℝ) ^ (10 * k) :=
      mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg _)
    _ ≤ (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (10 * k) :=
      mul_le_mul_of_nonneg_right hK (pow_nonneg (by positivity) _)
    _ ≤ (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k + 7) :=
      mul_le_mul_of_nonneg_left hhalf (sq_nonneg _)
    _ ≤ 1 / 100 := hfrac

lemma pp_halasz_constant_exp_bound (R₀ k : ℕ) (hk : 2 ≤ k) :
    (OAI.TwoPointCorrelations.halaszIterationConstant R₀ k (10 * k ^ 2) : ℝ) ≤
      Real.exp (300 * ((R₀ : ℝ) + 33) * (k : ℝ) ^ 6) := by
  let n := 10 * k ^ 2
  let b := R₀ + k + 32
  have hb32 : 32 ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hk1 : 1 ≤ k := by omega
  have hbase := OAI.TwoPointCorrelations.halasz_iteration_base_growth
    (R₀ := R₀) hk
  have h1 :
      OAI.TwoPointCorrelations.halaszIterationBase R₀ k ^ (n + 1) ≤
        b ^ (11 * k ^ 3 * (n + 1)) := by
    calc
      _ ≤ (b ^ (11 * k ^ 3)) ^ (n + 1) := Nat.pow_le_pow_left hbase _
      _ = b ^ (11 * k ^ 3 * (n + 1)) := by
        exact (pow_mul b (11 * k ^ 3) (n + 1)).symm
  have h2 :
      32 ^ (k * n * (n + 1)) ≤ b ^ (k * n * (n + 1)) :=
    Nat.pow_le_pow_left hb32 _
  have hexpNat :
      11 * k ^ 3 * (n + 1) + k * n * (n + 1) ≤ 300 * k ^ 5 := by
    have hformula :
        11 * k ^ 3 * (n + 1) + k * n * (n + 1) = 210 * k ^ 5 + 21 * k ^ 3 := by
      dsimp [n]
      ring
    have hk35 : k ^ 3 ≤ k ^ 5 := pow_le_pow_right₀ hk1 (by decide)
    rw [hformula]
    nlinarith
  have hconstNat :
      OAI.TwoPointCorrelations.halaszIterationConstant R₀ k n ≤ b ^ (300 * k ^ 5) := by
    unfold OAI.TwoPointCorrelations.halaszIterationConstant
    calc
      _ ≤ b ^ (11 * k ^ 3 * (n + 1)) * b ^ (k * n * (n + 1)) := Nat.mul_le_mul h1 h2
      _ = b ^ (11 * k ^ 3 * (n + 1) + k * n * (n + 1)) := by rw [← pow_add]
      _ ≤ b ^ (300 * k ^ 5) := pow_le_pow_right₀ hb1 hexpNat
  have hbD : (b : ℝ) ≤ ((R₀ : ℝ) + 33) * (k : ℝ) := by
    dsimp [b]
    have hR₀ : (0 : ℝ) ≤ R₀ := Nat.cast_nonneg _
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkminus : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    have h₁ := mul_nonneg hR₀ hkminus
    have h₂ := mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hkminus
    push_cast
    nlinarith
  have hbExp : (b : ℝ) ≤ Real.exp (b : ℝ) := by
    have h := Real.add_one_le_exp (b : ℝ)
    linarith
  have hprod :
      (300 * (k : ℝ) ^ 5) * (b : ℝ) ≤
        300 * ((R₀ : ℝ) + 33) * (k : ℝ) ^ 6 := by
    calc
      _ ≤ (300 * (k : ℝ) ^ 5) * (((R₀ : ℝ) + 33) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hbD (by positivity)
      _ = _ := by ring
  have hconstReal :
      (OAI.TwoPointCorrelations.halaszIterationConstant R₀ k n : ℝ) ≤
        (b : ℝ) ^ (300 * k ^ 5) := by exact_mod_cast hconstNat
  calc
    _ ≤ (b : ℝ) ^ (300 * k ^ 5) := hconstReal
    _ ≤ (Real.exp (b : ℝ)) ^ (300 * k ^ 5) :=
      pow_le_pow_left₀ (by positivity) hbExp _
    _ = Real.exp ((300 * k ^ 5 : ℕ) * (b : ℝ)) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (300 * ((R₀ : ℝ) + 33) * (k : ℝ) ^ 6) := by
      apply Real.exp_le_exp.mpr
      exact_mod_cast hprod

theorem vinogradovCount_le_halasz (s k M : ℕ) :
    vinogradovCount s k M ≤
      OAI.TwoPointCorrelations.halaszVinogradovCount s k M := by
  classical
  let S := (((boundedTuples s M).product (boundedTuples s M)).filter fun uv =>
    (∀ j : Fin k, ∑ i : Fin s, uv.1 i ^ (j.val + 1) =
      ∑ i : Fin s, uv.2 i ^ (j.val + 1)) ∧
    (∀ i, 1 ≤ uv.1 i ∧ uv.1 i ≤ M) ∧
    (∀ i, 1 ≤ uv.2 i ∧ uv.2 i ≤ M))
  let D := S.attach
  let encode (z : {uv // uv ∈ S}) : (Fin s → Fin M) × (Fin s → Fin M) :=
    (fun i => ⟨z.val.1 i - 1, by
      have hi := (Finset.mem_filter.mp z.property).2.2.1 i
      omega⟩,
     fun i => ⟨z.val.2 i - 1, by
      have hi := (Finset.mem_filter.mp z.property).2.2.2 i
      omega⟩)
  have hrec₁ (z : {uv // uv ∈ S}) (i : Fin s) :
      ((encode z).1 i).val + 1 = z.val.1 i := by
    simp only [encode]
    have hi := (Finset.mem_filter.mp z.property).2.2.1 i
    omega
  have hrec₂ (z : {uv // uv ∈ S}) (i : Fin s) :
      ((encode z).2 i).val + 1 = z.val.2 i := by
    simp only [encode]
    have hi := (Finset.mem_filter.mp z.property).2.2.2 i
    omega
  have hinj : Function.Injective encode := by
    intro z w h
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hi := congrArg (fun uv : (Fin s → Fin M) × (Fin s → Fin M) =>
        (uv.1 i).val + 1) h
      rw [hrec₁ z i, hrec₁ w i] at hi
      exact hi
    · funext i
      have hi := congrArg (fun uv : (Fin s → Fin M) × (Fin s → Fin M) =>
        (uv.2 i).val + 1) h
      rw [hrec₂ z i, hrec₂ w i] at hi
      exact hi
  have himage : D.image encode ⊆ ppHalaszSolutions s k M := by
    intro uv huv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp huv
    simp only [ppHalaszSolutions, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    have hjlo : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjhi : j ≤ k := (Finset.mem_Icc.mp hj).2
    let jj : Fin k := ⟨j - 1, by omega⟩
    have hp := (Finset.mem_filter.mp z.property).2.1 jj
    have hval : jj.val + 1 = j := Nat.sub_add_cancel hjlo
    have hsum₁ :
        (∑ i : Fin s, (((encode z).1 i).val + 1) ^ j) =
          ∑ i : Fin s, z.val.1 i ^ j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrec₁ z i]
    have hsum₂ :
        (∑ i : Fin s, (((encode z).2 i).val + 1) ^ j) =
          ∑ i : Fin s, z.val.2 i ^ j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrec₂ z i]
    rw [hsum₁, hsum₂]
    rw [hval] at hp
    exact hp
  have hbridge : S.card ≤ (ppHalaszSolutions s k M).card := by
    calc
      S.card = (D.image encode).card := by
        rw [Finset.card_image_of_injective D hinj]
        simp [D, Finset.card_attach]
      _ ≤ (ppHalaszSolutions s k M).card := Finset.card_le_card himage
  unfold vinogradovCount
  rw [← ppHalaszSolutions_card s k M]
  change S.card ≤ (ppHalaszSolutions s k M).card
  exact hbridge

theorem mean_value_from_halasz :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ k : ℕ, 2 ≤ k →
        ∃ s : ℕ, k ≤ s ∧ (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 ∧
          ∀ M : ℕ, 1 ≤ M →
            (vinogradovCount s k M : ℝ) ≤
              Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
                Real.rpow (M : ℝ)
                  (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + 1 / 100 : ℝ) := by
  obtain ⟨R₀, hmean⟩ := OAI.TwoPointCorrelations.halasz_classical_mean_value
  let C₁ : ℝ := 300 * ((R₀ : ℝ) + 33) + 11
  let C₂ : ℝ := 6
  refine ⟨C₁, C₂, ?_, ?_, ?_⟩
  · dsimp [C₁]
    positivity
  · norm_num [C₂]
  · intro k hk
    let n : ℕ := 10 * k ^ 2
    let s : ℕ := (n + 1) * k
    have hk0 : 0 < k := by omega
    have hks : k ≤ s := by
      dsimp [s, n]
      have hcoef : 1 ≤ 10 * k ^ 2 + 1 := by omega
      simpa using Nat.mul_le_mul_right k hcoef
    have hsSmall : (s : ℝ) ≤ 11 * (k : ℝ) ^ 4 := by
      have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hk34 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 4 :=
        pow_le_pow_right₀ hk1R (by decide : 3 ≤ 4)
      have hk14 : (k : ℝ) ≤ (k : ℝ) ^ 4 :=
        by simpa only [pow_one] using
          (pow_le_pow_right₀ hk1R (by decide : 1 ≤ 4))
      dsimp [s, n]
      push_cast
      nlinarith
    have hC₁ : 11 ≤ C₁ := by
      dsimp [C₁]
      have hR₀ : (0 : ℝ) ≤ R₀ := Nat.cast_nonneg _
      nlinarith
    have hs : (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 := by
      calc
        (s : ℝ) ≤ 11 * (k : ℝ) ^ 4 := hsSmall
        _ ≤ C₁ * (k : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hC₁ (pow_nonneg (Nat.cast_nonneg _) _)
    refine ⟨s, hks, hs, ?_⟩
    intro M hM
    have hbridge := vinogradovCount_le_halasz s k M
    have hbridgeR :
        (vinogradovCount s k M : ℝ) ≤
          (OAI.TwoPointCorrelations.halaszVinogradovCount s k M : ℝ) := by
      exact_mod_cast hbridge
    have hOAI :
        (OAI.TwoPointCorrelations.halaszVinogradovCount s k M : ℝ) ≤
          (OAI.TwoPointCorrelations.halaszIterationConstant R₀ k n : ℝ) *
            (M : ℝ) ^ (OAI.TwoPointCorrelations.halaszClassicalExponent k n) := by
      simpa [s] using hmean k hk n M hM
    have hdefect := pp_halasz_defect_small k hk
    have hExponent :
        OAI.TwoPointCorrelations.halaszClassicalExponent k n ≤
          2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + 1 / 100 := by
      have hdefect' :
          OAI.TwoPointCorrelations.halaszClassicalDefect k n ≤ 1 / 100 := by
        simpa [n] using hdefect
      rw [OAI.TwoPointCorrelations.halaszClassicalExponent]
      rw [OAI.TwoPointCorrelations.halasz_total_degree_cast hk0]
      have hbase :
          2 * (((n + 1) * k : ℕ) : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 =
            2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 := by
        simp [s]
      rw [hbase]
      linarith
    have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hMpow :
        (M : ℝ) ^ (OAI.TwoPointCorrelations.halaszClassicalExponent k n) ≤
          Real.rpow (M : ℝ)
            (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + 1 / 100) := by
      exact Real.rpow_le_rpow_of_exponent_le hMreal hExponent
    have hconst := pp_halasz_constant_exp_bound R₀ k hk
    have hconst' :
      (OAI.TwoPointCorrelations.halaszIterationConstant R₀ k n : ℝ) ≤
          Real.exp (C₁ * Real.rpow (k : ℝ) C₂) := by
      have hrpow : (k : ℝ).rpow C₂ = (k : ℝ) ^ 6 := by
        have hc₂ : C₂ = ((6 : ℕ) : ℝ) := by norm_num [C₂]
        rw [hc₂]
        change (k : ℝ) ^ ((6 : ℕ) : ℝ) = (k : ℝ) ^ 6
        exact Real.rpow_natCast (k : ℝ) 6
      apply hconst.trans
      apply Real.exp_le_exp.mpr
      rw [hrpow]
      dsimp [C₁]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ k by positivity) 6]
    calc
      (vinogradovCount s k M : ℝ) ≤
          (OAI.TwoPointCorrelations.halaszVinogradovCount s k M : ℝ) := hbridgeR
      _ ≤ (OAI.TwoPointCorrelations.halaszIterationConstant R₀ k n : ℝ) *
            (M : ℝ) ^ (OAI.TwoPointCorrelations.halaszClassicalExponent k n) := hOAI
      _ ≤ Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
            Real.rpow (M : ℝ)
              (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + 1 / 100) :=
        mul_le_mul hconst' hMpow
          (Real.rpow_nonneg (by exact_mod_cast (show 0 ≤ M by omega)) _)
          (Real.exp_nonneg _)

end ArtinPrimitiveRoots.TypeII.PP
