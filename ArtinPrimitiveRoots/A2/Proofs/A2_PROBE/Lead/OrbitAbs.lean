import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

private theorem prc_qI_ext_pos (I : S.ExtIdeal) : 0 < qI I.1 := by
  unfold qI
  have h := Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using I.2.1)⟩
  exact_mod_cast h

private theorem prc_qI_ext_ge_one (I : S.ExtIdeal) : 1 ≤ qI I.1 := by
  have hpos : (0 : ℝ) < (Ideal.absNorm I.1 : ℝ) := by
    simpa [qI] using prc_qI_ext_pos (S := S) I
  have hposNat : 0 < Ideal.absNorm I.1 := by exact_mod_cast hpos
  have hNat : 1 ≤ Ideal.absNorm I.1 := Nat.one_le_iff_ne_zero.mpr hposNat.ne'
  have hNatR : (1 : ℝ) ≤ (Ideal.absNorm I.1 : ℝ) := by exact_mod_cast hNat
  simpa [qI] using hNatR

private theorem prc_qI_sqf_pos (c : S.SqfExtIdeal) : 0 < qI c.1 := by
  unfold qI
  have h := Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨c.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using c.2.1.1)⟩
  exact_mod_cast h

private theorem prc_ext_rpow_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun I : S.ExtIdeal => qI I.1 ^ (-s)) := by
  simpa [qI, idealNorm] using a2_bridge_COUNT_summable S s hs

private theorem prc_sqf_rpow_summable
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (s : ℝ) (hs : 1 < s) :
    Summable (fun c : S.SqfExtIdeal => qI c.1 ^ (-s)) := by
  have hExt := prc_ext_rpow_summable (S := S) s hs
  let e : S.SqfExtIdeal → S.ExtIdeal := R0.exterior.ofSqf
  have he : Function.Injective e := by
    intro c d h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    simpa [e, R0.exterior.ofSqf_val] using hv
  have h := hExt.comp_injective he
  change Summable (fun c : S.SqfExtIdeal => qI (e c).1 ^ (-s)) at h
  simpa [e, qI, R0.exterior.ofSqf_val] using h

private theorem prc_summable_product {α β : Type*} (f : α → ℝ) (g : β → ℝ)
    (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  apply (summable_prod_of_nonneg (fun p : α × β => mul_nonneg (hf0 p.1) (hg0 p.2))).2
  constructor
  · intro x
    exact hg.mul_left (f x)
  · have hp : (fun x : α => ∑' y : β, f x * g y) =
        fun x => f x * ∑' y, g y := by
      funext x
      exact hg.tsum_mul_left (f x)
    rw [hp]
    exact hf.mul_right (∑' y, g y)

private theorem prc_summable_product5
    {α β γ δ ε : Type*} (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ)
    (k : δ → ℝ) (l : ε → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h)
    (hk : Summable k) (hl : Summable l)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hk0 : ∀ x, 0 ≤ k x) (hl0 : ∀ x, 0 ≤ l x) :
    Summable (fun p : α × β × γ × δ × ε =>
      f p.1 * g p.2.1 * h p.2.2.1 * k p.2.2.2.1 * l p.2.2.2.2) := by
  have hkl := prc_summable_product k l hk hl hk0 hl0
  have hhkl := prc_summable_product h (fun p : δ × ε => k p.1 * l p.2)
    hh hkl hh0 (fun p => mul_nonneg (hk0 p.1) (hl0 p.2))
  have hhkl' : Summable (fun p : γ × δ × ε => h p.1 * k p.2.1 * l p.2.2) := by
    simpa only [mul_assoc] using hhkl
  have hghkl := prc_summable_product g
    (fun p : γ × δ × ε => h p.1 * k p.2.1 * l p.2.2)
    hg hhkl' hg0 (fun p => mul_nonneg (mul_nonneg (hh0 p.1) (hk0 p.2.1))
      (hl0 p.2.2))
  have hghkl' : Summable
      (fun p : β × γ × δ × ε => g p.1 * h p.2.1 * k p.2.2.1 * l p.2.2.2) := by
    simpa only [mul_assoc] using hghkl
  have hfghkl := prc_summable_product f
    (fun p : β × γ × δ × ε => g p.1 * h p.2.1 * k p.2.2.1 * l p.2.2.2)
    hf hghkl' hf0 (fun p => mul_nonneg
      (mul_nonneg (mul_nonneg (hg0 p.1) (hh0 p.2.1)) (hk0 p.2.2.1))
      (hl0 p.2.2.2))
  refine hfghkl.congr ?_
  intro p
  ring

private theorem prc_frequency_inv_sq_summable :
    Summable (fun u : U.U => U.q u ^ (-2 : ℝ)) := by
  classical
  let shell (k : ℕ) : Set U.U :=
    {u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧ U.q u < ((2 ^ (k + 1) : ℕ) : ℝ)}
  have hpartition : ∀ u : U.U, ∃! k : ℕ, u ∈ shell k := by
    intro u
    have hq := U.q_ge_one u
    let n : ℕ := Nat.floor (U.q u)
    have hn : n ≠ 0 := by
      intro hn
      have hlt : U.q u < (n + 1 : ℕ) := by
        exact_mod_cast (Nat.lt_floor_add_one (U.q u))
      rw [hn] at hlt
      norm_num at hlt
      linarith
    let k : ℕ := Nat.log 2 n
    have hloN : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hn
    have hhiN : n < 2 ^ (k + 1) := by
      simpa [k, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hlo : ((2 ^ k : ℕ) : ℝ) ≤ U.q u := by
      calc
        _ ≤ (n : ℝ) := by exact_mod_cast hloN
        _ ≤ U.q u := Nat.floor_le (by linarith)
    have hfloor : U.q u < (n + 1 : ℕ) := by
      exact_mod_cast (Nat.lt_floor_add_one (U.q u))
    have hsucc : n + 1 ≤ 2 ^ (k + 1) := Nat.succ_le_iff.mpr hhiN
    have hhi : U.q u < ((2 ^ (k + 1) : ℕ) : ℝ) := by
      exact hfloor.trans_le (by exact_mod_cast hsucc)
    refine ⟨k, ⟨hlo, hhi⟩, ?_⟩
    intro j hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hjk | hkj
    · have hp : 2 ^ (j + 1) ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_iff.mpr hjk)
      have hpR : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hp
      linarith [hj.2, hlo]
    · have hp : 2 ^ (k + 1) ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_iff.mpr hkj)
      have hpR : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hp
      linarith [hj.1, hhi]
  obtain ⟨Cd, hCd, hdyad⟩ := U.dyadic_count
  obtain ⟨Cl, hCl, hlowFin, hlowBound⟩ := U.low_shell_bound
  let C : ℝ := max Cd Cl
  have hC : 0 < C := lt_of_lt_of_le hCd (le_max_left _ _)
  have hfinite (k : ℕ) : (shell k).Finite := by
    by_cases hk : k = 0
    · subst k
      apply hlowFin.subset
      intro u hu
      exact ⟨by simpa using hu.1, lt_trans hu.2 (by norm_num)⟩
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hX : 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
        have hp : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkpos
        exact_mod_cast hp
      obtain ⟨hfin, _⟩ := hdyad ((2 ^ k : ℕ) : ℝ) hX
      exact hfin.subset (by
        intro u hu
        refine ⟨hu.1, ?_⟩
        simpa [pow_succ, mul_comm] using hu.2)
  have hcount (k : ℕ) : (shell k).ncard ≤ C * ((2 ^ k : ℕ) : ℝ) := by
    by_cases hk : k = 0
    · subst k
      have hsub : shell 0 ⊆ {u | 1 ≤ U.q u ∧ U.q u < 4} := by
        intro u hu
        exact ⟨by simpa using hu.1, lt_trans hu.2 (by norm_num)⟩
      have hc := Set.ncard_le_ncard hsub hlowFin
      calc
        (shell 0).ncard ≤ ({u | 1 ≤ U.q u ∧ U.q u < 4}.ncard : ℝ) := by exact_mod_cast hc
        _ ≤ Cl := hlowBound
        _ ≤ C := le_max_right _ _
        _ = C * ((2 ^ 0 : ℕ) : ℝ) := by simp [C]
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hX : 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
        have hp : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkpos
        exact_mod_cast hp
      obtain ⟨hfin, hb⟩ := hdyad ((2 ^ k : ℕ) : ℝ) hX
      have hsub : shell k ⊆ {u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧
          U.q u < 2 * ((2 ^ k : ℕ) : ℝ)} := by
        intro u hu
        refine ⟨hu.1, ?_⟩
        simpa [pow_succ, mul_comm] using hu.2
      have hc := Set.ncard_le_ncard hsub hfin
      calc
        (shell k).ncard ≤
            ({u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧ U.q u < 2 * ((2 ^ k : ℕ) : ℝ)}.ncard : ℝ) := by
          exact_mod_cast hc
        _ ≤ Cd * ((2 ^ k : ℕ) : ℝ) := hb
        _ ≤ C * ((2 ^ k : ℕ) : ℝ) := by
          dsimp [C]
          gcongr
          exact le_max_left _ _
  have hinner (k : ℕ) : Summable (fun u : {u // u ∈ shell k} => U.q u.1 ^ (-2 : ℝ)) := by
    letI : Fintype {u // u ∈ shell k} := (hfinite k).fintype
    exact Summable.of_finite
  have hmass (k : ℕ) :
      (∑' u : {u // u ∈ shell k}, U.q u.1 ^ (-2 : ℝ)) ≤ C * (1 / 2 : ℝ) ^ k := by
    let X : ℝ := ((2 ^ k : ℕ) : ℝ)
    have hX : 0 < X := by positivity
    have hterm (u : {u // u ∈ shell k}) : U.q u.1 ^ (-2 : ℝ) ≤ X ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hX (by simpa [X] using u.2.1) (by norm_num)
    letI : Fintype {u // u ∈ shell k} := (hfinite k).fintype
    calc
      _ ≤ ∑' u : {u // u ∈ shell k}, X ^ (-2 : ℝ) :=
        (hinner k).tsum_le_tsum (fun u => hterm u) (Summable.of_finite)
      _ = (Fintype.card {u // u ∈ shell k} : ℝ) * X ^ (-2 : ℝ) := by simp
      _ = ((shell k).ncard : ℝ) * X ^ (-2 : ℝ) := by simp
      _ ≤ (C * X) * X ^ (-2 : ℝ) := by
        gcongr
        exact hcount k
      _ = C * (1 / 2 : ℝ) ^ k := by
        have hXpow : X = (2 : ℝ) ^ k := by dsimp [X]; norm_cast
        rw [hXpow, Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ) ^ k) 2, Real.rpow_two]
        simp only [one_div_pow, one_pow]
        field_simp
  have houter : Summable (fun k : ℕ => ∑' u : {u // u ∈ shell k}, U.q u.1 ^ (-2 : ℝ)) := by
    have hg : Summable (fun k : ℕ => C * (1 / 2 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun u => ?_) hmass hg
    exact Real.rpow_nonneg (U.q_pos u.1).le _
  have hnonneg : ∀ u : U.U, 0 ≤ U.q u ^ (-2 : ℝ) :=
    fun u => Real.rpow_nonneg (U.q_pos u).le _
  exact (summable_partition hnonneg hpartition).2 ⟨hinner, houter⟩

private theorem prc_hecke_ideal_norm_le_one (χ : HeckeChar F)
    (hχ : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (I : Ideal (𝓞 F)) :
    ‖χ.idealValue I‖ ≤ 1 := by
  classical
  have hprime (v : FinPlace F) : ‖χ.primeValue v‖ ≤ 1 := by
    unfold HeckeChar.primeValue
    split_ifs with hv
    · have h := hχ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))))
      simpa [HeckeChar.loc] using h.le
    · simp
  have hprod {α : Type} (s : Multiset α) (f : α → ℂ)
      (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _)
        (ih fun x hx => hf x (Multiset.mem_cons_of_mem hx))
  unfold HeckeChar.idealValue
  apply hprod
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using hprime ⟨P, h.1, h.2⟩
  · simp [h]

private theorem prc_gamma_norm_le_one (c : S.SqfExtIdeal) :
    ‖gamma D S A 2 c.1 (cgen R c)‖ ≤ 1 := by
  obtain ⟨a, ha, hgen, hallowed⟩ := cgen_valid R c
  rw [← ha]
  exact ArtinPrimitiveRoots.Proofs.a2_rffwd_sol.gamma_sqf_norm_le_one
    D S H Bd A c.1 c.2.1 c.2.2 a ⟨hgen, hallowed⟩

private theorem prc_generator_mem_sIntegers (I : S.ExtIdeal) (a : Fˣ)
    (hgen : S.IsGen (a : F) I.1) : (a : F) ∈ S.R := by
  change ∀ v : FinPlace F, v ∉ S.Sf → v.valuation F (a : F) ≤ 1
  intro v hv
  have hcount := hgen.2.2 v hv
  have hnonneg : 0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) := by
    rw [hcount]
    exact FractionalIdeal.count_coe_nonneg F v I.1
  have hprincipal := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (a : F) (Units.ne_zero a)
  have hlog : WithZero.log (v.valuation F (a : F)) ≤ 0 := by
    have hnonneg' : 0 ≤ -WithZero.log (v.valuation F (a : F)) := by
      rw [← hprincipal]
      exact hnonneg
    linarith
  have hvalNe : v.valuation F (a : F) ≠ 0 := by
    apply (Valuation.ne_zero_iff _).2
    exact Units.ne_zero a
  calc
    v.valuation F (a : F) = WithZero.exp (WithZero.log (v.valuation F (a : F))) :=
      (WithZero.exp_log hvalNe).symm
    _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr hlog
    _ = 1 := WithZero.exp_zero

private theorem prc_w1_s_norm_summable (Y : ℝ) (hY : 0 < Y) :
    Summable (fun s : S.ExtIdeal => qI s.1 * ‖W.W1 (qI s.1 / Y)‖) := by
  classical
  let f : S.ExtIdeal → ℝ := fun s => qI s.1 * ‖W.W1 (qI s.1 / Y)‖
  have hcompact : IsCompact (tsupport W.W1) := W.W1_compact
  obtain ⟨B, hB⟩ := hcompact.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (Y * B)
  have hactive :
      {s : S.ExtIdeal | W.W1 (qI s.1 / Y) ≠ 0}.Finite := by
    have hfin := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N).preimage
      (f := fun s : S.ExtIdeal => s.1) Subtype.val_injective.injOn
    apply hfin.subset
    intro s hs
    change Ideal.absNorm s.1 ≤ N
    have hts : qI s.1 / Y ∈ tsupport W.W1 :=
      subset_closure (Function.mem_support.mpr hs)
    have hsupport := hB hts
    have hnorm : qI s.1 ≤ Y * B := by
      calc
        qI s.1 = (qI s.1 / Y) * Y := (div_mul_cancel₀ _ hY.ne').symm
        _ ≤ B * Y := mul_le_mul_of_nonneg_right hsupport hY.le
        _ = Y * B := mul_comm _ _
    have hnatReal : (Ideal.absNorm s.1 : ℝ) < N := by
      rw [qI] at hnorm
      exact lt_of_le_of_lt hnorm hN
    exact_mod_cast hnatReal.le
  have hsupport : Function.support f ⊆ {s : S.ExtIdeal | W.W1 (qI s.1 / Y) ≠ 0} := by
    intro s hs
    change f s ≠ 0 at hs
    by_contra hz
    change ¬ W.W1 (qI s.1 / Y) ≠ 0 at hz
    have hz0 : W.W1 (qI s.1 / Y) = 0 := not_ne_iff.mp hz
    apply hs
    simp [f, hz0]
  exact summable_of_hasFiniteSupport (hactive.subset hsupport)

/-- IMPL: full absolute-sheet control and Gaussian order 4 give all five sums. -/
theorem orbit_abs_summable
    (hfinite : LeadFiniteContract R) (hsheets : LeadSheetsContract R sd W)
    (hequiv : LeadEquivContract (bc := bc) η U) :
    ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
      Summable (fun p => ‖leadOrbitTerm R sd W η U X Y Z p‖) := by
  intro X Y Z hX hY hZ
  obtain ⟨Cpg, hCpg, hPG⟩ := PG_decay (4 : ℝ)
  rcases hsheets with ⟨hSheetIntegrable, Csheet, hCsheet, hSheetBound⟩
  let fC : S.SqfExtIdeal → ℝ := fun c => qI c.1 ^ (-2 : ℝ)
  let fN : S.ExtIdeal → ℝ := fun n => qI n.1 ^ (-7 : ℝ)
  let fS : S.ExtIdeal → ℝ := fun s => qI s.1 * ‖W.W1 (qI s.1 / Y)‖
  let fU : U.U → ℝ := fun u => U.q u ^ (-2 : ℝ)
  let fR : S.ExtIdeal → ℝ := fun r => qI r.1 ^ (-12 : ℝ)
  let Ctot : ℝ := Cpg * Csheet * (Z ^ (4 : ℝ) / X ^ 2)
  have hCtot : 0 ≤ Ctot := by positivity
  have hC := prc_sqf_rpow_summable R 2 (by norm_num)
  have hN := prc_ext_rpow_summable (S := S) 7 (by norm_num)
  have hS := prc_w1_s_norm_summable (W := W) Y hY
  have hU := prc_frequency_inv_sq_summable (U := U)
  have hR := prc_ext_rpow_summable (S := S) 12 (by norm_num)
  have hProd := prc_summable_product5 fC fN fS fU fR hC hN hS hU hR
    (fun c => Real.rpow_nonneg (prc_qI_sqf_pos (S := S) c).le _)
    (fun n => Real.rpow_nonneg (prc_qI_ext_pos (S := S) n).le _)
    (fun s => mul_nonneg (prc_qI_ext_pos (S := S) s).le (norm_nonneg _))
    (fun u => Real.rpow_nonneg (U.q_pos u).le _)
    (fun r => Real.rpow_nonneg (prc_qI_ext_pos (S := S) r).le _)
  have hmajor (p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal) :
      ‖leadOrbitTerm R sd W η U X Y Z p‖ ≤
        Ctot * (fC p.1 * fN p.2.1 * fS p.2.2.1 *
          fU p.2.2.2.1 * fR p.2.2.2.2) := by
    let c := p.1
    let n := p.2.1
    let s := p.2.2.1
    let u := p.2.2.2.1
    let r := p.2.2.2.2
    let qc : ℝ := qI c.1
    let qn : ℝ := qI n.1
    let qs : ℝ := qI s.1
    let qa : ℝ := qI (Aideal R c n).1
    let qu : ℝ := U.q u
    let qr : ℝ := qI r.1
    let T : ℝ := X * qu * qr ^ 6 / qa
    have hqc : 0 < qc := by dsimp [qc]; exact prc_qI_sqf_pos (S := S) c
    have hqn : 0 < qn := by dsimp [qn]; exact prc_qI_ext_pos (S := S) n
    have hqs : 0 < qs := by dsimp [qs]; exact prc_qI_ext_pos (S := S) s
    have hqa : 0 < qa := by
      dsimp [qa]
      exact prc_qI_ext_pos (S := S) (Aideal R c n)
    have hqu : 0 < qu := by dsimp [qu]; exact U.q_pos u
    have hqr : 0 < qr := by dsimp [qr]; exact prc_qI_ext_pos (S := S) r
    have hqc1 : 1 ≤ qc := by
      have h := prc_qI_ext_ge_one (S := S) (R.exterior.ofSqf c)
      simpa [qc, R.exterior.ofSqf_val] using h
    have hqn1 : 1 ≤ qn := prc_qI_ext_ge_one (S := S) n
    have hqs1 : 1 ≤ qs := prc_qI_ext_ge_one (S := S) s
    have hqr1 : 1 ≤ qr := prc_qI_ext_ge_one (S := S) r
    have hqA : qa = qc * qn ^ 3 := by
      simp [qa, qc, qn, Aideal, qI, R.exterior.mul_val,
        R.exterior.ofSqf_val, R.exterior.pow_val]
    have hAdata := ArtinPrimitiveRoots.Proofs.a2_rffwd_sol.exterior_cube_generator
      D S H Bd bc R.exterior c n
    have hAgen : S.IsGen (Agen R c n : F) (Aideal R c n).1 := hAdata.1
    have hAallowed : Bd.Allowed (Agen R c n) := hAdata.2
    have hrgen : S.IsGen (bc.gen r : F) r.1 := (bc.gen_spec r).1
    have hrmem : (bc.gen r : F) ∈ S.R := prc_generator_mem_sIntegers r (bc.gen r) hrgen
    have hrpow : ((bc.gen r : F) ^ 6) ∈ S.R := S.R.pow_mem hrmem 6
    let harg : S.R := ⟨(U.repr u : F) * (bc.gen r : F) ^ 6,
      S.R.mul_mem (U.repr u).property hrpow⟩
    have hFF0 := (hfinite.1 s (Aideal R c n) (Agen R c n) hAgen hAallowed harg).2.1
    have hFF : ‖leadFiniteFactor R s (Aideal R c n) (Agen R c n)
        ((U.repr u : F) * (bc.gen r : F) ^ 6)‖ ≤ qs * qa := by
      simpa [harg, qs, qa] using hFF0
    have hgamma := prc_gamma_norm_le_one (R := R) c
    have htheta := prc_hecke_ideal_norm_le_one ϑ R.vartheta_unitary
      (Aideal R c n).1
    have hT : 0 < T := by
      dsimp [T]
      positivity
    have hPGpos : 0 ≤ PG (qa / Z) := by
      rw [PG_formula]
      positivity
    have hPGbound := hPG (qa / Z) (div_pos hqa hZ)
    have hhalf : qc ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hqc1 (by norm_num)
    have hV0 : ‖leadV0 R sd W T‖ ≤ Csheet / T ^ 2 := by
      unfold leadV0
      calc
        _ ≤ ∫ y, ‖leadFourier sd W y‖ ∂(R.sheets.sheet T) :=
          norm_integral_le_integral_norm _
        _ ≤ Csheet / T ^ 2 := hSheetBound T hT
    have hqnpos : 0 < qI n.1 := prc_qI_ext_pos (S := S) n
    have hqapos : 0 < qI (Aideal R c n).1 :=
      prc_qI_ext_pos (S := S) (Aideal R c n)
    have hPGposExpr : 0 ≤ PG (qI (Aideal R c n).1 / Z) := by
      simpa [qa] using hPGpos
    have hqcpowP : 0 ≤ qI p.1.1 ^ (-2⁻¹ : ℝ) :=
      Real.rpow_nonneg (prc_qI_sqf_pos (S := S) p.1).le _
    have hqnposP : 0 < qI p.2.1.1 := by
      simpa [n] using hqnpos
    have hqaposP : 0 < qI (Aideal R p.1 p.2.1).1 := by
      simpa [c, n] using hqapos
    have hPGposP : 0 ≤ PG (qI (Aideal R p.1 p.2.1).1 / Z) := by
      simpa [c, n] using hPGposExpr
    have hnorm :
        ‖leadOrbitTerm R sd W η U X Y Z p‖ =
          ‖gamma D S A 2 c.1 (cgen R c)‖ * ‖ϑ.idealValue (Aideal R c n).1‖ *
            (qc ^ (-(1 / 2 : ℝ)) / qn / qa) * PG (qa / Z) *
              ‖W.W1 (qs / Y)‖ *
                ‖leadFiniteFactor R s (Aideal R c n) (Agen R c n)
                  ((U.repr u : F) * (bc.gen r : F) ^ 6)‖ * ‖leadV0 R sd W T‖ := by
      simp [leadOrbitTerm, c, n, s, u, r, qc, qn, qs, qa, qu, qr, T,
        norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hqcpowP, abs_of_pos hqnposP,
        abs_of_pos hqaposP, abs_of_nonneg hPGposP]
    have hraw :
        ‖leadOrbitTerm R sd W η U X Y Z p‖ ≤
          (1 / qn / qa) *
            (Cpg * (qa / Z) ^ (-4 : ℝ)) *
              ‖W.W1 (qs / Y)‖ * (qs * qa) * (Csheet / T ^ 2) := by
      rw [hnorm]
      calc
        _ ≤ 1 * 1 * (1 / qn / qa) *
              (Cpg * (qa / Z) ^ (-4 : ℝ)) * ‖W.W1 (qs / Y)‖ *
                (qs * qa) * (Csheet / T ^ 2) := by
            gcongr
            all_goals first
            | exact hgamma
            | exact htheta
            | exact hhalf
            | exact hPGbound
            | exact hFF
            | exact hV0
            | positivity
        _ = _ := by ring
    have hPGpow : (qa / Z) ^ (-4 : ℝ) = qa ^ (-4 : ℝ) * Z ^ (4 : ℝ) := by
      calc
        (qa / Z) ^ (-4 : ℝ) = qa ^ (-4 : ℝ) / Z ^ (-4 : ℝ) :=
          Real.div_rpow hqa.le hZ.le _
        _ = qa ^ (-4 : ℝ) / ((Z ^ (4 : ℝ))⁻¹) := by
          rw [Real.rpow_neg hZ.le (4 : ℝ)]
        _ = qa ^ (-4 : ℝ) * Z ^ (4 : ℝ) := by
          rw [div_eq_mul_inv, inv_inv]
    have hqaNegTwo : qa ^ (-2 : ℝ) = (qa ^ 2)⁻¹ := by
      calc
        qa ^ (-2 : ℝ) = (qa ^ (2 : ℝ))⁻¹ := Real.rpow_neg hqa.le (2 : ℝ)
        _ = (qa ^ 2)⁻¹ := congrArg Inv.inv (Real.rpow_natCast qa 2)
    have hXNegTwo : X ^ (-2 : ℝ) = (X ^ 2)⁻¹ := by
      calc
        X ^ (-2 : ℝ) = (X ^ (2 : ℝ))⁻¹ := Real.rpow_neg hX.le (2 : ℝ)
        _ = (X ^ 2)⁻¹ := congrArg Inv.inv (Real.rpow_natCast X 2)
    have hTpow : T ^ (-2 : ℝ) =
        X ^ (-2 : ℝ) * qu ^ (-2 : ℝ) * qr ^ (-12 : ℝ) * qa ^ (2 : ℝ) := by
      dsimp [T]
      rw [Real.div_rpow (by positivity) hqa.le,
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hX.le hqu.le]
      rw [← Real.rpow_pow_comm hqr.le (-2 : ℝ) 6,
        ← Real.rpow_mul_natCast hqr.le (-2 : ℝ) 6]
      norm_num
      all_goals
        rw [hqaNegTwo]
        simp only [div_eq_mul_inv, inv_inv]
        ring_nf
    have hTinv : (T ^ 2 : ℝ)⁻¹ = T ^ (-2 : ℝ) := by
      calc
        (T ^ 2 : ℝ)⁻¹ = (T ^ (2 : ℝ))⁻¹ := by
          congr 1
          exact (Real.rpow_natCast T 2).symm
        _ = T ^ (-2 : ℝ) := (Real.rpow_neg hT.le (2 : ℝ)).symm
    have hqaNeg : qa ^ (-2 : ℝ) = qc ^ (-2 : ℝ) * qn ^ (-6 : ℝ) := by
      rw [hqA, Real.mul_rpow hqc.le (by positivity)]
      rw [← Real.rpow_pow_comm hqn.le (-2 : ℝ) 3,
        ← Real.rpow_mul_natCast hqn.le (-2 : ℝ) 3]
      norm_num
    have hqnCombine : qn ^ (-1 : ℝ) * qn ^ (-6 : ℝ) = qn ^ (-7 : ℝ) := by
      rw [← Real.rpow_add hqn]
      norm_num
    have hqaCombine : qa ^ (-4 : ℝ) * qa ^ (2 : ℝ) = qa ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hqa]
      norm_num
    have hqnInv : qn ^ (-1 : ℝ) = qn⁻¹ := by
      rw [Real.rpow_neg hqn.le 1, Real.rpow_one]
    have hrawSimplify :
        (1 / qn / qa) *
            (Cpg * ((qa / Z) ^ (-4 : ℝ))) *
              ‖W.W1 (qs / Y)‖ * (qs * qa) * (Csheet / T ^ 2) =
          Ctot * qn ^ (-1 : ℝ) * qs * ‖W.W1 (qs / Y)‖ *
            qu ^ (-2 : ℝ) * qr ^ (-12 : ℝ) * (qa ^ (-4 : ℝ) * qa ^ (2 : ℝ)) := by
      rw [hPGpow]
      simp_rw [div_eq_mul_inv]
      rw [hTinv, hTpow, hqnInv, hXNegTwo]
      dsimp [Ctot]
      simp_rw [div_eq_mul_inv]
      field_simp [hqn.ne', hqa.ne', hX.ne', hZ.ne'] <;> ring_nf
    calc
      _ ≤ (1 / qn / qa) *
          (Cpg * ((qa / Z) ^ (-4 : ℝ))) *
            ‖W.W1 (qs / Y)‖ * (qs * qa) * (Csheet / T ^ 2) := hraw
      _ = Ctot * qn ^ (-1 : ℝ) * qa ^ (-2 : ℝ) * qs *
          ‖W.W1 (qs / Y)‖ * qu ^ (-2 : ℝ) * qr ^ (-12 : ℝ) := by
        calc
          _ = Ctot * qn ^ (-1 : ℝ) * qs * ‖W.W1 (qs / Y)‖ *
              qu ^ (-2 : ℝ) * qr ^ (-12 : ℝ) *
                (qa ^ (-4 : ℝ) * qa ^ (2 : ℝ)) := hrawSimplify
          _ = _ := by rw [hqaCombine]; ring_nf
      _ = Ctot * (qc ^ (-2 : ℝ) * qn ^ (-7 : ℝ)) *
          qs * ‖W.W1 (qs / Y)‖ * qu ^ (-2 : ℝ) * qr ^ (-12 : ℝ) := by
        rw [hqaNeg]
        calc
          _ = Ctot * (qc ^ (-2 : ℝ) *
              (qn ^ (-1 : ℝ) * qn ^ (-6 : ℝ))) *
                qs * ‖W.W1 (qs / Y)‖ * qu ^ (-2 : ℝ) * qr ^ (-12 : ℝ) := by ring
          _ = _ := by rw [hqnCombine]
      _ = Ctot * (fC c * fN n * fS s * fU u * fR r) := by
        simp [fC, fN, fS, fU, fR, qc, qn, qs, qu, qr] <;> ring_nf
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _) hmajor
    (hProd.mul_left Ctot)

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
