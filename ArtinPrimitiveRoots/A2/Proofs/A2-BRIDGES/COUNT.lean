import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open NumberField.Units Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private lemma bridge_ext_norm_pos (S : SData F CE condη) (I : S.ExtIdeal) :
    0 < Ideal.absNorm I.1 :=
  Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
      (by simpa [Ideal.zero_eq_bot] using I.2.1)⟩

private theorem bridge_ideal_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) ≤ C * t := by
  classical
  let L : ℝ :=
    (2 ^ NumberField.InfinitePlace.nrRealPlaces F *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        regulator F * NumberField.classNumber F) /
      (NumberField.Units.torsionOrder F * Real.sqrt |NumberField.discr F|)
  have hlim : Filter.Tendsto
      (fun s : ℝ =>
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ s} : ℝ) / s)
      Filter.atTop (𝓝 L) := by
    simpa [L] using (Ideal.tendsto_norm_le_div_atTop F)
  have hcard (t : ℝ) (ht : 0 ≤ t) :
      ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) =
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) := by
    have hsub :
        {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} ≃
          {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ ⌊t⌋₊} :=
      Equiv.subtypeEquivRight fun I => (Nat.le_floor_iff ht).symm
    have hset :
        ({I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊t⌋₊} : Set (Ideal (𝓞 F))).Finite :=
      Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊
    have hnat :
        Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ ⌊t⌋₊} =
          (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card := by
      change Nat.card ({I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊t⌋₊} : Set (Ideal (𝓞 F))) = _
      rw [Nat.card_coe_set_eq,
        Set.ncard_eq_toFinset_card
          ({I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊t⌋₊} : Set (Ideal (𝓞 F))) hset]
    calc
      _ = (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ ⌊t⌋₊} : ℝ) := by
        exact_mod_cast hnat.symm
      _ = _ := by exact_mod_cast (Nat.card_congr hsub).symm
  have hnear_event : ∀ᶠ s : ℝ in Filter.atTop,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ s} : ℝ) / s ∈ Metric.ball L 1 :=
    hlim.eventually (Metric.ball_mem_nhds L (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hnear_event
  let T₀ : ℝ := max T 1
  let B₀ : ℝ :=
    ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊T₀⌋₊).toFinset.card : ℝ)
  let C : ℝ := max (|L| + 2) (B₀ + 1)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro t ht
    by_cases hTt : T ≤ t
    · have hnear := hT t hTt
      have hnear' : |(Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) / t - L| < 1 := by
        simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hnear
      have hratio :
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) / t ≤ |L| + 1 := by
        rcases abs_lt.mp hnear' with ⟨_, hright⟩
        linarith [le_abs_self L]
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht
      have hC : |L| + 1 ≤ C := by dsimp [C]; linarith [le_max_left (|L| + 2) (B₀ + 1)]
      have hmul := mul_le_mul_of_nonneg_right (hratio.trans hC) ht0
      calc
        ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) =
            (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) := hcard t ht0
        _ = ((Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ t} : ℝ) / t) * t := by
          field_simp
        _ ≤ C * t := hmul
    · have hlt : t < T := lt_of_not_ge hTt
      have htT : t ≤ T₀ := by dsimp [T₀]; exact le_trans hlt.le (le_max_left T 1)
      have hfloor : ⌊t⌋₊ ≤ ⌊T₀⌋₊ := Nat.floor_mono htT
      have hfinset :
          (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset ⊆
            (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊T₀⌋₊).toFinset := by
        intro I hI
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI ⊢
        exact hI.trans hfloor
      have hcount :
          ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊t⌋₊).toFinset.card : ℝ) ≤ B₀ := by
        dsimp [B₀]
        exact_mod_cast (Finset.card_le_card hfinset)
      have hC : B₀ ≤ C := by dsimp [C]; exact le_max_of_le_right (le_of_lt (by linarith))
      have hmul := le_trans hcount hC
      exact hmul.trans (by nlinarith [ht, le_of_lt (by positivity : 0 < C)])

/-- Exact norm cutoffs and their finiteness.
Uses bridgeNormFinset and Ideal.finite_setOfPred_absNorm_le. -/
theorem a2_bridge_COUNT_finite (S : SData F CE condη) (X : ℝ) (hX : 0 ≤ X) :
    {I : S.ExtIdeal | idealNorm I.1 ≤ X}.Finite ∧
    (∀ I : S.ExtIdeal, I ∈ bridgeNormFinset S X ↔ idealNorm I.1 ≤ X) := by
  constructor
  · have hset :
        ({J : Ideal (𝓞 F) | Ideal.absNorm J ≤ ⌊X⌋₊} : Set (Ideal (𝓞 F))).Finite :=
      Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊
    have hpre :
        {I : S.ExtIdeal | Ideal.absNorm I.1 ≤ ⌊X⌋₊}.Finite := by
      exact hset.preimage (f := fun I : S.ExtIdeal => I.1) (by
        intro a ha b hb hab
        exact Subtype.ext hab)
    apply hpre.subset
    intro I hI
    change Ideal.absNorm I.1 ≤ ⌊X⌋₊
    exact (Nat.le_floor_iff hX).mpr (by simpa [idealNorm] using hI)
  · intro I
    change (⟨I.1, I.2⟩ : {J : Ideal (𝓞 F) // S.IsExterior J}) ∈
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).toFinset.subtype
        S.IsExterior ↔ idealNorm I.1 ≤ X
    simp only [Finset.mem_subtype, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    simp [idealNorm, Nat.le_floor_iff hX]

/-- Sharp linear count, including the initial compact range.
Uses NumberField.Ideal.tendsto_norm_le_div_atTop. -/
theorem a2_bridge_COUNT (S : SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ({I : S.ExtIdeal | idealNorm I.1 ≤ X}.ncard : ℝ) ≤ C * X := by
  obtain ⟨C, hC, hbound⟩ := bridge_ideal_count_bound (F := F)
  refine ⟨C, hC, ?_⟩
  intro X hX
  have hfin := a2_bridge_COUNT_finite S X (by linarith)
  have hto : hfin.1.toFinset = bridgeNormFinset S X := by
    ext I
    rw [Set.Finite.mem_toFinset]
    exact (hfin.2 I).symm
  have hnat : {I : S.ExtIdeal | idealNorm I.1 ≤ X}.ncard =
      (bridgeNormFinset S X).card := by
    rw [Set.ncard_eq_toFinset_card _ hfin.1, hto]
  have hcard :
      (bridgeNormFinset S X).card ≤
        (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).toFinset.card := by
    change ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).toFinset.subtype
      S.IsExterior).card ≤ _
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  calc
    ({I : S.ExtIdeal | idealNorm I.1 ≤ X}.ncard : ℝ) =
        (bridgeNormFinset S X).card := by exact_mod_cast hnat
    _ ≤ ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).toFinset.card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ C * X := hbound X hX

private def bridge_normShell (S : SData F CE condη) (k : ℕ) : Set S.ExtIdeal :=
  {I | 2 ^ k ≤ Ideal.absNorm I.1 ∧ Ideal.absNorm I.1 < 2 ^ (k + 1)}

private lemma bridge_normShell_partition (S : SData F CE condη) :
    ∀ I : S.ExtIdeal, ∃! k : ℕ, I ∈ bridge_normShell S k := by
  intro I
  let n := Ideal.absNorm I.1
  have hn : n ≠ 0 := (bridge_ext_norm_pos S I).ne'
  refine ⟨Nat.log 2 n, ?_, ?_⟩
  · change 2 ^ Nat.log 2 n ≤ n ∧ n < 2 ^ (Nat.log 2 n + 1)
    exact ⟨Nat.pow_log_le_self 2 hn,
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n⟩
  · intro k hk
    change 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) at hk
    exact ((Nat.log_eq_iff (Or.inr ⟨by norm_num, hn⟩)).2 hk).symm

private lemma bridge_normShell_finite (S : SData F CE condη) (k : ℕ) :
    (bridge_normShell S k).Finite := by
  have hcut := a2_bridge_COUNT_finite S ((2 ^ (k + 1) : ℕ) : ℝ) (by positivity)
  apply hcut.1.subset
  intro I hI
  change 2 ^ k ≤ Ideal.absNorm I.1 ∧ Ideal.absNorm I.1 < 2 ^ (k + 1) at hI
  change (Ideal.absNorm I.1 : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ)
  exact_mod_cast hI.2.le

private lemma bridge_dyad_scale (k : ℕ) (s : ℝ) :
    ((2 ^ (k + 1) : ℕ) : ℝ) * Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) =
      2 * Real.rpow (Real.rpow 2 (1 - s)) k := by
  have hcast (n : ℕ) : ((2 ^ n : ℕ) : ℝ) = Real.rpow 2 n := by
    calc
      ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by norm_cast
      _ = Real.rpow 2 n := (Real.rpow_natCast 2 n).symm
  have hleft : Real.rpow (Real.rpow 2 (k : ℝ)) (-s) =
      Real.rpow 2 ((k : ℝ) * (-s)) := by
    exact (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) (k : ℝ) (-s)).symm
  have hright : Real.rpow (Real.rpow 2 (1 - s)) (k : ℝ) =
      Real.rpow 2 ((1 - s) * (k : ℝ)) := by
    exact (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) (1 - s) (k : ℝ)).symm
  calc
    ((2 ^ (k + 1) : ℕ) : ℝ) * Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) =
      Real.rpow 2 (k + 1) * Real.rpow 2 ((k : ℝ) * (-s)) := by
      rw [hcast (k + 1), hcast k, hleft]
      norm_cast
    _ = Real.rpow 2 ((k + 1) + (k : ℝ) * (-s)) :=
      (Real.rpow_add (by norm_num : 0 < (2 : ℝ)) _ _).symm
    _ = Real.rpow 2 (1 + (1 - s) * (k : ℝ)) := by congr 1 <;> ring
    _ = Real.rpow 2 1 * Real.rpow 2 ((1 - s) * (k : ℝ)) :=
      Real.rpow_add (by norm_num : 0 < (2 : ℝ)) _ _
    _ = Real.rpow 2 1 * Real.rpow (Real.rpow 2 (1 - s)) (k : ℝ) := by rw [hright.symm]
    _ = 2 * Real.rpow (Real.rpow 2 (1 - s)) k := by
      exact congrArg (fun z : ℝ => z * Real.rpow (Real.rpow 2 (1 - s)) k)
        (Real.rpow_one (2 : ℝ))

private lemma bridge_normShell_tsum_le (S : SData F CE condη) (s C : ℝ)
    (hcount : ∀ X : ℝ, 1 ≤ X →
      ({I : S.ExtIdeal | idealNorm I.1 ≤ X}.ncard : ℝ) ≤ C * X)
    (hs : 1 < s) (k : ℕ) :
    ∑' I : bridge_normShell S k, Real.rpow (idealNorm I.1.1) (-s) ≤
      C * ((2 ^ (k + 1) : ℕ) : ℝ) * Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) := by
  let U : ℝ := ((2 ^ (k + 1) : ℕ) : ℝ)
  have hU : 1 ≤ U := by
    dsimp [U]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)))
  have hcut := a2_bridge_COUNT_finite S U (by linarith)
  have hsubset : bridge_normShell S k ⊆ {I : S.ExtIdeal | idealNorm I.1 ≤ U} := by
    intro I hI
    change 2 ^ k ≤ Ideal.absNorm I.1 ∧ Ideal.absNorm I.1 < 2 ^ (k + 1) at hI
    change idealNorm I.1 ≤ U
    dsimp [U, idealNorm]
    exact_mod_cast hI.2.le
  have hcard := Set.ncard_le_ncard hsubset hcut.1
  have hbound :
      ((bridge_normShell S k).ncard : ℝ) ≤ C * U := by
    calc
      ((bridge_normShell S k).ncard : ℝ) ≤
          ({I : S.ExtIdeal | idealNorm I.1 ≤ U}.ncard : ℝ) := by exact_mod_cast hcard
      _ ≤ C * U := hcount U hU
  have hfinite := bridge_normShell_finite S k
  letI : Fintype (bridge_normShell S k) := hfinite.fintype
  have hterm (I : bridge_normShell S k) :
      Real.rpow (idealNorm I.1.1) (-s) ≤ Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) := by
    have hlo : ((2 ^ k : ℕ) : ℝ) ≤ idealNorm I.1.1 := by
      change ((2 ^ k : ℕ) : ℝ) ≤ (Ideal.absNorm I.1.1 : ℝ)
      exact_mod_cast I.2.1
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith)
  rw [tsum_fintype]
  calc
    ∑ I : bridge_normShell S k, Real.rpow (idealNorm I.1.1) (-s) ≤
        ∑ I : bridge_normShell S k, Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) :=
      Finset.sum_le_sum fun I _ => hterm I
    _ = (Fintype.card (bridge_normShell S k) : ℝ) *
        Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) := by simp
    _ = ((bridge_normShell S k).ncard : ℝ) *
        Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) := by simp
    _ ≤ (C * U) * Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) :=
      mul_le_mul_of_nonneg_right hbound
        (Real.rpow_pos_of_pos (by positivity : 0 < ((2 ^ k : ℕ) : ℝ)) _).le
    _ = C * ((2 ^ (k + 1) : ℕ) : ℝ) *
        Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) := by dsimp [U]

/-- Sharp convergence at s>1, required for σ just above 1/2.
Uses COUNT and dyadic geometric series. -/
theorem a2_bridge_COUNT_summable (S : SData F CE condη) (s : ℝ) (hs : 1 < s) :
    Summable (fun I : S.ExtIdeal => Real.rpow (idealNorm I.1) (-s)) := by
  let f : S.ExtIdeal → ℝ := fun I => Real.rpow (idealNorm I.1) (-s)
  change Summable f
  have hf : ∀ I, 0 ≤ f I := by
    intro I
    have hnorm : 0 < idealNorm I.1 := by
      change 0 < (Ideal.absNorm I.1 : ℝ)
      exact_mod_cast bridge_ext_norm_pos S I
    exact (Real.rpow_pos_of_pos hnorm _).le
  have hinner : ∀ k, Summable fun I : bridge_normShell S k => f I.1 := by
    intro k
    letI : Fintype (bridge_normShell S k) := (bridge_normShell_finite S k).fintype
    exact Summable.of_finite
  obtain ⟨C, hC, hcount⟩ := a2_bridge_COUNT S
  let r : ℝ := Real.rpow 2 (1 - s)
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable fun k : ℕ => r ^ k :=
    summable_geometric_of_lt_one hrpos.le hrlt
  have hmajor : Summable fun k : ℕ => (2 * C) * r ^ k := hgeom.mul_left (2 * C)
  have houter : Summable fun k : ℕ =>
      ∑' I : bridge_normShell S k, f I.1 := by
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun I => hf I.1) ?_ hmajor
    intro k
    calc
      ∑' I : bridge_normShell S k, f I.1 ≤
          C * ((2 ^ (k + 1) : ℕ) : ℝ) *
            Real.rpow ((2 ^ k : ℕ) : ℝ) (-s) := by
        simpa [f] using bridge_normShell_tsum_le S s C hcount hs k
      _ = C * (2 * r ^ k) := by
        calc
          _ = C * (((2 ^ (k + 1) : ℕ) : ℝ) *
              Real.rpow ((2 ^ k : ℕ) : ℝ) (-s)) := by ring
          _ = C * (2 * r ^ k) := by rw [bridge_dyad_scale]; simp [r]
      _ = (2 * C) * r ^ k := by ring
  exact (summable_partition hf (bridge_normShell_partition S)).2 ⟨hinner, houter⟩

private lemma bridge_harmonic_fiber_le (S : SData F CE condη)
    (T : Finset S.ExtIdeal) (C : ℝ)
    (hcount : ∀ X : ℝ, 1 ≤ X →
      ({I : S.ExtIdeal | idealNorm I.1 ≤ X}.ncard : ℝ) ≤ C * X) (k : ℕ) :
    (∑ I ∈ T with Nat.log 2 (Ideal.absNorm I.1) = k, (idealNorm I.1)⁻¹) ≤ 2 * C := by
  classical
  let Fk := T.filter (fun I => Nat.log 2 (Ideal.absNorm I.1) = k)
  let V : ℝ := ((2 ^ (k + 1) : ℕ) : ℝ)
  have hV : 1 ≤ V := by
    dsimp [V]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)))
  have hcut := a2_bridge_COUNT_finite S V (by linarith)
  have hsubset : (Fk : Set S.ExtIdeal) ⊆ {I : S.ExtIdeal | idealNorm I.1 ≤ V} := by
    intro I hI
    have hIfin : I ∈ Fk := by simpa using hI
    have hIfilter : I ∈ T.filter (fun I => Nat.log 2 (Ideal.absNorm I.1) = k) := by
      simpa [Fk] using hIfin
    rcases Finset.mem_filter.mp hIfilter with ⟨_, hlog⟩
    have hqpos : Ideal.absNorm I.1 ≠ 0 := (bridge_ext_norm_pos S I).ne'
    have hlow : 2 ^ k ≤ Ideal.absNorm I.1 := by
      rw [← hlog]
      exact Nat.pow_log_le_self 2 hqpos
    have hhigh : Ideal.absNorm I.1 < 2 ^ (k + 1) := by
      rw [← hlog]
      exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
    change idealNorm I.1 ≤ V
    dsimp [V, idealNorm]
    exact_mod_cast hhigh.le
  have hcardNat : (Fk : Set S.ExtIdeal).ncard ≤
      {I : S.ExtIdeal | idealNorm I.1 ≤ V}.ncard := Set.ncard_le_ncard hsubset hcut.1
  have hcard : (Fk.card : ℝ) ≤ C * V := by
    calc
      (Fk.card : ℝ) = ((Fk : Set S.ExtIdeal).ncard : ℝ) := by simp
      _ ≤ ({I : S.ExtIdeal | idealNorm I.1 ≤ V}.ncard : ℝ) := by exact_mod_cast hcardNat
      _ ≤ C * V := hcount V hV
  have hbase : 0 < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hratio : V * ((2 ^ k : ℕ) : ℝ)⁻¹ = 2 := by
    dsimp [V]
    rw [pow_succ, Nat.cast_mul]
    field_simp [hbase.ne']
    norm_num
  have hterm {I : S.ExtIdeal} (hI : I ∈ Fk) :
      (idealNorm I.1)⁻¹ ≤ ((2 ^ k : ℕ) : ℝ)⁻¹ := by
    have hIfilter : I ∈ T.filter (fun I => Nat.log 2 (Ideal.absNorm I.1) = k) := by
      simpa [Fk] using hI
    rcases Finset.mem_filter.mp hIfilter with ⟨_, hlog⟩
    have hqpos : Ideal.absNorm I.1 ≠ 0 := (bridge_ext_norm_pos S I).ne'
    have hlow : 2 ^ k ≤ Ideal.absNorm I.1 := by
      rw [← hlog]
      exact Nat.pow_log_le_self 2 hqpos
    have hlowReal : ((2 ^ k : ℕ) : ℝ) ≤ idealNorm I.1 := by
      change ((2 ^ k : ℕ) : ℝ) ≤ (Ideal.absNorm I.1 : ℝ)
      exact_mod_cast hlow
    simpa [one_div] using one_div_le_one_div_of_le hbase hlowReal
  change (∑ I ∈ Fk, (idealNorm I.1)⁻¹) ≤ 2 * C
  calc
    ∑ I ∈ Fk, (idealNorm I.1)⁻¹ ≤
        ∑ I ∈ Fk, ((2 ^ k : ℕ) : ℝ)⁻¹ := Finset.sum_le_sum fun I hI => hterm hI
    _ = (Fk.card : ℝ) * ((2 ^ k : ℕ) : ℝ)⁻¹ := by simp
    _ ≤ (C * V) * ((2 ^ k : ℕ) : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * C := by
      calc
        _ = C * (V * ((2 ^ k : ℕ) : ℝ)⁻¹) := by ring
        _ = C * 2 := by rw [hratio]
        _ = 2 * C := by ring

/-- Harmonic mass on finite norm cutoffs.
Uses COUNT, COUNT_finite and dyadic decomposition. -/
theorem a2_bridge_COUNT_harmonic (S : SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∑ I ∈ bridgeNormFinset S X, (idealNorm I.1)⁻¹ ≤ C * Real.log (2 * X) := by
  obtain ⟨C₀, hC₀, hcount⟩ := a2_bridge_COUNT S
  let C : ℝ := (2 * C₀) / Real.log 2
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro X hX
    classical
    let n : ℕ := ⌊X⌋₊
    let N : ℕ := Nat.log 2 n
    let T : Finset S.ExtIdeal := bridgeNormFinset S X
    have hfinite := a2_bridge_COUNT_finite S X (by linarith)
    have hmaps : (T : Set S.ExtIdeal).MapsTo
        (fun I : S.ExtIdeal => Nat.log 2 (Ideal.absNorm I.1)) (Finset.range (N + 1)) := by
      intro I hI
      simp only [Finset.mem_coe, Finset.mem_range]
      have hnorm : idealNorm I.1 ≤ X := by
        exact (hfinite.2 I).mp (by simpa [T] using hI)
      have hnormNat : Ideal.absNorm I.1 ≤ n := by
        apply (Nat.le_floor_iff (le_trans (by norm_num) hX)).mpr
        simpa [idealNorm] using hnorm
      dsimp [N]
      exact Nat.lt_succ_of_le (Nat.log_mono_right hnormNat)
    have hdecomp :
        (∑ I ∈ T, (idealNorm I.1)⁻¹) =
          ∑ k ∈ Finset.range (N + 1),
            ∑ I ∈ T with Nat.log 2 (Ideal.absNorm I.1) = k, (idealNorm I.1)⁻¹ := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    have hfibers :
        (∑ k ∈ Finset.range (N + 1),
          ∑ I ∈ T with Nat.log 2 (Ideal.absNorm I.1) = k, (idealNorm I.1)⁻¹) ≤
          ∑ k ∈ Finset.range (N + 1), (2 * C₀) :=
      Finset.sum_le_sum fun k hk => bridge_harmonic_fiber_le S T C₀ hcount k
    let H : ℝ := 2 * C₀
    have hn : 1 ≤ n := by
      dsimp [n]
      exact Nat.le_floor (by exact_mod_cast hX)
    have hpow : 2 ^ (N + 1) ≤ 2 * n := by
      calc
        2 ^ (N + 1) = 2 ^ N * 2 := by rw [pow_succ]
        _ ≤ n * 2 := Nat.mul_le_mul_right 2
          (Nat.pow_log_le_self 2 (by omega : n ≠ 0))
        _ = 2 * n := by omega
    have hlogNat : N + 1 ≤ Nat.log 2 (2 * n) := by
      dsimp [N]
      exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
    have hlogb : ((N + 1 : ℕ) : ℝ) ≤ Real.logb 2 (2 * (n : ℝ)) := by
      calc
        ((N + 1 : ℕ) : ℝ) ≤ (Nat.log 2 (2 * n) : ℝ) := by exact_mod_cast hlogNat
        _ = (Nat.log2 (2 * n) : ℝ) := by simp [Nat.log2_eq_log_two]
        _ ≤ Real.logb 2 (2 * (n : ℝ)) := by
          convert Real.log2_le_logb (2 * n) using 1 <;> norm_cast
    have hfloor : (n : ℝ) ≤ X := by dsimp [n]; exact Nat.floor_le (le_trans (by norm_num) hX)
    have hlogbX : Real.logb 2 (2 * (n : ℝ)) ≤ Real.logb 2 (2 * X) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
        (by nlinarith [hfloor])
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogCount : ((N + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (2 * X) := by
      apply (le_div_iff₀ hlog2).1
      simpa [Real.logb] using hlogb.trans hlogbX
    have hsum : (∑ I ∈ T, (idealNorm I.1)⁻¹) ≤ H * (N + 1 : ℕ) := by
      rw [hdecomp]
      calc
        _ ≤ ∑ k ∈ Finset.range (N + 1), (2 * C₀) := hfibers
        _ = H * (N + 1 : ℕ) := by simp [H, Finset.sum_const, nsmul_eq_mul]; ring
    have hfinal : H * (N + 1 : ℕ) ≤ C * Real.log (2 * X) := by
      dsimp [C, H]
      calc
        2 * C₀ * (N + 1 : ℕ) ≤
            (2 * C₀ * Real.log (2 * X)) / Real.log 2 := by
          apply (le_div_iff₀ hlog2).2
          calc
            2 * C₀ * (N + 1 : ℕ) * Real.log 2 =
                (2 * C₀) * (((N + 1 : ℕ) : ℝ) * Real.log 2) := by ring
            _ ≤ (2 * C₀) * Real.log (2 * X) :=
              mul_le_mul_of_nonneg_left hlogCount
                (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hC₀))
        _ = (2 * C₀ / Real.log 2) * Real.log (2 * X) := by ring
    calc
      ∑ I ∈ bridgeNormFinset S X, (idealNorm I.1)⁻¹ = ∑ I ∈ T, (idealNorm I.1)⁻¹ := by rfl
      _ ≤ H * (N + 1 : ℕ) := hsum
      _ ≤ C * Real.log (2 * X) := hfinal

end ArtinPrimitiveRoots.A2
