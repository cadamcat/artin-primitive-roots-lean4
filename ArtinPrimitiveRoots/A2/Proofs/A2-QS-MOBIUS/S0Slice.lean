import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0

/-!
# A2-QS-MOBIUS, part S0: class/dyad slicing for positive row scale

`qs_class_dyad_slice_S0` has no hypothesis on the row scale `M`.  For `M ≤ 0` every row has
`N a / M ≤ 0`, where the cap weight need not vanish (`W(0) ≥ 1`), so `qsHighEnergy` has no
finite row support and the Cauchy–Schwarz step over the parts has no finite sum to act on.  The
corrected statement below adds `0 < M` and is otherwise identical.  With `0 < M`,
`W(N a / M) = 0` once `N a ≥ 5M/2`, so each energy is a finite sum.  Its consumer is the
high-core bound B0 (`qs_high_core_bound_B0`), whose rows are empty at `M = 0` and which has
`M > 0` otherwise.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

private theorem qs_dyad_partition_index_spec_slice_pos
    (N : ℝ) (hN : 1 ≤ N) (c : Ideal (𝓞 K)) (hc : QSAdm m qS c)
    (hcn : qsN c ≤ N) :
    ⌊Real.logb 2 (N / qsN c)⌋₊ < Nat.ceil (Real.logb 2 N) + 1 ∧
      N / 2 ^ (⌊Real.logb 2 (N / qsN c)⌋₊ + 1) < qsN c ∧
      qsN c ≤ N / 2 ^ ⌊Real.logb 2 (N / qsN c)⌋₊ := by
  have hc0 : c ≠ ⊥ := hc.2.1.1
  have hnormNat : 0 < Ideal.absNorm c := by
    apply Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
    exact mem_nonZeroDivisors_iff_ne_zero.mpr hc0
  have hnormPos : 0 < qsN c := by exact_mod_cast hnormNat
  have hnormOne : 1 ≤ qsN c := by
    have hn : 1 ≤ Ideal.absNorm c := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnormNat)
    exact_mod_cast hn
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have htpos : 0 < N / qsN c := div_pos hNpos hnormPos
  have htge : 1 ≤ N / qsN c := (le_div_iff₀ hnormPos).2 (by simpa using hcn)
  have htle : N / qsN c ≤ N := div_le_self hNpos.le hnormOne
  let j : ℕ := ⌊Real.logb 2 (N / qsN c)⌋₊
  have hlog0 : 0 ≤ Real.logb 2 (N / qsN c) :=
    Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) htge
  have hjlo : (j : ℝ) ≤ Real.logb 2 (N / qsN c) := Nat.floor_le hlog0
  have hjhi : Real.logb 2 (N / qsN c) < (j : ℝ) + 1 := by
    simpa [j] using Nat.lt_floor_add_one (Real.logb 2 (N / qsN c))
  have hlogN : Real.logb 2 (N / qsN c) ≤ Real.logb 2 N :=
    (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ)) htpos hNpos).2 htle
  have hceil : Real.logb 2 N ≤ (Nat.ceil (Real.logb 2 N) : ℝ) := Nat.le_ceil _
  have hjbound : j ≤ Nat.ceil (Real.logb 2 N) := by
    exact_mod_cast le_trans hjlo (le_trans hlogN hceil)
  have hpowloR : (2 : ℝ) ^ (j : ℝ) ≤ N / qsN c :=
    (Real.le_logb_iff_rpow_le (by norm_num : 1 < (2 : ℝ)) htpos).mp hjlo
  have hpowlo : (2 : ℝ) ^ j ≤ N / qsN c := by
    simpa only [Real.rpow_natCast] using hpowloR
  have hjhi' : Real.logb 2 (N / qsN c) < ((j + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hjhi
  have hpowhiR : N / qsN c < (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num : 1 < (2 : ℝ)) htpos).mp hjhi'
  have hpowhi : N / qsN c < (2 : ℝ) ^ (j + 1) := by
    simpa only [Real.rpow_natCast] using hpowhiR
  have hNlt : N < (2 : ℝ) ^ (j + 1) * qsN c := (div_lt_iff₀ hnormPos).mp hpowhi
  have hlowDen : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hlow : N / (2 : ℝ) ^ (j + 1) < qsN c :=
    (div_lt_iff₀ hlowDen).2 (by simpa [mul_comm] using hNlt)
  have hmul : (2 : ℝ) ^ j * qsN c ≤ N := (le_div_iff₀ hnormPos).mp hpowlo
  have hhighDen : 0 < (2 : ℝ) ^ j := by positivity
  have hhigh : qsN c ≤ N / (2 : ℝ) ^ j :=
    (le_div_iff₀ hhighDen).2 (by simpa [mul_comm] using hmul)
  refine ⟨Nat.lt_succ_of_le hjbound, ?_, ?_⟩
  · simpa [j] using hlow
  · simpa [j] using hhigh

private theorem qs_class_dyad_partition_slice_pos
    (F : QSFamily m qS) (N : ℝ) (hN : 1 ≤ N)
    (hcols : ∀ c ∈ qsUpTo m qS N, QSAdm m qS c) :
    ∃ parts : Finset (Finset (Ideal (𝓞 K))),
      ((parts.card : ℕ) : ℝ) ≤
          (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
            ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) ∧
      (∀ P ∈ parts, P ⊆ qsUpTo m qS N) ∧
      (∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) ∧
      (∀ P ∈ parts, ∃ j : ℕ, ∀ c ∈ P,
        N / 2 ^ (j + 1) < qsN c ∧ qsN c ≤ N / 2 ^ j) ∧
      (∀ P ∈ parts, ∀ c ∈ P, ∀ d ∈ P,
        ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
          (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
          ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd) ∧
      (∀ c ∈ qsUpTo m qS N, ∃ P ∈ parts, c ∈ P) := by
  classical
  letI : Finite (ClassFieldTheory.RayClassGroup m) := ClassFieldTheory.rayClassGroup_finite K m
  let G := ClassFieldTheory.RayClassGroup m
  letI : Fintype G := Fintype.ofFinite G
  let cols := qsUpTo m qS N
  let L := Nat.ceil (Real.logb 2 N) + 1
  let rayOf (c : Ideal (𝓞 K)) : G :=
    if hc : c ∈ cols then
      ArtinPrimitiveRoots.Hecke.rayClass m c (hcols c hc).2.1
    else 1
  let dyadOf (c : Ideal (𝓞 K)) : ℕ :=
    if hc : c ∈ cols then ⌊Real.logb 2 (N / qsN c)⌋₊ else 0
  have hdyadLt (c : Ideal (𝓞 K)) (hc : c ∈ cols) : dyadOf c < L := by
    have hcn : qsN c ≤ N := by
      dsimp [cols, qsUpTo] at hc
      exact (Finset.mem_filter.mp hc).2.2
    simpa [dyadOf, hc, L] using
      (qs_dyad_partition_index_spec_slice_pos N hN c (hcols c hc) hcn).1
  let label (c : Ideal (𝓞 K)) : G × Fin L :=
    (rayOf c, ⟨dyadOf c, by
      by_cases hc : c ∈ cols
      · exact hdyadLt c hc
      · simp [dyadOf, hc, L]⟩)
  let part (i : G × Fin L) : Finset (Ideal (𝓞 K)) :=
    cols.filter (fun c => label c = i)
  let idxAll : Finset (G × Fin L) := Finset.univ
  let idxNZ : Finset (G × Fin L) := idxAll.filter (fun i => (part i).Nonempty)
  let parts : Finset (Finset (Ideal (𝓞 K))) := idxNZ.image part
  have hcardNat : parts.card ≤ Nat.card G * L := by
    calc
      parts.card ≤ idxNZ.card := by
        dsimp [parts]
        exact Finset.card_image_le
      _ ≤ idxAll.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.card G * L := by
        simp [idxAll, L, Nat.card_eq_fintype_card]
  have hcardReal : (parts.card : ℝ) ≤
      (Nat.card G : ℝ) * ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) := by
    simpa [L] using (show (parts.card : ℝ) ≤ (Nat.card G * L : ℕ) by exact_mod_cast hcardNat)
  have hsubset : ∀ P ∈ parts, P ⊆ cols := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨i, hi, rfl⟩
    exact Finset.filter_subset _ _
  have hdisjoint : ∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q := by
    intro P hP Q hQ hPQ
    rcases Finset.mem_image.mp hP with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hQ with ⟨j, hj, rfl⟩
    apply Finset.disjoint_left.mpr
    intro c hcP hcQ
    have hci := (Finset.mem_filter.mp hcP).2
    have hcj := (Finset.mem_filter.mp hcQ).2
    have hij : i = j := hci.symm.trans hcj
    exact hPQ (congrArg part hij)
  have hdyad : ∀ P ∈ parts, ∃ j : ℕ, ∀ c ∈ P,
      N / 2 ^ (j + 1) < qsN c ∧ qsN c ≤ N / 2 ^ j := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨i, hi, rfl⟩
    refine ⟨i.2, ?_⟩
    intro c hc
    have hfilter := (Finset.mem_filter.mp hc).2
    have hlabel := congrArg (fun x : G × Fin L => x.2.val) hfilter
    have hdyadEq : dyadOf c = i.2.val := by simpa [label] using hlabel
    have hcCols := (Finset.mem_filter.mp hc).1
    have hcn : qsN c ≤ N := by
      dsimp [cols, qsUpTo] at hcCols
      exact (Finset.mem_filter.mp hcCols).2.2
    have hspec := qs_dyad_partition_index_spec_slice_pos N hN c (hcols c hcCols) hcn
    have hfloorEq : ⌊Real.logb 2 (N / qsN c)⌋₊ = i.2.val := by
      simpa [dyadOf, hcCols] using hdyadEq
    simpa [hfloorEq] using hspec.2
  have hray : ∀ P ∈ parts, ∀ c ∈ P, ∀ d ∈ P,
      ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
        (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
        ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd := by
    intro P hP c hcP d hdP
    rcases Finset.mem_image.mp hP with ⟨i, hi, rfl⟩
    have hcFilt := Finset.mem_filter.mp hcP
    have hdFilt := Finset.mem_filter.mp hdP
    rcases hcols c hcFilt.1 with ⟨_, hcRay, _⟩
    rcases hcols d hdFilt.1 with ⟨_, hdRay, _⟩
    have hrc : ArtinPrimitiveRoots.Hecke.rayClass m c hcRay = rayOf c := by
      dsimp [rayOf]
      rw [dif_pos hcFilt.1]
    have hrd : ArtinPrimitiveRoots.Hecke.rayClass m d hdRay = rayOf d := by
      dsimp [rayOf]
      rw [dif_pos hdFilt.1]
    have hci : rayOf c = i.1 := congrArg (fun x : G × Fin L => x.1) hcFilt.2
    have hdi : rayOf d = i.1 := congrArg (fun x : G × Fin L => x.1) hdFilt.2
    refine ⟨hcRay, hdRay, ?_⟩
    calc
      ArtinPrimitiveRoots.Hecke.rayClass m c hcRay = rayOf c := hrc
      _ = i.1 := hci
      _ = rayOf d := hdi.symm
      _ = ArtinPrimitiveRoots.Hecke.rayClass m d hdRay := hrd.symm
  have hcover : ∀ c ∈ cols, ∃ P ∈ parts, c ∈ P := by
    intro c hc
    have hidxNZ : label c ∈ idxNZ := by
      apply Finset.mem_filter.mpr
      have hidxAll : label c ∈ idxAll := by simp [idxAll]
      refine ⟨hidxAll, ?_⟩
      refine ⟨c, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨hc, rfl⟩
    refine ⟨part (label c), Finset.mem_image.mpr ⟨label c, hidxNZ, rfl⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hc, rfl⟩
  exact ⟨parts, hcardReal, hsubset, hdisjoint, hdyad, hray, hcover⟩

private theorem qs_high_energy_finite_sum_slice_pos
    (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ : ℝ) (hM : 0 < M) (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) :
    qsHighEnergy F W M κ cols z =
      ∑ a ∈ qsHighRows m qS M κ,
        W (qsN a / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2 := by
  classical
  let rows := qsHighRows m qS M κ
  let rowCond (I : Ideal (𝓞 K)) :=
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ∧ IsCoprime I qS ∧ κ < (qsSfNorm I : ℝ)
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun a =>
    if rowCond a.1 then
      W (qsN a.1 / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a.1‖ ^ 2
    else 0
  have hrow_nebot (I : Ideal (𝓞 K)) (hI : I ∈ rows) : I ≠ ⊥ := by
    dsimp [rows, qsHighRows] at hI
    exact (Finset.mem_filter.mp hI).2.1.1
  let rowEmbed (r : rows) : {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    ⟨r.1, hrow_nebot r.1 r.2⟩
  have hEmbedInj : Function.Injective rowEmbed := by
    intro r s h
    apply Subtype.ext
    change (rowEmbed r).1 = (rowEmbed s).1
    exact congrArg (fun x : {I : Ideal (𝓞 K) // I ≠ ⊥} => x.1) h
  let rowsNZ : Finset {I : Ideal (𝓞 K) // I ≠ ⊥} := rows.attach.image rowEmbed
  have hzero : ∀ a : {I : Ideal (𝓞 K) // I ≠ ⊥}, a ∉ rowsNZ → f a = 0 := by
    intro a ha
    by_cases hrow : rowCond a.1
    · by_cases hWzero : W (qsN a.1 / M) = 0
      · simp [f, hrow, hWzero]
      · have hlt : qsN a.1 / M < 5 / 2 := by
          apply lt_of_not_ge
          intro hge
          exact hWzero (hW.2.2.2 _ hge)
        have hNbound : (Ideal.absNorm a.1 : ℝ) < 3 * M := by
          dsimp [qsN] at hlt ⊢
          have hlt' := (div_lt_iff₀ hM).mp hlt
          nlinarith
        have hFloor : Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊ := Nat.le_floor hNbound.le
        have hbase : a.1 ∈
            (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset := by
          exact (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).mem_toFinset.mpr hFloor
        have hrowmem : a.1 ∈ rows := by
          dsimp [rows, qsHighRows]
          rw [Finset.mem_filter]
          exact ⟨hbase, hrow⟩
        let r : rows := ⟨a.1, hrowmem⟩
        have hmem : rowEmbed r ∈ rowsNZ :=
          Finset.mem_image.mpr ⟨r, Finset.mem_attach _ _, rfl⟩
        have heq : rowEmbed r = a := by
          apply Subtype.ext
          rfl
        have hmemA : a ∈ rowsNZ := by rw [← heq]; exact hmem
        exact (ha hmemA).elim
    · simp [f, hrow]
  have hfinite :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) = ∑ a ∈ rowsNZ, f a := by
    exact tsum_eq_sum (L := SummationFilter.unconditional _) hzero
  have hrowTerm (r : rows) :
      f (rowEmbed r) =
        W (qsN r.1 / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue r.1‖ ^ 2 := by
    have hr : rowCond r.1 := by
      have hrmem : r.1 ∈ rows := r.2
      change r.1 ∈
        ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊).toFinset).filter
          (fun I => rowCond I) at hrmem
      exact (Finset.mem_filter.mp hrmem).2
    simp [f, rowCond, rowEmbed, hr]
  unfold qsHighEnergy
  change (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) = _
  rw [hfinite]
  calc
    ∑ a ∈ rowsNZ, f a = ∑ r ∈ rows.attach, f (rowEmbed r) :=
      Finset.sum_image hEmbedInj.injOn
    _ = ∑ r ∈ rows.attach,
          W (qsN r.1 / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue r.1‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hrowTerm r
    _ = ∑ a ∈ rows,
          W (qsN a / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2 :=
          Finset.sum_attach rows (fun a =>
            W (qsN a / M) * ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2)

/-- S0 (IMPL, corrected `qs_class_dyad_slice_S0`): class and dyad slicing for `0 < M`: the
up-to columns split into at most `h_m (⌈log₂ N⌉₊ + 1)` pairwise disjoint parts, each inside one
ray class and one dyad `(N/2^{j+1}, N/2^j]`, and the high-core energy is at most the number of
parts times the sum of the part energies. -/
theorem qs_class_dyad_slice_pos_S0 (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hM : 0 < M) (hN : 1 ≤ N) (z : Ideal (𝓞 K) → ℂ) :
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
  classical
  have hcols : ∀ c ∈ qsUpTo m qS N, QSAdm m qS c := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2.1
  obtain ⟨parts, hcard, hsubset, hdisjoint, hdyad, hray, hcover⟩ :=
    qs_class_dyad_partition_slice_pos F N hN hcols
  refine ⟨parts, hcard, hsubset, hdisjoint, hdyad, hray, ?_⟩
  have hpairwise :
      Set.PairwiseDisjoint (↑parts : Set (Finset (Ideal (𝓞 K)))) (fun P => P) := by
    intro P hP Q hQ hPQ
    exact hdisjoint P hP Q hQ hPQ
  have hunion : parts.biUnion id = qsUpTo m qS N := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_biUnion.mp hc with ⟨P, hP, hcP⟩
      exact hsubset P hP hcP
    · intro hc
      obtain ⟨P, hP, hcP⟩ := hcover c hc
      exact Finset.mem_biUnion.mpr ⟨P, hP, hcP⟩
  have hsplit (a : Ideal (𝓞 K)) :
      (∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue a) =
        ∑ P ∈ parts, ∑ c ∈ P, z c * (F.character c).idealValue a := by
    rw [← hunion]
    exact Finset.sum_biUnion hpairwise
  have hrowCauchy (a : Ideal (𝓞 K)) :
      ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue a‖ ^ 2 ≤
        (parts.card : ℝ) *
          ∑ P ∈ parts, ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 := by
    rw [hsplit a]
    have htri :
        ‖∑ P ∈ parts, ∑ c ∈ P, z c * (F.character c).idealValue a‖ ≤
          ∑ P ∈ parts, ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ := by
      exact norm_sum_le _ _
    have hnormNonneg :
        0 ≤ ‖∑ P ∈ parts, ∑ c ∈ P, z c * (F.character c).idealValue a‖ := norm_nonneg _
    have hsumNonneg :
        0 ≤ ∑ P ∈ parts, ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ :=
      Finset.sum_nonneg fun P hP => norm_nonneg _
    calc
      ‖∑ P ∈ parts, ∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 ≤
          (∑ P ∈ parts, ‖∑ c ∈ P, z c * (F.character c).idealValue a‖) ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr htri) (add_nonneg hnormNonneg hsumNonneg)]
      _ ≤ (parts.card : ℝ) *
            ∑ P ∈ parts, ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
  let rows := qsHighRows m qS M κ
  have hrowWeighted (a : Ideal (𝓞 K)) :
      W (qsN a / M) * ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue a‖ ^ 2 ≤
        (parts.card : ℝ) *
          ∑ P ∈ parts,
            W (qsN a / M) * ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 := by
    calc
      _ ≤ W (qsN a / M) *
            ((parts.card : ℝ) *
              ∑ P ∈ parts, ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hrowCauchy a) (hW.2.1 _)
      _ = (parts.card : ℝ) *
            ∑ P ∈ parts,
              W (qsN a / M) * ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 := by
        calc
          _ = (parts.card : ℝ) *
                (W (qsN a / M) *
                  ∑ P ∈ parts, ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2) := by ring
          _ = _ := by rw [Finset.mul_sum]
  have hsumBound :
      (∑ a ∈ rows,
        W (qsN a / M) * ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue a‖ ^ 2) ≤
        (parts.card : ℝ) *
          ∑ P ∈ parts, ∑ a ∈ rows,
            W (qsN a / M) * ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 := by
    calc
      _ ≤ ∑ a ∈ rows,
            (parts.card : ℝ) *
              ∑ P ∈ parts,
                W (qsN a / M) * ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 :=
          Finset.sum_le_sum fun a ha => hrowWeighted a
      _ = (parts.card : ℝ) *
            ∑ a ∈ rows, ∑ P ∈ parts,
              W (qsN a / M) * ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (parts.card : ℝ) *
            ∑ P ∈ parts, ∑ a ∈ rows,
              W (qsN a / M) * ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 := by
          congr 1
          rw [Finset.sum_comm]
  calc
    qsHighEnergy F W M κ (qsUpTo m qS N) z =
        ∑ a ∈ rows,
          W (qsN a / M) * ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue a‖ ^ 2 :=
      qs_high_energy_finite_sum_slice_pos F W hW M κ hM (qsUpTo m qS N) z
    _ ≤ (parts.card : ℝ) *
          ∑ P ∈ parts, ∑ a ∈ rows,
            W (qsN a / M) * ‖∑ c ∈ P, z c * (F.character c).idealValue a‖ ^ 2 := hsumBound
    _ = (parts.card : ℝ) * ∑ P ∈ parts, qsHighEnergy F W M κ P z := by
          congr 1
          apply Finset.sum_congr rfl
          intro P hP
          exact (qs_high_energy_finite_sum_slice_pos F W hW M κ hM P z).symm

end ArtinPrimitiveRoots.A2
