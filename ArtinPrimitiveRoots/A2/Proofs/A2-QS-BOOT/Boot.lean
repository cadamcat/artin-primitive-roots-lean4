import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».Block
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M2
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0Slice
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».B0.Final

/-!
# A2-QS-BOOT: monotone row norm, finite descent, bootstrap and the core theorem
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- Row split (IMPL; RETIER `qs_monotone_row_norm`): the squarefree rows of norm
`≤ κ` give `B1(κ, N)`; the rows with `κ < N a ≤ M` have `sf(a) = N a > κ` and `W(N a/M) ≥ 1`,
so they are dominated by the high-core matrix. -/
theorem qs_row_split_B (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hM : 0 < M) (hκ : 0 ≤ κ) :
    qsNorm F M N ≤ qsNorm F κ N + qsHighNorm F W M N κ := by
  classical
  let rowsM := qsUpTo m qS M
  let rowsLow := rowsM.filter (fun d => (Ideal.absNorm d : ℝ) ≤ κ)
  let rowsHigh := rowsM.filter (fun d => κ < (Ideal.absNorm d : ℝ))
  have hlowSub : rowsLow ⊆ qsUpTo m qS κ := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdM, hdk⟩
    rcases Finset.mem_filter.mp hdM with ⟨_, ⟨hadm, _⟩⟩
    have hfloor : Ideal.absNorm d ≤ ⌊κ⌋₊ := Nat.le_floor (by exact_mod_cast hdk)
    have hbase : d ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊κ⌋₊).toFinset :=
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊κ⌋₊).mem_toFinset.mpr hfloor
    change d ∈ ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊κ⌋₊).toFinset).filter
      (fun I => QSAdm m qS I ∧ (Ideal.absNorm I : ℝ) ≤ κ)
    exact Finset.mem_filter.mpr ⟨hbase, hadm, hdk⟩
  have sum_mono_of_subset {ι : Type} [DecidableEq ι] (s t : Finset ι) (hst : s ⊆ t)
      (g : ι → ℝ) (hg : ∀ I, 0 ≤ g I) :
      (∑ I ∈ s, g I) ≤ ∑ I ∈ t, g I := by
    have hdecomp : (∑ I ∈ t, g I) =
        (∑ I ∈ t \ s, g I) + ∑ I ∈ s, g I := by
      rw [Finset.sum_sdiff hst]
    have hnonneg : 0 ≤ ∑ I ∈ t \ s, g I := Finset.sum_nonneg fun I _ => hg I
    rw [hdecomp]
    linarith
  have hB : 0 ≤ qsNorm F κ N + qsHighNorm F W M N κ := by
    change 0 ≤ ‖OAI.FiniteSieveOperator.operator (qsMatrix F κ N)‖ ^ 2 +
      ‖OAI.FiniteSieveOperator.operator (qsHighMatrix F W M N κ)‖ ^ 2
    positivity
  apply qs_norm_le_of_energy_M0 F M N _ hB
  intro z
  let E : Ideal (𝓞 K) → ℝ := fun d =>
    ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue d‖ ^ 2
  have hsplit : (∑ d ∈ rowsM, E d) =
      (∑ d ∈ rowsLow, E d) + ∑ d ∈ rowsHigh, E d := by
    dsimp [rowsM, rowsLow, rowsHigh]
    rw [← Finset.sum_filter_add_sum_filter_not (s := qsUpTo m qS M)
      (p := fun d => (Ideal.absNorm d : ℝ) ≤ κ)]
    simp [not_le]
  have hlow : (∑ d ∈ rowsLow, E d) ≤
      qsNorm F κ N * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 := by
    calc
      (∑ d ∈ rowsLow, E d) ≤ ∑ d ∈ qsUpTo m qS κ, E d :=
        sum_mono_of_subset rowsLow (qsUpTo m qS κ) hlowSub E (fun _ => sq_nonneg _)
      _ ≤ qsNorm F κ N * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 :=
        qs_energy_le_norm_M0 F κ N z
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ := fun a =>
    if ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
        κ < (qsSfNorm a.1 : ℝ) then
      W (qsN a.1 / M) *
        ‖∑ c ∈ qsUpTo m qS N, z c * (F.character c).idealValue a.1‖ ^ 2
    else 0
  have hSupportFinite :
      {a : {I : Ideal (𝓞 K) // I ≠ ⊥} | Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊}.Finite := by
    apply Set.Finite.of_injOn (f := fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} => a.1)
      (s := {a : {I : Ideal (𝓞 K) // I ≠ ⊥} | Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊})
      (t := {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ ⌊3 * M⌋₊}) ?_ ?_
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊3 * M⌋₊)
    · intro a ha
      exact ha
    · intro a ha b hb hab
      exact Subtype.ext hab
  let support := hSupportFinite.toFinset
  have hzeroOutside (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) (ha : a ∉ support) : f a = 0 := by
    by_contra hne
    have hcond : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a.1 ∧ IsCoprime a.1 qS ∧
        κ < (qsSfNorm a.1 : ℝ) := by
      dsimp [f] at hne
      split_ifs at hne with hcond
      · exact hcond
      · exact (hne rfl).elim
    have hWne : W (qsN a.1 / M) ≠ 0 := by
      intro hW0
      have hne' := hne
      dsimp [f] at hne'
      rw [if_pos hcond, hW0] at hne'
      simp at hne'
    have hcut : qsN a.1 / M < 5 / 2 := by
      by_contra hcut
      exact hWne (hW.2.2.2 _ (le_of_not_gt hcut))
    have hnorm : qsN a.1 ≤ 3 * M := by
      have hmul := (div_lt_iff₀ hM).mp hcut
      dsimp [qsN] at hmul ⊢
      nlinarith
    have hfloor : Ideal.absNorm a.1 ≤ ⌊3 * M⌋₊ := Nat.le_floor (by exact_mod_cast hnorm)
    exact ha (hSupportFinite.mem_toFinset.mpr hfloor)
  have hsumSupport : (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a) =
      ∑ a ∈ support, f a := tsum_eq_sum hzeroOutside
  have hf_nonneg (a : {I : Ideal (𝓞 K) // I ≠ ⊥}) : 0 ≤ f a := by
    dsimp [f]
    split_ifs
    · exact mul_nonneg (hW.2.1 _) (sq_nonneg _)
    · exact le_rfl
  have hrowNonbot (d : Ideal (𝓞 K)) (hd : d ∈ rowsM) : d ≠ ⊥ := by
    have hAdm := (Finset.mem_filter.mp hd).2.1
    exact ((qs_isCoprimeTo_iff_M0 d).mp hAdm.2.1).1
  let toSub : {d : Ideal (𝓞 K) // d ∈ rowsHigh} → {I : Ideal (𝓞 K) // I ≠ ⊥} :=
    fun d => ⟨d.1, hrowNonbot d.1 (Finset.mem_filter.mp d.2).1⟩
  have htoSubInj : Set.InjOn toSub rowsHigh.attach := by
    intro a ha b hb h
    apply Subtype.ext
    exact congrArg (fun x : {I : Ideal (𝓞 K) // I ≠ ⊥} => x.1) h
  let highSub : Finset {I : Ideal (𝓞 K) // I ≠ ⊥} := rowsHigh.attach.image toSub
  have hhighSub : highSub ⊆ support := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    have hdM := (Finset.mem_filter.mp d.2).1
    have hnormM := (Finset.mem_filter.mp hdM).2.2
    have hnorm : Ideal.absNorm d.1 ≤ 3 * M := by
      have : qsN d.1 ≤ M := hnormM
      dsimp [qsN] at this ⊢
      nlinarith [hM]
    have hfloor : Ideal.absNorm d.1 ≤ ⌊3 * M⌋₊ := Nat.le_floor (by exact_mod_cast hnorm)
    exact hSupportFinite.mem_toFinset.mpr hfloor
  have hhighTerm (d : Ideal (𝓞 K)) (hd : d ∈ rowsHigh) :
      E d ≤ f (toSub ⟨d, hd⟩) := by
    have hdM := (Finset.mem_filter.mp hd).1
    have hgt := (Finset.mem_filter.mp hd).2
    rcases Finset.mem_filter.mp hdM with ⟨_, ⟨hAdm, hnormM⟩⟩
    have hsf : qsSfNorm d = Ideal.absNorm d := by
      simpa [pow_two, Ideal.top_mul, Ideal.mul_top] using
        (qs_sfNorm_eq_M1 d ⊤ hAdm.1 (by simp))
    have hcond : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d ∧ IsCoprime d qS ∧
        κ < (qsSfNorm d : ℝ) := by
      exact ⟨hAdm.2.1, hAdm.2.2, by simpa [hsf, qsN] using hgt⟩
    have hWge : 1 ≤ W (qsN d / M) := by
      apply hW.2.2.1
      exact ⟨by positivity, (div_le_one hM).2 hnormM⟩
    have hcond' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m (toSub ⟨d, hd⟩).1 ∧
        IsCoprime (toSub ⟨d, hd⟩).1 qS ∧ κ < (qsSfNorm (toSub ⟨d, hd⟩).1 : ℝ) := by
      simpa [toSub] using hcond
    simp only [E, f, if_pos hcond', toSub]
    simpa using mul_le_mul_of_nonneg_right hWge (sq_nonneg _)
  have hhighRowsEnergy : (∑ d ∈ rowsHigh, E d) ≤
      ∑ a ∈ highSub, f a := by
    calc
      (∑ d ∈ rowsHigh, E d) =
          ∑ d ∈ rowsHigh.attach, E d.1 := by rw [Finset.sum_attach]
      _ ≤ ∑ d ∈ rowsHigh.attach, f (toSub d) :=
        Finset.sum_le_sum fun d hd => hhighTerm d.1 d.2
      _ = ∑ a ∈ highSub, f a := (Finset.sum_image htoSubInj).symm
  have hhighSupport : ∑ a ∈ highSub, f a ≤ ∑ a ∈ support, f a := by
    apply sum_mono_of_subset highSub support hhighSub f hf_nonneg
  have hhighEnergy : (∑ d ∈ rowsHigh, E d) ≤
      qsHighEnergy F W M κ (qsUpTo m qS N) z := by
    calc
      (∑ d ∈ rowsHigh, E d) ≤ ∑ a ∈ highSub, f a := hhighRowsEnergy
      _ ≤ ∑ a ∈ support, f a := hhighSupport
      _ = ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, f a := hsumSupport.symm
      _ = qsHighEnergy F W M κ (qsUpTo m qS N) z := by rfl
  have hhighBound := (qs_high_norm_energy_S0 F W hW M N κ hM).1 z
  have henergy : (∑ d ∈ rowsM, E d) ≤
      (qsNorm F κ N + qsHighNorm F W M N κ) *
        ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 := by
    rw [hsplit]
    calc
      (∑ d ∈ rowsLow, E d) + ∑ d ∈ rowsHigh, E d ≤
          qsNorm F κ N * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 +
            qsHighEnergy F W M κ (qsUpTo m qS N) z := add_le_add hlow hhighEnergy
      _ ≤ qsNorm F κ N * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 +
            qsHighNorm F W M N κ * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 :=
        add_le_add le_rfl hhighBound
      _ = (qsNorm F κ N + qsHighNorm F W M N κ) *
            ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2 := by ring
  exact henergy

/-- B0 (SOL-LEAD; RETIER `qs_boot_parameters_B0`): the high-core norm in the optimized range,
by `r ≥ 40/ε` successive gcd descents with the original `G = N^{1/r}` (`qs_gcd_descent_S0`),
class/dyad slicing (`qs_class_dyad_slice_pos_S0`; rows are empty at `M = 0`), the residual form (`qs_residual_form_S0`), the
block bound (`qs_residual_block_bound_C4`) with `n = N/N g`, `𝔮 = qsBadRad · g`,
`Σ_{N g ≤ G} (N𝔮)^8 ≪ G^{9+η}`, and the terminal unit-column case.  Here
`κ = N²/M · (MN)^η` and `2N(MN)^η ≤ M ≤ N²`. -/
theorem qs_high_core_bound_B0 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ N →
      2 * N * (M * N) ^ η ≤ M → M ≤ N ^ (2 : ℝ) →
      qsHighNorm F W M N (N ^ (2 : ℝ) / M * (M * N) ^ η) ≤
        C * (M * N) ^ δ * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) :=
  QSB0.b0_main F hrf hqS W hW α hα1 hα2 hexp δ hδ

set_option maxHeartbeats 600000 in
open Classical in
/-- Recursion (IMPL): `HasExponent α ⇒ B1(M,N) ≪_δ (MN)^δ (M + N + N^{2α-1} M^{1-α})` for
`M ≥ N ≥ 1`: row split at `κ = N²/M (MN)^η`, `B1(κ,N) = B1(N,κ) ≪ N + κ^α`
with `κ^α ≤ N^{2α-1}M^{1-α}(MN)^{αη}`, B0 for the high rows; endpoints `M ≥ N²` (exponent
`α ≤ 2`) and `N ≤ M < 2N(MN)^η` (`N^α = N^{2α-1}M^{1-α}(M/N)^{α-1}`); a cap weight exists by
`qs_cap_weight_exists_P0`. -/
theorem qs_upTo_recursion_B [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ N → N ≤ M →
      qsNorm F M N ≤ C * (M * N) ^ δ * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
  classical
  obtain ⟨W, hW⟩ := qs_cap_weight_exists_P0
  intro δ hδ
  let δ₀ : ℝ := min (δ / 8) 1
  have hδ8 : 0 < δ / 8 := by positivity
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; exact lt_min hδ8 one_pos
  have hδ₀δ : δ₀ ≤ δ / 8 := by dsimp [δ₀]; exact min_le_left _ _
  have hδ₀1 : δ₀ ≤ 1 := by dsimp [δ₀]; exact min_le_right _ _
  have hδ₀leδ : δ₀ ≤ δ := by linarith
  obtain ⟨η, hη, hηδ₀, C₀, hC₀, hhigh⟩ :=
    qs_high_core_bound_B0 F hrf hqS W hW α hα1 hα2 hexp δ₀ hδ₀
  have hηδ8 : η ≤ δ / 8 := hηδ₀.trans hδ₀δ
  have hη1 : η ≤ 1 := hηδ₀.trans hδ₀1
  let β : ℝ := δ / 8
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβδ : β ≤ δ := by dsimp [β]; linarith
  obtain ⟨C₁, hC₁, hExp⟩ := hexp β hβ
  let q : ℝ := α - 1
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  let C : ℝ := C₀ + C₁ + 2 * C₁ + C₁ * (2 : ℝ) ^ q + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro M N hN hNM
  have hM : 1 ≤ M := hN.trans hNM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let P : ℝ := M * N
  let B : ℝ := N ^ (2 * α - 1) * M ^ (1 - α)
  let H : ℝ := M + N + B
  have hP : 1 ≤ P := by dsimp [P]; nlinarith
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hHbound : M + N ≤ H := by dsimp [H]; nlinarith [hB]
  have hMNpow : P ^ β ≤ P ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hP hβδ
  by_cases hlarge : N ^ 2 ≤ M
  · have hNpow2 : N ^ (2 : ℝ) = N ^ 2 := Real.rpow_natCast N 2
    have hN2M : N ^ (2 : ℝ) ≤ M := by rw [hNpow2]; exact hlarge
    have hNαM : N ^ α ≤ M := by
      calc
        N ^ α ≤ N ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hα2
        _ ≤ M := hN2M
    have hlargeShape : M + N ^ α ≤ 2 * H := by
      dsimp [H]
      nlinarith [hNαM, hB]
    have hlargeBound : qsNorm F M N ≤ 2 * C₁ * P ^ δ * H := by
      calc
        qsNorm F M N ≤ C₁ * P ^ β * (M + N ^ α) := hExp M N hM hN
        _ ≤ C₁ * P ^ β * (2 * H) :=
          mul_le_mul_of_nonneg_left hlargeShape (by positivity)
        _ = 2 * C₁ * P ^ β * H := by ring
        _ ≤ 2 * C₁ * P ^ δ * H := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMNpow (by positivity)) hH
    have hcoef : 2 * C₁ ≤ C := by
      dsimp [C]
      have hpos : 0 ≤ C₁ * (2 : ℝ) ^ q := by positivity
      linarith
    calc
      qsNorm F M N ≤ 2 * C₁ * P ^ δ * H := hlargeBound
      _ ≤ C * P ^ δ * H := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) hH
  · have hMltN2 : M < N ^ 2 := lt_of_not_ge hlarge
    by_cases hsmall : M < 2 * N * P ^ η
    · have hMratio : M / N ≤ 2 * P ^ η := by
        apply (div_le_iff₀ hNpos).2
        calc
          M ≤ 2 * N * P ^ η := le_of_lt hsmall
          _ = (2 * P ^ η) * N := by ring
      have hNshift : N ^ (2 * α) = N ^ (2 * α - 1) * N := by
        calc
          N ^ (2 * α) = N ^ ((2 * α - 1) + 1) :=
            congrArg (fun x : ℝ => N ^ x) (by ring)
          _ = N ^ (2 * α - 1) * N := by rw [Real.rpow_add hNpos, Real.rpow_one]
      have hMshift : (M ^ α)⁻¹ = M ^ (1 - α) / M := by
        rw [← Real.rpow_neg hMpos.le, show (-α : ℝ) = (1 - α) - 1 by ring,
          Real.rpow_sub hMpos, Real.rpow_one]
      have hbase : N ^ (2 * α) / M ^ α = B * (N / M) := by
        calc
          N ^ (2 * α) / M ^ α = N ^ (2 * α) * (M ^ α)⁻¹ := by rw [div_eq_mul_inv]
          _ = (N ^ (2 * α - 1) * N) * (M ^ α)⁻¹ := by rw [hNshift]
          _ = B * (N / M) := by rw [hMshift]; dsimp [B]; ring
      have hsmallEq : N ^ α = B * (M / N) ^ q := by
        have hMcancel : M ^ (1 - α) * M ^ q = 1 := by
          rw [← Real.rpow_add hMpos]
          have hqexp : (1 - α) + q = 0 := by dsimp [q]; ring
          rw [hqexp, Real.rpow_zero]
        have hNquot : N ^ (2 * α - 1) / N ^ q = N ^ α := by
          rw [← Real.rpow_sub hNpos]
          exact congrArg (fun x : ℝ => N ^ x) (by dsimp [q]; ring)
        calc
          N ^ α = (N ^ (2 * α - 1) / N ^ q) *
              (M ^ (1 - α) * M ^ q) := by rw [hNquot, hMcancel]; ring
          _ = N ^ (2 * α - 1) * M ^ (1 - α) * (M ^ q / N ^ q) := by ring
          _ = B * (M / N) ^ q := by
            rw [Real.div_rpow hMpos.le hNpos.le]
      have hratioPow : (M / N) ^ q ≤ (2 * P ^ η) ^ q :=
        Real.rpow_le_rpow (by positivity) hMratio hq0
      have hratioPowEq : (2 * P ^ η) ^ q = (2 : ℝ) ^ q * P ^ (η * q) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul hPpos.le]
      have hsmallNα : N ^ α ≤ B * ((2 : ℝ) ^ q * P ^ (η * q)) := by
        rw [hsmallEq]
        calc
          B * (M / N) ^ q ≤ B * (2 * P ^ η) ^ q :=
            mul_le_mul_of_nonneg_left hratioPow hB
          _ = B * ((2 : ℝ) ^ q * P ^ (η * q)) := by rw [hratioPowEq]
      have hsmallFactor : 1 ≤ (2 : ℝ) ^ q * P ^ (η * q) := by
        have h2 : 1 ≤ (2 : ℝ) ^ q := Real.one_le_rpow (by norm_num) hq0
        have hPηq : 1 ≤ P ^ (η * q) :=
          Real.one_le_rpow hP (mul_nonneg hη.le hq0)
        exact one_le_mul_of_one_le_of_one_le h2 hPηq
      have hsmallShape : M + N ^ α ≤ H * ((2 : ℝ) ^ q * P ^ (η * q)) := by
        calc
          M + N ^ α ≤ M * ((2 : ℝ) ^ q * P ^ (η * q)) +
              B * ((2 : ℝ) ^ q * P ^ (η * q)) := by
            apply add_le_add
            · simpa using mul_le_mul_of_nonneg_left hsmallFactor (by linarith : 0 ≤ M)
            · exact hsmallNα
          _ = (M + B) * ((2 : ℝ) ^ q * P ^ (η * q)) := by ring
          _ ≤ H * ((2 : ℝ) ^ q * P ^ (η * q)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            dsimp [H]
            nlinarith [hN]
      have hetaQ : η * q ≤ η := by
        have hmul := mul_le_mul_of_nonneg_left hq1 hη.le
        nlinarith
      have hsmallExp : β + η * q ≤ δ := by
        dsimp [β]
        nlinarith [hetaQ, hηδ8]
      have hsmallPower : P ^ β * ((2 : ℝ) ^ q * P ^ (η * q)) ≤
          (2 : ℝ) ^ q * P ^ δ := by
        calc
          P ^ β * ((2 : ℝ) ^ q * P ^ (η * q)) =
              (2 : ℝ) ^ q * (P ^ β * P ^ (η * q)) := by ring
          _ = (2 : ℝ) ^ q * P ^ (β + η * q) := by rw [← Real.rpow_add hPpos]
          _ ≤ (2 : ℝ) ^ q * P ^ δ :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hP hsmallExp) (by positivity)
      have hsmallBound : qsNorm F M N ≤ C₁ * (2 : ℝ) ^ q * P ^ δ * H := by
        calc
          qsNorm F M N ≤ C₁ * P ^ β * (M + N ^ α) := hExp M N hM hN
          _ ≤ C₁ * P ^ β * (H * ((2 : ℝ) ^ q * P ^ (η * q))) :=
            mul_le_mul_of_nonneg_left hsmallShape (by positivity)
          _ = C₁ * (P ^ β * ((2 : ℝ) ^ q * P ^ (η * q))) * H := by ring
          _ ≤ C₁ * ((2 : ℝ) ^ q * P ^ δ) * H := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsmallPower hC₁.le) hH
          _ = C₁ * (2 : ℝ) ^ q * P ^ δ * H := by ring
      have hcoef : C₁ * (2 : ℝ) ^ q ≤ C := by
        dsimp [C]
        linarith [hC₀.le, hC₁.le]
      calc
        qsNorm F M N ≤ C₁ * (2 : ℝ) ^ q * P ^ δ * H := hsmallBound
        _ ≤ C * P ^ δ * H := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef (by positivity)) hH
    · have hcutoff : 2 * N * P ^ η ≤ M := le_of_not_gt hsmall
      have hMup : M ≤ N ^ (2 : ℝ) := by
        calc
          M ≤ N ^ 2 := le_of_lt hMltN2
          _ = N ^ (2 : ℝ) := (Real.rpow_natCast N 2).symm
      have hhighBound := hhigh M N hN (by simpa [P] using hcutoff) hMup
      let κ : ℝ := N ^ (2 : ℝ) / M * P ^ η
      have hκpos : 0 < κ := by dsimp [κ]; positivity
      have hκ1 : 1 ≤ κ := by
        have hdiv : 1 ≤ N ^ (2 : ℝ) / M :=
          (le_div_iff₀ hMpos).2 (by simpa using hMup)
        have hηpow : 1 ≤ P ^ η := Real.one_le_rpow hP hη.le
        dsimp [κ]
        exact one_le_mul_of_one_le_of_one_le hdiv hηpow
      have hηpowUpper : P ^ η ≤ M / (2 * N) := by
        apply (le_div_iff₀ (by positivity)).2
        calc
          P ^ η * (2 * N) = 2 * N * P ^ η := by ring
          _ ≤ M := hcutoff
      have hκleN : κ ≤ N := by
        dsimp [κ]
        have hNpow2 : N ^ (2 : ℝ) = N ^ 2 := Real.rpow_natCast N 2
        rw [hNpow2]
        have hdivnonneg : 0 ≤ N ^ 2 / M := by positivity
        calc
          N ^ 2 / M * P ^ η ≤ N ^ 2 / M * (M / (2 * N)) :=
            mul_le_mul_of_nonneg_left hηpowUpper hdivnonneg
          _ = N / 2 := by
            field_simp [ne_of_gt hMpos, ne_of_gt hNpos] <;> ring
          _ ≤ N := by nlinarith
      have hκleM : κ ≤ M := hκleN.trans hNM
      have hNκ : N * κ ≤ P := by
        calc
          N * κ ≤ N * M := mul_le_mul_of_nonneg_left hκleM hNpos.le
          _ = P := by dsimp [P]; ring
      have hNdivM : N / M ≤ 1 := (div_le_one hMpos).2 hNM
      have hbasic : N ^ (2 * α) / M ^ α = B * (N / M) := by
        have hNshift : N ^ (2 * α) = N ^ (2 * α - 1) * N := by
          calc
            N ^ (2 * α) = N ^ ((2 * α - 1) + 1) :=
              congrArg (fun x : ℝ => N ^ x) (by ring)
            _ = N ^ (2 * α - 1) * N := by rw [Real.rpow_add hNpos, Real.rpow_one]
        have hMshift : (M ^ α)⁻¹ = M ^ (1 - α) / M := by
          rw [← Real.rpow_neg hMpos.le, show (-α : ℝ) = (1 - α) - 1 by ring,
            Real.rpow_sub hMpos, Real.rpow_one]
        calc
          N ^ (2 * α) / M ^ α = N ^ (2 * α) * (M ^ α)⁻¹ := by rw [div_eq_mul_inv]
          _ = (N ^ (2 * α - 1) * N) * (M ^ α)⁻¹ := by rw [hNshift]
          _ = B * (N / M) := by rw [hMshift]; dsimp [B]; ring
      have hκpowEq : κ ^ α = B * (N / M) * P ^ (η * α) := by
        unfold κ
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.div_rpow (by positivity) hMpos.le,
          ← Real.rpow_mul hNpos.le, ← Real.rpow_mul hPpos.le, hbasic]
      have hκpow : κ ^ α ≤ B * P ^ (η * α) := by
        rw [hκpowEq]
        calc
          B * (N / M) * P ^ (η * α) ≤ B * 1 * P ^ (η * α) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hNdivM hB) (by positivity)
          _ = B * P ^ (η * α) := by ring
      have hmidFactor : 1 ≤ P ^ (η * α) :=
        Real.one_le_rpow hP (mul_nonneg hη.le (by linarith))
      have hmidShape : N + κ ^ α ≤ H * P ^ (η * α) := by
        calc
          N + κ ^ α ≤ N * P ^ (η * α) + B * P ^ (η * α) :=
            add_le_add
              (by simpa using mul_le_mul_of_nonneg_left hmidFactor hNpos.le) hκpow
          _ = (N + B) * P ^ (η * α) := by ring
          _ ≤ H * P ^ (η * α) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            dsimp [H]
            nlinarith [hM]
      have hηα : η * α ≤ 2 * η := by
        calc
          η * α ≤ η * 2 := mul_le_mul_of_nonneg_left hα2 hη.le
          _ = 2 * η := by ring
      have hmidExp : β + η * α ≤ δ := by
        dsimp [β]
        nlinarith [hηα, hηδ8]
      have hmidPower : P ^ β * P ^ (η * α) ≤ P ^ δ := by
        rw [← Real.rpow_add hPpos]
        exact Real.rpow_le_rpow_of_exponent_le hP hmidExp
      have hlowExponent : qsNorm F κ N ≤ C₁ * (N * κ) ^ β * (N + κ ^ α) := by
        calc
          qsNorm F κ N = qsNorm F N κ := qs_norm_symm_M0 F hrf κ N
          _ ≤ C₁ * (N * κ) ^ β * (N + κ ^ α) := hExp N κ hN hκ1
      have hlowPower : (N * κ) ^ β ≤ P ^ β :=
        Real.rpow_le_rpow (by positivity) hNκ (by positivity)
      have hlowProduct : (N * κ) ^ β * (N + κ ^ α) ≤
          P ^ β * (H * P ^ (η * α)) :=
        mul_le_mul hlowPower hmidShape (by positivity) (by positivity)
      have hlowBound : qsNorm F κ N ≤ C₁ * P ^ δ * H := by
        calc
          qsNorm F κ N ≤ C₁ * ((N * κ) ^ β * (N + κ ^ α)) := by
            calc
              _ ≤ C₁ * (N * κ) ^ β * (N + κ ^ α) := hlowExponent
              _ = C₁ * ((N * κ) ^ β * (N + κ ^ α)) := by ring
          _ ≤ C₁ * (P ^ β * (H * P ^ (η * α))) :=
            mul_le_mul_of_nonneg_left hlowProduct hC₁.le
          _ = C₁ * (P ^ β * P ^ (η * α)) * H := by ring
          _ ≤ C₁ * P ^ δ * H := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hmidPower hC₁.le) hH
      have hhigh' : qsHighNorm F W M N κ ≤ C₀ * P ^ δ * H := by
        calc
          qsHighNorm F W M N κ ≤ C₀ * P ^ δ₀ * H := by simpa [P, κ, B, H] using hhighBound
          _ ≤ C₀ * P ^ δ * H := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hP hδ₀leδ) hC₀.le) hH
      have hsplit := qs_row_split_B F W hW M N κ hMpos hκpos.le
      have hcoef : C₁ + C₀ ≤ C := by
        dsimp [C]
        have hpos : 0 ≤ 2 * C₁ + C₁ * (2 : ℝ) ^ q + 1 := by positivity
        linarith
      calc
        qsNorm F M N ≤ qsNorm F κ N + qsHighNorm F W M N κ := hsplit
        _ ≤ C₁ * P ^ δ * H + C₀ * P ^ δ * H := add_le_add hlowBound hhigh'
        _ = (C₁ + C₀) * P ^ δ * H := by ring
        _ ≤ C * P ^ δ * H := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef (by positivity)) hH

/-- B1 (IMPL; numeric core `monotone_threshold_improvement`): the recursion and monotonicity
(`qs_norm_mono_M0`) give `HasExponent (2 - 1/α)` (`M' = max(M, N^{2-1/α})`). -/
theorem qs_boot_step_B1 (F : QSFamily m qS) (α : ℝ) (hα1 : 1 ≤ α)
    (hrec : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ N → N ≤ M →
      qsNorm F M N ≤ C * (M * N) ^ δ * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) :
    QSHasExponent F (2 - 1 / α) := by
  intro ε hε
  let β : ℝ := 2 - 1 / α
  have hαpos : 0 < α := by linarith
  have hinv : 0 < 1 / α := by positivity
  have hinv_le : 1 / α ≤ 1 := (div_le_one hαpos).2 hα1
  have hβ1 : 1 ≤ β := by dsimp [β]; linarith
  have hβ2 : β ≤ 2 := by dsimp [β]; linarith [hinv]
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, hrec'⟩ := hrec δ hδ
  refine ⟨3 * C, by positivity, ?_⟩
  intro M N hM hN
  let M' : ℝ := max M (N ^ β)
  have hNpow : N ≤ N ^ β := by
    calc
      N = N ^ (1 : ℝ) := by simp
      _ ≤ N ^ β := Real.rpow_le_rpow_of_exponent_le hN hβ1
  have hNM' : N ≤ M' := by
    dsimp [M']
    exact hNpow.trans (le_max_right _ _)
  have hMM' : M ≤ M' := by dsimp [M']; exact le_max_left _ _
  have hM'1 : 1 ≤ M' := le_trans hM hMM'
  have hMN1 : 1 ≤ M * N := by nlinarith
  have hMle : M ≤ (M * N) ^ (2 : ℝ) := by
    calc
      M ≤ M * N := by nlinarith
      _ ≤ (M * N) ^ (2 : ℝ) := Real.self_le_rpow_of_one_le hMN1 (by norm_num)
  have hNβle : N ^ β ≤ (M * N) ^ (2 : ℝ) := by
    calc
      N ^ β ≤ N ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hβ2
      _ ≤ (M * N) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
  have hM'le : M' ≤ (M * N) ^ (2 : ℝ) := by
    dsimp [M']
    exact max_le hMle hNβle
  have hlen : M' * N ≤ (M * N) ^ (3 : ℝ) := by
    calc
      M' * N ≤ (M * N) ^ (2 : ℝ) * N :=
        mul_le_mul_of_nonneg_right hM'le (by positivity)
      _ ≤ (M * N) ^ (2 : ℝ) * (M * N) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = (M * N) ^ (3 : ℝ) := by
        calc
          (M * N) ^ (2 : ℝ) * (M * N) =
              (M * N) ^ (2 : ℝ) * (M * N) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (M * N) ^ ((2 : ℝ) + 1) := by rw [Real.rpow_add (by positivity)]
          _ = (M * N) ^ (3 : ℝ) := by congr 1 <;> norm_num
  have hpow : (M' * N) ^ δ ≤ (M * N) ^ ε := by
    calc
      (M' * N) ^ δ ≤ ((M * N) ^ (3 : ℝ)) ^ δ :=
        Real.rpow_le_rpow (by positivity) hlen (by positivity)
      _ = (M * N) ^ ε := by
        rw [← Real.rpow_mul (by positivity)]
        congr 1
        dsimp [δ]
        ring
  let q : ℝ := α - 1
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hExp : 2 * α - 1 = β * q + β := by
    dsimp [β, q]
    field_simp [hαpos.ne']
    ring
  have hqpow : N ^ (β * q) ≤ (M' : ℝ) ^ q := by
    calc
      N ^ (β * q) = (N ^ β) ^ q := by rw [Real.rpow_mul (by positivity)]
      _ ≤ M' ^ q := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hq
  have hhigh : N ^ (2 * α - 1) * M' ^ (1 - α) ≤ N ^ β := by
    have hM'pos : 0 < M' := lt_of_lt_of_le zero_lt_one hM'1
    have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
    have hpowNeg : M' ^ (1 - α) = (M' ^ q)⁻¹ := by
      rw [show (1 - α : ℝ) = -q by dsimp [q]; ring, Real.rpow_neg (le_of_lt hM'pos)]
    rw [hExp, Real.rpow_add hNpos, hpowNeg]
    calc
      N ^ (β * q) * N ^ β * (M' ^ q)⁻¹ =
          N ^ β * (N ^ (β * q) / M' ^ q) := by ring
      _ ≤ N ^ β * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one (Real.rpow_pos_of_pos hM'pos q)).2 hqpow
      _ = N ^ β := by ring
  have hshape : M' + N + N ^ (2 * α - 1) * M' ^ (1 - α) ≤ 3 * M' := by
    have hM'β : N ^ β ≤ M' := by dsimp [M']; exact le_max_right _ _
    have hhigh' := hhigh.trans hM'β
    nlinarith [hNM', hhigh']
  have hM'sum : M' ≤ M + N ^ β := by
    dsimp [M']
    exact max_le (le_add_of_nonneg_right (by positivity))
      (le_add_of_nonneg_left (by positivity))
  have hrecBound := hrec' M' N hN hNM'
  have hbound : qsNorm F M N ≤ (3 * C) * (M * N) ^ ε * (M + N ^ β) := by
    calc
      qsNorm F M N ≤ qsNorm F M' N := qs_norm_mono_M0 F hMM' le_rfl
      _ ≤ C * (M' * N) ^ δ * (M' + N + N ^ (2 * α - 1) * M' ^ (1 - α)) := hrecBound
      _ ≤ C * (M' * N) ^ δ * (3 * M') :=
        mul_le_mul_of_nonneg_left hshape (by positivity)
      _ ≤ C * (M * N) ^ ε * (3 * (M + N ^ β)) := by
        calc
          C * (M' * N) ^ δ * (3 * M') ≤
              C * (M * N) ^ ε * (3 * M') := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow hC.le) (by positivity)
          _ ≤ C * (M * N) ^ ε * (3 * (M + N ^ β)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hM'sum (by norm_num)) (by positivity)
      _ = (3 * C) * (M * N) ^ ε * (M + N ^ β) := by ring
  calc
    qsNorm F M N ≤ (3 * C) * (M * N) ^ ε * (M + N ^ β) := hbound
    _ = (3 * C) * (M * N) ^ ε * (M + N ^ (2 - 1 / α)) := by simp [β]

/-- B2 (IMPL): the iteration `α₀ = 2`, `α_{j+1} = 2 - 1/α_j = 1 + 1/(j+2)` (M2, recursion,
B1; `exponent_step`). -/
theorem qs_exponent_iteration_B2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) :
    ∀ j : ℕ, QSHasExponent F (1 + 1 / ((j : ℝ) + 1)) := by
  intro j
  induction j with
  | zero =>
      convert qs_hasExponent_two_M2 F hrf hqS using 1 <;> norm_num
  | succ j ih =>
      let α : ℝ := 1 + 1 / ((j : ℝ) + 1)
      have hden : 0 < (j : ℝ) + 1 := by positivity
      have hα1 : 1 < α := by
        dsimp [α]
        have hrecip : 0 < 1 / ((j : ℝ) + 1) := by positivity
        linarith
      have hα2 : α ≤ 2 := by
        dsimp [α]
        have hden1 : 1 ≤ (j : ℝ) + 1 := by
          have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        have hfrac : 1 / ((j : ℝ) + 1) ≤ 1 := (div_le_one hden).2 hden1
        linarith
      have hrec := qs_upTo_recursion_B F hrf hqS α hα1 hα2 ih
      have hnext := qs_boot_step_B1 F α (by linarith) hrec
      have hindex : (2 - 1 / α : ℝ) = 1 + 1 / (((j + 1 : ℕ) : ℝ) + 1) := by
        dsimp [α]
        push_cast
        field_simp
        ring
      rw [← hindex]
      exact hnext

/-- B2 (IMPL): the sharp core bound: choose `j` with `1/(j+1) < ε/4`; then
`N^{α_j} ≤ N (MN)^{ε/4}`. -/
theorem qs_core_large_sieve_B2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) :
    QSCoreBound F := by
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_gt (4 / ε - 1)
  have hj' : 4 / ε < (j : ℝ) + 1 := by
    have hjr : 4 / ε - 1 < (j : ℝ) := by exact_mod_cast hj
    linarith
  have hden : 0 < (j : ℝ) + 1 := by positivity
  have hsmall : 1 / ((j : ℝ) + 1) < ε / 4 := by
    rw [div_lt_iff₀ hden]
    have hmul := (div_lt_iff₀ hε).mp hj'
    nlinarith
  obtain ⟨C, hC, hhas⟩ := qs_exponent_iteration_B2 F hrf hqS j (ε / 2) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  have hMN : 1 ≤ M * N := by nlinarith
  have hMNpos : 0 < M * N := lt_of_lt_of_le zero_lt_one hMN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ (1 / ((j : ℝ) + 1)) ≤ (M * N) ^ (ε / 4) := by
    calc
      N ^ (1 / ((j : ℝ) + 1)) ≤ N ^ (ε / 4) :=
        Real.rpow_le_rpow_of_exponent_le hN hsmall.le
      _ ≤ (M * N) ^ (ε / 4) :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
  have hNalpha : N ^ (1 + 1 / ((j : ℝ) + 1)) ≤
      N * (M * N) ^ (ε / 4) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hfactor : 1 ≤ (M * N) ^ (ε / 4) :=
    Real.one_le_rpow hMN (by positivity)
  have hshape : M + N ^ (1 + 1 / ((j : ℝ) + 1)) ≤
      (M + N) * (M * N) ^ (ε / 4) := by
    calc
      M + N ^ (1 + 1 / ((j : ℝ) + 1)) ≤
          M * (M * N) ^ (ε / 4) + N * (M * N) ^ (ε / 4) := by
        apply add_le_add
        · simpa using mul_le_mul_of_nonneg_left hfactor (by linarith : 0 ≤ M)
        · exact hNalpha
      _ = (M + N) * (M * N) ^ (ε / 4) := by ring
  have hcombined : (M * N) ^ (ε / 2) * (M * N) ^ (ε / 4) ≤ (M * N) ^ ε := by
    rw [← Real.rpow_add hMNpos]
    apply Real.rpow_le_rpow_of_exponent_le hMN
    norm_num
    linarith
  calc
    qsNorm F M N ≤ C * (M * N) ^ (ε / 2) *
        (M + N ^ (1 + 1 / ((j : ℝ) + 1))) := hhas M N hM hN
    _ ≤ C * (M * N) ^ (ε / 2) *
        ((M + N) * (M * N) ^ (ε / 4)) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ ≤ C * (M + N) * (M * N) ^ ε := by
      have hnonneg : 0 ≤ C * (M + N) := by positivity
      calc
        C * (M * N) ^ (ε / 2) * ((M + N) * (M * N) ^ (ε / 4)) =
            (C * (M + N)) * ((M * N) ^ (ε / 2) * (M * N) ^ (ε / 4)) := by ring
        _ ≤ (C * (M + N)) * (M * N) ^ ε := mul_le_mul_of_nonneg_left hcombined hnonneg
        _ = C * (M + N) * (M * N) ^ ε := by ring

end ArtinPrimitiveRoots.A2
