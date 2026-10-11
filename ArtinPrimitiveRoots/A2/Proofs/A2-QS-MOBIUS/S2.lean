import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S1
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2

/-!
# A2-QS-MOBIUS, part S2: the full error tuple of one residual pair

Insert
`qs_coprime_square_pieces_P2` into both low kernels of `qs_squarefree_removal_S1`.  In the
guide's names: `E₁ = dual highDiv`, `E₂ = dual res`, `E₃ = dual trans`, `E₄ = orig highDiv`,
`E₀ = orig res`, `E₅ = orig trans`; the main terms are kept as the signed difference
`dual main − orig main` (C1).  Cutoffs: original `Z/Λ ≤ ΛZ`, dual `r/(2Λ) ≤ 2Λr` (`Λ ≥ 1`).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

private theorem qs_norm_pos_of_ne_zero_S2 (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < qsN I := by
  have h := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_of_ne_zero hI)
  exact_mod_cast h

private theorem qs_divisor_ne_zero_S2 (q e : Ideal (𝓞 K)) (hq : q ≠ ⊥)
    (he : e ∈ qsDivisors q) : e ≠ ⊥ := by
  classical
  intro he0
  have hdiv := (Finset.mem_filter.mp he).2
  rcases hdiv with ⟨u, hu⟩
  apply hq
  rw [he0] at hu
  simpa using hu

private theorem qs_cutoff_order_S2 (x y : ℝ) (hx : 0 < x) (hy : 1 ≤ y) :
    x / y ≤ y * x := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hy2 : 1 ≤ y ^ 2 := by
    have h := mul_le_mul hy hy (by norm_num) hypos.le
    simpa [pow_two] using h
  apply (div_le_iff₀ hypos).2
  calc
    x = 1 * x := by ring
    _ ≤ y ^ 2 * x := mul_le_mul_of_nonneg_right hy2 hx.le
    _ = (y * x) * y := by ring

private theorem qs_orig_kernel_piece_expansion_S2 [IsTotallyComplex K]
    (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ Λ : ℝ) (hM : 0 < M) (hΛ : 1 ≤ Λ)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮0 : 𝔮 ≠ ⊥) (hcd0 : c * d ≠ ⊥) :
    qsOrigKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫) F W M κ Λ 𝔮 c d =
      qsOrigKernel (qsInnerMain K) F W M κ Λ 𝔮 c d -
        qsOrigKernel (qsInnerHighDiv K) F W M κ Λ 𝔮 c d +
        qsOrigKernel (qsInnerRes K) F W M κ Λ 𝔮 c d +
        qsOrigKernel (qsInnerTrans K) F W M κ Λ 𝔮 c d +
        qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d := by
  classical
  let A := qsSqfUpTo κ 𝔮
  have hF : IsQSSquareWeight K (fun y => (W (y ^ 2) : ℂ)) :=
    ⟨fun x => (W x : ℂ), hW.1, Or.inl rfl⟩
  have h𝔫0 : 𝔮 * (c * d) ≠ (⊥ : Ideal (𝓞 K)) := mul_ne_zero h𝔮0 hcd0
  unfold qsOrigKernel
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have ha0 : a ≠ ⊥ := (Finset.mem_filter.mp ha).2.1
  have hNa : 0 < qsN a := qs_norm_pos_of_ne_zero_S2 a ha0
  let Z := Real.sqrt (M / qsN a)
  have hZ : 0 < Z := Real.sqrt_pos.2 (div_pos hM hNa)
  have hYZ := qs_cutoff_order_S2 Z Λ hZ hΛ
  have hP2 := qs_coprime_square_pieces_P2 (K := K)
    (fun y => (W (y ^ 2) : ℂ)) hF Z hZ (𝔮 * (c * d)) h𝔫0
    (Z / Λ) (Λ * Z) hYZ
  have hweighted := congrArg (fun z : ℂ => (qsPairChar F c d).idealValue a * z) hP2
  calc
    (qsPairChar F c d).idealValue a *
        qsCoprimeSq (fun y => (W (y ^ 2) : ℂ)) Z (𝔮 * (c * d)) =
      (qsPairChar F c d).idealValue a *
        (qsInnerMain K (fun y => (W (y ^ 2) : ℂ)) Z (𝔮 * (c * d)) (Z / Λ) (Λ * Z) -
          qsInnerHighDiv K (fun y => (W (y ^ 2) : ℂ)) Z (𝔮 * (c * d)) (Z / Λ) (Λ * Z) +
          qsInnerRes K (fun y => (W (y ^ 2) : ℂ)) Z (𝔮 * (c * d)) (Z / Λ) (Λ * Z) +
          qsInnerTrans K (fun y => (W (y ^ 2) : ℂ)) Z (𝔮 * (c * d)) (Z / Λ) (Λ * Z) +
          qsInnerTail K (fun y => (W (y ^ 2) : ℂ)) Z (𝔮 * (c * d)) (Z / Λ) (Λ * Z)) := by
            simpa [Z] using hweighted
    _ = _ := by ring

private theorem qs_dual_kernel_piece_expansion_S2 [IsTotallyComplex K]
    (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ Λ n : ℝ) (hM : 0 < M) (hΛ : 1 ≤ Λ) (hn : 0 < n)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮0 : 𝔮 ≠ ⊥) (hcd0 : c * d ≠ ⊥) :
    qsDualKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫) F W M κ Λ n 𝔮 c d =
      qsDualKernel (qsInnerMain K) F W M κ Λ n 𝔮 c d -
        qsDualKernel (qsInnerHighDiv K) F W M κ Λ n 𝔮 c d +
        qsDualKernel (qsInnerRes K) F W M κ Λ n 𝔮 c d +
        qsDualKernel (qsInnerTrans K) F W M κ Λ n 𝔮 c d +
        qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d := by
  classical
  let A := qsSqfUpTo κ (⊤ : Ideal (𝓞 K))
  let E := qsDivisors 𝔮
  have hF : IsQSSquareWeight K
      (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) :=
    ⟨fun x => (W x : ℂ), hW.1, Or.inr rfl⟩
  have he0 (e : Ideal (𝓞 K)) (he : e ∈ E) : e ≠ ⊥ :=
    qs_divisor_ne_zero_S2 𝔮 e h𝔮0 he
  have hInner (e : Ideal (𝓞 K)) (he : e ∈ E) :
      (∑ a ∈ A, (qsPairChar F c d).idealValue a *
        qsCoprimeSq (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
          (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)) =
      (∑ a ∈ A, (qsPairChar F c d).idealValue a *
        qsInnerMain K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
          (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
          (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
          (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) -
      (∑ a ∈ A, (qsPairChar F c d).idealValue a *
        qsInnerHighDiv K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
          (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
          (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
          (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) +
      (∑ a ∈ A, (qsPairChar F c d).idealValue a *
        qsInnerRes K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
          (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
          (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
          (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) +
      (∑ a ∈ A, (qsPairChar F c d).idealValue a *
        qsInnerTrans K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
          (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
          (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
          (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) +
      (∑ a ∈ A, (qsPairChar F c d).idealValue a *
        qsInnerTail K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
          (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
          (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
          (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have ha0 : a ≠ ⊥ := (Finset.mem_filter.mp ha).2.1
    have heN : 0 < qsN e := qs_norm_pos_of_ne_zero_S2 e (he0 e he)
    have haN : 0 < qsN a := qs_norm_pos_of_ne_zero_S2 a ha0
    have hcdN : 0 < qsN (c * d) := qs_norm_pos_of_ne_zero_S2 (c * d) hcd0
    let Z := Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))
    let X := Real.sqrt (qsN e * n ^ 2 / (M * qsN a))
    have hZ : 0 < Z := Real.sqrt_pos.2
      (div_pos (mul_pos heN hcdN) (mul_pos hM haN))
    have hX : 0 < X := Real.sqrt_pos.2
      (div_pos (mul_pos heN (sq_pos_of_pos hn)) (mul_pos hM haN))
    have hY := qs_cutoff_order_S2 X (2 * Λ) hX (by nlinarith [hΛ])
    have hP2 := qs_coprime_square_pieces_P2 (K := K)
      (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) hF Z hZ (c * d) hcd0
      (X / (2 * Λ)) (2 * Λ * X) hY
    have hweighted := congrArg (fun z : ℂ => (qsPairChar F c d).idealValue a * z) hP2
    calc
      (qsPairChar F c d).idealValue a *
          qsCoprimeSq (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) Z (c * d) =
        (qsPairChar F c d).idealValue a *
          (qsInnerMain K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) Z (c * d)
              (X / (2 * Λ)) (2 * Λ * X) -
            qsInnerHighDiv K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) Z (c * d)
              (X / (2 * Λ)) (2 * Λ * X) +
            qsInnerRes K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) Z (c * d)
              (X / (2 * Λ)) (2 * Λ * X) +
            qsInnerTrans K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) Z (c * d)
              (X / (2 * Λ)) (2 * Λ * X) +
            qsInnerTail K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) Z (c * d)
              (X / (2 * Λ)) (2 * Λ * X)) := by
                simpa [Z, X] using hweighted
      _ = _ := by ring
  unfold qsDualKernel
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  let coeff := (qsMu e : ℂ) * (qsPairChar F c d).idealValue e *
    ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ)
  have hi := hInner e he
  calc
    coeff * (∑ a ∈ A, (qsPairChar F c d).idealValue a *
        qsCoprimeSq (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
          (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)) =
      coeff * ((∑ a ∈ A, (qsPairChar F c d).idealValue a *
          qsInnerMain K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
            (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
            (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
            (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) -
        (∑ a ∈ A, (qsPairChar F c d).idealValue a *
          qsInnerHighDiv K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
            (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
            (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
            (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) +
        (∑ a ∈ A, (qsPairChar F c d).idealValue a *
          qsInnerRes K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
            (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
            (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
            (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) +
        (∑ a ∈ A, (qsPairChar F c d).idealValue a *
          qsInnerTrans K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
            (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
            (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
            (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a)))) +
        (∑ a ∈ A, (qsPairChar F c d).idealValue a *
          qsInnerTail K (fun y => qsTransform K (fun x => (W x : ℂ)) (y ^ 2))
            (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a))) (c * d)
            (Real.sqrt (qsN e * n ^ 2 / (M * qsN a)) / (2 * Λ))
            (2 * Λ * Real.sqrt (qsN e * n ^ 2 / (M * qsN a))))) := by
              exact congrArg (fun z : ℂ => coeff * z) hi
    _ = _ := by ring

/-- S2 (IMPL): the exact error tuple of one residual pair. -/
theorem qs_pair_error_tuple_S2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ Λ n : ℝ) (hM : 0 < M) (hΛ : 1 ≤ Λ) (hn : 0 < n)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮) (h𝔮bad : qsBadRad m qS ∣ 𝔮)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d) (hcd1 : c * d ≠ ⊤)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hc𝔮 : IsCoprime c 𝔮) (hd𝔮 : IsCoprime d 𝔮) :
    qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) =
      (qsDualKernel (qsInnerMain K) F W M κ Λ n 𝔮 c d -
          qsOrigKernel (qsInnerMain K) F W M κ Λ 𝔮 c d)
        - qsDualKernel (qsInnerHighDiv K) F W M κ Λ n 𝔮 c d
        + qsDualKernel (qsInnerRes K) F W M κ Λ n 𝔮 c d
        + qsDualKernel (qsInnerTrans K) F W M κ Λ n 𝔮 c d
        + qsOrigKernel (qsInnerHighDiv K) F W M κ Λ 𝔮 c d
        - qsOrigKernel (qsInnerRes K) F W M κ Λ 𝔮 c d
        - qsOrigKernel (qsInnerTrans K) F W M κ Λ 𝔮 c d
        + (qsDualKernel (qsInnerTail K) F W M κ Λ n 𝔮 c d
            - qsOrigKernel (qsInnerTail K) F W M κ Λ 𝔮 c d
            + qsDualHighKernel F W M κ 𝔮 c d) := by
  have hcd0 : c * d ≠ ⊥ := mul_ne_zero hc.1.ne_zero hd.1.ne_zero
  have hq0 : 𝔮 ≠ ⊥ := h𝔮.ne_zero
  have hS1 := qs_squarefree_removal_S1 F hrf hqS W hW M κ Λ n hM
    𝔮 c d h𝔮 h𝔮bad hc hd hcd hcd1 hcl hc𝔮 hd𝔮
  have hdual := qs_dual_kernel_piece_expansion_S2 F W hW M κ Λ n hM hΛ hn
    𝔮 c d hq0 hcd0
  have horig := qs_orig_kernel_piece_expansion_S2 F W hW M κ Λ hM hΛ
    𝔮 c d hq0 hcd0
  calc
    qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) =
        qsDualKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫) F W M κ Λ n 𝔮 c d +
          qsDualHighKernel F W M κ 𝔮 c d -
            qsOrigKernel (fun G Z 𝔫 _ _ => qsCoprimeSq G Z 𝔫) F W M κ Λ 𝔮 c d := hS1
    _ = _ := by rw [hdual, horig]; ring

end ArtinPrimitiveRoots.A2
